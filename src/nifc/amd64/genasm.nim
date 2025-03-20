#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# We produce PreASM code as a list of NIF tokens.

import std / [assertions, syncio, tables, sets, intsets, strutils]
from std / os import changeFileExt, splitFile, extractFilename

import .. / .. / lib / [bitabs, lineinfos, nifstreams, nifcursors]
import ".." / [nifc_model, typenav]
import ".." / native / [slots, analyser]
import asm_model, machine, emitter

type
  Label = distinct int
  TempVar = distinct int

type
  LitId = SymId

  Scope = object
    vars: seq[LitId]

  Section = enum
    Data
    Text
    Init
  
  GeneratedCode* = object
    m: Module
    data: TokenBuf
    code: TokenBuf
    init: TokenBuf
    section: Section
    rega: RegAllocator
    intmSize, inConst, labels, prologAt: int
    loopExits: seq[Label]
    generatedTypes: HashSet[SymId]
    requestedSyms: HashSet[string]
    fields: Table[LitId, AsmSlot]
    types: Table[LitId, AsmSlot]
    locals: Table[LitId, Location]
    strings: Table[string, int]
    floats: Table[FloatId, int]
    scopes: seq[Scope]
    returnLoc: Location
    exitProcLabel: Label
    globals: Table[LitId, Location]

  # LitId = nifc_model.StrId

proc initGeneratedCode*(m: sink Module; intmSize: int): GeneratedCode =
  result = GeneratedCode(m: m, intmSize: intmSize, section: Text)

proc error(m: Module; msg: string; n: Cursor) {.noreturn.} =
  let info = n.info
  if info.isValid:
    let rawInfo = unpack(pool.man, info)
    if rawInfo.file.isValid:
      write stdout, pool.files[rawInfo.file]
      write stdout, "(" & $rawInfo.line & ", " & $(rawInfo.col+1) & ") "
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(n, false)
  when defined(debug):
    echo getStackTrace()
  quit 1

# Atoms

proc tree(c: var GeneratedCode): var TokenBuf {.inline.} =
  case c.section
  of Data: result = c.data
  of Text: result = c.code
  of Init: result = c.init

proc genIntLit(c: var GeneratedCode; litId: IntId; info: PackedLineInfo) =
  c.tree.addIntLit pool.integers[litId], info

proc genIntLit(c: var GeneratedCode; i: BiggestInt; info: PackedLineInfo) =
  c.tree.addIntLit i, info

proc genIntLit(c: var TokenBuf; i: BiggestInt; info: PackedLineInfo) =
  c.addIntLit i, info

proc genUIntLit(c: var GeneratedCode; litId: UintId; info: PackedLineInfo) =
  c.tree.add uintToken(litId, info)

proc genUIntLit(c: var GeneratedCode; i: BiggestUInt; info: PackedLineInfo) =
  let id = pool.uintegers.getOrIncl(i)
  c.tree.add uintToken(id, info)

proc genFloatLit(c: var GeneratedCode; litId: FloatId; info: PackedLineInfo) =
  c.tree.add floatToken(litId, info)

proc genFloatLit(c: var GeneratedCode; i: float; info: PackedLineInfo) =
  let id = pool.floats.getOrIncl(i)
  c.tree.add floatToken(id, info)

proc genCharLit(c: var GeneratedCode; ch: char; info: PackedLineInfo) =
  c.tree.add charToken(ch, info)

proc addIdent(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.tree.add identToken(pool.strings.getOrIncl(s), info)

proc addEmpty(c: var GeneratedCode; info: PackedLineInfo) =
  c.tree.add dotToken(info)

proc addKeyw(c: var GeneratedCode; keyw: TagId; info = NoLineInfo) =
  c.tree.buildTree keyw, info: discard

proc addKeywUnchecked(c: var GeneratedCode; keyw: string; info = NoLineInfo) =
  c.tree.buildTree pool.tags.getOrIncl(keyw), info: discard

proc addSymDef(c: var TokenBuf; s: string; info: PackedLineInfo) =
  c.add symdefToken(pool.syms.getOrIncl(s), info)

proc addSym(c: var GeneratedCode; s: SymId; info: PackedLineInfo) =
  c.tree.add symToken(s, info)

proc addSym(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.tree.add symToken(pool.syms.getOrIncl(s), info)

proc getLabel(c: var GeneratedCode): Label =
  result = Label(c.labels)
  inc c.labels

proc useLabel(c: var GeneratedCode; lab: Label; info: PackedLineInfo) =
  c.addSym "L." & $int(lab), info

proc defineTemp(c: var GeneratedCode; tmp: TempVar; info: PackedLineInfo) =
  c.tree.addSymDef "v." & $int(tmp), info

proc useTemp(c: var GeneratedCode; tmp: TempVar; info: PackedLineInfo) =
  c.addSym "v." & $int(tmp), info

template buildTree(c: var GeneratedCode; keyw: TagId; body: untyped) =
  c.tree.buildTree keyw, NoLineInfo:
    body

template buildTreeI(c: var GeneratedCode; keyw: TagId; info: PackedLineInfo; body: untyped) =
  c.tree.buildTree keyw, info:
    body

proc defineLabel(c: var GeneratedCode; lab: Label; info: PackedLineInfo; opc = LabT) =
  c.tree.buildTree opc, info:
    c.tree.addSymDef "L." & $int(lab), info

# Type graph

include genpreasm_t

# Procs

proc genWas(c: var GeneratedCode; n: var Cursor) =
  skip n # TODO: fix was
  # c.tree.buildTree(CommentT, t[ch].info):
  #  c.addIdent toString(t, ch.firstSon, c.m), t[ch].info

type
  ProcFlag = enum
    isSelectAny, isVarargs

proc genProcPragmas(c: var GeneratedCode; n: var Cursor;
                    flags: var set[ProcFlag]) =
  # ProcPragma ::= (inline) | (noinline) | CallingConvention | (varargs) | (was Identifier) |
  #               (selectany) | Attribute
  if n.kind == DotToken:
    inc n
  elif n.substructureKind == PragmasU:
    inc n
    while n.kind != ParRi:
      case n.pragmaKind
      of NoPragma, AlignP, BitsP, VectorP, NodeclP, StaticP:
        if n.callConvKind != NoCallConv:
          skip n
        else:
          error c.m, "invalid proc pragma: ", n
      of VarargsP:
        flags.incl isVarargs
        skip n
      of SelectanyP:
        flags.incl isSelectAny
        skip n
      of InlineP, AttrP, NoinlineP:
        # Ignore for PreASM
        discard " __attribute__((noinline))"
        skip n
      of WasP: genWas(c, n)
      of ErrsP, RaisesP:
        skip n
    inc n # ParRi
  else:
    error c.m, "expected proc pragmas but got: ", n

proc genSymDef(c: var GeneratedCode; n: Cursor): string =
  if n.kind == SymbolDef:
    let lit = n.symId
    result = pool.syms[lit]
    c.tree.addSymDef result, n.info
  else:
    error c.m, "expected SymbolDef but got: ", n
    result = ""
#[
proc genParamPragmas(c: var GeneratedCode; t: Tree; n: NodePos) =
  # ProcPragma ::= (was Identifier) | Attribute
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of AttrC:
        discard "Ignore for now"
      of WasC:
        genWas c, t, ch
      else:
        error c.m, "invalid pragma: ", t, ch
  else:
    error c.m, "expected pragmas but got: ", t, n

proc genVarPragmas(c: var GeneratedCode; t: Tree; n: NodePos; alignOverride: var int) =
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of AlignC:
        let intId = t[ch.firstSon].litId
        alignOverride = parseInt(c.m.lits.strings[intId])
      of AttrC:
        discard "ignore attribute"
      of WasC:
        genWas c, t, ch
      else:
        error c.m, "invalid pragma: ", t, ch
  else:
    error c.m, "expected pragmas but got: ", t, n
]#

template moveToDataSection(body: untyped) =
  c.section = Data
  body
  c.section = Text

include genasm_e

include register_allocator
include genasm_s

proc genProcDecl(c: var GeneratedCode; n: var Cursor) =
  c.labels = 0 # reset so that we produce nicer code
  c.exitProcLabel = Label(-1)
  var prc = takeProcDecl(n)
  if prc.body.kind == DotToken: return # ignore procs without body
  # (proc SYMBOLDEF Params Type ProcPragmas (OR . StmtList)
  c.openScope() # open scope for the parameters
  c.m.openScope()
  c.rega = initRegAllocator()
  c.buildTreeI TextT, n.info:
    discard genSymDef(c, prc.name)

    c.genProlog()

    if prc.returnType.kind != DotToken:
      let returnSlot = typeToSlot(c, prc.returnType)
      allocResultWin64 c.rega, returnSlot, c.returnLoc

    if prc.params.kind != DotToken:
      var paramTypes: seq[AsmSlot] = @[]
      var paramLocs: seq[Location] = @[]
      var p = prc.params.firstSon
      while p.kind != ParRi:
        var d = takeParamDecl(n)
        if d.name.kind == SymbolDef:
          paramTypes.add typeToSlot(c, d.typ)
          paramLocs.add Location(kind: Undef)
        else:
          error c.m, "expected SymbolDef but got: ", d.name
      
      allocParamsWin64 c.rega, paramTypes, paramLocs
      
      var symDef = 0
      p = prc.params.firstSon
      while p.kind != ParRi:
        var d = takeParamDecl(n)
        if d.name.kind == SymbolDef:
          let lit = d.name.symId
          c.locals[lit] = paramLocs[symDef]
          inc symDef

    var flags: set[ProcFlag] = {}
    genProcPragmas c, prc.pragmas, flags
    allocateVars c, prc.body
    genStmt c, prc.body
    if c.exitProcLabel.int >= 0:
      c.defineLabel(c.exitProcLabel, n.info)
    c.genEpilog()
    c.fixupProlog()
  c.closeScope() # close parameter scope
  c.m.closeScope()

proc genToplevel(c: var GeneratedCode; n: var Cursor) =
  # ExternDecl ::= (imp ProcDecl | VarDecl | ConstDecl)
  # Include ::= (incl StringLiteral)
  # TopLevelConstruct ::= ExternDecl | ProcDecl | VarDecl | ConstDecl |
  #                       TypeDecl | Include | EmitStmt
  case n.stmtKind
  of ImpS:
    discard "ignore imp"
    skip n
  of InclS:
    discard "genInclude c, n"
    skip n
  of ProcS:
    genProcDecl(c, n)
  of VarS: genStmt c, n
  of ConstS: genStmt c, n
  of TypeS:
    discard "handled in a different pass"
    skip n
  of EmitS: genEmitStmt c, n
  else:
    if n.pragmaKind == NodeclP:
      skip n
    else:
      error c.m, "expected top level construct but got: ", n

proc traverseCode(c: var GeneratedCode; n: var Cursor) =
  if n.stmtKind == StmtsS:
    inc n
    while n.kind != ParRi: genToplevel(c, n)
    # missing `inc n` here is intentional
  else:
    error c.m, "expected `stmts` but got: ", n

proc generateAsm*(inp, outp: string) =
  registerTags()
  var c = initGeneratedCode(load(inp), 8)
  
  var co = TypeOrder()
  traverseTypes(c.m, co)
  generateTypes(c, co)

  var n = beginRead(c.m.src)
  traverseCode c, n
  var f = ""
  f.add "(.nif24)\n(stmts"
  f.add toString(c.data)
  f.add toString(c.code)
  f.add ")\n"

  when defined(debug):
    echo f

  if c.init.len > 0:
    quit "no init code implemented"
  produceAsmCode f, outp

when isMainModule:
  # How to test following code:
  # Uncomment registerTags() in produceAsmCode proc in emitter.nim.
  # Produce foobar.s with: nim c -r genasm.nim
  # Assemble and link it with: goo -o foobar foobar.s

  const
    CallPrintf = when defined(windows): """
 (lea
  (rcx)
  (rel str.1))
 (lea
  (rdx)
  (rel str.2))
 (call printf.c)
 (lea
  (rcx)
  (rel str.3))
 (mov
  (rdx) +12)
 (call printf.c)
 (lea
  (rcx)
  (rel str.3))
 (mov
  (rdx)
  (rbx))
 (call printf.c)"""
                 else: """
 (lea
  (rdi)
  (rel str.1))
 (lea
  (rsi)
  (rel str.2))
 (call printf.c)
 (lea
  (rdi)
  (rel str.3))
 (mov
  (rsi) +12)
 (call printf.c)
 (lea
  (rdi)
  (rel str.3))
 (mov
  (rsi)
  (rbx))
 (call printf.c)"""

    TestCode = """(.nif24)
(stmts
(rodata
  :str.1 (string "str.1 %s\0A")
  :str.2 (string "str.2 ")
  :str.3 (string "str.3 value=%d\0A") )
(global main.c)
(text :main.c
 (push (rbp))
 (mov (rbp) (rsp))
 (mov
  (rbx) +12) """ & CallPrintf & """
 (mov
  (rax) +0)
 (jmp L.0)
 (lab :L.0)
 (mov (rsp) (rbp))
 (pop (rbx))
 (ret)))"""

  produceAsmCode TestCode, "foobar.s"
