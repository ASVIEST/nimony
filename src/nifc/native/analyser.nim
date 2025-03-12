#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Collect useful information for a native code generator.

import std / [assertions, syncio, tables, sets, intsets, strutils]

import bitabs, nifstreams, nifcursors
import .. / nifc_model

import slots

## Records how often every local variable is used
## and whether its address has been taken.

type
  VarInfo* = object
    defs*, usages*: int # how often the variable is defined&used.
    weight*: int # similar to `usages` but takes into consideration
                 # whether the variable is used within a loop.
    props*: set[VarProp]

  ProcBodyProps* = object
    vars*: Table[SymId, VarInfo]
    inlineStructs*: bool # candidate for struct inlining
    hasCall*: bool

  Scope = object
    vars: seq[SymId]
    hasCall: bool

  Context = object
    inLoops, inAddr, inAsgnTarget, inArrayIndex: int
    res: ProcBodyProps
    scopes: seq[Scope]

proc openScope(c: var Context) =
  c.scopes.add Scope()

proc closeScope(c: var Context) =
  let finished = c.scopes.pop()
  if not finished.hasCall:
    for v in finished.vars:
      c.res.vars[v].props.incl AllRegs
  else:
    assert c.scopes.len > 0
    # a scope has a call if some inner scope has a call:
    c.scopes[^1].hasCall = true

const
  LoopWeight = 3 # assume that the usual loop runs 3 times. This is used
                 # to make the register allocator keep variables that are
                 # used in loops more important.

proc analyseVarUsages(c: var Context; n: var Cursor) =
  # Step 1. Analyse variable usages.
  if n.kind == DotToken:
    inc n
  
  case n.stmtkind
  of StmtsS, ScopeS:
    c.openScope()
    inc n
    while n.kind != ParRi: 
      analyseVarUsages(c, n)
    c.closeScope()
    inc n
  of VarS, GvarS, TvarS, ConstS:
    let v = takeVarDecl(n)
    assert v.name.kind == SymbolDef
    let lit = v.name.symId
    let hasValue = v.value.kind != DotToken
    c.res.vars[lit] = VarInfo(defs: ord(hasValue))
    c.scopes[^1].vars.add lit
    let oldN = n
    n = v.value
    if hasValue:
      analyseVarUsages(c, n)
    n = oldN
  of CallS, OnErrS:
    inc n
    while n.kind != ParRi:
      analyseVarUsages(c, n)
    c.scopes[^1].hasCall = true
  of AsgnS:
    inc n
    inc c.inAsgnTarget
    analyseVarUsages(c, n)
    dec c.inAsgnTarget
    analyseVarUsages(c, n)
  
  of RetS:
    inc n
    while n.kind != ParRi: 
      analyseVarUsages(c, n)
    inc n
  
  of NoStmt:
    skip n # skip node
  
  elif n.symKind != NoSym:
    let sk = n.symKind
    if sk == ParamY:
      # TODO: join with VarS etc.
      let d = takeParamDecl(n)
      assert d.name.kind == SymbolDef
      let lit = d.name.symId
      c.res.vars[lit] = VarInfo(defs: 1)
      c.scopes[^1].vars.add lit
    else:
      echo "SYM FOUND"
#   
#   #  if n.exprKind != NoExpr:
#     #  case n.exprKind
#     # of IdentC, IntLit, UIntLit, FloatLit, CharLit, StrLit, Err,
#     #    NilC, FalseC, TrueC, SizeofC, AlignofC, OffsetofC, InfC, NegInfC, NanC:
#     #    skip n
#     ## f 
#   else: skip n
  
#   of CallC, OnErrC:
#     # XXX Special case `cold` procs like `raiseIndexError` in order
#     # to produce better code for the common case.
#     for ch in sons(t, n):
#       analyseVarUsages(c, t, ch)
#     c.scopes[^1].hasCall = true
  
#   of ParamC:
#     let v = asParamDecl(t, n)
#     assert t[v.name].kind == SymDef
#     let vn = t[v.name].litId
#     c.res.vars[vn] = VarInfo(defs: 1) # it is a parameter, it has a value
#     c.scopes[^1].vars.add vn
#   of Sym:
#     let vn = t[n].litId
#     if c.res.vars.hasKey(vn):
#       let entry = addr(c.res.vars[vn])
#       if c.inAsgnTarget > 0:
#         inc entry.defs
#       else:
#         inc entry.usages
#       inc entry.weight, c.inLoops*LoopWeight
#       if (c.inAddr + c.inArrayIndex) > 0:
#         # arrays on the stack cannot be in registers either as registers
#         # cannot be aliased!
#         entry.props.incl AddrTaken
#   of EmitC:
#     for ch in sons(t, n):
#       analyseVarUsages(c, t, ch)
#   of WhileC:
#     inc c.inLoops
#     for ch in sons(t, n):
#       analyseVarUsages(c, t, ch)
#     dec c.inLoops
#   of AtC, PatC:
#     let (a, idx) = sons2(t, n)
#     if k == AtC: inc c.inArrayIndex
#     analyseVarUsages(c, t, a)
#     if k == AtC: dec c.inArrayIndex
#     # don't pessimize array indexes:
#     let oldAddr = c.inAddr
#     let oldTarget = c.inAsgnTarget
#     c.inAddr = 0
#     c.inAsgnTarget = 0
#     analyseVarUsages(c, t, idx)
#     c.inAddr = oldAddr
#     c.inAsgnTarget = oldTarget
#   of DerefC:
#     let oldTarget = c.inAsgnTarget
#     c.inAsgnTarget = 0
#     analyseVarUsages(c, t, n.firstSon)
#     c.inAsgnTarget = oldTarget
#   of AddrC:
#     inc c.inAddr
#     analyseVarUsages(c, t, n.firstSon)
#     dec c.inAddr
#   of DotC:
#     let inStackFrame = t[n.firstSon].kind != DerefC
#     if inStackFrame: inc c.inArrayIndex
#     analyseVarUsages(c, t, n.firstSon)
#     if inStackFrame: dec c.inArrayIndex
#   of AsgnC:
#     let (dest, src) = sons2(t, n)
#     inc c.inAsgnTarget
#     analyseVarUsages(c, t, dest)
#     dec c.inAsgnTarget
#     analyseVarUsages(c, t, src)
#   of ParC, AndC, OrC, NotC, NegC, OconstrC, AconstrC, KvC,
#      AddC, SubC, MulC, DivC, ModC, ShrC, ShlC, BitandC, BitorC, BitxorC, BitnotC,
#      EqC, NeqC, LeC, LtC, CastC, ConvC, RangeC, RangesC, IfC, ElifC, ElseC,
#      BreakC, CaseC, OfC, LabC, JmpC, RetC, ParamsC, DiscardC, TryC:
#     for ch in sons(t, n):
#       analyseVarUsages(c, t, ch)
#   of ProcC, FldC,
#      UnionC, ObjectC, EfldC, EnumC, ProctypeC, AtomicC, RoC, RestrictC,
#      IntC, UIntC, FloatC, CharC, BoolC, VoidC, PtrC, ArrayC, FlexarrayC,
#      APtrC, TypeC, CdeclC, StdcallC, SafecallC, SyscallC, FastcallC, ThiscallC,
#      NoconvC, MemberC, AttrC, InlineC, NoinlineC, VarargsC, WasC, SelectanyC,
#      PragmasC, AlignC, BitsC, VectorC, ImpC, NodeclC, InclC, SufC, RaiseC, ErrsC,
#      RaisesC, ErrC, StaticC:
#     discard "do not traverse these"

proc analyseVarUsages*(n: var Cursor): ProcBodyProps =
  var c = Context()
  c.scopes.add Scope() # there is always one scope
  analyseVarUsages c, n
  c.res.hasCall = c.scopes[0].hasCall
  result = ensureMove(c.res)
