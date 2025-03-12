#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

proc opposite(t: TagId): TagId =
  if t == JeT: JneT
  elif t == JneT: JeT
  elif t == JzT: JnzT
  elif t == JnzT: JzT
  elif t == JgT: JngT
  elif t == JgeT: JngeT
  elif t == JngeT: JgeT
  elif t == JaT: JnaT
  elif t == JnaT: JaeT
  elif t == JaeT: JnaeT
  elif t == JnaeT: JaT
  else: NopT

proc jumpToPutInstr(t: TagId): TagId =
  # negation is not a bug here!
  if t == JeT: SetneT
  elif t == JneT: SeteT
  elif t == JzT: SetnzT
  elif t == JnzT: SetzT
  elif t == JgT: SetngT
  elif t == JgeT: SetngeT
  elif t == JngeT: SetgeT
  elif t == JaT: SetnaT
  elif t == JnaT: SetaT
  elif t == JaeT: SetnaeT
  elif t == JnaeT: SetaeT
  else: NopT

proc emitDataRaw(c: var GeneratedCode; loc: Location) =
  c.addSym pool.syms[loc.data], NoLineInfo

proc emitImmediate*(c: var GeneratedCode; ival: int) =
  c.genIntLit ival, NoLineInfo

proc emitLoc*(c: var GeneratedCode; loc: Location) =
  case loc.kind
  of Undef:
    assert false, "location should have been set"
  of ImmediateInt:
    c.genIntLit loc.ival, NoLineInfo
  of ImmediateUInt:
    c.genUIntLit loc.uval, NoLineInfo
  of ImmediateFloat:
    c.genFloatLit loc.fval, NoLineInfo
  of InReg:
    c.addKeywUnchecked regName(loc.reg1)
  of InRegFp:
    c.addKeywUnchecked regName(loc.regf)
  of InFlag:
    assert false, "not implemented"
  of JumpMode:
    c.addIdent "L." & $loc.label, NoLineInfo
  of InData:
    c.buildTree RelT:
      c.emitDataRaw loc
  of InTextSection:
    c.emitDataRaw loc
  of InTls:
    c.buildTree FsT:
      c.emitDataRaw loc
  of InRegOffset:
    c.buildTree Mem2T:
      c.addKeywUnchecked regName(loc.reg1)
      c.genIntLit loc.typ.offset, NoLineInfo
  of InRegRegScaledOffset:
    if loc.typ.offset == 0:
      c.buildTree Mem3T:
        c.addKeywUnchecked regName(loc.reg1)
        c.addKeywUnchecked regName(loc.reg2)
        c.genIntLit loc.typ.size, NoLineInfo
    else:
      c.buildTree Mem4T:
        c.addKeywUnchecked regName(loc.reg1)
        c.addKeywUnchecked regName(loc.reg2)
        c.genIntLit loc.typ.size, NoLineInfo
        c.genIntLit loc.typ.offset, NoLineInfo

proc genx(c: var GeneratedCode; n: var Cursor; dest: var Location)

proc gen(c: var GeneratedCode; n: var Cursor): Location =
  result = Location(kind: Undef)
  genx c, n, result

proc makeReg(c: var GeneratedCode; x: Location; opc = MovT): Location =
  if x.kind != InReg:
    result = scratchReg(c.rega, x.typ)
    if result.kind == Undef:
      c.buildTree MovT:
        c.buildTree Mem2T:
          c.addKeyw RspT
          c.genIntLit getScratchStackSlot(c.rega), NoLineInfo
        c.addKeyw RcxT   # Rcx is as good as any other
      result = Location(typ: x.typ, kind: InReg, reg1: Rcx, flags: {Reg1NeedsPop})
    c.buildTree opc:
      emitLoc c, result
      emitLoc c, x
  else:
    result = x

proc genForceReg(c: var GeneratedCode; n: var Cursor): Location =
  result = Location(kind: Undef)
  genx c, n, result
  result = makeReg(c, result)

proc freeTemp(c: var GeneratedCode; loc: Location) =
  if Reg1NeedsPop in loc.flags:
    assert(Reg1Temp notin loc.flags, "pushed reg must not be marked as temporary")
    c.buildTree MovT:
      c.addKeyw RcxT
      c.buildTree Mem2T:
        c.addKeyw RspT
        c.genIntLit getScratchStackSlot(c.rega), NoLineInfo
    # KEEP THE REGISTER MARKED AS "USED"! Do not call `freeTempRaw` here!
  else:
    freeTempRaw c.rega, loc

proc combine(c: var GeneratedCode; a, b: Location; opc: TagId) =
  # x86 has no Mem-Mem operations for ALU operations, so instead of
  # Mem[a] + Mem[b] we need to produce `mov reg, Mem[b]; Mem[a] + reg`
  # We need a scratch register to accomplish that. If we have no available
  # we push&pop a used register.
  if invalidCombination(a, b):
    let tmp = makeReg(c, b)
    c.buildTree opc:
      emitLoc c, a
      emitLoc c, tmp
    c.freeTemp tmp
  else:
    c.buildTree opc:
      emitLoc c, a
      emitLoc c, b

proc genMov(c: var GeneratedCode; dest, src: Location) =
  if sameLocation(dest, src):
    discard "don't generate `mov rax, rax` etc"
  elif Indirect in src.flags:
    c.buildTree MovT:
      c.emitLoc dest
      c.emitLoc src
  elif dest.typ.kind == AFloat:
    c.buildTree MovapdT:
      c.emitLoc dest
      c.emitLoc src
  elif src.kind == InFlag:
    if dest.kind == JumpMode:
      c.buildTree src.flag:
        c.emitLoc dest
    else:
      assert dest.kind != InFlag
      c.buildTree jumpToPutInstr(src.flag):
        c.emitLoc dest
  elif dest.typ.size < 0'i32 or dest.typ.size > 8'i32:
    assert dest.typ.size > 0'i32, "size not set!"
    assert false, "implement rep byte copy loop"
  elif invalidCombination(dest, src):
    let tmp = makeReg(c, src)
    c.buildTree MovT:
      emitLoc c, dest
      emitLoc c, tmp
    c.freeTemp tmp
  elif src.kind == InData:
    c.buildTree LeaT:
      c.emitLoc dest
      c.emitLoc src
  else:
    c.buildTree MovT:
      c.emitLoc dest
      c.emitLoc src

proc into(c: var GeneratedCode; dest: var Location; src: Location) =
  if dest.kind == Undef:
    dest = src
  elif dest.kind == InFlag and src.kind == InFlag and dest.flag == NopT:
    dest.flag = src.flag
  else:
    genMov c, dest, src

#[
proc genCall(c: var GeneratedCode; n: var Cursor; dest: var Location) =
  var args: seq[NodePos] = @[] # so that we can also do it backwards
  for ch in sonsFromX(n): args.add ch

  let sig = asProcType(t, getType(c.m, n.firstSon).rawPos)
  var stackSpace = HomeSpace
  var argTypes: seq[AsmSlot] = @[]
  if t[sig.params].kind == ParamsC:
    for param in sons(t, sig.params):
      let p = asParamDecl(t, param)
      argTypes.add c.typeToSlot(p.typ)
  # can happen for varargs:
  for i in argTypes.len ..< args.len:
    argTypes.add c.getAsmSlot(args[i])

  # we use this "RegAllocator" here only to compute the where the
  # expressions need to end up:
  var regb = initRegAllocator()
  if t[sig.returnType].kind in {VoidC, Empty}:
    discard "no return type"
  else:
    let ts = c.typeToSlot(sig.returnType)
    var dummy = default(Location)
    allocResultWin64(regb, ts, dummy)
  var argLocs: seq[Location] = @[]
  for argType in argTypes:
    argLocs.add regb.allocParamWin64(argType)
  reverseStackParamsWin64 argLocs

  for i in 0 ..< args.len:
    genx c, t, args[i], argLocs[i]

  let fn = gen(c, n.firstSon)
  c.buildTreeI CallT, t[n].info:
    c.emitLoc fn

  if t[sig.returnType].kind in {VoidC, Empty}:
    discard "no return type"
  else:
    let ts = c.typeToSlot(sig.returnType)
    stackSpace += stackSpaceResultWin64(ts)
    if dest.kind == Undef:
      dest = resultWin64(ts)
    else:
      c.genMov(dest, resultWin64(ts))
]#
const
  AddrTyp = AsmSlot(kind: AInt, size: WordSize, align: WordSize, offset: 0)

from std / math import isPowerOfTwo

proc genMulImm(c: var GeneratedCode; dest: Location; imm: int) =
  if isPowerOfTwo(imm):
    var shift = 0
    var imm = imm
    while imm > 1:
      inc shift
      imm = imm shr 1
    if shift > 0:
      c.buildTree ShlT:
        emitLoc c, dest
        emitImmediate c, shift
  else:
    c.buildTree MulT:
      emitLoc c, dest
      emitImmediate c, imm

proc ensureTempReg(c: var GeneratedCode; loc: Location): Location =
  if loc.kind == InReg and Reg1Temp in loc.flags:
    result = loc
  else:
    result = scratchReg(c.rega, loc.typ)
    if result.kind == Undef:
      c.buildTree MovT:
        c.buildTree Mem2T:
          c.addKeyw RspT
          c.genIntLit getScratchStackSlot(c.rega), NoLineInfo
        c.addKeyw RcxT   # Rcx is as good as any other
      result = Location(typ: loc.typ, kind: InReg, reg1: Rcx, flags: {Reg1NeedsPop})
    c.buildTree MovT:
      c.addKeyw RcxT
      emitLoc c, loc


proc genAddr(c: var GeneratedCode; n: var Cursor; dest: var Location) =
  let info = n.info
  case n.exprKind
  of NoExpr:
    if n.kind == Symbol:
      let lit = n.symId
      let def = c.m.defs.getOrDefault(lit)
      case def.kind
      of ProcY:
        let d = Location(typ: AddrTyp, kind: InTextSection, data: lit)
        into c, dest, d
      of VarY, ParamY:
        let d = c.locals[lit]
        assert d.kind == InRegOffset and d.reg1 in {Rsp, Rsp2},
          "attempt to use addr() of a variable not in the stack"
        into c, dest, d
      of GvarY, ConstY:
        let d = c.globals[lit]
        into c, dest, d
      of TvarY:
        let d = c.globals[lit]
        into c, dest, d
      of EfldY:
        assert false, "enum fields not implemented"
      else:
        error c.m, "undeclared identifier: ", n
  of DerefC:
    # genx means "produce value"
    inc n
    genx c, n, dest
    when false:
      let tmp = genForceReg(c, n)
      assert(not tmp.indirect)
      c.buildTreeI Mem1T, n.info:
        c.emitLoc tmp
      c.freeTemp tmp
  of AtC, PatC:
    inc n
    var arrType = getType(c.m, n)
    var a = n
    skip n
    
    var loc = Location(kind: Undef)
    genAddr(c, a, loc)
    loc.typ = c.typeToSlot arrType
    assert loc.kind != Undef
    let idx = genForceReg(c, n)
    # materialize complex addressing:
    case loc.kind:
    of InRegRegScaledOffset:
      loc = makeReg(c, loc, LeaT)
    of InReg, InRegOffset:
      discard "nothing to do"
    of InData, InTls:
      loc = makeReg(c, loc, LeaT)
    else:
      error c.m, "BUG: overly complex address computation A: ", n

    case loc.kind
    of InReg, InRegOffset:
      if loc.typ.size in [1, 2, 4, 8]:
        loc.kind = InRegRegScaledOffset
        loc.reg2 = idx.reg1
        if Reg1NeedsPop in idx.flags:
          loc.flags.incl Reg2NeedsPop
        elif Reg1Temp in idx.flags:
          loc.flags.incl Reg2Temp
      else:
        let idx = ensureTempReg(c, idx)
        genMulImm c, idx, loc.typ.size
        loc.kind = InRegRegScaledOffset
        loc.typ.size = 1 # scale is unused
        if Reg1NeedsPop in idx.flags:
          loc.flags.incl Reg2NeedsPop
        else:
          loc.flags.incl Reg2Temp
        loc.reg2 = idx.reg1
    else:
      error c.m, "BUG: overly complex address computation B: ", n
    # we computed an address, so this must be reflected:
    loc.flags.incl Indirect
    into c, dest, loc

  of DotC:
    inc n
    var loc = Location(kind: Undef)
    genAddr(c, n, loc) #  obj
    var fld = n # fld
    skip n # _

    let field = fld.symId
    let ftyp = c.fields[field]

    case loc.kind
    of InReg, InRegOffset:
      loc.kind = InRegOffset
      loc.typ.offset += ftyp.offset
    of InRegRegScaledOffset:
      loc.typ.offset += ftyp.offset
    of InData, InTls:
      loc = makeReg(c, loc, LeaT)
      loc.kind = InRegOffset
      loc.typ.offset += ftyp.offset
    else:
      error c.m, "BUG: overly complex address computation C: ", n

    # we computed an address, so this must be reflected:
    loc.flags.incl Indirect
    into c, dest, loc
  else:
    error c.m, "expected expression but got: ", n

proc genLoad(c: var GeneratedCode; dest: var Location; address: Location) =
  if dest.kind == Undef:
    dest = scratchReg(c.rega, address.typ)
  # XXX Floating point? What if it doesn't even fit a register?

  let opc = if address.typ.kind == AFloat: MovapdT else: MovT
  c.buildTree opc:
    emitLoc c, dest
    c.buildTree Mem1T:
      emitLoc c, address

proc genAsgn(c: var GeneratedCode; n: var Cursor) =
  inc n
  var a = n
  skip n
  var b = n
  # special case local variables as these can be in registers
  # which have no address:
  if a.kind == Symbol:
    let lit = a.symId
    let def = c.m.defs.getOrDefault(lit)
    if def.kind in {VarY, ParamY}:
      let d = c.locals[lit]

      let y = gen(c, b)
      genMov c, d, y
      freeTemp c, y
      return
  var d = Location(kind: Undef)
  genAddr c, a, d

  var y = gen(c, b)
  if y.inMemory:
    y = c.makeReg(y)

  # XXX also handle case kind == AMem!
  let opc = if d.typ.kind == AFloat: MovapdT else: MovT
  c.buildTree opc:
    emitLoc c, d
    emitLoc c, y
  freeTemp c, y

proc genLvalue(c: var GeneratedCode; n: var Cursor; dest: var Location) =
  case n.exprKind
  of NoExpr:
    if n.kind == Symbol:
      let lit = n.symId
      let def = c.m.defs.getOrDefault(n.symId)
      case def.kind
      of ProcY:
        let d = Location(typ: AddrTyp, kind: InTextSection, data: lit)
        into c, dest, d
      of VarY, ParamY:
        let d = c.locals[lit]
        if d.kind in {InRegOffset, InRegRegScaledOffset}:
          assert d.reg1 in {Rsp, Rsp2}
          genLoad c, dest, d
        else:
          into c, dest, d
      of GvarY, ConstY:
        let d = c.globals[lit]
        genLoad c, dest, d
      of TvarY:
        let d = c.globals[lit]
        genLoad c, dest, d
      # of EfldS:
      #   assert false, "enum fields not implemented"
      else:
        error c.m, "undeclared identifier: ", n
  # of DerefC, AtC, PatC, DotC:
    # var d = Location(kind: Undef)
    # genAddr c, n, d
    # genLoad c, dest, d
  else:
    error c.m, "expected expression but got: ", n

proc genStrLit(c: var GeneratedCode; s: string; info: PackedLineInfo; dest: var Location) =
  var id = c.strings.getOrDefault(s, -1)
  var symId: string
  if id < 0:
    id = c.strings.len + 1
    c.strings[s] = id
    symId = "str." & $id
    c.data.buildTree RodataT, info:
      c.data.addSymDef symId, info
      c.data.buildTree StringT, info:
        c.data.addStrLit s, info
      c.data.buildTree ByteT, info:
        c.data.genIntLit 0, info
  else:
    symId = "str." & $id
  let d = Location(typ: AddrTyp, kind: InData, data: pool.syms.getOrIncl(symId))
  into c, dest, d

proc genFloatLit(c: var GeneratedCode; litId: FloatId; info: PackedLineInfo; dest: var Location) =
  var id = c.floats.getOrDefault(litId, -1)
  let symId: string
  if id < 0:
    id = c.floats.len + 1
    c.floats[litId] = id
    symId = "flt." & $id
    c.data.buildTree RodataT, info:
      c.data.addSymDef symId, info
      c.data.buildTree QuadT, info:
        c.genFloatLit(litId, info)
  else:
    symId = "flt." & $id
  let d = Location(typ: AddrTyp, kind: InData, data: pool.syms.getOrIncl(symId))
  into c, dest, d

#[
proc genConv(c: var GeneratedCode; n: var Cursor; dest: var Location) =
  let (typ, arg) = sons2(n)
  let src = getAsmSlot(c, arg)
  var dest = AsmSlot()
  fillTypeSlot c, typeFromPos(typ), dest
  let info = t[n].info
  var opc: TagId
  if src.size == dest.size:
    opc = ErrT
  elif src.kind == AFloat and dest.kind != AFloat:
    if dest.kind == AInt:
      opc = FtoiT
    else:
      opc = FtouT
  elif dest.kind == AFloat and src.kind != AFloat:
    if src.kind == AInt:
      opc = ItofT
    else:
      opc = UtofT
  elif src.size > dest.size:
    if dest.kind == AFloat:
      opc = FnarrowT
    else:
      opc = TruncT
  else:
    case dest.kind
    of AUInt, AMem, ABool:
      opc = ZextT
    of AInt:
      opc = SextT
    of AFloat:
      opc = FextT

  if opc != ErrT:
    genSlot c, dest, info
    genSlot c, src, info
  genx c, t, arg, WantValue
  if opc != ErrT:
    c.code.addParRi()

proc genFjmp(c: var GeneratedCode; n: var Cursor; jmpTarget: Label; opc = FjmpT) =
  let info = t[n].info
  let k = t[n].kind
  case k
  of ParC:
    genFjmp c, n.firstSon, jmpTarget, opc
  of NotC:
    genFjmp c, n.firstSon, jmpTarget, (if opc == FjmpT: TjmpT else: FjmpT)
  of AndC, OrC:
    if (k == AndC and opc == FjmpT) or
       (k == OrC and opc == TjmpT):
      # easy case
      let (a, b) = sons2(n)
      genFjmp c, t, a, jmpTarget, opc
      genFjmp c, t, b, jmpTarget, opc
    else:
      # "or" case:
      let (a, b) = sons2(n)
      # "if not a: b"
      let neg = (if opc == FjmpT: TjmpT else: FjmpT)
      let lab = getLabel(c)
      genFjmp c, t, a, lab, neg
      genFjmp c, t, b, jmpTarget, opc
      c.buildTree LabT, info:
        c.defineLabel lab, info
  else:
    c.buildTree opc, info:
      genx c, n, WantValue
      c.useLabel jmpTarget, info
]#

type
  CondJmpKind = enum
    Fjmp # jump if the condition is false (the `and` operator)
    Tjmp # jump if the condition is true  (the `or` operator)

proc genCond(c: var GeneratedCode; n: var Cursor; dest: var Location; jk: CondJmpKind) =
  let l1 = getLabel(c)
  inc n
  var a = n
  skip n
  var b = n
  skip n
  skipParRi n

  # tell the pipeline we need the result in a flag:
  var destA = Location(kind: InFlag, flag: NopT)
  genx(c, a, destA)
  assert destA.kind == InFlag
  let opc = if jk == Tjmp: destA.flag else: opposite(destA.flag)
  c.buildTree opc:
    c.useLabel l1, n.info
  genx(c, b, dest)
  c.defineLabel l1, n.info

proc genCmp(c: var GeneratedCode; n: var Cursor; dest: var Location; opc: TagId) =
  var d = Location(kind: InFlag, flag: opc)
  
  inc n
  var a = n
  skip n
  var b = n
  skip n
  skipParRi n

  let x = gen(c, a)
  let y = gen(c, b)
  c.buildTree CmpT:
    emitLoc c, x
    emitLoc c, y
  c.freeTemp y
  c.freeTemp x
  c.into dest, d

proc genDataVal(c: var GeneratedCode; n: var Cursor) =
  let d = gen(c, n)
  emitLoc c, d

proc binArithOp(c: var GeneratedCode; n: var Cursor; dest: var Location; opc: TagId) =
  # let (typ, a, b) = sons3(n)
  inc n
  var typ = n
  skip n
  var a = n
  skip n
  var b = n
  skip n
  skipParRi n




  if dest.kind == Undef:
    # tmp = a + b
    # -->
    # tmp = a
    # tmp += b
    let x = gen(c, a)
    let y = gen(c, b)
    dest = makeReg(c, x, (if x.kind == InRegFp: MovapdT else: MovT))
    c.buildTree opc:
      emitLoc c, dest
      emitLoc c, y
    freeTemp c, y
  else:
    # easy case, we have an explicit dest we can work on directly:
    genx(c, a, dest)
    let y = gen(c, b)
    c.buildTree opc:
      emitLoc c, dest
      emitLoc c, y
    freeTemp c, y

template typedBinOp(opc) =
  binArithOp c, n, dest, opc

#[
proc unArithOp(c: var GeneratedCode; n: var Cursor; dest: var Location; opc: TagId) =
  let (typ, a) = sons2(n)
  if dest.kind == Undef:
    # tmp = a + b
    # -->
    # tmp = a
    # tmp += b
    let x = gen(c, t, a)
    dest = makeReg(c, x, (if x.kind == InRegFp: MovapdT else: MovT))
    c.buildTree opc:
      emitLoc c, dest
  else:
    # easy case, we have an explicit dest we can work on directly:
    genx(c, t, a, dest)
    c.buildTree opc:
      emitLoc c, dest

template typedUnOp(opc) =
  unArithOp c, n, dest, opc
]#
proc immInt(c: var GeneratedCode; n: var Cursor; dest: var Location;
                typ: AsmSlot) =
  let lit = n.intId
  let src = immediateLoc(pool.integers[lit], typ)
  if dest.kind in {InReg, Undef} or
    (src.ival >= low(int32) and src.ival <= high(int32)):
    into c, dest, src
  else:
    let d = makeReg(c, src)
    into c, dest, d

proc immUInt(c: var GeneratedCode; n: var Cursor; dest: var Location;
                typ: AsmSlot) =
  let lit = n.uintId
  let u = pool.uintegers[lit]
  let ival = cast[int64](u)
  let src = immediateLoc(u, typ)
  if dest.kind in {InReg, Undef} or
    (ival >= low(int32) and ival <= high(int32)):
    into c, dest, immediateLoc(ival, typ)
  else:
    let d = makeReg(c, src)
    into c, dest, d

proc immFloat(c: var GeneratedCode; n: var Cursor; dest: var Location;
                typ: AsmSlot) =
  let lit = n.floatId
  genFloatLit c, lit, n.info, dest

proc genSuffix(c: var GeneratedCode; n: var Cursor; dest: var Location) =
  inc n
  var value = n
  skip n
  let suffix = n
  skip n
  skipParRi n

  case value.kind
  of StringLit:
    genx c, value, dest
  of IntLit:
    let typ =
      case pool.strings[suffix.litId]
      of "i64":
        AsmSlot(kind: AInt, size: 8, align: 8)
      of "i32":
        AsmSlot(kind: AInt, size: 4, align: 4)
      of "i16":
        AsmSlot(kind: AInt, size: 2, align: 2)
      of "i8":
        AsmSlot(kind: AInt, size: 1, align: 1)
      else:
        quit "unsupported suffix"
    immInt c, value, dest, typ
  of UIntLit:
    let typ =
      case pool.strings[suffix.litId]
      of "u64":
        AsmSlot(kind: AUInt, size: 8, align: 8)
      of "u32":
        AsmSlot(kind: AUInt, size: 4, align: 4)
      of "u16":
        AsmSlot(kind: AUInt, size: 2, align: 2)
      of "u8":
        AsmSlot(kind: AUInt, size: 1, align: 1)
      else:
        quit "unsupported suffix"
    immUInt c, value, dest, typ
  of FloatLit:
    let typ =
      case pool.strings[suffix.litId]
      of "f64":
        AsmSlot(kind: AFloat, size: 8, align: 8)
      of "f32":
        AsmSlot(kind: AFloat, size: 4, align: 4)
      else:
        quit "unsupported suffix"
    immFloat c, value, dest, typ
  else:
    error c.m, "unsupported suffix ", n

#[
proc genNot(c: var GeneratedCode; n: var Cursor; dest: var Location; jk: CondJmpKind) =
  let neg = if jk == Fjmp: Tjmp else: Fjmp
  case t[n].kind
  of NotC: genNot c, n.firstSon, desneg
  of AndC: genCond c, n, dest, jk
  of OrC: genCond c, n, desneg
  of EqC: genCmp c, n, dest, (if jk == Tjmp: JeT else: JneT)
  of LeC: genCmp c, n, dest, (if jk == Tjmp: JngT else: JgT)
  of LtC: genCmp c, n, dest, (if jk == Tjmp: JngeT else: JgeT)
  of ParC: genNot c, n.firstSon, dest, jk
  else:
    # (not x) == (x xor 1):
    genx c, n, dest
    c.buildTree XorT:
      emitLoc c, dest
      let typ = AsmSlot(kind: AUInt, size: 1, align: 1)
      let one = immediateLoc(1'u64, typ)
      emitLoc c, one
]#
proc genx(c: var GeneratedCode; n: var Cursor, dest: var Location) =
  case n.exprKind
  of NoExpr:
    case n.kind
    of IntLit:
      let typ = AsmSlot(kind: AInt, size: WordSize, align: WordSize)
      immInt c, n, dest, typ
      inc n
    of UIntLit:
      let typ = AsmSlot(kind: AUInt, size: WordSize, align: WordSize)
      immUInt c, n, dest, typ
      inc n
    of FloatLit:
      let typ = AsmSlot(kind: AFloat, size: WordSize, align: WordSize)
      immFloat c, n, dest, typ
      inc n
    of CharLit:
      let typ = AsmSlot(kind: AUInt, size: 1, align: 1)
      let ch = uint64 n.charLit
      let d = immediateLoc(ch, typ)
      into c, dest, d
      inc n
    of StringLit:
      genStrLit(c, pool.strings[n.litId], n.info, dest)
      inc n
    else:
      genLvalue c, n, dest
  of FalseC:
    let typ = AsmSlot(kind: AUInt, size: 1, align: 1)
    let d = immediateLoc(0'u64, typ)
    into c, dest, d
  of TrueC:
    let typ = AsmSlot(kind: AUInt, size: 1, align: 1)
    let d = immediateLoc(1'u64, typ)
    into c, dest, d  
  of NilC:
    let typ = AsmSlot(kind: AUInt, size: WordSize, align: WordSize)
    let d = immediateLoc(0'u64, typ)
    into c, dest, d
  # of AconstrC:
  #   if c.inConst > 0:
  #     for ch in sonsFromX(n):
  #       c.genDataVal t, ch
  #   else:
  #     error c.m, "runtime array constructor not implemented: ", n
  # of OconstrC:
  #   if c.inConst > 0:
  #     for ch in sonsFromX(n):
  #       if t[ch].kind == OconstrC:
  #         # Inheritance
  #         c.genDataVal t, ch
  #       else:
  #         let (_, v) = sons2(t, ch)
  #         c.genDataVal t, v
  #   else:
  #     error c.m, "runtime object constructor not implemented: ", n
  of ParC:
    inc n
    genx c, n, dest
  # of AddrC:
  #   genAddr c, n.firstSon, dest
  # of SizeofC:
  #   # we evaluate it at compile-time:
  #   let a = typeToSlot(c, n.firstSon)
  #   let typ = AsmSlot(kind: AUInt, size: WordSize, align: WordSize)
  #   let d = immediateLoc(uint(a.size), typ)
  #   into c, dest, d
  # of AlignofC:
  #   # we evaluate it at compile-time:
  #   let a = typeToSlot(c, n.firstSon)
  #   let typ = AsmSlot(kind: AUInt, size: WordSize, align: WordSize)
  #   let d = immediateLoc(uint(a.align), typ)
  #   into c, dest, d
  # of OffsetofC:
  #   let (obj, fld) = sons2(n)
  #   let field = t[fld].litId
  #   let ftyp = c.fields[field]
  #   let typ = AsmSlot(kind: AUInt, size: WordSize, align: WordSize)
  #   let d = immediateLoc(uint(ftyp.offset), typ)
  #   into c, dest, d
  # of CallC: genCall c, n, dest
  of AddC: typedBinOp AddT
  of SubC: typedBinOp SubT
  of MulC: typedBinOp ImulT
  of DivC: typedBinOp IdivT
  of ModC: typedBinOp IdivT # FIXME
  of ShlC: typedBinOp ShlT
  of ShrC: typedBinOp ShrT
  of BitandC: typedBinOp AndT
  of BitorC: typedBinOp OrT
  of BitxorC: typedBinOp XorT
  # of BitnotC: typedUnOp NotT
  # of NegC: typedUnOp NegT
  of AndC: genCond c, n, dest, Fjmp
  of OrC: genCond c, n, dest, Tjmp
  of EqC: genCmp c, n, dest, JneT
  of LeC: genCmp c, n, dest, JgT
  of LtC: genCmp c, n, dest, JgeT
  # of NotC: genNot c, n.firstSon, dest, Tjmp
  #of CastC, ConvC:
  #  genConv c, n
  of SufC:
    genSuffix(c, n, dest)
  of InfC, NegInfC, NanC:
    # TODO:
    discard
  else:
    genLvalue c, n, dest
