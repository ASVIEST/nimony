#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

##[

Inserts `haddr` and `hderef` nodes for the code generators or analysis passes that
need to care (move analyser, etc.).

Expressions
===========

There are 4 cases:

1. `var T` to `var T` transfer: Nothing to do.
2. `var T` to `T` transfer: Insert HiddenDeref instruction.
3. `T` to `var T` transfer: Insert HiddenAddr instruction.
4. `T` to `T` transfer: Nothing to do.

]##

import std / [assertions]

include nifprelude

import ".." / models / tags
import nimony_model, programs, decls, typenav, sembasics, reporters, renderer, typeprops

type
  Expects = enum
    WantT
    WantTButSkipDeref
    WantVarT
    WantVarTResult
    WantMutableT  # `var openArray` does need derefs but mutable locations regardless
    WantForwarding

  CurrentRoutine = object
    returnExpects: Expects
    firstParam: SymId
    firstParamKind: TypeKind
    resultSym: SymId
    dangerousLocations: seq[(SymId, Cursor)] # Cursor is only used for line information

  Context = object
    dest: TokenBuf
    r: CurrentRoutine
    typeCache: TypeCache

proc takeToken(c: var Context; n: var Cursor) {.inline.} =
  c.dest.add n
  inc n

proc takeParRi(c: var Context; n: var Cursor) =
  if n.kind == ParRi:
    c.dest.add n
    inc n
  else:
    error "expected ')', but got: ", n

proc rootOf(n: Cursor; allowIndirection = false): SymId =
  var n = n
  while true:
    case n.exprKind
    of DotX, AtX, ArrAtX, TupatX, ParX:
      inc n
    of PatX, DdotX:
      # not protected from mutation
      if allowIndirection:
        inc n
      else:
        break
    of DconvX, OconvX:
      inc n
      skip n # skip the type
    else: break
  case n.kind
  of Symbol, SymbolDef:
    result = n.symId
  else:
    result = NoSymId

proc isAddressable*(n: Cursor): bool =
  ## Addressable means that we can take the address of the expression.
  let s = rootOf(n, allowIndirection = true)
  if s != NoSymId:
    let res = tryLoadSym(s)
    assert res.status == LacksNothing
    let local = asLocal(res.decl)
    result = local.kind in {ParamY, LetY, ResultY, VarY, CursorY, ConstY, GletY, TletY, GvarY, TvarY}
    # Assignments to `ConstY` are prevented later.
  else:
    result = false

proc tr(c: var Context; n: var Cursor; e: Expects)

proc trSons(c: var Context; n: var Cursor; e: Expects) =
  if n.kind != ParLe:
    takeToken c, n
  else:
    takeToken c, n
    while n.kind != ParRi:
      tr c, n, e
    takeParRi c, n

proc validBorrowsFrom(c: var Context; n: Cursor): bool =
  # --------------------------------------------------------------------------
  # We need to borrow from a location that is derived from the proc's
  # first parameter.
  # --------------------------------------------------------------------------
  var n = n
  var someIndirection = false
  while true:
    case n.exprKind
    of DotX, AtX, ArrAtX, TupatX, ParX:
      inc n
    of HderefX, HaddrX, DerefX, AddrX, DdotX, PatX:
      inc n
      someIndirection = true
    of DconvX, OconvX, ConvX, CastX:
      inc n
      skip n # skip the type
    of ExprX:
      inc n
      while true:
        if isLastSon(n): break
        skip n
    of CallKinds:
      inc n
      let fn = n
      skip n # skip the `fn`
      if n.kind != ParRi:
        var fnType = skipProcTypeToParams(getType(c.typeCache, fn))
        assert fnType == "params"
        inc fnType
        let firstParam = asLocal(fnType)
        if firstParam.kind == ParamY:
          let mightForward = firstParam.typ.typeKind in {MutT, OutT, LentT}
          if not mightForward:
            someIndirection = true
        # borrowing only work from first parameters:
        discard "n already at the correct position"
      else:
        break
    else:
      break
  if n.kind == Symbol:
    let res = tryLoadSym(n.symId)
    assert res.status == LacksNothing
    # XXX Is this check really reliable for local symbols
    # that are not guaranteed to be unique?
    if res.decl == "param" and n.symId == c.r.firstParam:
      # There is a difference between
      # proc forward(x: var int): var int = x
      # and
      # proc access(x: Table): var int = x[].field[0]
      # and we do not try to hide it!
      result = c.r.firstParamKind in {MutT, OutT, LentT} or someIndirection
    else:
      result = false
  else:
    result = false

proc borrowsFromReadonly(c: var Context; n: Cursor): bool =
  var n = n
  while true:
    case n.exprKind
    of DotX, AtX, ArrAtX, TupatX, ParX:
      inc n
    of DconvX, HconvX, ConvX, CastX:
      inc n
      skip n
    of CallKinds:
      inc n
      skip n # skip the `fn`
      if n.kind != ParRi:
        # borrowing only work from first parameters:
        discard "n already at the correct position"
      else:
        break
    else:
      break
  if n.kind == Symbol:
    let res = tryLoadSym(n.symId)
    assert res.status == LacksNothing
    let local = asLocal(res.decl)
    case local.kind
    of ConstY:
      result = true
    of LetY, GletY, TletY:
      let tk = local.typ.typeKind
      result = tk notin {MutT, OutT, LentT}
      if result and isViewType(local.typ):
        # Special rule to make `toOpenArray` work:
        result = borrowsFromReadonly(c, local.val)
    of VarY, GvarY, TvarY:
      result = local.typ.typeKind == LentT
    of ParamY:
      result = local.typ.typeKind notin {MutT, OutT, LentT}
    else:
      result = false
  elif n.kind in {StringLit, IntLit, UIntLit, FloatLit, CharLit} or
       n.exprKind in {SufX, OconstrX, NewobjX, AconstrX}:
    result = true
  else:
    result = false

proc isResultUsage(c: Context; n: Cursor): bool {.inline.} =
  result = false
  if n.kind == Symbol:
    result = n.symId == c.r.resultSym

proc trReturn(c: var Context; n: var Cursor) =
  takeToken c, n
  if isResultUsage(c, n):
    takeTree c.dest, n
  else:
    let err = c.r.returnExpects == WantVarTResult and not validBorrowsFrom(c, n)
    if err:
      buildLocalErr(c.dest, n.info, "cannot borrow from " & asNimCode(n))
    else:
      tr c, n, c.r.returnExpects
  takeParRi c, n

proc trYield(c: var Context; n: var Cursor) =
  takeToken c, n
  tr c, n, WantForwarding # c.r.returnExpects
  takeParRi c, n

proc mightBeDangerous(c: var Context; n: Cursor) =
  let root = rootOf(n)
  if root != NoSymId:
    for d in items(c.r.dangerousLocations):
      if d[0] == root:
        buildLocalErr c.dest, n.info, "cannot mutate " & asNimCode(n) &
          "; binding created here: " & infoToStr(d[1].info)

proc checkForDangerousLocations(c: var Context; n: var Cursor) =
  template recurse =
    while n.kind != ParRi:
      checkForDangerousLocations c, n

  if isDeclarative(n):
    skip n
  elif n.stmtKind == AsgnS:
    inc n
    mightBeDangerous(c, n)
    recurse()
  elif n.exprKind in CallKinds:
    inc n # skip `(call)`
    let orig = n
    var fnType = skipProcTypeToParams(getType(c.typeCache, n))
    skip n # skip `fn`
    assert fnType == "params"
    inc fnType
    while n.kind != ParRi:
      let previousFormalParam = fnType
      let param = takeLocal(fnType, SkipFinalParRi)
      let pk = param.typ.typeKind
      if pk in {MutT, OutT, LentT}:
        mightBeDangerous(c, n)
      elif pk == VarargsT:
        # do not advance formal parameter:
        fnType = previousFormalParam
      skip n
    n = orig
    recurse()
  elif n.kind == ParLe:
    recurse()

proc trProcDecl(c: var Context; n: var Cursor) =
  c.typeCache.openScope()
  takeToken c, n
  let symId = n.symId
  var isGeneric = false
  var r = CurrentRoutine(returnExpects: WantT)
  for i in 0..<BodyPos:
    if i == TypevarsPos:
      isGeneric = n.substructureKind == TypevarsU
    if i == ParamsPos:
      c.typeCache.registerParams(symId, n)
      var params = n
      inc params
      let firstParam = asLocal(params)
      if firstParam.kind == ParamY:
        r.firstParam = firstParam.name.symId
        r.firstParamKind = firstParam.typ.typeKind

    if i == ResultPos and n.typeKind in {MutT, OutT, LentT}:
      r.returnExpects = WantVarTResult
    takeTree c.dest, n
  if isGeneric:
    takeTree c.dest, n
    takeParRi c, n
  else:
    swap c.r, r
    var body = n
    trSons c, n, r.returnExpects
    if c.r.dangerousLocations.len > 0:
      checkForDangerousLocations c, body
    swap c.r, r
    takeParRi c, n
  c.typeCache.closeScope()

proc trCallArgs(c: var Context; n: var Cursor; fnType: Cursor) =
  var fnType = skipProcTypeToParams(fnType)
  assert fnType == "params"
  inc fnType
  while n.kind != ParRi:
    var e = WantT
    let previousFormalParam = fnType
    let param = takeLocal(fnType, SkipFinalParRi)
    var pk = param.typ.typeKind
    if pk in {MutT, LentT}:
      var elemType = param.typ
      inc elemType
      if isViewType(elemType):
        e = WantMutableT
      else:
        e = WantVarT
    elif pk == OutT:
      e = WantVarT
    elif pk == VarargsT:
      # do not advance formal parameter:
      fnType = previousFormalParam
    tr c, n, e

proc firstArgIsMutable(c: var Context; n: Cursor): bool =
  assert n.exprKind in CallKinds
  var n = n
  inc n
  if n.kind != ParRi:
    result = not borrowsFromReadonly(c, n)
  else:
    result = false

proc cannotPassToVar(dest: var TokenBuf; info: PackedLineInfo; arg: Cursor) =
  let msg = "cannot pass " & asNimCode(arg) & " to var/out T parameter"
  when defined(debug):
    writeStackTrace()
    echo infoToStr(info) & " Error: " & msg
    quit msg
  dest.buildTree ErrT, info:
    dest.addSubtree arg
    dest.add strToken(pool.strings.getOrIncl(msg), info)

proc wantMutable(e: Expects): bool {.inline.} =
  e in {WantVarT, WantVarTResult, WantMutableT}

proc trCall(c: var Context; n: var Cursor; e: Expects; dangerous: var bool) =
  let info = n.info
  let callExpr = n

  var callBuf = createTokenBuf()

  swap c.dest, callBuf
  takeToken c, n
  let fnType = skipProcTypeToParams(getType(c.typeCache, n))
  assert fnType == "params"
  tr c, n, WantT # `fn` part of the call
  var retType = fnType
  skip retType

  var needHderef = false
  if retType.typeKind in {MutT, LentT}:
    if e == WantT:
      needHderef = true
      trCallArgs(c, n, fnType)
      takeParRi c, n
    elif e in {WantVarTResult, WantTButSkipDeref} or firstArgIsMutable(c, callExpr):
      trCallArgs(c, n, fnType)
      takeParRi c, n
    elif not dangerous:
      # DANGER-ZONE HERE! Consider: `for d in items(a)` where `a` is immutable.
      # Which is turned to `var d: var T = a[i]`.
      # Wether we can allow this or not depends on whether `d` is used later on for mutations!
      # Thus we mark the binding as "dangerous". In a second pass we then look for the pattern
      # `passedToVar(d)` or `d[] = value` and flag them as errornous.
      dangerous = true
      trCallArgs(c, n, fnType)
      takeParRi c, n
    else:
      cannotPassToVar c.dest, info, callExpr
      skipToEnd n
  elif e.wantMutable:
    if isViewType(retType) and firstArgIsMutable(c, callExpr):
      trCallArgs(c, n, fnType)
      takeParRi c, n
    else:
      cannotPassToVar c.dest, info, callExpr
      skipToEnd n
  else:
    trCallArgs(c, n, fnType)
    takeParRi c, n

  swap c.dest, callBuf
  if needHderef and c.dest[c.dest.len-1].tag != TagId(HderefTagId):
    c.dest.addParLe(HderefX, info)
    c.dest.add callBuf
    c.dest.addParRi()
  else:
    c.dest.add callBuf

proc trAsgnRhs(c: var Context; le: Cursor; ri: var Cursor; e: Expects) =
  if ri.exprKind in CallKinds:
    var dangerous = false
    trCall c, ri, e, dangerous
    if dangerous:
      let s = rootOf(le)
      if s != NoSymId:
        c.r.dangerousLocations.add (s, ri)
  else:
    tr c, ri, e

type
  LvalueStatus = enum
    Valid
    InvalidBorrow
    LocationIsConst

proc trAsgn(c: var Context; n: var Cursor) =
  takeToken c, n
  var e = WantT
  var err = Valid
  let le = n
  if isResultUsage(c, le):
    e = c.r.returnExpects
    if e == WantVarTResult:
      tr c, n, e
      if not validBorrowsFrom(c, n):
        err = InvalidBorrow
    else:
      tr c, n, e
  elif borrowsFromReadonly(c, n):
    err = LocationIsConst
  else:
    tr c, n, e
  case err
  of InvalidBorrow:
    buildLocalErr c.dest, n.info, "cannot borrow from " & asNimCode(n)
    skip n
  of LocationIsConst:
    buildLocalErr c.dest, n.info, "cannot mutate expression " & asNimCode(n)
    tr c, n, e
    tr c, n, e
  else:
    trAsgnRhs c, le, n, e
  takeParRi c, n

proc trLocation(c: var Context; n: var Cursor; e: Expects) =
  # Idea: A variable like `x` does not own its value as it can be read multiple times.
  let typ = getType(c.typeCache, n)
  let k = typ.typeKind
  if k in {MutT, OutT, LentT}:
    if e.wantMutable:
      # Consider `fvar(returnsVar(someLet))`: We must not allow this.
      if borrowsFromReadonly(c, n):
        cannotPassToVar c.dest, n.info, n
        skip n
      else:
        trSons c, n, WantT
    else:
      if (k in {MutT, LentT} and not isViewType(typ.firstSon)) or k == OutT:
        if c.dest[c.dest.len-1].tag == TagId(HderefTagId):
          trSons c, n, WantT
        else:
          c.dest.addParLe(HderefX, n.info)
          trSons c, n, WantT
          c.dest.addParRi()
      else:
        trSons c, n, WantT
  elif e.wantMutable:
    if e == WantVarTResult:
      c.dest.addParLe(HaddrX, n.info)
      if n.kind == Symbol:
        takeToken c, n
      else:
        trSons c, n, WantT
      c.dest.addParRi()
    elif borrowsFromReadonly(c, n):
      cannotPassToVar c.dest, n.info, n
      skip n
    else:
      c.dest.addParLe(HaddrX, n.info)
      trSons c, n, WantT
      c.dest.addParRi()
  else:
    trSons c, n, WantT

proc trLocal(c: var Context; n: var Cursor) =
  let kind = n.symKind
  takeToken c, n
  let name = n
  if kind == ResultY:
    c.r.resultSym = name.symId
  for i in 0..<LocalTypePos:
    takeTree c.dest, n
  let typ = n
  takeTree c.dest, n
  c.typeCache.registerLocal(name.symId, kind, typ)
  let e = if typ.typeKind in {OutT, MutT, LentT}: WantVarT else: WantT
  trAsgnRhs c, name, n, e
  takeParRi c, n

proc trStmtListExpr(c: var Context; n: var Cursor; outerE: Expects) =
  takeToken c, n
  while n.kind != ParRi:
    if isLastSon(n):
      tr c, n, outerE
    else:
      tr c, n, WantT
  takeParRi c, n

proc fieldMode(k: TypeKind; outerE: Expects): Expects {.inline.} =
  if k in {MutT, OutT, LentT}:
    (if outerE == WantForwarding: WantVarTResult else: WantVarT)
  else:
    WantT

proc trObjConstr(c: var Context; n: var Cursor; outerE: Expects) =
  takeToken c, n
  takeTree c.dest, n # type
  while n.kind != ParRi:
    assert n.substructureKind == KvU
    takeToken c, n
    takeTree c.dest, n # key
    let fieldType = getType(c.typeCache, n)
    tr c, n, fieldMode(fieldType.typeKind, outerE)
    takeParRi c, n
  takeParRi c, n

proc trTupleConstr(c: var Context; n: var Cursor; outerE: Expects) =
  takeToken c, n
  var typ = n
  assert typ.typeKind == TupleT
  inc typ
  takeTree c.dest, n # type
  while n.kind != ParRi:
    let fieldType = getTupleFieldType(typ)
    skip typ
    let e = fieldMode(fieldType.typeKind, outerE)
    if n.substructureKind == KvU:
      takeToken c, n
      takeTree c.dest, n # skip key
      tr c, n, e
      takeParRi c, n
    else:
      tr c, n, e
  takeParRi c, n

proc trVarHook(c: var Context; n: var Cursor) =
  takeToken c, n
  tr c, n, WantVarT
  if n.kind != ParRi:
    tr c, n, WantT
  takeParRi c, n

proc tr(c: var Context; n: var Cursor; e: Expects) =
  case n.kind
  of Symbol:
    trLocation c, n, e
  of IntLit, UIntLit, FloatLit, CharLit, StringLit:
    if e.wantMutable:
      # Consider `fvar(returnsVar(someLet))`: We must not allow this.
      cannotPassToVar c.dest, n.info, n
      inc n
    else:
      takeToken c, n
  of UnknownToken, ParRi, EofToken, DotToken, Ident, SymbolDef:
    takeToken c, n
  of ParLe:
    case n.exprKind
    of CallKinds:
      var disallowDangerous = true
      trCall c, n, e, disallowDangerous
    of DotX, DdotX, AtX, ArrAtX, TupatX, PatX:
      trLocation c, n, e
    of OconstrX, NewobjX:
      if e.wantMutable:
        cannotPassToVar c.dest, n.info, n
        skip n
      else:
        trObjConstr c, n, e
    of TupConstrX:
      if e.wantMutable:
        cannotPassToVar c.dest, n.info, n
        skip n
      else:
        trTupleConstr c, n, e
    of ExprX:
      trStmtListExpr c, n, e
    of DconvX, OconvX:
      trSons c, n, WantT
    of ParX:
      trSons c, n, e
    of CopyX, WasMovedX, SinkhX, TraceX:
      trVarHook c, n
    of DupX, DestroyX:
      trSons c, n, WantT
    of HconvX, ConvX, CastX:
      if e.wantMutable:
        cannotPassToVar c.dest, n.info, n
        skip n
      else:
        trSons c, n, WantT

    else:
      case n.stmtKind
      of RetS:
        trReturn(c, n)
      of YldS:
        trYield(c, n)
      of AsgnS:
        trAsgn c, n
      of LocalDecls:
        trLocal c, n
      of ProcS, FuncS, MacroS, MethodS, ConverterS:
        trProcDecl c, n
      of ScopeS:
        c.typeCache.openScope()
        trSons c, n, WantT
        c.typeCache.closeScope()
      else:
        if isDeclarative(n):
          takeTree c.dest, n
        else:
          trSons c, n, WantT

proc injectDerefs*(n: Cursor): TokenBuf =
  var c = Context(typeCache: createTypeCache(),
    r: CurrentRoutine(returnExpects: WantT, firstParam: NoSymId), dest: TokenBuf())
  c.typeCache.openScope()
  var n2 = n
  var n3 = n
  c.takeToken n2
  while n2.kind != ParRi:
    tr(c, n2, WantT)
  if c.r.dangerousLocations.len > 0:
    checkForDangerousLocations(c, n3)
  # Must close the `(stmts)` here **after** `checkForDangerousLocations`
  # because the latter may add error nodes.
  c.dest.addParRi()
  c.typeCache.closeScope()
  result = ensureMove(c.dest)
