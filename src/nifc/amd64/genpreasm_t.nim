#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

## Generates PreASM types from NIFC types.

proc mergeBranch(arg: var AsmSlot; value: AsmSlot) =
  arg.offset = max(arg.offset, value.offset)
  arg.align = max(arg.align, value.align)

type
  TypeList = object
    processed: IntSet
    s: seq[Cursor]

proc add(dest: var TypeList; elem: Cursor) =
  if not containsOrIncl(dest.processed, elem.toUniqueId()):
    dest.s.add elem

type
  TypeOrder = object
    ordered: TypeList
    lookedAt: IntSet
    lookedAtBodies: HashSet[SymId]

proc traverseObjectBody(m: Module; o: var TypeOrder; t: Cursor)

proc recordDependency(m: Module; o: var TypeOrder; parent, child: Cursor) =
  var ch = child
  var viaPointer = false
  while true:
    case ch.typeKind
    of APtrT, PtrT:
      viaPointer = true
      ch = elementType(ch)
    of FlexarrayT:
      ch = elementType(ch)
    else:
      break

  case ch.typeKind
  of ObjectT, UnionT:
    let obj = ch
    if viaPointer:
      discard "we know the size of a pointer anyway"
    else:
      if not containsOrIncl(o.lookedAt, obj.toUniqueId()):
        traverseObjectBody(m, o, obj)
      o.ordered.add tracebackTypeC(ch)
  of ArrayT:
    if viaPointer:
      discard "we know the size of a pointer anyway"
    else:
      if not containsOrIncl(o.lookedAt, ch.toUniqueId()):
        traverseObjectBody(m, o, ch)
      o.ordered.add tracebackTypeC(ch)
  of EnumT:
    raiseAssert "Enums is not supported"
  else:
    if ch.kind == Symbol:
      # follow the symbol to its definition:
      let id = ch.symId
      let def = m.defs.getOrDefault(id)
      if def.pos == 0:
        error m, "undeclared symbol: ", ch
      else:
        var n = readonlyCursorAt(m.src, def.pos)
        let decl = asTypeDecl(n)
        
        if not containsOrIncl(o.lookedAtBodies, decl.name.symId):
          recordDependency m, o, n, decl.body
    else:
      discard "uninteresting type as we only focus on the required struct declarations"

proc traverseObjectBody(m: Module; o: var TypeOrder; t: Cursor) =
  var n = t
  inc n
  if n.kind == Symbol:
    # inheritance
    recordDependency m, o, t, n
    inc n
  elif n.kind == DotToken:
    inc n
  else:
    error m, "expected `Symbol` or `.` for inheritance but got: ", n
  while n.substructureKind == FldU:
    let decl = takeFieldDecl(n)
    recordDependency m, o, t, decl.typ

proc traverseTypes(m: Module; o: var TypeOrder) =
  for ch in m.types:
    let n = readonlyCursorAt(m.src, ch)
    let decl = asTypeDecl(n)
    let t = decl.body
    case t.typeKind
    of ObjectT:
      traverseObjectBody m, o, t
    of UnionT:
      traverseObjectBody m, o, t
    of ArrayT:
      traverseObjectBody m, o, t.firstSon
    of ProctypeT:
      o.ordered.add n
    of EnumT:
      # (efld SymbolDef Expr)
      # EnumDecl ::= (enum Type EnumFieldDecl+)
      o.ordered.add n
    else: discard

template integralBits(c: GeneratedCode; t: Cursor): int =
  var n = t
  let res = pool.integers[n.intId]
  case res
  of -1:
    c.intmSize
  else: # 8, 16, 32, 64 etc.
   res

proc genFieldPragmas(c: var GeneratedCode; n: var Cursor;
                     field: var AsmSlot; bits: var BiggestInt) =
  # CommonPragma ::= (align Number) | (was Identifier) | Attribute
  # FieldPragma ::= CommonPragma | (bits Number)
  if n.kind == DotToken:
    inc n
  elif n.substructureKind == PragmasU:
    inc n
    while n.kind != ParRi:
      case n.pragmaKind
      of AlignP:
        field.align = pool.integers[n.intId]
      of WasP, AttrP:
        discard "ignore attributes"
      of BitsP:
        error c.m, "bit sizes fields are not supported: ", n
      else:
        error c.m, "invalid proc type pragma: ", n
  else:
    error c.m, "expected field pragmas but got: ", n

proc fieldName(c: var GeneratedCode; n: Cursor): LitId =
  # TODO: maybe need fix and fieldName as string???
  if n.kind in {Symbol, SymbolDef}:
    result = n.symId
  else:
    result = LitId(0)#"InvalidFieldName"
    error c.m, "field name must be a SymDef, but got: ", n

proc setField(c: var GeneratedCode; name: LitId; obj: AsmSlot; t: var AsmSlot) =
  t.offset = obj.size + (obj.size mod t.align)
  c.fields[name] = t

proc fillTypeSlot(c: var GeneratedCode; n: Cursor; dest: var AsmSlot)

proc genObjectOrUnionBody(c: var GeneratedCode; n: var Cursor;
                   obj: var AsmSlot; isObject: bool) =
  obj.kind = AMem

  inc n
  if n.kind == DotToken:
    inc n
  elif n.kind == Symbol:
    fillTypeSlot c, n, obj
  
  
  while n.kind != ParRi:
    if n.substructureKind == FldU:
      var decl = takeFieldDecl(n)
      let fn = fieldName(c, decl.name)
      var bits = 0'i64
      var f = AsmSlot()
      genFieldPragmas c, decl.pragmas, f, bits
      fillTypeSlot c, decl.typ, f
      setField c, fn, obj, f
      if isObject:
        inc obj.size, f.size
      else:
        # union:
        obj.size = max(obj.size, f.size)
      obj.align = max(obj.align, f.align)
    else:
      error c.m, "expected `fld` but got: ", n
  # padding at object end:
  obj.size = obj.size + (obj.size mod obj.align)

proc inBytes(bits: int): int =
  if bits < 0: 8 # wordsize
  else: bits div 8

proc fillTypeSlot(c: var GeneratedCode; n: Cursor; dest: var AsmSlot) =
  var n = n
  case n.typeKind
  of VoidT:
    error c.m, "internal error: Cannot handle 'void' type: ", n
  of IT:
    inc n
    let bytes = integralBits(c, n).inBytes
    dest = AsmSlot(kind: AInt, size: bytes, align: bytes)
  of UT, CT:
    inc n
    let bytes = integralBits(c, n).inBytes
    dest = AsmSlot(kind: AUInt, size: bytes, align: bytes)
  of FT:
    inc n
    let bytes = integralBits(c, n).inBytes
    dest = AsmSlot(kind: AFloat, size: bytes, align: bytes)
  of BoolT:
    dest = AsmSlot(kind: ABool, size: 1, align: 1)
  of NoType:
    if n.kind == Symbol:
      let id = n.symId
      let def = c.m.defs.getOrDefault(id)
      if def.pos == 0:
        error c.m, "undeclared symbol: ", n
      else:
        if c.types.hasKey(id):
          dest = c.types[id]
        else:
          let n = readonlyCursorAt(c.m.src, def.pos)
          var decl = asTypeDecl(n)
          fillTypeSlot c, decl.body, dest
          c.types[id] = dest
  of PtrT, APtrT, ProctypeT:
    dest = AsmSlot(kind: AUInt, size: c.intmSize, align: c.intmSize)
  of FlexarrayT:
    # Call `elementType` to get the alignment right:
    inc n
    fillTypeSlot c, n, dest
    dest.kind = AMem
    dest.size = 0
  of EnumT:
    var baseType = n.firstSon
    fillTypeSlot c, baseType, dest
  of ArrayT:
    var decl = takeTypeDecl(n)
    var a = decl.body.firstSon
    fillTypeSlot c, a, dest
    dest.kind = AMem
    dest.size *= pool.integers[n.intId] # TODO: uinteger sizes?
  of ObjectT:
    genObjectOrUnionBody c, n, dest, true
  of UnionT:
    genObjectOrUnionBody c, n, dest, false
  else:
    error c.m, "node is not a type: ", n

proc generateTypes(c: var GeneratedCode; o: TypeOrder) =
  for d in o.ordered.s:
    var n = d
    var decl = asTypeDecl(n)

    let litId = decl.name.symId
    if not c.generatedTypes.containsOrIncl(litId):
      var dest = AsmSlot()
      fillTypeSlot c, decl.body, dest
      c.types[litId] = dest

proc getAsmSlot(c: var GeneratedCode; n: Cursor): AsmSlot =
  var t = getType(c.m, n)
  result = AsmSlot()
  fillTypeSlot c, t, result

proc typeToSlot(c: var GeneratedCode; n: Cursor): AsmSlot =
  result = AsmSlot()
  var n = n
  fillTypeSlot c, n, result
