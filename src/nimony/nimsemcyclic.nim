## nimsemcyclic is part of semantic checker that used
## before nimsem. It working for cyclic import group (realy SCC)
## Unfortunately, this requires restarting on the entire SCC,
## but fortunately SCC is usually small (maximum of 3-4 modules)


import std / [parseopt, strutils, assertions, syncio, tables, osproc, deques, algorithm, sets, hashes]
import ".." / lib / [nifstreams, nifcursors, bitabs, lineinfos, nifreader, nifbuilder, tooldirs, nifindexes]
import ".." / nimony / [nimony_model, decls, symtabs, programs, semos, semdata, nifconfig, indexgen]
include sem


proc initSemContext(fileName: string): SemContext =
  let outp = splitModulePath(fileName)
  var moduleFlags: set[ModuleFlag] = {}
  moduleFlags.incl IsMain # TODO: use real moduleFlags
  var config = initNifConfig("")
  semos.setupPaths(config)

  result = SemContext(
    dest: createTokenBuf(),
    types: createBuiltinTypes(),
    thisModuleSuffix: outp.name,
    moduleFlags: moduleFlags,
    g: ProgramContext(config: config),
    phase: SemcheckTopLevelSyms,
    routine: SemRoutine(kind: NoSym),
    # commandLineArgs: commandLineArgs,
    canSelfExec: false, #TODO: check this one
    pending: createTokenBuf(),
    inCyclicGroup: true,
    executeCall: exprexec.executeCall,
    semStmtCallback: semStmtCallback,
    semGetSize: semGetSize)

  for magic in ["typeof", "compiles", "defined", "declared"]:
    result.unoverloadableMagics.incl(pool.strings.getOrIncl(magic))


proc semcheckToplevel(c: var SemContext; n0: Cursor): TokenBuf =
  c.pending.add parLeToken(StmtsS, NoLineInfo)
  c.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  let path = getFile(n0.info) # gets current module path, maybe there is a better way
  addSelfModuleSym(c, path)

  if {SkipSystem, IsSystem} * c.moduleFlags == {}:
    let systemFile = ImportedFilename(path: stdlibFile("std/system"), name: "system", isSystem: true)
    importSingleFile(c, systemFile, "", ImportFilter(kind: ImportAll), n0.info)

  result = phaseX(c, n0, SemcheckTopLevelSyms)
  # c.pending.addParRi()


type
  NodeKind = enum
    nkSymbol
    nkLayout

  Node = object
    s: SymId
    kind: NodeKind

proc hash(x: Node): Hash =
  var h: Hash = 0
  h = h !& hash(x.s)
  h = h !& hash(x.kind)
  !$h

type
  Conditions = object
    evaluated: seq[bool] # is condition already evaluated, index
    evalResults: seq[NimonyExpr]
    nodes: seq[Cursor]
    cursorUids: Table[int, Condition] # node (condition) position to it's Condition
    branchIds: seq[int]

  Condition = object # Same condition can be used for different decls
    id: int          # and shouldn't be evaluated twice
    isNegative: bool

proc `$`(c: Condition): string =
  result = ""
  if c.isNegative:
    result.add "!"
  result.add $c.id

proc store(c: var Conditions, n: Cursor, branchId: int): Condition =
  result = Condition(id: c.evaluated.len, isNegative: false)
  c.evaluated.add false
  c.evalResults.add FalseX
  c.nodes.add n
  c.cursorUids[toUniqueId n] = result
  c.branchIds.add branchId

proc addEvalResult(c: var Conditions, cond: Condition, res: NimonyExpr) =
  c.evaluated[cond.id] = true
  c.evalResults[cond.id] = res

proc makeNegative(cond: var Condition) =
  cond.isNegative = true

proc hasCondition(c: sink Conditions, n: Cursor): bool =
  toUniqueId(n) in c.cursorUids

proc cursorToCondition(c: sink Conditions, n: Cursor): Condition =
  c.cursorUids[toUniqueId n]

proc branchId(c: sink Conditions, cond: Condition): int {.inline.} =
  c.branchIds[cond.id]

type Euler[T] = object
  graph: Table[T, seq[T]]
  order: seq[T]
  subtreeStart, subtreeEnd: Table[T, int]

proc addEdge[T](e: var Euler[T], u, v: T) =
  e.graph.mgetOrPut(u, @[]).add v
  if v notin e.graph: e.graph[v] = @[]

proc euler[T](e: var Euler[T], root: T) =
  var st: seq[tuple[u: T, i: int]] = @[(root, 0)]
  while st.len > 0:
    let (u, i) = st[^1]
    if i == 0:
      e.subtreeStart[u] = e.order.len
      e.order.add u
    let ch = e.graph.getOrDefault(u, @[])
    if i < ch.len:
      st[^1].i = i + 1
      st.add (ch[i], 0)
    else:
      e.subtreeEnd[u] = e.order.len - 1
      discard st.pop()

proc visible[T](e: Euler[T], u: T): seq[T] =
  # If we’re talking about scopes, it should be the first node in the scope that begins the subtree.
  if e.graph.getOrDefault(u, @[]).len == 0: @[u]
  else: e.order[e.subtreeStart[u] .. e.subtreeEnd[u]]

type
  CyclicContext = object
    resolveGraph: Table[Node, seq[Node]]
    semContexts: Table[string, SemContext]
    depsStack: seq[Node] # used to spread decls to inner contexts

    conditions: Conditions
    usedConditions: Table[SymId, seq[Condition]] # what conditions uses symbol
    conditionsStack: seq[Condition] # used to spread conditions to inner contexts
    
    branchesStack: seq[int]
    symBranches: Table[SymId, seq[int]] # when branch (id) associated with symbol
    mergedBranches: Table[string, HashSet[int]]
    whenBranchEuler: Euler[int]
    whenBranchSubtreeStart: Table[int, int] # when branch to first when branch in this scope

proc layoutNode(sym: SymId): Node {.inline.} =
  Node(s: sym, kind: nkLayout)

proc symbolNode(sym: SymId): Node {.inline.} =
  Node(s: sym, kind: nkSymbol)

proc ensureNode(c: var CyclicContext; node: Node) =
  discard c.resolveGraph.hasKeyOrPut(node, @[])

proc addEdge(c: var CyclicContext; fromNode, toNode: Node) =
  var dest {.cursor.} = c.resolveGraph.mgetOrPut(fromNode, @[])
  if toNode notin dest:
    c.resolveGraph[fromNode].add toNode

proc addLayoutToSymbolEdge(c: var CyclicContext; sym: SymId) =
  c.ensureNode(layoutNode(sym))
  c.ensureNode(symbolNode(sym))
  c.addEdge(layoutNode(sym), symbolNode(sym))

proc ensureBranchNode(c: var CyclicContext; branchId: int) =
  discard c.whenBranchEuler.graph.hasKeyOrPut(branchId, @[])

proc resolveSym(c: var CyclicContext, sym: SymId, syms: var seq[SymId]) =
  let suffix = extractModule(pool.syms[sym])
  if suffix in c.semContexts: # check that symbol from this SCC
    var load = tryLoadSym(sym)
    assert load.status == LacksNothing
    if symKind(load.decl) != TypevarY: # In resolve graph Type shouldn't depend to TypeVar
      syms.add sym

proc resolveIdent(c: var CyclicContext, n: sink Cursor, s: ptr SemContext, syms: var seq[SymId]) =
  let insertPos = s[].dest.len
  let count = buildSymChoice(s[], n.litId, n.info, InnerMost)
  if count == 1:
    let sym = s[].dest[insertPos+1].symId
    resolveSym c, sym, syms
  
  if s[].currentScope.kind == ToplevelScope and s[].currentScope.up == nil:
    # It need because we don't have whenBranchSubtreeStart for
    # toplevel scope
    for branchScope in s[].whenBranchScopes.values:
      for sym in branchScope.tab.getOrDefault(n.litId):
        resolveSym c, sym.name, syms
  
  elif c.branchesStack.len > 0 and c.branchesStack[^1] in c.whenBranchSubtreeStart:
    for branchId in c.whenBranchEuler.visible(c.whenBranchSubtreeStart[c.branchesStack[^1]]):
      if branchId in s[].whenBranchScopes:
        let scope = s[].whenBranchScopes[branchId]
        for sym in scope.tab.getOrDefault(n.litId):
          resolveSym c, sym.name, syms

  s[].dest.shrink insertPos

proc scanExprSyms(c: var CyclicContext, n: var Cursor, s: ptr SemContext, syms: var seq[SymId]) =
  if n.kind == ParLe:
    var nested = 0
    while true:
      inc n
      if n.kind == ParRi:
        if nested == 0: break
        dec nested
      elif n.kind == ParLe: inc nested
      elif n.kind in {Symbol, SymbolDef}:
        resolveSym c, n.symId, syms
      elif n.kind == Ident:
        resolveIdent c, n, s, syms
  elif n.kind in {Symbol, SymbolDef}:
    resolveSym c, n.symId, syms
  elif n.kind == Ident:
    resolveIdent c, n, s, syms
  
  inc n

proc genWhenBranchGraph(c: var CyclicContext, n: var Cursor, branchStack: var seq[int]) =
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      genWhenBranchGraph(c, n, branchStack)
    inc n # ParRi
  of WhenS:
    inc n
    skip n # (id )
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        inc n # (id
        let branchId = pool.integers[n.intId]
        inc n
        inc n # )
        c.ensureBranchNode(branchId)
        if branchStack.len > 0:
          let parent = branchStack[^1]
          c.ensureBranchNode(parent)
          if parent notin c.whenBranchSubtreeStart:
            # start of subtree
            c.whenBranchSubtreeStart[parent] = branchId
            c.whenBranchEuler.addEdge(parent, branchId)
          else:
            let root = c.whenBranchSubtreeStart[parent]
            if branchId != root:
              c.whenBranchEuler.addEdge(root, branchId)
        branchStack.add branchId
        skip n # cond
        genWhenBranchGraph(c, n, branchStack)
        branchStack.shrink(branchStack.len - 1)
        inc n # ParRi
      of ElseU:
        inc n # (else
        inc n # (id
        let branchId = pool.integers[n.intId]
        inc n
        inc n # )
        c.ensureBranchNode(branchId)
        if branchStack.len > 0:
          let parent = branchStack[^1]
          c.ensureBranchNode(parent)
          if parent notin c.whenBranchSubtreeStart:
            c.whenBranchSubtreeStart[parent] = branchId
            c.whenBranchEuler.addEdge(parent, branchId)
          else:
            let root = c.whenBranchSubtreeStart[parent]
            if branchId != root:
              c.whenBranchEuler.addEdge(root, branchId)
        branchStack.add branchId
        genWhenBranchGraph(c, n, branchStack)
        branchStack.shrink(branchStack.len - 1)
        inc n # ParRi
      else:
        echo n
        quit "Invalid ast"
    inc n # ParRi
  else:
    skip n

proc dependencyKind(n: Cursor): NodeKind =
  case n.typeKind
  of RefT, PtrT, PointerT, CstringT:
    nkSymbol
  else:
    nkLayout

proc graphExpr(c: var CyclicContext, n: var Cursor, s: ptr SemContext, fromNode: Node) =
  let depKind = dependencyKind(n)
  var syms: seq[SymId] = @[]
  scanExprSyms c, n, s, syms
  for sym in syms:
    let load = tryLoadSym(sym)
    if load.status != LacksNothing:
      continue

    var target = layoutNode(sym)
    if symKind(load.decl) == TypeY and depKind == nkSymbol:
      c.addLayoutToSymbolEdge(sym)
      target = symbolNode(sym)
    else:
      c.ensureNode(target)
    c.addEdge(fromNode, target)

proc collectRoutineDeps(c: var CyclicContext; root: Cursor; s: ptr SemContext; outSyms: var seq[SymId]) =
  var stack = @[root]
  while stack.len > 0:
    var cur = stack.pop()
    if cursorIsNil(cur):
      continue
    if cur.kind == ParLe:
      var child = cur
      inc child
      while child.kind != ParRi:
        stack.add child
        skip child
    elif cur.kind in {Symbol, SymbolDef}:
      resolveSym(c, cur.symId, outSyms)
    elif cur.kind == Ident:
      var tmp = cur
      resolveIdent(c, tmp, s, outSyms)

proc genGraph(c: var CyclicContext, n: var Cursor, suffix: string) =
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      genGraph(c, n, suffix)
    inc n # ParRi
  of TypeS:
    let decl = asTypeDecl(n)
    n = decl.body
    inc n # skip `(object` token
    skip n # skip basetype

    if decl.name.kind == SymbolDef:
      let owner = layoutNode(decl.name.symId)
      c.ensureNode(owner)
      for dep in c.depsStack:
        c.ensureNode(dep)
        c.addEdge(owner, dep)

      c.usedConditions.mgetOrPut(decl.name.symId, @[]).add c.conditionsStack
      if c.branchesStack.len > 0:
        c.symBranches[decl.name.symId] = c.branchesStack

      var iter = initObjFieldIter()

      while nextField(iter, n, keepCase = false):
        # For case object we need to check all branches since
        # otherwise max(sizeof(branch1), sizeof(branch2)) can't be computed and
        # type cannot be built, so this checking correct
        var field = takeLocal(n, SkipFinalParRi)
        var s = addr c.semContexts[suffix]
        graphExpr c, field.typ, s, owner

    inc n
    inc n
  of WhenS:
    # when can make dependency for consts
    # when someConst:
    #   type A* = object
    # else:
    #   type B* = object
    # 
    # it means that A, B depend on someConst value
    # (all decls used in elif's should used as fromSym for future graphExpr)
    # Conditions stacked!
    # Ie: 
    # when a: body1
    # elif b: body2
    # means
    # body1 (if a): need know a
    # body2 (if not a and b): need know a and b
    var depsPos = c.depsStack.len
    var condsPos = c.conditionsStack.len
    var s = addr c.semContexts[suffix]
    inc n
    skip n # (id )
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        inc n # (id
        let branchId = pool.integers[n.intId]
        inc n
        inc n # )
        s[].currentScope = s[].whenBranchScopes[branchId]
        c.branchesStack.add branchId

        var syms: seq[SymId] = @[]
        c.conditionsStack.add store(c.conditions, n, branchId) # store condition
        scanExprSyms c, n, s, syms # cond
        for sym in syms:
          c.depsStack.add layoutNode(sym)
        genGraph(c, n, suffix)
        inc n # ParRi
        c.conditionsStack[^1].makeNegative # need for correct else
        s[].currentScope = s[].currentScope.up
        discard c.branchesStack.pop()
      of ElseU:
        inc n # (else
        inc n # (id
        let branchId = pool.integers[n.intId]
        inc n
        inc n # )
        s[].currentScope = s[].whenBranchScopes[branchId]
        c.branchesStack.add branchId
        genGraph(c, n, suffix)
        inc n # ParRi
        s[].currentScope = s[].currentScope.up
        discard c.branchesStack.pop()
      else:
        echo n
        quit "Invalid ast"
    inc n # ParRi
    c.depsStack.shrink(depsPos)
    c.conditionsStack.shrink(condsPos)
  elif n.symKind.isLocal:
    var decl = asLocal(n)
    if decl.name.kind == SymbolDef:
      var s = addr c.semContexts[suffix]
      graphExpr c, decl.val, s, layoutNode(decl.name.symId)
    skip n
  elif n.symKind.isRoutine:
    var decl = asRoutine(n)
    var s = addr c.semContexts[suffix]
    let owner = layoutNode(decl.name.symId)
    c.ensureNode(owner)
    var deps: seq[SymId] = @[]
    let declLoad = tryLoadSym(decl.name.symId)
    if declLoad.status == LacksNothing:
      collectRoutineDeps(c, declLoad.decl, s, deps)
    for depSym in deps:
      let load = tryLoadSym(depSym)
      if load.status != LacksNothing:
        continue

      if symKind(load.decl) == ResultY or depSym == decl.name.symId:
        continue
      let depNode = layoutNode(depSym)
      c.ensureNode(depNode)
      c.addEdge(owner, depNode)
    skip n
  else:
    skip n


proc addSym(s: SymId, n: Cursor) =
  # add decl to prog.mem
  var buf = createTokenBuf()
  buf.addSubtree n
  publish s, buf

proc prepareImports(c: var NifModule, n: var Cursor) =
  # fill prog.mods and prog.mem
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      prepareImports(c, n)
    inc n # ParRi
  of WhenS:
    inc n
    skip n # (id )
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        skip n # (id )
        skip n # cond; it is max interface so not need testing cond
        prepareImports(c, n)
        inc n # ParRi
      of ElseU:
        inc n # (else
        skip n # (id )
        prepareImports(c, n)
        inc n # ParRi
      else:
        echo n
        quit "Invalid ast"
    inc n # ParRi
  else:
    block nameSym:
      let sym: SymId
      let isPublic: bool
      if n.stmtKind == TypeS:
        let decl = asTypeDecl(n)
        if decl.name.kind != SymbolDef:
          break nameSym
        sym = decl.name.symId
        isPublic = decl.exported.kind != DotToken
      elif n.symKind.isRoutine:
        let decl = asRoutine(n)
        sym = decl.name.symId
        isPublic = decl.exported.kind != DotToken
      elif n.symKind.isLocal:
        let decl = asLocal(n)
        if decl.name.kind != SymbolDef:
          break nameSym
        sym = decl.name.symId
        isPublic = decl.exported.kind != DotToken
      else:
        break nameSym
      
      var dest =
        if isPublic:
          addr(c.index.public)
        else:
          addr(c.index.private)
      
      dest[][pool.syms[sym]] = NifIndexEntry() # Add sym to prog.mods
      addSym sym, n # Add sym to prog.mem

    skip n

proc topologicalSort(c: var CyclicContext): seq[Node] =
  # uses Kahn's algorithm for topological sorting

  var indegrees = initTable[Node, int]() # number of incoming nodes
  var queue = initDeque[Node]()

  for (owner, deps) in c.resolveGraph.pairs:
    indegrees[owner] = 0 # indegrees should be defined for all nodes to sort
    for dep in deps:
      indegrees[dep] = 0

  for (owner, deps) in c.resolveGraph.pairs:
    for dep in deps:
      inc indegrees[dep]

  for (node, indegree) in indegrees.pairs:
    if indegree == 0:
      queue.addLast node

  result = @[]
  while queue.len > 0:
    let u = queue.popFirst()
    result.add u

    for neighboor in c.resolveGraph.getOrDefault(u):
      dec indegrees[neighboor]
      if indegrees[neighboor] == 0:
        queue.addLast neighboor

  if len(result) != len(indegrees):
    error "cyclic type dependence detected"

proc evalCond(c: var CyclicContext, s: ptr SemContext, cond: Condition): NimonyExpr =
  let oldScope = s[].currentScope
  s[].currentScope = s[].whenBranchScopes[c.conditions.branchId cond]
  if not c.conditions.evaluated[cond.id]:
    let condStart = s[].dest.len
    var phase = SemcheckBodies
    swap s[].phase, phase
    var n = c.conditions.nodes[cond.id]
    semConstBoolExpr s[], n, allowUnresolved = false # perfomed only on toplevel
    swap s[].phase, phase
    result = cursorAt(s[].dest, condStart).exprKind
    c.conditions.addEvalResult(cond, result)
    endRead(s[].dest)
    s[].dest.shrink(condStart)
  else:
    result = c.conditions.evalResults[cond.id]
  s[].currentScope = oldScope

proc applyOrdinalSemcheck(
  c: var CyclicContext, n: var Cursor,
  s: ptr SemContext, topo: sink seq[SymId],
  mergedBranches: var HashSet[int]) =
  # try check that n not already semchecked after semchecking
  # topologicaly sorted decls
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      applyOrdinalSemcheck(c, n, s, topo, mergedBranches)
    inc n # ParRi
  of WhenS:
    # (top level) when implementation friendly to cached conditions
    inc n # (when
    skip n # (id )
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif

        inc n # (id
        let branchId = pool.integers[n.intId]
        inc n
        inc n # )

        if c.conditions.hasCondition n:
          # we know when cond so it can be already resolved
          var cond = c.conditions.cursorToCondition n
          skip n # cond
          let condValue = evalCond(c, s, cond)
          if condValue == TrueX:
            if branchId notin mergedBranches:
              s[].currentScope.mergeScope(s[].whenBranchScopes[branchId])
            applyOrdinalSemcheck(c, n, s, topo, mergedBranches) # body
            inc n # ParRi
            skipUntilEnd n
            break
          else:
            skip n # body
            inc n # ParRi
        else:
          skip n # cond
          skip n # body
          inc n # ParRi
          error "Condition should be known at this point"
      
      of ElseU:
        inc n # (else

        inc n # (id
        let branchId = pool.integers[n.intId]
        inc n
        inc n # )
        if branchId notin mergedBranches:
          s[].currentScope.mergeScope(s[].whenBranchScopes[branchId])
        applyOrdinalSemcheck(c, n, s, topo, mergedBranches) # body
        inc n # ParRi
      else:
        echo n
        quit "Invalid ast"
    
    inc n # ParRi
  of TypeS:
    let decl = asTypeDecl(n)
    if decl.name.kind == SymbolDef and decl.name.symId in topo:
      skip n
    else:
      semStmt s[], n, false
  elif n.symKind.isLocal:
    let decl = asLocal(n)
    if decl.name.kind == SymbolDef and decl.name.symId in topo:
      skip n
    else:
      semStmt s[], n, false
  elif n.symKind.isRoutine:
    let decl = asRoutine(n)
    if decl.name.kind == SymbolDef and decl.name.symId in topo:
      skip n
    else:
      semStmt s[], n, false
  else:
    semStmt s[], n, false

proc semcheckSignatures(c: var CyclicContext, topo: seq[SymId], trees: var Table[string, TokenBuf]) =
  # SemcheckSignatures is unusual because it working in topologic order on some decls.
  # so it need to generate true dest:
  # (stmts
  #   Semchecked decls
  #   Input tree without semchecked decls
  # )
  for s in c.semContexts.mvalues:
    s.phase = SemcheckSignatures
    s.dest.addParLe TagId(StmtsS), NoLineInfo

  for sym in topo:
    var load = tryLoadSym(sym)
    let suffix = extractModule(pool.syms[sym])
    var s = addr c.semContexts[suffix]
    
    var canGenerate = true # can become false if some of conditions is false    
    for cond in c.usedConditions.getOrDefault(sym, @[]):
      let condValue = evalCond(c, s, cond)

      canGenerate = canGenerate and (
        condValue == FalseX and cond.isNegative or
        condValue == TrueX and not cond.isNegative)

    discard c.mergedBranches.hasKeyOrPut(suffix, initHashSet[int]())
    if canGenerate:
      if sym in c.symBranches:
        for branchId in c.symBranches[sym]:
          if branchId in c.mergedBranches[suffix]: continue
          s[].currentScope.mergeScope(s[].whenBranchScopes[branchId])
          c.mergedBranches[suffix].incl branchId
      semStmt s[], load.decl, false
    s[].pragmaStack.setLen(0) # {.pop.} fixed?

  for suffix in c.semContexts.keys:
    # ordinal SemcheckSignatures for not semchecked things
    var s = addr c.semContexts[suffix]
    discard c.mergedBranches.hasKeyOrPut(suffix, initHashSet[int]())
    var n = beginRead(trees[suffix])
    inc n
    while n.kind != ParRi:
      applyOrdinalSemcheck(c, n, s, topo, c.mergedBranches[suffix])
  
  for suffix in c.semContexts.keys:
    var s = addr c.semContexts[suffix]
    s[].dest.addParRi
    trees[suffix] = move s[].dest

proc hasCyclicPragma(x: var Cursor): bool =
  if x.kind == ParLe and x.exprKind == PragmaxX:
    var y = x
    inc y
    skip y
    if y.substructureKind == PragmasU:
      inc y
      if y.kind == Ident and pool.strings[y.litId] == "cyclic":
        return true
  false

proc checkCyclicPragma(c: sink CyclicContext, n: var Cursor, s: ptr SemContext) =
  # We already in SCC, so only need to check that
  # all modules defined in SCC marked with pragma
  # other modules (of course not need to be marked)
  # all very simple
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      checkCyclicPragma(c, n, s)
    inc n # ParRi
  of WhenS:
    inc n
    skip n # (id )
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        skip n # (id )
        skip n # cond; it is max interface so not need testing cond
        checkCyclicPragma(c, n, s)
        inc n # ParRi
      of ElseU:
        inc n # (else
        skip n # (id )
        checkCyclicPragma(c, n, s)
        inc n # ParRi
      else:
        echo n
        quit "Invalid ast"
    inc n # ParRi
  of ImportS, FromImportS, ImportExceptS:
    let info = n.info
    let origin = getFile(info)
    var x = n
    inc x
    if hasCyclicPragma(x):
      var files: seq[ImportedFilename] = @[]
      var errors: set[FilenameErr] = {}
      filenameVal(x, files, errors, true, true)
      for f1 in files:
        let f2 = resolveFile(s[].g.config.paths, origin, f1.path)
        let suffix = moduleSuffix(f2, s[].g.config.paths)

        if suffix notin c.semContexts: # O(1)
          buildErr s[], info, "Unnecessary {.cyclic.} pragma: import `" & f1.name & "` does not form a cycle. Remove {.cyclic.} pragma"
    else:
      var files: seq[ImportedFilename] = @[]
      var errors: set[FilenameErr] = {}
      filenameVal(x, files, errors, true, true)
      for f1 in files:
        let f2 = resolveFile(s[].g.config.paths, origin, f1.path)
        let suffix = moduleSuffix(f2, s[].g.config.paths)

        if suffix in c.semContexts: # O(1)
          buildErr s[], info, "Missing {.cyclic.} pragma: import `" & f1.name & "` is part of cycle. Mark it with {.cyclic.}"

    skip n
  else:
    skip n

proc cyclicSem(fileNames: seq[string], outputFileNames: seq[string], validateCyclicPragma: bool) =
  var c = CyclicContext()
  
  var trees = initTable[string, TokenBuf]()
  for fileName in fileNames:
    var sc = initSemContext(fileName)
    var n0 = setupProgram(fileName, fileName & ".tmp.nif") # TODO: replace
    
    let suffix = splitModulePath(fileName).name
    trees[suffix] = semcheckToplevel(sc, n0)
    c.semContexts[suffix] = sc

    if suffix notin prog.mods:
      prog.mods[suffix] = NifModule()
    
    var n = beginRead(trees[suffix])
    prepareImports(prog.mods[suffix], n)
  
  for fileName in fileNames:
    let suffix = splitModulePath(fileName).name
    var s = addr c.semContexts[suffix]

    if validateCyclicPragma:
      var n1 = beginRead(trees[suffix])
      takeTree s[], n1
      var n2 = beginRead(trees[suffix])
      
      s[].dest.shrink(s[].dest.len - 1) # remove last ParRi to get space for errors
      checkCyclicPragma(c, n2, s)
      s[].dest.addParRi() # add last ParRi
      trees[suffix] = move s[].dest
      
    var n = beginRead(trees[suffix])
    var tree = phaseX(s[], n, SemcheckImports)
    trees[suffix] = tree
  
  # Import errors on SCC much simpler to understand when it reported together
  var hasErr = false
  for fileName in fileNames:
    let suffix = splitModulePath(fileName).name
    var s = addr c.semContexts[suffix]
    swap s[].dest, trees[suffix]
    if reportErrors(s[]) > 0:
      hasErr = true
    swap s[].dest, trees[suffix]
  
  if hasErr:
    quit 1

  # Now we have importTab. It means that we can use anything with imported symbols.
  # For example, buildSymChoice should work with imported Symbols

  for fileName in fileNames:
    let suffix = splitModulePath(fileName).name
    var n = beginRead(trees[suffix])
    var branchStack: seq[int] = @[]
    c.genWhenBranchGraph(n, branchStack)

  var visitedRoots = initHashSet[int]()
  for root in c.whenBranchSubtreeStart.values:
    if root notin visitedRoots:
      visitedRoots.incl root
      c.whenBranchEuler.euler(root)

  for fileName in fileNames:
    let suffix = splitModulePath(fileName).name
    var n = beginRead(trees[suffix])
    c.genGraph n, suffix
  
  when false:
    for node, deps in c.resolveGraph:
      let nodeKind = if node.kind == nkSymbol: "symbol" else: "layout"
      echo pool.syms[node.s], " (", nodeKind, ")"
      for dep in deps:
        let depKind = if dep.kind == nkSymbol: "symbol" else: "layout"
        echo "  -> ", pool.syms[dep.s], " (", depKind, ")"
      echo ""
    
    echo "conds: "
    for i, v in c.usedConditions:
      echo pool.syms[i]
      echo ": "
      for j in v:
        echo c.conditions.nodes[j.id]
        echo j.isNegative
    echo "------"

  
  # Realy it not so important because
  # all declared syms already in prog.mem
  # So realy semcheck can be runned in any order
  # And after semcheck we have updated decl in prog.mem
  # But if do it in wrong order, generating new type
  # will use prog.mem on SemcheckImports phase
  # and it not a big problem because of no forward declaration for types etc.
  # But it need for when feature. Also it guarantee that
  # type fully semchecked and nothing bad will happen.
  var nodeOrder = c.topologicalSort()
  nodeOrder.reverse()

  when false:
    for node in nodeOrder:
      let nodeKind = if node.kind == nkSymbol: "symbol" else: "layout"
      echo pool.syms[node.s], " (", nodeKind, ")"

  var topo: seq[SymId] = @[]
  for node in nodeOrder:
    if node.kind == nkLayout:
      topo.add node.s

  semcheckSignatures c, topo, trees
  
  var i = 0
  for fileName in fileNames:
    let suffix = splitModulePath(fileName).name
    var n = beginRead(trees[suffix])
    
    var s = addr c.semContexts[suffix]
    s[].phase = SemcheckBodies
    takeToken s[], n
    while n.kind != ParRi:
      semStmt s[], n, false
    
    s[].pending.addParRi()
    var cur = beginRead(s[].pending)
    inc cur
    s[].phase = SemcheckBodies
    while cur.kind != ParRi:
      semStmt s[], cur, false
    skipParRi(cur)
    endRead(s[].pending)
    
    instantiateGenerics s[]
    for val in s[].typeInstDecls:
      let sym = fetchSym(s[], val)
      let res = declToCursor(s[], sym)
      if res.status == LacksNothing:
        requestHookInstance(s[], res.decl)
        requestMethods(s[], val, res.decl)
        s[].dest.copyTree res.decl
    instantiateGenericHooks s[]
    takeParRi s[], n
    s[].dest.addParRi

    if reportErrors(s[]) == 0:
      var afterSem = move s[].dest
      when true: #defined(enableContracts):
        var moreErrors = analyzeContracts(afterSem)
        if reporters.reportErrors(moreErrors) > 0:
          quit 1
      var finalBuf = beginRead afterSem
      s[].dest = injectDerefs(finalBuf)
    else:
      quit 1

    if reportErrors(s[]) == 0:
      writeOutput s[], outputFileNames[i]
    else:
      quit 1
    
    inc i

type
  Command = enum
    cmdHelp
    cmdVersion
    cmdRun
  
  Mode = enum
    mInputs
    mOutputs

proc writeVersion() =
  echo "nimsemcyclic 0.1"
  quit(0)

proc writeHelp() =
  echo """nimsemcyclic - Nimony cyclic dependency resolver

Usage:
  nimsemcyclic [options] <command> [module1.1.nif] [module2.1.nif] ...

Commands:
  run [module1.1.nif] [module2.1.nif]      Resolves cyclic dependend .1.nif files
  outputs [module1.1.nif] [module2.1.nif]  Specify where semchecked files will be written

Options:
  --validateCyclicPragma                   Enables {.cyclic.} pragma checking
  --help, -h                               Show this help
  --version, -v                            Show version

Examples:
  nimsemcyclic run a.1.nif b.1.nif outputs a.2.nif b.2.nif
"""
  quit(0)

proc handleCmdLine() =
  var
    cmd = cmdHelp
    sccFiles: seq[string] = @[]
    mode = mInputs
    outputId = 0
    outputFiles: seq[string] = @[]
    validateCyclicPragma = false # check for correct {.cyclic.} usage
  
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      case key.normalize
      of "run": cmd = cmdRun
      of "outputs": mode = mOutputs
      else:
        case mode
        of mInputs:
          sccFiles.add key
        of mOutputs:
          outputFiles.add key

    of cmdLongOption, cmdShortOption:
      case key.normalize
      of "help", "h": cmd = cmdHelp
      of "version", "v": cmd = cmdVersion
      of "validatecyclicpragma": validateCyclicPragma = true
      else:
        echo "Unknown option: --", key
        quit(1)
    of cmdEnd: assert false, "cannot happen"
  
  case cmd
  of cmdVersion: writeVersion()
  of cmdHelp: writeHelp()
  of cmdRun: 
    if sccFiles.len == 0:
      echo "At least one file in SCC required"
      quit(1)
    
    if outputFiles.len != sccFiles.len:
      echo "Each input file must correspond to exactly one output file"
      quit(1)

    cyclicSem(sccFiles, outputFiles, validateCyclicPragma)


when isMainModule:
  handleCmdLine()
