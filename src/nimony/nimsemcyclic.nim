## nimsemcyclic is part of semantic checker that used
## before nimsem. It working for cyclic import group (realy SCC)
## Unfortunately, this requires restarting on the entire SCC,
## but fortunately SCC is usually small (maximum of 3-4 modules)


import std / [parseopt, strutils, assertions, syncio, tables, osproc, deques, algorithm]
import ".." / lib / [nifstreams, nifcursors, bitabs, lineinfos, nifreader, nifbuilder, tooldirs, nifindexes]
import ".." / nimony / [nimony_model, decls, symtabs, programs, semos, semdata, nifconfig, indexgen]
include sem


proc initSemContext(fileName: string): SemContext =
  let (_, file, _) = splitModulePath(fileName)
  var moduleFlags: set[ModuleFlag] = {}
  moduleFlags.incl IsMain # TODO: use real moduleFlags
  var config = initNifConfig("")
  semos.setupPaths(config)

  result = SemContext(
    dest: createTokenBuf(),
    types: createBuiltinTypes(),
    thisModuleSuffix: file,
    moduleFlags: moduleFlags,
    g: ProgramContext(config: config),
    phase: SemcheckTopLevelSyms,
    routine: SemRoutine(kind: NoSym),
    # commandLineArgs: commandLineArgs,
    canSelfExec: false, #TODO: check this one
    pending: createTokenBuf())

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
  Conditions = object
    evaluated: seq[bool] # is condition already evaluated, index
    evalResults: seq[NimonyExpr]
    nodes: seq[Cursor]
    cursorUids: Table[int, Condition] # node (condition) position to it's Condition
  
  Condition = object # Same condition can be used for different decls
    id: int          # and shouldn't be evaluated twice
    isNegative: bool

proc `$`(c: Condition): string =
  result = ""
  if c.isNegative:
    result.add "!"
  result.add $c.id

proc store(c: var Conditions, n: Cursor): Condition =
  result = Condition(id: c.evaluated.len, isNegative: false)
  c.evaluated.add false
  c.evalResults.add FalseX
  c.nodes.add n
  c.cursorUids[toUniqueId n] = result

proc addEvalResult(c: var Conditions, cond: Condition, res: NimonyExpr) =
  c.evaluated[cond.id] = true
  c.evalResults[cond.id] = res

proc makeNegative(cond: var Condition) =
  cond.isNegative = true

proc hasCondition(c: sink Conditions, n: Cursor): bool =
  toUniqueId(n) in c.cursorUids

proc cursorToCondition(c: sink Conditions, n: Cursor): Condition =
  c.cursorUids[toUniqueId n]

type
  CyclicContext = object
    resolveGraph: Table[SymId, seq[SymId]]
    semContexts: Table[string, SemContext]
    depsStack: seq[SymId] # used to spread decls to inner contexts

    conditions: Conditions
    usedConditions: Table[SymId, seq[Condition]] # what conditions uses symbol
    conditionsStack: seq[Condition] # used to spread conditions to inner contexts 

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

proc graphExpr(c: var CyclicContext, n: var Cursor, s: ptr SemContext, fromSym: SymId) =
  var syms: seq[SymId] = @[]
  scanExprSyms c, n, s, syms
  for sym in syms:
    c.resolveGraph.mgetOrPut(fromSym, @[]).add sym

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
      for sym in c.depsStack:
        c.resolveGraph.mgetOrPut(decl.name.symId, @[]).add sym
      
      c.usedConditions.mgetOrPut(decl.name.symId, @[]).add c.conditionsStack

      var iter = initObjFieldIter()
      
      while nextField(iter, n, keepCase = false):
        # For case object we need to check all branches since
        # otherwise max(sizeof(branch1), sizeof(branch2)) can't be computed and
        # type cannot be built, so this checking correct
        var field = takeLocal(n, SkipFinalParRi)
        var s = addr c.semContexts[suffix]
        graphExpr c, field.typ, s, decl.name.symId

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
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        var syms: seq[SymId] = @[]
        c.conditionsStack.add store(c.conditions, n) # store condition
        scanExprSyms c, n, s, syms # cond
        c.depsStack.add syms
        genGraph(c, n, suffix)
        inc n # ParRi
        c.conditionsStack[^1].makeNegative # need for correct else
      of ElseU:
        inc n # (else
        genGraph(c, n, suffix)
        inc n # ParRi
      else:
        echo n
        quit "Invalid ast"
    inc n # ParRi
    c.depsStack.shrink(depsPos)
    c.conditionsStack.shrink(condsPos)
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
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        skip n # cond; it is max interface so not need testing cond
        prepareImports(c, n)
        inc n # ParRi
      of ElseU:
        inc n # (else
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

proc topologicalSort(c: var CyclicContext): seq[SymId] =
  # uses Kahn's algorithm for topological sorting

  var indegrees = initTable[SymId, int]() # number of incoming nodes
  var queue = initDeque[SymId]()
  
  for (toSym, fromSyms) in c.resolveGraph.pairs:
    indegrees[toSym] = 0 # indegrees should be defined for all syms to sort
    for fromSym in fromSyms:
      indegrees[fromSym] = 0
  
  for (toSym, fromSyms) in c.resolveGraph.pairs:
    for fromSym in fromSyms:
      inc indegrees[fromSym]
  
  for (sym, indegree) in indegrees.pairs:
    if indegree == 0:
      queue.addLast sym

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

proc applyOrdinalSemcheck(c: var CyclicContext, n: var Cursor, s: ptr SemContext, topo: sink seq[SymId]) =
  # try check that n not already semchecked after semchecking
  # topologicaly sorted decls
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      applyOrdinalSemcheck(c, n, s, topo)
    inc n # ParRi
  of WhenS:
    # (top level) when implementation friendly to cached conditions
    inc n # (when
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        
        if c.conditions.hasCondition n:
          # we know when cond so it can be already resolved
          var cond = c.conditions.cursorToCondition n
          skip n # cond
          let condValue = evalCond(c, s, cond)
          if condValue == TrueX:
            applyOrdinalSemcheck(c, n, s, topo) # body
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
        applyOrdinalSemcheck(c, n, s, topo) # body
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

    if canGenerate:
      semStmt s[], load.decl, false
    s[].pragmaStack.setLen(0) # {.pop.} fixed?

  for suffix in c.semContexts.keys:
    # ordinal SemcheckSignatures for not semchecked things
    var s = addr c.semContexts[suffix]
    var n = beginRead(trees[suffix])
    inc n
    while n.kind != ParRi:
      applyOrdinalSemcheck(c, n, s, topo)
  
  for suffix in c.semContexts.keys:
    var s = addr c.semContexts[suffix]
    s[].dest.addParRi
    trees[suffix] = move s[].dest

proc cyclicSem(fileNames: seq[string]) =
  var c = CyclicContext()
  
  var trees = initTable[string, TokenBuf]()
  for fileName in fileNames:
    var sc = initSemContext(fileName)
    var n0 = setupProgram(fileName, fileName & ".tmp.nif") # TODO: replace
    
    let (_, suffix, _) = splitModulePath(fileName)
    trees[suffix] = semcheckToplevel(sc, n0)
    c.semContexts[suffix] = sc

    if suffix notin prog.mods:
      prog.mods[suffix] = NifModule()
    
    var n = beginRead(trees[suffix])
    prepareImports(prog.mods[suffix], n)
  
  for fileName in fileNames:
    let (_, suffix, _) = splitModulePath(fileName)
    var n = beginRead(trees[suffix])
    var tree = phaseX(c.semContexts[suffix], n, SemcheckImports)
    trees[suffix] = tree
  
  # Now we have importTab. It means that we can use anything with imported symbols.
  # For example, buildSymChoice should work with imported Symbols

  for fileName in fileNames:
    let (_, suffix, _) = splitModulePath(fileName)
    var n = beginRead(trees[suffix])
    c.genGraph n, suffix
  
  for i, v in c.resolveGraph:
    echo pool.syms[i]
    echo ": "
    for j in v:
      echo pool.syms[j]
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
  var topo = c.topologicalSort()
  topo.reverse()

  for i in topo:
    echo pool.syms[i], ", "
  
  semcheckSignatures c, topo, trees
  
  for fileName in fileNames:
    let (_, suffix, _) = splitModulePath(fileName)
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
      writeOutput s[], fileName.substr(0, fileName.len - ".nif".len - 1).changeFileExt(".2.nif")
    else:
      quit 1


cyclicSem(@["nimcache/atxy29s.1.nif", "nimcache/bvhuex5.1.nif"])





















# type
#   Command = enum
#     cmdHelp
#     cmdVersion
#     cmdRun

# proc writeVersion() =
#   echo "nimsemcyclic 0.1"
#   quit(0)

# proc writeHelp() =
#   echo """nifface - Nimony cyclic dependency resolver

# Usage:
#   nimcyclicsem [options] <command> [module1.1.nif] [module2.1.nif] ...

# Commands:
#   run [module1.1.nif] [module2.1.nif]  Resolves cyclic dependend things
#   help, -h                             Show this help
#   version, -v                          Show version

# Options:
#   -o, --output:<file> output file for SCC info

# Examples:
#   nimcyclicsem run mymodule.1.max_iface.nif mymodule.2.max_iface.nif
# """
#   quit(0)

# proc handleCmdLine() =
#   var
#     cmd = cmdHelp
#     sccFiles: seq[string] = @[]
#     outputFile = ""
  
#   for kind, key, val in getopt():
#     case kind
#     of cmdArgument:
#       case key.normalize
#       of "run": cmd = cmdRun
#       else:
#         sccFiles.add key

#     of cmdLongOption, cmdShortOption:
#       case key.normalize
#       of "help", "h": cmd = cmdHelp
#       of "version", "v": cmd = cmdVersion
#       of "output", "o":
#         outputFile = val
#       else:
#         echo "Unknown option: --", key
#         quit(1)
#     of cmdEnd: assert false, "cannot happen"
  
#   case cmd
#   of cmdVersion: writeVersion()
#   of cmdHelp: writeHelp()
#   of cmdRun: 
#     if sccFiles.len == 0:
#       echo "At least one file in SCC required"
#       quit(1)
    
#     if outputFile == "":
#       echo "Output file required"
#       quit(1)
    
#     processScc(sccFiles, outputFile)


# when isMainModule:
#   handleCmdLine()
