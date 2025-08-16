## nimsemcyclic is part of semantic checker that used
## before nimsem. It working for cyclic import group (realy SCC)
## Unfortunately, this requires restarting on the entire SCC,
## but fortunately SCC is usually small (maximum of 3-4 modules)


import std / [parseopt, strutils, assertions, syncio, tables, osproc]
import ".." / lib / [nifstreams, nifcursors, bitabs, lineinfos, nifreader, nifbuilder, tooldirs, nifindexes]
import ".." / nimony / [nimony_model, decls, symtabs, programs, semos, semdata, nifconfig, indexgen]
include sem


proc initSemContext(fileName: string): SemContext =
  let (_, file, _) = splitModulePath(fileName)
  var moduleFlags: set[ModuleFlag] = {}
  moduleFlags.incl IsMain # TODO: use real moduleFlags
  var config = initNifConfig()
  semos.setupPaths(config, true)

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
  # c.pending.add parLeToken(StmtsS, NoLineInfo)
  c.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  let path = getFile(n0.info) # gets current module path, maybe there is a better way
  addSelfModuleSym(c, path)

  if {SkipSystem, IsSystem} * c.moduleFlags == {}:
    let systemFile = ImportedFilename(path: stdlibFile("std/system"), name: "system", isSystem: true)
    importSingleFile(c, systemFile, "", ImportFilter(kind: ImportAll), n0.info)

  result = phaseX(c, n0, SemcheckTopLevelSyms)
  # c.pending.addParRi()


type
  CyclicContext = object
    syms: Table[string, seq[SymId]]
    resolveGraph: Table[SymId, SymId] # 

    currentModuleName: string

    semContexts: Table[string, SemContext]


    typeOrder: Table[SymId, int] # mapping from type symbol to declare number,
                                 # it realy helpful to keep correct order and not allow use
                                 # currently undefined types
    currentTypeOrder: int

proc collectSyms*(c: var CyclicContext, n: var Cursor) =
  # working after executed SemToplevelSyms phase to collect all known syms
  echo "COLLECT: ", n
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      collectSyms(c, n)
    inc n # ParRi
  else:
    block nameSym:
      let name: SymId
      if n.stmtKind == TypeS:
        name = asTypeDecl(n).name.symId
        c.typeOrder[name] = c.currentTypeOrder
        inc c.currentTypeOrder
      elif n.symKind.isRoutine:
        name = asRoutine(n).name.symId
      elif n.symKind.isLocal:
        # don't have global locals symId at SemToplevelSyms phase currently in nimony...
        break nameSym # TODO: add Symbol generation to toplevel locals in SemToplevelSyms...
        name = asLocal(n).name.symId
      else:
        break nameSym
      
      mgetOrPut(c.syms, c.currentModuleName).add name
    
    skip n

proc genGraph(c: var CyclicContext, n: var Cursor) =
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      genGraph(c, n)
    inc n # ParRi
  of TypeS:
    echo "Scanning type: ", n
    let decl = asTypeDecl(n)
    n = decl.body
    inc n # skip `(object` token
    skip n # skip basetype

    var iter = initObjFieldIter()
    
    while nextField(iter, n, keepCase = false):
      # For case object we need to check all branches since
      # otherwise max(sizeof(branch1), sizeof(branch2)) can't be computed and
      # type cannot be built, so this checking correct
      var field = takeLocal(n, SkipFinalParRi)
      var c = addr c.semContexts[c.currentModuleName]
      let insertPos = c[].dest.len
      let count = buildSymChoice(c[], field.typ.litId, field.typ.info, InnerMost)
      # TODO: using field.typ.litId not correct because of ref obj, SomeGeneric[A, B], etc. It should be rewritten to adition proc that iterates on idents
      echo c[].currentScope.kind
      # echo beginRead(c[].dest)
      if count == 1:
        let sym = c[].dest[insertPos+1].symId
        echo pool.syms[sym]
      echo "cnt: ", count
      echo field.typ

      # var it = c[].currentScope
      # while it != nil:
      #   for k, v in it.tab:
      #     var s = pool.strings[k] & " : "
      #     for i in v:
      #       s.add pool.syms[i.name] & ", "
      #     echo s
      #   it = it.up

      skip n
      # inc n

    inc n
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
        inc n # cond; it is max interface so not need testing cond
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
        sym = decl.name.symId
        isPublic = decl.exported.kind != DotToken
      elif n.symKind.isRoutine:
        let decl = asRoutine(n)
        sym = decl.name.symId
        isPublic = decl.exported.kind != DotToken
      elif n.symKind.isLocal:
        # don't have global locals symId at SemcheckToplevelSyms phase currently in nimony...
        break nameSym # TODO: add Symbol generation for toplevel locals in SemToplevelSyms...
        let decl = asLocal(n)
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

proc cyclicSem(fileNames: seq[string]) =
  var c = CyclicContext()
  
  var trees = initTable[string, TokenBuf]()
  for fileName in fileNames:
    var sc = initSemContext(fileName)
    var n0 = setupProgram(fileName, fileName & ".tmp.nif") # TODO: replace
    trees[fileName] = semcheckToplevel(sc, n0)
    
    var n = beginRead(trees[fileName])
    c.currentModuleName = fileName
    c.semContexts[fileName] = sc
    
    let (_, suffix, _) = splitModulePath(fileName)
    if suffix notin prog.mods:
      prog.mods[suffix] = NifModule()
    
    prepareImports(prog.mods[suffix], n)
  
  for fileName in fileNames:
    var n = beginRead(trees[fileName])
    var tree = phaseX(c.semContexts[fileName], n, SemcheckImports)
    trees[fileName] = tree
  
  # Now we have importTab. It means that we can use anything with imported symbols.
  # For example, buildSymChoice should work with imported Symbols

  for fileName in fileNames:
    var n = beginRead(trees[fileName])
    c.genGraph n



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
