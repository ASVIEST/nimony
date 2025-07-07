## nimsemcyclic is part of semantic checker that used
## before nimsem. It working for cyclic import group (realy SCC)
## Unfortunately, this requires restarting on the entire SCC,
## but fortunately SCC is usually small (maximum of 3-4 modules)
## tasks:
## 1. Apply some required sem (recursively):
##      analyzes the declarations for Types, When stategments, Consts, Procs (currently only signature)
##      and get it dependences
##      build DAG for dependences, apply topological sort
##      and you have correct order to semcheck stategments
##      run sem for it, then add to common file (.cyclic.nif and .cyclic.idx.nif)
##      final.
##
##      when nifmake working with SCC it should add this files to nimsem.
##      Nimsem use common constructs from .cyclic.nif that used between modules
##      and not trying to semcheck it
##
## 2. Generate variable initalize list (file .init.nif):
##    requires checking that variable changed in module scope
##    (it should not be reassigned)
##    # a.nim
##    import b
##    var foo* = baz
##    var buz* = 10
##    # b.nim
##    import a
##    var bar* = buz
##    
##    algorithm: build DAG for variables, apply topological sort
##    and you have [a.buz, b.bar, a.foo] - correct initalize list
##    create .init.nif
##    final.
##
## type A = object
##   b: B
## 
## type B = ref object
##   a: A
## graph: A -> B; B -> A


import std / [parseopt, strutils, assertions, syncio, tables]
import ".." / lib / [nifstreams, nifcursors, bitabs, lineinfos, nifreader, nifbuilder]
import ".." / nimony / [nimony_model, decls, symtabs, programs, sem, semos, semdata]

type
  Context = object
    dest: TokenBuf
    globals: Table[string, int]
    thisModuleSuffix: string
    sem: SemContext # Need for type sem etc.

proc graphStmt(c: var Context; n: var Cursor) =
  # 1. make dependence graph + 
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      graphStmt(c, n)
    inc n # ParRi
  of TypeS:
    let decl = asTypeDecl(n)
    skip n
  else:
    echo n
    skip n

proc processSccFile(c: var Context, fileName: string) =
  var stream = nifstreams.open(filename)
  defer: nifstreams.close(stream)

  discard processDirectives(stream.r)

  var buf = fromStream(stream)
  var n = beginRead(buf)
  defer: endRead(buf)

  let (_, file, _) = splitModulePath(fileName)
  c.thisModuleSuffix = file # just as in setupProgram prog.main
  graphStmt(c, n)

proc processScc(fileNames: seq[string], outputFilename: string) =
  var c = Context(dest: createTokenBuf())

  c.dest.buildTree TagId(StmtsS), NoLineInfo:
    for fileName in fileNames:
      c.processSccFile(fileName)
  
  writeFile outputFilename, "(.nif24)\n" & toString(c.dest)

type
  Command = enum
    cmdHelp
    cmdVersion
    cmdRun

proc writeVersion() =
  echo "nimsemcyclic 0.1"
  quit(0)

proc writeHelp() =
  echo """nifface - Nimony cyclic dependency resolver

Usage:
  nimcyclicsem [options] <command> [module1.1.nif] [module2.1.nif] ...

Commands:
  run [module1.1.nif] [module2.1.nif]  Resolves cyclic dependend things
  help, -h                             Show this help
  version, -v                          Show version

Options:
  -o, --output:<file> output file for SCC info

Examples:
  nimcyclicsem run mymodule.1.max_iface.nif mymodule.2.max_iface.nif
"""
  quit(0)

proc handleCmdLine() =
  var
    cmd = cmdHelp
    sccFiles: seq[string] = @[]
    outputFile = ""
  
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      case key.normalize
      of "run": cmd = cmdRun
      else:
        sccFiles.add key

    of cmdLongOption, cmdShortOption:
      case key.normalize
      of "help", "h": cmd = cmdHelp
      of "version", "v": cmd = cmdVersion
      of "output", "o":
        outputFile = val
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
    
    if outputFile == "":
      echo "Output file required"
      quit(1)
    
    processScc(sccFiles, outputFile)


when isMainModule:
  handleCmdLine()
