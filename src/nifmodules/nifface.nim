## Simple program that get maximum public interface of module
## It need to say that file that depend on other file not need to be
## recompiled because public interface not changed
## maximum means that it not fully accurate because it can depend on when conditions
## and if ident can be exported in at least one branch, then it will be in public interface
## It also usefull for cyclic modules, partialsem should run on full SCC only if some of modules changed partial interface. 

import std / [parseopt, strutils, assertions, os, syncio]
import ".." / lib / [nifstreams, nifcursors, bitabs, lineinfos, nifreader, nifbuilder]
import ".." / nimony / [nimony_model, decls]

type
  Context = object
    dest: TokenBuf

proc ifaceStmt(c: var Context; n: var Cursor) =
  case n.stmtKind
  of StmtsS:
    inc n
    while n.kind != ParRi:
      ifaceStmt(c, n)
    inc n # ParRi
  of WhenS:
    inc n
    while n.kind != ParRi:
      case n.substructureKind
      of ElifU:
        inc n # (elif
        inc n # cond; it is max interface so not need testing cond
        ifaceStmt(c, n)
        inc n # ParRi
      of ElseU:
        inc n # (else
        ifaceStmt(c, n)
        inc n # ParRi
      else:
        echo n
        quit "Invalid ast"
    inc n # ParRi
  of TypeS:
    let decl = asTypeDecl(n)
    
    if decl.exported.kind != DotToken:
      c.dest.buildTree(TagId(TypeS), n.info):
        c.dest.add(decl.name.load)
        c.dest.add(decl.exported.load)
        c.dest.addSubtree(decl.typevars)
        c.dest.addSubtree(decl.pragmas)
        c.dest.addSubtree(decl.body)
    
    skip n
  elif n.symKind.isRoutine:
    let decl = asRoutine(n)

    if decl.exported.kind != DotToken:
      c.dest.buildTree(TagId(n.stmtKind), n.info):
        c.dest.add(decl.name.load)
        c.dest.add(decl.exported.load)

        c.dest.addSubtree(decl.pattern)
        c.dest.addSubtree(decl.typevars)
        c.dest.addSubtree(decl.params)
        c.dest.addSubtree(decl.retType)
        c.dest.addSubtree(decl.pragmas)
        c.dest.addSubtree(decl.effects)
        c.dest.addDotToken()
    
    skip n
  elif n.symKind.isLocal:
    let decl = asLocal(n) # no way to enter local scope, so it's in global

    if decl.exported.kind != DotToken:
      c.dest.buildTree(TagId(n.stmtKind), n.info):
        c.dest.add(decl.name.load)
        c.dest.add(decl.exported.load)
        c.dest.addSubtree(decl.pragmas)
        c.dest.add(decl.typ.load)
        c.dest.addDotToken()
    
    skip n
  else:
    skip n

proc processNifFile(filename: string, outputFilename: string) =
  if not fileExists(filename):
    quit "File not found: " & filename

  var stream = nifstreams.open(filename)
  defer: nifstreams.close(stream)

  discard processDirectives(stream.r)

  var buf = fromStream(stream)
  var n = beginRead(buf)
  defer: endRead(buf)

  var c = Context(dest: createTokenBuf())
  
  c.dest.buildTree TagId(StmtsS), NoLineInfo:
    ifaceStmt(c, n)
  
  writeFile outputFilename, "(.nif24)\n" & toString(c.dest)

type
  Command = enum
    cmdHelp
    cmdVersion
    cmdRun

proc writeVersion() =
  echo "nifface 0.1"
  quit(0)

proc writeHelp() =
  echo """nifface - Nimony public interface extractor

Usage:
  nifface [options] <command> [file]

Commands:
  run <file.nif>   Extracts the public interface from an input NIF file
  help, -h         Show this help
  version, -v      Show version

Options:
  -o, --output:<file> Specify the output file for the public interface (default: <input>.max_iface.nif)

Examples:
  nifface run mymodule.1.nif
"""
  quit(0)

proc handleCmdLine() =
  var
    cmd = cmdHelp
    inputFile = ""
    outputFile = ""
  
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      case key.normalize
      of "run": cmd = cmdRun
      else:
        if inputFile == "":
          inputFile = key
        else:
          quit "Too many arguments"
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
    if inputFile == "":
      echo "Input file required"
      quit(1)
    
    if outputFile == "":
      outputFile = inputFile.changeFileExt("max_iface.nif")
    
    processNifFile(inputFile, outputFile)


when isMainModule:
  handleCmdLine()
