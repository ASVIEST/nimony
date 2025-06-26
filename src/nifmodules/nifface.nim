## Simple program that get maximum public interface of module
## It need to say that file that depend on other file not need to be
## recompiled because public interface not changed
## maximum means that it not fully accurate because it can depend on when conditions
## and if ident can be exported in at least one branch, then it will be in public interface
## It also usefull for cyclic modules, partialsem should run on full SCC only if some of modules changed partial interface. 

import std / [parseopt, strutils, assertions, os]
import ".." / lib / [nifstreams, nifcursors, bitabs, lineinfos, nifreader, nifbuilder]
import ".." / nimony / nimony_model

type
  Context = object
    b: Builder

proc ifaceGen(c: var Context; n: var Cursor) =
  c.b.addHeader "nimony", "nifface"
  c.b.addTree("stmts")

  c.b.endTree()

proc processNifFile(filename: string, outputFilename: string) =
  if not fileExists(filename):
    quit "File not found: " & filename

  var stream = nifstreams.open(filename)
  defer: nifstreams.close(stream)

  discard processDirectives(stream.r)

  var buf = fromStream(stream)
  var n = beginRead(buf)
  defer: endRead(buf)

  var b = nifbuilder.open(outputFilename)
  var c = Context(b: b)
  c.ifaceGen(n)
  c.b.close()

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