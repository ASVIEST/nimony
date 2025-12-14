#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Path handling and `exec` like features as `sem.nim` needs it.

from std / strutils import multiReplace, split, strip
import std / [tables, sets, os, syncio, formatfloat, assertions]
from std / osproc import execCmdEx

include nifprelude
import ".." / lib / [nifchecksums, tooldirs, argsfinder]

import nimony_model, symtabs, builtintypes, decls, symparser, asthelpers,
  programs, sigmatch, magics, reporters, nifconfig, nifindexes,
  semdata

import ".." / gear2 / modnames

proc nimonyDir(): string =
  let appDir = getAppDir()
  let (head, tail) = splitPath(appDir)
  if tail == "bin":
    result = head
  else:
    result = appDir

proc stdlibDir*(): string =
  result = nimonyDir() / "lib"

proc setupPaths*(config: var NifConfig) =
  config.paths.add stdlibDir()
  let pathsFile = findArgs(config.baseDir, "nimony.paths")
  processPathsFile pathsFile, config.paths
  #echo getAppFilename(), "CONFIG.BASEDIR: ", config.baseDir, " CONFIG.PATHS: ", config.paths

proc stdlibFile*(f: string): string =
  result = stdlibDir() / f

proc compilerDir*(): string =
  let appDir = getAppDir()
  let (head, tail) = splitPath(appDir)
  if tail == "bin":
    return head
  else: return tail

proc absoluteParentDir*(f: string): string =
  result = f.absolutePath().parentDir()

proc fileExists*(f: string): bool =
  result = os.fileExists(f)

proc toAbsolutePath*(f: string): string =
  if f.isAbsolute: return f
  result = os.absolutePath(f)

proc toAbsolutePath*(f: string, dir: string): string =
  if f.isAbsolute: return f
  result = normalizedPath(dir / f)

proc toRelativePath*(f: string, dir: string): string =
  if not f.isAbsolute: return f
  result = f.relativePath(dir)

proc exec*(cmd: string) =
  if execShellCmd(cmd) != 0: quit("FAILURE: " & cmd)

proc nimexec(cmd: string) =
  let t = findExe("nim")
  if t.len == 0:
    quit("FAILURE: cannot find nim.exe / nim binary")
  exec quoteShell(t) & " " & cmd

proc requiresTool*(tool, src: string; forceRebuild: bool) =
  let t = findTool(tool)
  # XXX: hack for more convenient development
  if not fileExists(t) or forceRebuild:
    let src = compilerDir() / src
    let args = # compiler bin path
      when not defined(debug):
        "c -d:release --outdir:" & binDir()
      else: "c --outdir:" & binDir()
    # compile required tool
    nimexec(args & "  " & src)

proc resolveFile*(paths: openArray[string]; origin: string; toResolve: string): string =
  let nimFile = toResolve.addFileExt(".nim")
  #if toResolve.startsWith("std/") or toResolve.startsWith("ext/"):
  #  result = stdFile nimFile
  if toResolve.isAbsolute:
    result = nimFile
  elif toResolve.len > 0 and toResolve[0] == '$':
    var key = ""
    var i = 1
    while i < toResolve.len:
      if toResolve[i] in {'/', '\\'}:
        break
      key.add toResolve[i]
      inc i
    let val = getEnv(key)
    if val.len == 0:
      result = nimFile
    else:
      result = val / nimFile.substr(i)
  else:
    result = splitFile(origin).dir / nimFile
    var i = 0
    while not fileExists(result) and i < paths.len:
      result = paths[i] / nimFile
      inc i

type
  ImportedFilename* = object
    path*: string ## stringified path from AST that has to be resolved
    name*: string ## extracted module name to define a sym for in `import`
    plugin*: string ## plugin name if any (usually empty)
    isSystem*: bool
  
  FilenameErr* = enum
    UnspecifiedErr
    CyclicPragmaErr

proc moduleNameFromPath*(path: string): string =
  result = splitFile(path).name

proc filenameVal*(n: var Cursor; res: var seq[ImportedFilename]; errors: var set[FilenameErr]; allowAs: bool; allowCyclic: bool = true) =
  case n.kind
  of StringLit:
    let s = pool.strings[n.litId]
    # string literal could contain a path or .nim extension:
    let name = moduleNameFromPath(s)
    res.add ImportedFilename(path: s, name: name)
    inc n
  of Ident:
    let s = pool.strings[n.litId]
    res.add ImportedFilename(path: s, name: s)
    inc n
  of Symbol:
    var s = pool.syms[n.symId]
    extractBasename s
    res.add ImportedFilename(path: s, name: s)
    inc n
  of ParLe:
    case exprKind(n)
    of OchoiceX, CchoiceX:
      inc n
      if n.kind == ParRi:
        errors.incl UnspecifiedErr
      else:
        filenameVal(n, res, errors, allowAs, allowCyclic)
      skipToEnd n
    of QuotedX:
      let s = pool.strings[takeUnquoted(n)]
      res.add ImportedFilename(path: s, name: s)
    of CallX, InfixX:
      var x = n
      skip n # ensure we skipped it completely
      inc x
      let opId = takeIdent(x)
      if opId == StrId(0):
        errors.incl UnspecifiedErr
        return
      let op = pool.strings[opId]
      if op == "as":
        if not allowAs:
          errors.incl UnspecifiedErr
          return
        if x.kind == ParRi:
          errors.incl UnspecifiedErr
          return
        var rhs = x
        skip rhs # skip lhs
        if rhs.kind == ParRi:
          errors.incl UnspecifiedErr
          return
        let aliasId = takeIdent(rhs)
        if aliasId == StrId(0):
          errors.incl UnspecifiedErr
          return
        let alias = pool.strings[aliasId]
        var prefix: seq[ImportedFilename] = @[]
        filenameVal(x, prefix, errors, allowAs = false, allowCyclic)
        if rhs.kind != ParRi or prefix.len == 0:
          errors.incl UnspecifiedErr
        for pre in mitems(prefix):
          res.add ImportedFilename(path: pre.path, name: alias)
      else: # any operator, could restrict to slash-like
        var prefix: seq[ImportedFilename] = @[]
        filenameVal(x, prefix, errors, allowAs = false, allowCyclic)
        var suffix: seq[ImportedFilename] = @[]
        filenameVal(x, suffix, errors, allowAs = allowAs, allowCyclic)
        if x.kind != ParRi or prefix.len == 0 or suffix.len == 0:
          errors.incl UnspecifiedErr
        for pre in mitems(prefix):
          for suf in mitems(suffix):
            res.add ImportedFilename(path: pre.path & op & suf.path, name: suf.name, plugin: suf.plugin)
    of PrefixX:
      var x = n
      skip n # ensure we skipped it completely
      inc x
      let opId = takeIdent(x)
      if opId == StrId(0):
        errors.incl UnspecifiedErr
        return
      let op = pool.strings[opId] # any operator, could restrict to slash-like
      var suffix: seq[ImportedFilename] = @[]
      filenameVal(x, suffix, errors, allowAs = allowAs, allowCyclic)
      if x.kind != ParRi or suffix.len == 0:
        errors.incl UnspecifiedErr
      for suf in mitems(suffix):
        res.add ImportedFilename(path: op & suf.path, name: suf.name, plugin: suf.plugin)
    of ParX, TupX, BracketX:
      inc n
      if n.kind == ParRi:
        errors.incl UnspecifiedErr
      else:
        while n.kind != ParRi:
          filenameVal(n, res, errors, allowAs, allowCyclic)
      inc n
    of AconstrX, TupConstrX:
      inc n
      skip n # skip type
      if n.kind == ParRi:
        errors.incl UnspecifiedErr
      else:
        while n.kind != ParRi:
          filenameVal(n, res, errors, allowAs, allowCyclic)
      inc n
    of PragmaxX:
      let orig = n
      inc n
      let start = res.len
      if n.kind == ParRi:
        errors.incl UnspecifiedErr
      else:
        filenameVal(n, res, errors, allowAs, allowCyclic)
        var success = false
        if n.substructureKind == PragmasU:
          inc n
          if n.substructureKind == KvU:
            inc n
            if n.kind == Ident and pool.strings[n.litId] == "plugin":
              inc n
              if n.kind == StringLit:
                for i in start ..< res.len:
                  res[i].plugin = pool.strings[n.litId]
                  success = true
                inc n
                if n.kind == ParRi: inc n
                else: errors.incl UnspecifiedErr
          elif n.kind == Ident and pool.strings[n.litId] == "cyclic":
            if not allowCyclic:
              errors.incl CyclicPragmaErr
            success = true
            inc n # ident
            inc n # pragmas ParRi
            inc n # pragmax ParRi
        if not success:
          n = orig
          skip n
          errors.incl UnspecifiedErr
    else:
      errors.incl UnspecifiedErr
      skip n
  else:
    errors.incl UnspecifiedErr
    skip n

proc replaceSubs*(fmt, currentFile: string; config: NifConfig): string =
  # Unpack Current File to Absolute
  let nifcache = config.nifcachePath
  var path = absolutePath(currentFile)
  if os.fileExists(path):
    path = parentDir(path)
  # Replace matches with paths
  path = fmt.multiReplace(
    ("${path}", path),
    ("${nifcache}", nifcache))
  result = path.normalizedPath()

# ------------------ include/import handling ------------------------

proc parseFile*(nimFile: string; paths: openArray[string], nifcachePath: string): TokenBuf =
  let nifler = findTool("nifler")
  let name = moduleSuffix(nimFile, paths)
  let src = nifcachePath / name & ".p.nif"
  exec quoteShell(nifler) & " --portablePaths --deps parse " & quoteShell(nimFile) & " " &
    quoteShell(src)

  var stream = nifstreams.open(src)
  try:
    discard processDirectives(stream.r)
    result = fromStream(stream)
  finally:
    nifstreams.close(stream)

proc parseFileIntoFile*(nimFile: string; paths: openArray[string], nifcachePath: string): string =
  let nifler = findTool("nifler")
  let name = moduleSuffix(nimFile, paths)
  let src = nifcachePath / name & ".p.nif"
  exec quoteShell(nifler) & " --portablePaths --deps parse " & quoteShell(nimFile) & " " &
    quoteShell(src)
  
  src

proc getFile*(info: PackedLineInfo): string =
  let fid = unpack(pool.man, info).file
  if fid.isValid:
    result = pool.files[fid]
  else:
    result = ""

proc selfExec*(c: var SemContext; file: string; moreArgs: string) =
  let nimonyExe = findTool("nimony")
  exec quoteShell(nimonyExe) & c.commandLineArgs & moreArgs & " --ischild m " & quoteShell(file)
  #exec os.getAppFilename() & c.commandLineArgs & moreArgs & " --ischild m " & quoteShell(file)

# ------------------ plugin handling --------------------------

proc compilePlugin(c: var SemContext; info: PackedLineInfo; nf, exefile: string) =
  let pluginDir = nimonyDir() / "src/nimony/lib"
  let cmd = "nim c -d:nimonyPlugin -o:" & quoteShell(exefile) & " -p:" & quoteShell(pluginDir) &
    " " & quoteShell(nf)
  exec cmd

proc writeFileIfChanged(file, content: string) =
  if fileExists(file) and readFile(file) == content:
    # do not touch the timestamp
    discard "nothing to do here"
  else:
    writeFile file, content

proc runPlugin*(c: var SemContext; dest: var TokenBuf; info: PackedLineInfo; pluginName, input: string;
                additionalInput = "") =
  let p = splitFile(pluginName)
  let checksumA = if additionalInput.len > 0: "_" & computeChecksum(additionalInput) else: ""
  let basename = c.g.config.nifcachePath / p.name & "_" & computeChecksum(input) & checksumA
  let inputFile = basename & ".in.nif"
  let outputFile = basename & ".out.nif"
  let inputFileB = basename & ".types.nif"
  let pluginExe = c.g.config.nifcachePath / p.name.addFileExt(ExeExt)

  let nf = resolveFile(c.g.config.paths, getFile(info), pluginName)
  if needsRecompile(nf, pluginExe):
    compilePlugin(c, info, nf, pluginExe)

  writeFileIfChanged(inputFile, input)
  if additionalInput.len > 0:
    writeFileIfChanged(inputFileB, additionalInput)

  if needsRecompile(pluginExe, outputFile):
    var cmd = quoteShell(pluginExe) & " " & quoteShell(inputFile) & " " & quoteShell(outputFile)
    if additionalInput.len > 0:
      cmd &= " "
      cmd &= quoteShell(inputFileB)
    exec cmd
  var s = nifstreams.open(outputFile)
  try:
    parse s, dest, NoLineInfo
  finally:
    close s

proc runProgram(file: string; usedModules: HashSet[string]): tuple[output: string, exitCode: int] =
  let nimonyExe = findTool("nimsem")
  var cmd = quoteShell(nimonyExe) & " e " & quoteShell(file)
  for module in usedModules:
    cmd &= " " & quoteShell(module)
  result = execCmdEx(cmd)

const
  writeNifModuleSuffix* = "wriwhv7qv"

proc prepareEval*(c: var SemContext): string =
  if not c.checkedForWriteNifModule:
    c.checkedForWriteNifModule = true
    if not fileExists(c.g.config.nifcachePath / writeNifModuleSuffix & ".s.nif"):
      # precompile the module
      let nimonyExe = findTool("nimony")
      var cmd = quoteShell(nimonyExe) & " c " & quoteShell(stdlibFile("std/writenif.nim"))
      let (output, exitCode) = execCmdEx(cmd)
      if exitCode != 0:
        return ensureMove(output)
  return ""

proc runEval*(c: var SemContext; dest: var TokenBuf; srcName: string; src: TokenBuf; usedModules: HashSet[string]): string =
  ## Returns an error message if the evaluation failed, "" on success.
  #echo "HEREES ", toString(src, false)
  let progfile = c.g.config.nifcachePath / srcName.addFileExt(".2.nif")
  writeFileAndIndex(progfile, src)

  let (output, exitCode) = runProgram(progfile, usedModules)
  if exitCode != 0:
    result = ensureMove(output)
  else:
    let outfile = c.g.config.nifcachePath / srcName.addFileExt(".out.nif")
    var s = nifstreams.open(outfile)
    try:
      parse s, dest, NoLineInfo
    finally:
      close s
    result = ""
