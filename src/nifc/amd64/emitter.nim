#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "license.txt", included in this
#    distribution, for details about the copyright.
#

## Emits real ASM code from the NIF based format.

import std / [assertions, syncio, formatfloat]
import nifreader, nifstreams, nifcursors, bitabs, lineinfos
from std / strutils import escape

import asm_model
import ".." / mangler

type
  Context = object
    current: Cursor
    input: TokenBuf
    dest: string
    stack: seq[string]
    inStack: bool
    stackSave: seq[string]

proc fatal*(msg: string) =
  quit msg

proc setupInput(c: var Context; buffer: string) =
  var s = nifstreams.openFromBuffer(buffer)
  let res = processDirectives(s.r)
  assert res == Success
  c.input = default(TokenBuf)
  while true:
    let t = next(s)
    if t.kind == EofToken: break
    c.input.add t

proc startStack(c: var Context) =
  c.inStack = true
  assert len(c.stack) == 0

proc endStack(c: var Context) =
  c.inStack = false
  for i in c.stack:
    c.dest.add i
  c.stack = @[]

proc popStack(c: var Context): string =
  c.stack.pop()

proc addStr(c: var Context, s: string) =
  if not c.inStack: c.dest.add s
  else: c.stack.add s

proc matchIntLit(c: var Context): bool =
  if c.current.kind == IntLit:
    var outp = ""
    outp.addInt pool.integers[c.current.intId]
    c.addStr(outp)

    inc c.current
    result = true
  else:
    result = false

proc matchUIntLit(c: var Context): bool =
  if c.current.kind == UIntLit:
    var outp = ""
    outp.add $pool.uintegers[c.current.uintId]
    c.addStr(outp)
    inc c.current
    result = true
  else:
    result = false

proc matchFloatLit(c: var Context): bool =
  if c.current.kind == FloatLit:
    var outp = ""
    outp.add $cast[int64](pool.floats[c.current.floatId])
    c.addStr(outp)
    inc c.current
    result = true
  else:
    result = false

proc matchStringLit(c: var Context): bool =
  if c.current.kind == StringLit:
    var outp = ""
    outp.add escape(pool.strings[c.current.litId])
    c.addStr(outp)
    inc c.current
    result = true
  else:
    result = false

proc matchIdent(c: var Context): bool =
  if c.current.kind == Ident:
    var outp = ""
    outp.add pool.strings[c.current.litId]
    c.addStr(outp)
    inc c.current
    result = true
  else:
    result = false

proc getStack(c: var Context): seq[string] =
  c.stack

proc restoreStack(c: var Context, stack: seq[string]) =
  c.stack = stack

proc isTag(c: var Context; tag: TagId): bool =
  if c.current.kind == ParLe and c.current.tagId == tag:
    inc c.current
    result = true
  else:
    result = false

proc error(c: var Context; msg: string) {.noreturn.} =
  if c.current.info.isValid:
    let rawInfo = unpack(pool.man, c.current.info)
    if rawInfo.file.isValid:
      echo "[Error] ", pool.files[rawInfo.file] & "(" & $rawInfo.line & ", " & $(rawInfo.col+1) & "): " & msg
    else:
      echo "[Error] ???: " & msg
  else:
    echo "[Error] ???: " & msg
  when defined(debug):
    writeStackTrace()
  quit 1

proc matchParRi(c: var Context): bool =
  if c.current.kind == ParRi:
    inc c.current
    result = true
  else:
    result = false

proc peekParRi(c: var Context): bool {.inline.} =
  c.current.kind == ParRi

proc emitTag(c: var Context; tag: string) =
  var outp = ""
  outp.add tag
  outp.add " "
  c.addStr(outp)

proc emit(c: var Context; token: string) =
  c.addStr(token)

proc matchAndEmitTag(c: var Context; tag: TagId; asStr: string): bool =
  if c.current.kind == ParLe and c.current.tagId == tag:
    emit c, asStr
    inc c.current
    result = c.current.kind == ParRi
    if result:
      inc c.current
  else:
    result = false

proc matchAny(c: var Context): bool =
  result = false

  while true:
    case c.current.kind
    of UnknownToken, DotToken, Ident, Symbol, SymbolDef, StringLit, CharLit, IntLit, UIntLit, FloatLit:
      inc c.current
      result = true
    of EofToken:
      result = false
      break
    of ParRi:
      result = true
      break
    of ParLe:
      var nested = 0
      while true:
        let k = c.current.kind
        inc c.current
        if k == ParLe: inc nested
        elif k == ParRi:
          dec nested
          if nested == 0: break

proc nl(c: var Context) = c.addStr("\n")

proc lookupSym(c: var Context): bool =
  if c.current.kind in {Symbol, Ident}:
    if c.current.kind == Symbol: c.addStr mangle(pool.syms[c.current.symId])
    else: c.addStr mangle(pool.strings[c.current.litId])
      # allowing ident is very strange bug, 
      # for some unknown reason Symbol turns into Ident
      # so it realy need
    inc c.current
    result = true
  else:
    result = false

proc declareSym(c: var Context): bool =
  if c.current.kind == SymbolDef:
    c.addStr mangle(pool.syms[c.current.symId])
    inc c.current
    result = true
  else:
    result = false

template success(b: bool): bool = b

include asm_grammar

proc produceAsmCode*(buffer, outp: string) =
  #registerTags()
  var c = Context()
  setupInput c, buffer
  c.current = beginRead(c.input)
  if not genModule(c):
    error(c, "(stmts) expected")
  endRead(c.input)
  writeFile outp, c.dest
