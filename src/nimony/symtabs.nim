#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

import std / [tables]
include ".." / lib / nifprelude
import nimony_model

const
  InvalidPos* = -1
  ImportedPos* = -2

type
  Sym* = object
    kind*: SymKind
    name*: SymId
    pos*: int

  ScopeKind* = enum
    NormalScope, ToplevelScope, ImportScope
  Scope* {.acyclic.} = ref object
    tab*: Table[StrId, seq[Sym]] # 'seq' because of overloading
    
    undo: seq[Table[StrId, int]] # len of 'key' to reset tab[key] to.
    indexMap: Table[int, int] # id to index in undo
    idMap: seq[int] # index to id in undo
    shadowScopeId: int
    freezed: Table[int, bool]
    
    up*: Scope
    kind*: ScopeKind

proc openShadowScope*(s: Scope): int =
  result = s.shadowScopeId
  s.undo.add initTable[StrId, int]()
  s.idMap.add s.shadowScopeId
  s.indexMap[s.shadowScopeId] = s.undo.len - 1
  s.freezed[s.shadowScopeId] = false
  inc s.shadowScopeId

proc freezeShadowScope*(s: Scope, id: int) {.inline.} =
  s.freezed[id] = true

proc freezeShadowScope*(s: Scope) {.inline.} =
  s.freezeShadowScope s.idMap[s.undo.len - 1]

proc commitShadowScope*(s: Scope, id: int) {.inline.} =
  let idx = s.indexMap[id]
  let last = s.undo.len - 1
  if idx != last:
    # because order of undo is not important.
    # swap allow to have O(1) for commit
    swap(s.undo[idx], s.undo[last])
    swap(s.idMap[idx], s.idMap[last])
    s.indexMap[s.idMap[idx]] = idx
  
  s.idMap.shrink last
  s.indexMap.del(id)
  s.undo.shrink last
  s.freezed.del id

proc rollbackShadowScope*(s: Scope, id: int) =
  for k, oldLen in pairs(s.undo[s.indexMap[id]]):
    s.tab[k].shrink oldLen
  s.commitShadowScope id

proc commitShadowScope*(s: Scope) {.inline.} =
  s.commitShadowScope s.idMap[s.undo.len - 1]

proc rollbackShadowScope*(s: Scope) =
  s.rollbackShadowScope s.idMap[s.undo.len - 1]

proc remember(s: Scope; name: StrId) {.inline.} =
  let last = s.undo.len - 1
  if last >= 0 and not s.freezed[s.idMap[last]]:
    if not s.undo[last].hasKey(name):
      s.undo[last][name] = s.tab.getOrDefault(name).len

proc rememberZero(s: Scope; name: StrId) {.inline.} =
  let last = s.undo.len - 1
  if last >= 0 and not s.freezed[s.idMap[last]]:
    if not s.undo[last].hasKey(name):
      s.undo[last][name] = 0

proc isUnderscore*(lit: StrId): bool =
  # could speed up by caching id of _
  result = pool.strings[lit] == "_"

proc addOverloadable*(s: Scope; name: StrId; sym: Sym) =
  if not isUnderscore(name):
    s.remember name
    s.tab.mgetOrPut(name, @[]).add sym

type
  AddStatus* = enum
    Conflict, Success

proc addNonOverloadable*(s: Scope; name: StrId; sym: Sym): AddStatus =
  if isUnderscore(name):
    return Success
  let existing = s.tab.getOrDefault(name)
  if existing.len == 0:
    # no error
    s.rememberZero name
    s.tab.mgetOrPut(name, @[]).add sym
    result = Success
  else:
    # error: symbol already exists of the same name:
    result = Conflict
