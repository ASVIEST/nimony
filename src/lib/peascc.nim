## Implements Pearce algorithm for SCC finding in graph
## The only difference is the use of tables
import std/tables

type
  PeaSccContext[T] = object
    rindex: Table[T, int]
    index: int
    c: int
    vertexStack: seq[T]
    indexStack: seq[int]
    root: Table[T, bool]
    s: seq[T] # in some implementations it used with only with vS but it incorrect
                   # (https://github.com/php/php-src/pull/12528#issue-1963500321)
    
    vertexInvocations {.requiresInit.}: Table[T, seq[T]] # E(v)

proc beginVisiting[T](c: var PeaSccContext[T], vertex: T) =
  c.vertexStack.add vertex
  c.indexStack.add 0
  c.root[vertex] = true
  c.rindex[vertex] = c.index
  inc c.index

proc finishEdge[T](c: var PeaSccContext[T], vertex: T, k: int) =
  let w = c.vertexInvocations[vertex][k]
  if c.rindex[w] < c.rindex[vertex]:
    c.rindex[vertex] = c.rindex[w]
    c.root[vertex] = false

proc beginEdge[T](c: var PeaSccContext[T], vertex: T, k: int): bool =
  let w = c.vertexInvocations[vertex][k]
  if c.rindex[w] == 0:
    c.indexStack[^1] = k + 1
    c.beginVisiting(w)
    true
  else:
    false

proc finishVisiting[T](c: var PeaSccContext[T], vertex: T) =
  discard c.vertexStack.pop()
  discard c.indexStack.pop()
  if c.root[vertex]:
    dec c.index
    while c.s.len > 0 and c.rindex[vertex] <= c.rindex[c.s[^1]]:
      let w = c.s.pop()
      c.rindex[w] = c.c
      dec c.index
    c.rindex[vertex] = c.c
    dec c.c
  else:
    c.s.add vertex

proc visitLoop[T](c: var PeaSccContext[T]) =
  let vertex = c.vertexStack[^1]
  var i = c.indexStack[^1]
  let verticesCnt = len(c.vertexInvocations[vertex])
  while i <= verticesCnt:
    if i > 0: c.finishEdge(vertex, i-1)
    if i < verticesCnt and c.beginEdge(vertex, i): return
    inc i
  c.finishVisiting(vertex)

proc visit[T](c: var PeaSccContext, vertex: T) =
  c.beginVisiting(vertex)
  while c.vertexStack.len > 0:
    c.visitLoop()

proc findSccs*[T](invocations: Table[T, seq[T]]): Table[T, int] =
  # find SCCs using Pearce's algorithm
  # see https://www.sciencedirect.com/science/article/abs/pii/S0020019015001532
  #     https://www.timl.id.au/scc
  #   
  var s = PeaSccContext[T](vertexInvocations: invocations)
  for vertex in invocations.keys:
    s.rindex[vertex] = 0
  
  s.index = 1
  s.c = invocations.len - 1
  for vertex in invocations.keys:
    if s.rindex[vertex] == 0:
      s.visit(vertex)
  s.rindex
