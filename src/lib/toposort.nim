# Incremental topological sort using Pearce-Kelly algorithm
import std/[algorithm, tables]

type
  PearceKellyTopo*[T] = ref object
    adj: seq[seq[int]]
    radj: seq[seq[int]]
    topo*: seq[int]
    inv: seq[int]
    verts: seq[T]
    pos: Table[T, int]
    visited: seq[bool]

proc contains*[T](g: PearceKellyTopo[T], v: T): bool {.inline.} =
  v in g.pos

proc len*[T](g: PearceKellyTopo[T]): int {.inline.} =
  g.verts.len

proc initPearceKellyTopo*[T](verts: seq[T]): PearceKellyTopo[T] =
  let n = verts.len
  var g = PearceKellyTopo[T](
    adj: newSeq[seq[int]](n),
    radj: newSeq[seq[int]](n),
    topo: newSeq[int](n),
    inv: newSeq[int](n),
    verts: verts,
    visited: newSeq[bool](n))
  for i, v in verts:
    g.pos[v] = i
    g.topo[i] = i
    g.inv[i] = i
  g

proc initPearceKellyTopo*(n: int): PearceKellyTopo[int] =
  var verts = newSeq[int](n)
  for i in 0..<n:
    verts[i] = i
  initPearceKellyTopo(verts)

proc initPearceKellyTopo*[T](order: seq[T], edges: openArray[(T, T)]): PearceKellyTopo[T] =
  let g = initPearceKellyTopo(order)
  for (u, v) in edges:
    g.adj[g.pos[u]].add g.pos[v]
    g.radj[g.pos[v]].add g.pos[u]
  g

proc mergeOrders(a, b: seq[int]): seq[int] =
  # in Pearce-Kelly merge orders look like
  # merge from merge sort
  result = @[]
  var i = 0
  var j = 0
  while i < a.len or j < b.len:
    if j >= b.len or (i < a.len and a[i] <= b[j]): #TODO: remove i < a.len and 
      result.add a[i]
      inc i
    else:
      result.add b[j]
      inc j

proc dfsForward[T](g: var PearceKellyTopo[T], n, ub: int, deltaF: var seq[int], cycle: var bool) =
  var stack = @[n]
  while stack.len > 0 and not cycle:
    let cur = stack.pop()
    if g.visited[cur]: continue

    g.visited[cur] = true
    deltaF.add cur
    for w in g.adj[cur]:
      if g.topo[w] == ub:
        cycle = true
        break
      if not g.visited[w] and g.topo[w] < ub:
        stack.add w

proc dfsBackward[T](g: var PearceKellyTopo[T], n, lb: int, deltaB: var seq[int]) =
  var stack = @[n]
  while stack.len > 0:
    let cur = stack.pop()
    if g.visited[cur]: continue
    
    g.visited[cur] = true
    deltaB.add cur
    for w in g.radj[cur]:
      if not g.visited[w] and lb < g.topo[w]:
        stack.add w

proc reorder[T](g: PearceKellyTopo[T], deltaB, deltaF: var seq[int]) =
  let cmpOrd = proc (a, b: int): int =
    cmp(g.topo[a], g.topo[b])

  deltaB.sort(cmpOrd) # O(n log n)
  deltaF.sort(cmpOrd)

  var L: seq[int] = @[]

  for i, w in deltaB:
    deltaB[i] = g.topo[w]
    g.visited[w] = false
    L.add w

  for i, w in deltaF:
    deltaF[i] = g.topo[w]
    g.visited[w] = false
    L.add w

  let R = mergeOrders(deltaB, deltaF)

  for i, node in L:
    g.topo[node] = R[i]
    g.inv[R[i]] = node

proc addEdge*[T](g: var PearceKellyTopo[T], x, y: T): bool =
  var deltaF: seq[int] = @[]
  var deltaB: seq[int] = @[]
  var cycle = false

  if g.topo[g.pos[y]] < g.topo[g.pos[x]]:
    # dfsForward and dfsBackward require empty state
    for v in g.visited.mitems:
      v = false

    dfsForward(g, g.pos[y], g.topo[g.pos[x]], deltaF, cycle)
    if cycle:
      return false

    dfsBackward(g, g.pos[x], g.topo[g.pos[y]], deltaB)
    reorder(g, deltaB, deltaF)

  g.adj[g.pos[x]].add g.pos[y]
  g.radj[g.pos[y]].add g.pos[x]
  true
