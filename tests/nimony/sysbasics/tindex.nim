proc main() =
  var arr: array[3, int]
  var str: string
  var cstr: cstring
  let x = arr[1]
  let xt: int = x
  arr[1] = x
  when false:
    let y = str[1]
    let yt: char = y
    str[1] = y
  let z = cstr[1]
  let zt: char = z
  cstr[1] = zt

  var tup: tuple[a: int, b: string, c: bool]
  let t1 = tup[0]
  let t1t: int = t1
  tup[0] = t1t
  let t2 = tup[1]
  let t2t: string = t2
  tup[1] = t2t
  let t3 = tup[2]
  let t3t: bool = t3
  tup[2] = t3t
