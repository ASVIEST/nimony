import deps/minlineimportc
import std/syncio

callcfunc()
callcfuncInline()
assert callcfuncWithParam(123) == 123
assert callcfuncWithParamInline(321) == 321
