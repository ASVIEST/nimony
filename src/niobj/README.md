# niobj

Niobj is tool for analysing object files using universal NIF format.
It handles ELF and PE formats (Mach-O is not supported) and represent it in universal NIF
code. 
And with NIF code it can perform some analysis.

This can be used for cross-language FFI with generic functions.

Format spec:

| Tag     | Description                                                                                                                              |
|---------|------------------------------------------------------------------------------------------------------------------------------------------|
| arch    | specify target architecture                                                                                                              |
| machine | target CPU (essentially the same as cpusubtype in Mach-O), often skipped,  then any processor of the specified architecture is suitable. |
| type    | specify type: in general "exec", "dynlib", "core", others depend on target format                                                        |
| section | define section like "text", "data", "rodata", "bss", "debugInfo"                                                                                |
| segment | define segment (file parts to memory mapping)                                                                                                   |

References:
<br>
https://github.com/gitGNU/objconv/blob/master/src/elf2mac.cpp<br>
https://gist.github.com/x0nu11byt3/bcb35c3de461e5fb66173071a2379779<br>
https://github.com/aidansteele/osx-abi-macho-file-format-reference<br>
https://intezer.com/blog/research/executable-linkable-format-101-part1-sections-segments/<br>
