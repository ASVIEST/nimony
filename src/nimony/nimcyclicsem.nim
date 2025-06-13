## nimcyclicsem is part of semantic checker that used
## before nimsem. It working for cyclic import group (realy SCC)
## Unfortunately, this requires restarting on the entire SCC,
## but fortunately SC is usually small (maximum of 3-4 modules)
## tasks:
## 1. Apply some required sem (recursively):
##      analyzes the declarations for Types, When stategments, Consts, Procs (currently only signature)
##      and get it dependences
##      build DAG for dependences, apply topological sort
##      and you have correct order to semcheck stategments
##      run sem for it, then add to common file (.cyclic.nif and .cyclic.idx.nif)
##      final.
##
##      when nifmake working with SCC it should add this files to nimsem.
##      Nimsem use common constructs from .cyclic.nif that used between modules
##      and not trying to semcheck it
##
## 2. Generate variable initalize list (file .init.nif):
##    requires checking that variable changed in module scope
##    (it should not be reassigned)
##    # a.nim
##    import b
##    var foo* = baz
##    var buz* = 10
##    # b.nim
##    import a
##    var bar* = buz
##    
##    algorithm: build DAG for variables, apply topological sort
##    and you have [a.buz, b.bar, a.foo] - correct initalize list
##    create .init.nif
##    final.
