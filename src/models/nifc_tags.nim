# Generated by tools/gen_tags.nim from doc/tags.md. DO NOT EDIT!

import tags

type
  NifcExpr* = enum
    NoExpr
    SufC = (ord(SufTagId), "suf")  ## literal with suffix annotation
    AtC = (ord(AtTagId), "at")  ## array indexing operation
    DerefC = (ord(DerefTagId), "deref")  ## pointer deref operation
    DotC = (ord(DotTagId), "dot")  ## object field selection
    PatC = (ord(PatTagId), "pat")  ## pointer indexing operation
    ParC = (ord(ParTagId), "par")  ## syntactic parenthesis
    AddrC = (ord(AddrTagId), "addr")  ## address of operation
    NilC = (ord(NilTagId), "nil")  ## nil pointer value
    InfC = (ord(InfTagId), "inf")  ## positive infinity floating point value
    NeginfC = (ord(NeginfTagId), "neginf")  ## negative infinity floating point value
    NanC = (ord(NanTagId), "nan")  ## NaN floating point value
    FalseC = (ord(FalseTagId), "false")  ## boolean `false` value
    TrueC = (ord(TrueTagId), "true")  ## boolean `true` value
    AndC = (ord(AndTagId), "and")  ## boolean `and` operation
    OrC = (ord(OrTagId), "or")  ## boolean `or` operation
    NotC = (ord(NotTagId), "not")  ## boolean `not` operation
    NegC = (ord(NegTagId), "neg")  ## negation operation
    SizeofC = (ord(SizeofTagId), "sizeof")  ## `sizeof` operation
    AlignofC = (ord(AlignofTagId), "alignof")  ## `alignof` operation
    OffsetofC = (ord(OffsetofTagId), "offsetof")  ## `offsetof` operation
    OconstrC = (ord(OconstrTagId), "oconstr")  ## object constructor
    AconstrC = (ord(AconstrTagId), "aconstr")  ## array constructor
    OvfC = (ord(OvfTagId), "ovf")  ## access overflow flag
    AddC = (ord(AddTagId), "add")
    SubC = (ord(SubTagId), "sub")
    MulC = (ord(MulTagId), "mul")
    DivC = (ord(DivTagId), "div")
    ModC = (ord(ModTagId), "mod")
    ShrC = (ord(ShrTagId), "shr")
    ShlC = (ord(ShlTagId), "shl")
    BitandC = (ord(BitandTagId), "bitand")
    BitorC = (ord(BitorTagId), "bitor")
    BitxorC = (ord(BitxorTagId), "bitxor")
    BitnotC = (ord(BitnotTagId), "bitnot")
    EqC = (ord(EqTagId), "eq")
    NeqC = (ord(NeqTagId), "neq")
    LeC = (ord(LeTagId), "le")
    LtC = (ord(LtTagId), "lt")
    CastC = (ord(CastTagId), "cast")  ## `cast` operation
    ConvC = (ord(ConvTagId), "conv")  ## type conversion
    CallC = (ord(CallTagId), "call")  ## call operation
    ErrvC = (ord(ErrvTagId), "errv")  ## error flag for `NIFC`

proc rawTagIsNifcExpr*(raw: TagEnum): bool {.inline.} =
  raw in {SufTagId, AtTagId, DerefTagId, DotTagId, PatTagId, ParTagId, AddrTagId, NilTagId, InfTagId, NeginfTagId, NanTagId, FalseTagId, TrueTagId, AndTagId, OrTagId, NotTagId, NegTagId, SizeofTagId, AlignofTagId, OffsetofTagId, OconstrTagId, AconstrTagId, OvfTagId, AddTagId, SubTagId, MulTagId, DivTagId, ModTagId, ShrTagId, ShlTagId, BitandTagId, BitorTagId, BitxorTagId, BitnotTagId, EqTagId, NeqTagId, LeTagId, LtTagId, CastTagId, ConvTagId, CallTagId, ErrvTagId}

type
  NifcStmt* = enum
    NoStmt
    CallS = (ord(CallTagId), "call")  ## call operation
    GvarS = (ord(GvarTagId), "gvar")  ## global variable declaration
    TvarS = (ord(TvarTagId), "tvar")  ## thread local variable declaration
    VarS = (ord(VarTagId), "var")  ## variable declaration
    ConstS = (ord(ConstTagId), "const")  ## const variable declaration
    ProcS = (ord(ProcTagId), "proc")  ## proc declaration
    TypeS = (ord(TypeTagId), "type")  ## type declaration
    EmitS = (ord(EmitTagId), "emit")  ## emit statement
    AsgnS = (ord(AsgnTagId), "asgn")  ## assignment statement
    KeepovfS = (ord(KeepovfTagId), "keepovf")  ## keep overflow flag statement
    ScopeS = (ord(ScopeTagId), "scope")  ## explicit scope annotation, like `stmts`
    IfS = (ord(IfTagId), "if")  ## if statement header
    BreakS = (ord(BreakTagId), "break")  ## `break` statement
    WhileS = (ord(WhileTagId), "while")  ## `while` statement
    CaseS = (ord(CaseTagId), "case")  ## `case` statement
    LabS = (ord(LabTagId), "lab")  ## label, target of a `jmp` instruction
    JmpS = (ord(JmpTagId), "jmp")  ## jump/goto instruction
    RetS = (ord(RetTagId), "ret")  ## `return` instruction
    StmtsS = (ord(StmtsTagId), "stmts")  ## list of statements
    ImpS = (ord(ImpTagId), "imp")  ## import declaration
    InclS = (ord(InclTagId), "incl")  ## `#include` statement or `incl` set operation
    DiscardS = (ord(DiscardTagId), "discard")  ## `discard` statement
    TryS = (ord(TryTagId), "try")  ## `try` statement
    RaiseS = (ord(RaiseTagId), "raise")  ## `raise` statement
    OnerrS = (ord(OnerrTagId), "onerr")  ## error handling statement

proc rawTagIsNifcStmt*(raw: TagEnum): bool {.inline.} =
  raw in {CallTagId, GvarTagId, TvarTagId, VarTagId, ConstTagId, ProcTagId, TypeTagId, EmitTagId, AsgnTagId, KeepovfTagId, ScopeTagId, IfTagId, BreakTagId, WhileTagId, CaseTagId, LabTagId, JmpTagId, RetTagId, StmtsTagId, ImpTagId, InclTagId, DiscardTagId, TryTagId, RaiseTagId, OnerrTagId}

type
  NifcType* = enum
    NoType
    ParamsT = (ord(ParamsTagId), "params")  ## list of proc parameters, also used as a "proc type"
    UnionT = (ord(UnionTagId), "union")  ## union declaration
    ObjectT = (ord(ObjectTagId), "object")  ## object type declaration
    EnumT = (ord(EnumTagId), "enum")  ## enum type declaration
    ProctypeT = (ord(ProctypeTagId), "proctype")  ## proc type declaration (soon obsolete, use params instead)
    IT = (ord(ITagId), "i")  ## `int` builtin type
    UT = (ord(UTagId), "u")  ## `uint` builtin type
    FT = (ord(FTagId), "f")  ## `float` builtin type
    CT = (ord(CTagId), "c")  ## `char` builtin type
    BoolT = (ord(BoolTagId), "bool")  ## `bool` builtin type
    VoidT = (ord(VoidTagId), "void")  ## `void` return type
    PtrT = (ord(PtrTagId), "ptr")  ## `ptr` type contructor
    ArrayT = (ord(ArrayTagId), "array")  ## `array` type constructor
    FlexarrayT = (ord(FlexarrayTagId), "flexarray")  ## `flexarray` type constructor
    AptrT = (ord(AptrTagId), "aptr")  ## "pointer to array of" type constructor

proc rawTagIsNifcType*(raw: TagEnum): bool {.inline.} =
  raw in {ParamsTagId, UnionTagId, ObjectTagId, EnumTagId, ProctypeTagId, ITagId, UTagId, FTagId, CTagId, BoolTagId, VoidTagId, PtrTagId, ArrayTagId, FlexarrayTagId, AptrTagId}

type
  NifcOther* = enum
    NoSub
    KvU = (ord(KvTagId), "kv")  ## key-value pair
    RangeU = (ord(RangeTagId), "range")  ## `(range a b)` construct
    RangesU = (ord(RangesTagId), "ranges")
    ParamU = (ord(ParamTagId), "param")  ## parameter declaration
    TypevarU = (ord(TypevarTagId), "typevar")  ## type variable declaration
    EfldU = (ord(EfldTagId), "efld")  ## enum field declaration
    FldU = (ord(FldTagId), "fld")  ## field declaration
    ElifU = (ord(ElifTagId), "elif")  ## pair of (condition, action)
    ElseU = (ord(ElseTagId), "else")  ## `else` action
    OfU = (ord(OfTagId), "of")  ## `of` branch within a `case` statement
    PragmasU = (ord(PragmasTagId), "pragmas")  ## begin of pragma section

proc rawTagIsNifcOther*(raw: TagEnum): bool {.inline.} =
  raw in {KvTagId, RangeTagId, RangesTagId, ParamTagId, TypevarTagId, EfldTagId, FldTagId, ElifTagId, ElseTagId, OfTagId, PragmasTagId}

type
  NifcPragma* = enum
    NoPragma
    InlineP = (ord(InlineTagId), "inline")  ## `inline` proc annotation
    NoinlineP = (ord(NoinlineTagId), "noinline")  ## `noinline` proc annotation
    AttrP = (ord(AttrTagId), "attr")  ## general attribute annoation
    VarargsP = (ord(VarargsTagId), "varargs")  ## `varargs` proc annotation
    WasP = (ord(WasTagId), "was")
    SelectanyP = (ord(SelectanyTagId), "selectany")
    AlignP = (ord(AlignTagId), "align")
    BitsP = (ord(BitsTagId), "bits")
    VectorP = (ord(VectorTagId), "vector")
    NodeclP = (ord(NodeclTagId), "nodecl")  ## `nodecl` annotation
    RaisesP = (ord(RaisesTagId), "raises")  ## proc annotation
    ErrsP = (ord(ErrsTagId), "errs")  ## proc annotation
    StaticP = (ord(StaticTagId), "static")  ## `static` type or annotation

proc rawTagIsNifcPragma*(raw: TagEnum): bool {.inline.} =
  raw in {InlineTagId, NoinlineTagId, AttrTagId, VarargsTagId, WasTagId, SelectanyTagId, AlignTagId, BitsTagId, VectorTagId, NodeclTagId, RaisesTagId, ErrsTagId, StaticTagId}

type
  NifcTypeQualifier* = enum
    NoQualifier
    AtomicQ = (ord(AtomicTagId), "atomic")  ## `atomic` type qualifier for NIFC
    RoQ = (ord(RoTagId), "ro")  ## `readonly` (= `const`) type qualifier for NIFC
    RestrictQ = (ord(RestrictTagId), "restrict")  ## type qualifier for NIFC
    CpprefQ = (ord(CpprefTagId), "cppref")  ## type qualifier for NIFC that provides a C++ reference

proc rawTagIsNifcTypeQualifier*(raw: TagEnum): bool {.inline.} =
  raw >= AtomicTagId and raw <= CpprefTagId

type
  NifcSym* = enum
    NoSym
    GvarY = (ord(GvarTagId), "gvar")  ## global variable declaration
    TvarY = (ord(TvarTagId), "tvar")  ## thread local variable declaration
    VarY = (ord(VarTagId), "var")  ## variable declaration
    ParamY = (ord(ParamTagId), "param")  ## parameter declaration
    ConstY = (ord(ConstTagId), "const")  ## const variable declaration
    EfldY = (ord(EfldTagId), "efld")  ## enum field declaration
    FldY = (ord(FldTagId), "fld")  ## field declaration
    ProcY = (ord(ProcTagId), "proc")  ## proc declaration
    LabY = (ord(LabTagId), "lab")  ## label, target of a `jmp` instruction

proc rawTagIsNifcSym*(raw: TagEnum): bool {.inline.} =
  raw in {GvarTagId, TvarTagId, VarTagId, ParamTagId, ConstTagId, EfldTagId, FldTagId, ProcTagId, LabTagId}

