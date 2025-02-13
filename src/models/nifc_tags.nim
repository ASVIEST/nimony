# Generated by tools/gen_tags.nim from doc/tags.md. DO NOT EDIT!


type
  NifcExpr* = enum
    NoExpr
    SufC = (2, "suf")  ## literal with suffix annotation
    AtC = (3, "at")  ## array indexing operation
    DerefC = (4, "deref")  ## pointer deref operation
    DotC = (5, "dot")  ## object field selection
    PatC = (6, "pat")  ## pointer indexing operation
    ParC = (7, "par")  ## syntactic parenthesis
    AddrC = (8, "addr")  ## address of operation
    NilC = (9, "nil")  ## nil pointer value
    InfC = (10, "inf")  ## positive infinity floating point value
    NeginfC = (11, "neginf")  ## negative infinity floating point value
    NanC = (12, "nan")  ## NaN floating point value
    FalseC = (13, "false")  ## boolean `false` value
    TrueC = (14, "true")  ## boolean `true` value
    AndC = (15, "and")  ## boolean `and` operation
    OrC = (16, "or")  ## boolean `or` operation
    NotC = (17, "not")  ## boolean `not` operation
    NegC = (18, "neg")  ## negation operation
    SizeofC = (19, "sizeof")  ## `sizeof` operation
    AlignofC = (20, "alignof")  ## `alignof` operation
    OffsetofC = (21, "offsetof")  ## `offsetof` operation
    OconstrC = (22, "oconstr")  ## object constructor
    AconstrC = (24, "aconstr")  ## array constructor
    AddC = (29, "add")
    SubC = (30, "sub")
    MulC = (31, "mul")
    DivC = (32, "div")
    ModC = (33, "mod")
    ShrC = (34, "shr")
    ShlC = (35, "shl")
    BitandC = (36, "bitand")
    BitorC = (37, "bitor")
    BitxorC = (38, "bitxor")
    BitnotC = (39, "bitnot")
    EqC = (40, "eq")
    NeqC = (41, "neq")
    LeC = (42, "le")
    LtC = (43, "lt")
    CastC = (44, "cast")
    ConvC = (45, "conv")  ## type conversion
    CallC = (46, "call")  ## call operation
    ErrvC = (246, "errv")  ## error flag for `NIFC`

proc rawTagIsNifcExpr*(raw: uint32): bool {.inline.} =
  raw <= 255'u32 and raw.uint8 in {2'u8, 3'u8, 4'u8, 5'u8, 6'u8, 7'u8, 8'u8, 9'u8, 10'u8, 11'u8, 12'u8, 13'u8, 14'u8, 15'u8, 16'u8, 17'u8, 18'u8, 19'u8, 20'u8, 21'u8, 22'u8, 24'u8, 29'u8, 30'u8, 31'u8, 32'u8, 33'u8, 34'u8, 35'u8, 36'u8, 37'u8, 38'u8, 39'u8, 40'u8, 41'u8, 42'u8, 43'u8, 44'u8, 45'u8, 46'u8, 246'u8}

type
  NifcStmt* = enum
    NoStmt
    CallS = (46, "call")  ## call operation
    GvarS = (50, "gvar")  ## global variable declaration
    TvarS = (51, "tvar")  ## thread local variable declaration
    VarS = (52, "var")  ## variable declaration
    ConstS = (54, "const")  ## const variable declaration
    ProcS = (61, "proc")  ## proc declaration
    TypeS = (68, "type")  ## type declaration
    EmitS = (73, "emit")  ## emit statement
    AsgnS = (74, "asgn")  ## assignment statement
    ScopeS = (75, "scope")  ## explicit scope annotation, like `stmts`
    IfS = (76, "if")  ## if statement header
    BreakS = (81, "break")  ## `break` statement
    WhileS = (84, "while")  ## `while` statement
    CaseS = (85, "case")  ## `case` statement
    LabS = (87, "lab")  ## label, target of a `jmp` instruction
    JmpS = (88, "jmp")  ## jump/goto instruction
    RetS = (89, "ret")  ## `return` instruction
    StmtsS = (91, "stmts")  ## list of statements
    ImpS = (130, "imp")  ## import declaration
    InclS = (132, "incl")  ## `#include` statement or `incl` set operation
    DiscardS = (140, "discard")  ## `discard` statement
    TryS = (141, "try")  ## `try` statement
    RaiseS = (142, "raise")  ## `raise` statement
    OnerrS = (143, "onerr")  ## error handling statement

proc rawTagIsNifcStmt*(raw: uint32): bool {.inline.} =
  raw <= 255'u32 and raw.uint8 in {46'u8, 50'u8, 51'u8, 52'u8, 54'u8, 61'u8, 68'u8, 73'u8, 74'u8, 75'u8, 76'u8, 81'u8, 84'u8, 85'u8, 87'u8, 88'u8, 89'u8, 91'u8, 130'u8, 132'u8, 140'u8, 141'u8, 142'u8, 143'u8}

type
  NifcType* = enum
    NoType
    ParamsT = (92, "params")  ## list of proc parameters, also used as a "proc type"
    UnionT = (93, "union")  ## union declaration
    ObjectT = (94, "object")  ## object type declaration
    EnumT = (95, "enum")  ## enum type declaration
    ProctypeT = (96, "proctype")  ## proc type declaration (soon obsolete, use params instead)
    IT = (101, "i")  ## `int` builtin type
    UT = (102, "u")  ## `uint` builtin type
    FT = (103, "f")  ## `float` builtin type
    CT = (104, "c")  ## `char` builtin type
    BoolT = (105, "bool")  ## `bool` builtin type
    VoidT = (106, "void")  ## `void` return type
    PtrT = (107, "ptr")  ## `ptr` type contructor
    ArrayT = (108, "array")  ## `array` type constructor
    FlexarrayT = (109, "flexarray")  ## `flexarray` type constructor
    AptrT = (110, "aptr")  ## "pointer to array of" type constructor

proc rawTagIsNifcType*(raw: uint32): bool {.inline.} =
  raw <= 255'u32 and raw.uint8 in {92'u8, 93'u8, 94'u8, 95'u8, 96'u8, 101'u8, 102'u8, 103'u8, 104'u8, 105'u8, 106'u8, 107'u8, 108'u8, 109'u8, 110'u8}

type
  NifcOther* = enum
    NoSub
    KvU = (28, "kv")  ## key-value pair
    RangeU = (48, "range")  ## `(range a b)` construct
    RangesU = (49, "ranges")
    ParamU = (53, "param")  ## parameter declaration
    TypevarU = (58, "typevar")  ## type variable declaration
    EfldU = (59, "efld")  ## enum field declaration
    FldU = (60, "fld")  ## field declaration
    ElifU = (78, "elif")  ## pair of (condition, action)
    ElseU = (79, "else")  ## `else` action
    OfU = (86, "of")  ## `of` branch within a `case` statement
    PragmasU = (126, "pragmas")  ## begin of pragma section

proc rawTagIsNifcOther*(raw: uint32): bool {.inline.} =
  raw <= 255'u32 and raw.uint8 in {28'u8, 48'u8, 49'u8, 53'u8, 58'u8, 59'u8, 60'u8, 78'u8, 79'u8, 86'u8, 126'u8}

type
  NifcPragma* = enum
    NoPragma
    InlineP = (120, "inline")  ## `inline` proc annotation
    NoinlineP = (121, "noinline")  ## `noinline` proc annotation
    AttrP = (122, "attr")  ## general attribute annoation
    VarargsP = (123, "varargs")  ## `varargs` proc annotation
    WasP = (124, "was")
    SelectanyP = (125, "selectany")
    AlignP = (127, "align")
    BitsP = (128, "bits")
    VectorP = (129, "vector")
    NodeclP = (131, "nodecl")  ## `nodecl` annotation
    RaisesP = (144, "raises")  ## proc annotation
    ErrsP = (145, "errs")  ## proc annotation
    StaticP = (146, "static")  ## `static` type or annotation

proc rawTagIsNifcPragma*(raw: uint32): bool {.inline.} =
  raw <= 255'u32 and raw.uint8 in {120'u8, 121'u8, 122'u8, 123'u8, 124'u8, 125'u8, 127'u8, 128'u8, 129'u8, 131'u8, 144'u8, 145'u8, 146'u8}

type
  NifcTypeQualifier* = enum
    NoQualifier
    AtomicQ = (97, "atomic")  ## `atomic` type qualifier for NIFC
    RoQ = (98, "ro")  ## `readonly` (= `const`) type qualifier for NIFC
    RestrictQ = (99, "restrict")  ## type qualifier for NIFC
    CpprefQ = (100, "cppref")  ## type qualifier for NIFC that provides a C++ reference

proc rawTagIsNifcTypeQualifier*(raw: uint32): bool {.inline.} =
  raw >= 97'u32 and raw <= 100'u32

type
  NifcSym* = enum
    NoSym
    GvarY = (50, "gvar")  ## global variable declaration
    TvarY = (51, "tvar")  ## thread local variable declaration
    VarY = (52, "var")  ## variable declaration
    ParamY = (53, "param")  ## parameter declaration
    ConstY = (54, "const")  ## const variable declaration
    EfldY = (59, "efld")  ## enum field declaration
    FldY = (60, "fld")  ## field declaration
    ProcY = (61, "proc")  ## proc declaration
    LabY = (87, "lab")  ## label, target of a `jmp` instruction

proc rawTagIsNifcSym*(raw: uint32): bool {.inline.} =
  raw <= 255'u32 and raw.uint8 in {50'u8, 51'u8, 52'u8, 53'u8, 54'u8, 59'u8, 60'u8, 61'u8, 87'u8}

