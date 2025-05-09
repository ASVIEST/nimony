# Generated by tools/gen_tags.nim from doc/tags.md. DO NOT EDIT!

type
  TagEnum* = enum
    InvalidTagId
    ErrTagId
    SufTagId
    AtTagId
    DerefTagId
    DotTagId
    PatTagId
    ParTagId
    AddrTagId
    NilTagId
    InfTagId
    NeginfTagId
    NanTagId
    FalseTagId
    TrueTagId
    AndTagId
    OrTagId
    XorTagId
    NotTagId
    NegTagId
    SizeofTagId
    AlignofTagId
    OffsetofTagId
    OconstrTagId
    AconstrTagId
    BracketTagId
    CurlyTagId
    CurlyatTagId
    KvTagId
    VvTagId
    OvfTagId
    AddTagId
    SubTagId
    MulTagId
    DivTagId
    ModTagId
    ShrTagId
    ShlTagId
    BitandTagId
    BitorTagId
    BitxorTagId
    BitnotTagId
    EqTagId
    NeqTagId
    LeTagId
    LtTagId
    CastTagId
    ConvTagId
    CallTagId
    CmdTagId
    RangeTagId
    RangesTagId
    GvarTagId
    TvarTagId
    VarTagId
    ParamTagId
    ConstTagId
    ResultTagId
    GletTagId
    TletTagId
    LetTagId
    CursorTagId
    TypevarTagId
    EfldTagId
    FldTagId
    ProcTagId
    FuncTagId
    IteratorTagId
    ConverterTagId
    MethodTagId
    MacroTagId
    TemplateTagId
    TypeTagId
    BlockTagId
    ModuleTagId
    CchoiceTagId
    OchoiceTagId
    EmitTagId
    AsgnTagId
    KeepovfTagId
    ScopeTagId
    IfTagId
    WhenTagId
    ElifTagId
    ElseTagId
    TypevarsTagId
    BreakTagId
    ContinueTagId
    ForTagId
    WhileTagId
    CaseTagId
    OfTagId
    LabTagId
    JmpTagId
    RetTagId
    YldTagId
    StmtsTagId
    ParamsTagId
    UnionTagId
    ObjectTagId
    EnumTagId
    ProctypeTagId
    AtomicTagId
    RoTagId
    RestrictTagId
    CpprefTagId
    ITagId
    UTagId
    FTagId
    CTagId
    BoolTagId
    VoidTagId
    PtrTagId
    ArrayTagId
    FlexarrayTagId
    AptrTagId
    CdeclTagId
    StdcallTagId
    SafecallTagId
    SyscallTagId
    FastcallTagId
    ThiscallTagId
    NoconvTagId
    MemberTagId
    NimcallTagId
    InlineTagId
    NoinlineTagId
    AttrTagId
    VarargsTagId
    WasTagId
    SelectanyTagId
    PragmasTagId
    PragmaxTagId
    AlignTagId
    BitsTagId
    VectorTagId
    ImpTagId
    NodeclTagId
    InclTagId
    ExclTagId
    IncludeTagId
    ImportTagId
    ImportasTagId
    FromimportTagId
    ImportexceptTagId
    ExportTagId
    FromexportTagId
    ExportexceptTagId
    CommentTagId
    DiscardTagId
    TryTagId
    RaiseTagId
    OnerrTagId
    RaisesTagId
    ErrsTagId
    StaticTagId
    IteTagId
    GraphTagId
    ForbindTagId
    KillTagId
    UnpackflatTagId
    UnpacktupTagId
    UnpackdeclTagId
    ExceptTagId
    FinTagId
    TupleTagId
    OnumTagId
    RefTagId
    MutTagId
    OutTagId
    LentTagId
    SinkTagId
    NiltTagId
    ConceptTagId
    DistinctTagId
    ItertypeTagId
    RangetypeTagId
    UarrayTagId
    SetTagId
    AutoTagId
    SymkindTagId
    TypekindTagId
    TypedescTagId
    UntypedTagId
    TypedTagId
    CstringTagId
    PointerTagId
    OrdinalTagId
    MagicTagId
    ImportcTagId
    ImportcppTagId
    ExportcTagId
    HeaderTagId
    ThreadvarTagId
    GlobalTagId
    DiscardableTagId
    NoreturnTagId
    BorrowTagId
    NoSideEffectTagId
    NodestroyTagId
    PluginTagId
    BycopyTagId
    ByrefTagId
    NoinitTagId
    RequiresTagId
    EnsuresTagId
    AssumeTagId
    AssertTagId
    BuildTagId
    StringTagId
    ViewTagId
    QuotedTagId
    HderefTagId
    DdotTagId
    HaddrTagId
    NewrefTagId
    NewobjTagId
    TupTagId
    TupconstrTagId
    SetconstrTagId
    TabconstrTagId
    AshrTagId
    BaseobjTagId
    HconvTagId
    DconvTagId
    CallstrlitTagId
    InfixTagId
    PrefixTagId
    HcallTagId
    CompilesTagId
    DeclaredTagId
    DefinedTagId
    InstanceofTagId
    ProccallTagId
    HighTagId
    LowTagId
    TypeofTagId
    UnpackTagId
    FieldsTagId
    FieldpairsTagId
    EnumtostrTagId
    IsmainmoduleTagId
    DefaultobjTagId
    DefaulttupTagId
    ExprTagId
    DoTagId
    ArratTagId
    TupatTagId
    PlussetTagId
    MinussetTagId
    MulsetTagId
    XorsetTagId
    EqsetTagId
    LesetTagId
    LtsetTagId
    InsetTagId
    CardTagId
    EmoveTagId
    DestroyTagId
    DupTagId
    CopyTagId
    WasmovedTagId
    SinkhTagId
    TraceTagId
    ErrvTagId
    StaticstmtTagId
    BindTagId
    MixinTagId
    UsingTagId
    AsmTagId
    DeferTagId
    IndexTagId
    PublicTagId
    PrivateTagId
    InjectTagId
    GensymTagId
    ErrorTagId
    ReportTagId
    TagsTagId
    DeprecatedTagId
    SideEffectTagId
    KeepOverflowFlagTagId
    SemanticsTagId
    InheritableTagId
    BaseTagId
    PureTagId
    FinalTagId
    InternalTypeNameTagId
    InternalFieldPairsTagId
    FailedTagId
const
  TagData*: array[TagEnum, (string, int)] = [
    ("InvalidTagId", 0),
    ("err", 1),
    ("suf", 2),
    ("at", 3),
    ("deref", 4),
    ("dot", 5),
    ("pat", 6),
    ("par", 7),
    ("addr", 8),
    ("nil", 9),
    ("inf", 10),
    ("neginf", 11),
    ("nan", 12),
    ("false", 13),
    ("true", 14),
    ("and", 15),
    ("or", 16),
    ("xor", 17),
    ("not", 18),
    ("neg", 19),
    ("sizeof", 20),
    ("alignof", 21),
    ("offsetof", 22),
    ("oconstr", 23),
    ("aconstr", 24),
    ("bracket", 25),
    ("curly", 26),
    ("curlyat", 27),
    ("kv", 28),
    ("vv", 29),
    ("ovf", 30),
    ("add", 31),
    ("sub", 32),
    ("mul", 33),
    ("div", 34),
    ("mod", 35),
    ("shr", 36),
    ("shl", 37),
    ("bitand", 38),
    ("bitor", 39),
    ("bitxor", 40),
    ("bitnot", 41),
    ("eq", 42),
    ("neq", 43),
    ("le", 44),
    ("lt", 45),
    ("cast", 46),
    ("conv", 47),
    ("call", 48),
    ("cmd", 49),
    ("range", 50),
    ("ranges", 51),
    ("gvar", 52),
    ("tvar", 53),
    ("var", 54),
    ("param", 55),
    ("const", 56),
    ("result", 57),
    ("glet", 58),
    ("tlet", 59),
    ("let", 60),
    ("cursor", 61),
    ("typevar", 62),
    ("efld", 63),
    ("fld", 64),
    ("proc", 65),
    ("func", 66),
    ("iterator", 67),
    ("converter", 68),
    ("method", 69),
    ("macro", 70),
    ("template", 71),
    ("type", 72),
    ("block", 73),
    ("module", 74),
    ("cchoice", 75),
    ("ochoice", 76),
    ("emit", 77),
    ("asgn", 78),
    ("keepovf", 79),
    ("scope", 80),
    ("if", 81),
    ("when", 82),
    ("elif", 83),
    ("else", 84),
    ("typevars", 85),
    ("break", 86),
    ("continue", 87),
    ("for", 88),
    ("while", 89),
    ("case", 90),
    ("of", 91),
    ("lab", 92),
    ("jmp", 93),
    ("ret", 94),
    ("yld", 95),
    ("stmts", 96),
    ("params", 97),
    ("union", 98),
    ("object", 99),
    ("enum", 100),
    ("proctype", 101),
    ("atomic", 102),
    ("ro", 103),
    ("restrict", 104),
    ("cppref", 105),
    ("i", 106),
    ("u", 107),
    ("f", 108),
    ("c", 109),
    ("bool", 110),
    ("void", 111),
    ("ptr", 112),
    ("array", 113),
    ("flexarray", 114),
    ("aptr", 115),
    ("cdecl", 116),
    ("stdcall", 117),
    ("safecall", 118),
    ("syscall", 119),
    ("fastcall", 120),
    ("thiscall", 121),
    ("noconv", 122),
    ("member", 123),
    ("nimcall", 124),
    ("inline", 125),
    ("noinline", 126),
    ("attr", 127),
    ("varargs", 128),
    ("was", 129),
    ("selectany", 130),
    ("pragmas", 131),
    ("pragmax", 132),
    ("align", 133),
    ("bits", 134),
    ("vector", 135),
    ("imp", 136),
    ("nodecl", 137),
    ("incl", 138),
    ("excl", 139),
    ("include", 140),
    ("import", 141),
    ("importas", 142),
    ("fromimport", 143),
    ("importexcept", 144),
    ("export", 145),
    ("fromexport", 146),
    ("exportexcept", 147),
    ("comment", 148),
    ("discard", 149),
    ("try", 150),
    ("raise", 151),
    ("onerr", 152),
    ("raises", 153),
    ("errs", 154),
    ("static", 155),
    ("ite", 156),
    ("graph", 157),
    ("forbind", 158),
    ("kill", 159),
    ("unpackflat", 160),
    ("unpacktup", 161),
    ("unpackdecl", 162),
    ("except", 163),
    ("fin", 164),
    ("tuple", 165),
    ("onum", 166),
    ("ref", 167),
    ("mut", 168),
    ("out", 169),
    ("lent", 170),
    ("sink", 171),
    ("nilt", 172),
    ("concept", 173),
    ("distinct", 174),
    ("itertype", 175),
    ("rangetype", 176),
    ("uarray", 177),
    ("set", 178),
    ("auto", 179),
    ("symkind", 180),
    ("typekind", 181),
    ("typedesc", 182),
    ("untyped", 183),
    ("typed", 184),
    ("cstring", 185),
    ("pointer", 186),
    ("ordinal", 187),
    ("magic", 188),
    ("importc", 189),
    ("importcpp", 190),
    ("exportc", 191),
    ("header", 192),
    ("threadvar", 193),
    ("global", 194),
    ("discardable", 195),
    ("noreturn", 196),
    ("borrow", 197),
    ("noSideEffect", 198),
    ("nodestroy", 199),
    ("plugin", 200),
    ("bycopy", 201),
    ("byref", 202),
    ("noinit", 203),
    ("requires", 204),
    ("ensures", 205),
    ("assume", 206),
    ("assert", 207),
    ("build", 208),
    ("string", 209),
    ("view", 210),
    ("quoted", 211),
    ("hderef", 212),
    ("ddot", 213),
    ("haddr", 214),
    ("newref", 215),
    ("newobj", 216),
    ("tup", 217),
    ("tupconstr", 218),
    ("setconstr", 219),
    ("tabconstr", 220),
    ("ashr", 221),
    ("baseobj", 222),
    ("hconv", 223),
    ("dconv", 224),
    ("callstrlit", 225),
    ("infix", 226),
    ("prefix", 227),
    ("hcall", 228),
    ("compiles", 229),
    ("declared", 230),
    ("defined", 231),
    ("instanceof", 232),
    ("proccall", 233),
    ("high", 234),
    ("low", 235),
    ("typeof", 236),
    ("unpack", 237),
    ("fields", 238),
    ("fieldpairs", 239),
    ("enumtostr", 240),
    ("ismainmodule", 241),
    ("defaultobj", 242),
    ("defaulttup", 243),
    ("expr", 244),
    ("do", 245),
    ("arrat", 246),
    ("tupat", 247),
    ("plusset", 248),
    ("minusset", 249),
    ("mulset", 250),
    ("xorset", 251),
    ("eqset", 252),
    ("leset", 253),
    ("ltset", 254),
    ("inset", 255),
    ("card", 256),
    ("emove", 257),
    ("destroy", 258),
    ("dup", 259),
    ("copy", 260),
    ("wasmoved", 261),
    ("sinkh", 262),
    ("trace", 263),
    ("errv", 264),
    ("staticstmt", 265),
    ("bind", 266),
    ("mixin", 267),
    ("using", 268),
    ("asm", 269),
    ("defer", 270),
    ("index", 271),
    ("public", 272),
    ("private", 273),
    ("inject", 274),
    ("gensym", 275),
    ("error", 276),
    ("report", 277),
    ("tags", 278),
    ("deprecated", 279),
    ("sideEffect", 280),
    ("keepOverflowFlag", 281),
    ("semantics", 282),
    ("inheritable", 283),
    ("base", 284),
    ("pure", 285),
    ("final", 286),
    ("internalTypeName", 287),
    ("internalFieldPairs", 288),
    ("failed", 289)
  ]
