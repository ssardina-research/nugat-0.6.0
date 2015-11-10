/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         nusmv_yyparse
#define yylex           nusmv_yylex
#define yyerror         nusmv_yyerror
#define yydebug         nusmv_yydebug
#define yynerrs         nusmv_yynerrs

#define yylval          nusmv_yylval
#define yychar          nusmv_yychar

/* Copy the first part of user declarations.  */
#line 3 "grammar.y" /* yacc.c:339  */


#if HAVE_CONFIG_H
# include "nusmv-config.h"
#endif

#include <setjmp.h>

#if NUSMV_HAVE_MALLOC_H
# if NUSMV_HAVE_SYS_TYPES_H
#  include <sys/types.h>
# endif
# include <malloc.h>
#elif defined(NUSMV_HAVE_SYS_MALLOC_H) && NUSMV_HAVE_SYS_MALLOC_H
# if NUSMV_HAVE_SYS_TYPES_H
#  include <sys/types.h>
# endif
# include <sys/malloc.h>
#elif NUSMV_HAVE_STDLIB_H
# include <stdlib.h>
#endif

#include <limits.h>

#include "nusmv/core/parser/parserInt.h"
#include "nusmv/core/parser/psl/pslInt.h"
#include "nusmv/core/utils/utils.h"
#include "nusmv/core/utils/ustring.h"
#include "nusmv/core/node/node.h"
#include "nusmv/core/opt/opt.h"
#include "nusmv/core/prop/propPkg.h"
#include "nusmv/core/utils/ErrorMgr.h"

#include "nusmv/core/parser/symbols.h"
#include "nusmv/core/cinit/NuSMVEnv.h"
#define YYMAXDEPTH INT_MAX

#define GET_OPTS                                                \
  OPTS_HANDLER(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_OPTS_HANDLER))

  /* OPTIMIZATION[REAMa] Test performances. If poor, use ad-hoc variable */
#define NODEMGR                                                         \
  NODE_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_NODE_MGR))

#define SYNTAX_ERROR_HANDLING(dest, src) \
  {                                      \
    if (OptsHandler_get_bool_option_value(GET_OPTS, \
                                          OPT_PARSER_IS_LAX)) {         \
      dest = src;                                                       \
    }                                                                   \
    else {                                                              \
      YYABORT;                                                          \
    }                                                                   \
 }


node_ptr parsed_tree; /* the returned value of parsing */

/* TODO[AMa] Dirty hack. This var must be updated before all calls of the
   parser */
NuSMVEnv_ptr __nusmv_parser_env__;

enum PARSE_MODE parse_mode_flag; /* the flag what should be parsed */

extern int nusmv_yylineno;
int nusmv_yywrap(void);
void nusmv_yyerror(char *s);
void nusmv_yyerror_lined(const char *s, int line);
static node_ptr node2maincontext(node_ptr node);

/* this enum is used to distinguish
   different kinds of expressions: SIMPLE, NEXT, CTL and LTL.
   Since syntactically only one global kind of expressions exists,
   we have to invoke a special function which checks that an expression
   complies to the additional syntactic constrains.
   So, if a ctl-expression is expected then occurrences of NEXT
   operator will cause the termination of parsing.

   NB: An alternative to invoking a checking function would be to write quite
   intricate syntactic rules to distinguish all the cases.

   NB: This checking function could also be a part of the type checker,
   but it is more straightforward to write a separate function.
*/
  enum EXP_KIND {EXP_SIMPLE, EXP_NEXT, EXP_LTL, EXP_CTL};

  static boolean isCorrectExp(node_ptr exp, enum EXP_KIND expectedKind);

  static node_ptr build_case_colon_node(node_ptr l,
                                        node_ptr r,
                                        int linum);

  static int nusmv_parse_psl(void);

#line 169 "grammar.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "y.tab.h".  */
#ifndef YY_NUSMV_YY_Y_TAB_H_INCLUDED
# define YY_NUSMV_YY_Y_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int nusmv_yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TOK_CONSTRAINT = 258,
    TOK_ITYPE = 259,
    TOK_MODULE = 260,
    TOK_PROCESS = 261,
    TOK_CONTEXT = 262,
    TOK_EU = 263,
    TOK_AU = 264,
    TOK_EBU = 265,
    TOK_ABU = 266,
    TOK_MINU = 267,
    TOK_MAXU = 268,
    TOK_VAR = 269,
    TOK_FROZENVAR = 270,
    TOK_IVAR = 271,
    TOK_FUN = 272,
    TOK_DEFINE = 273,
    TOK_ARRAY_DEFINE = 274,
    TOK_INIT = 275,
    TOK_TRANS = 276,
    TOK_INVAR = 277,
    TOK_SPEC = 278,
    TOK_CTLSPEC = 279,
    TOK_LTLSPEC = 280,
    TOK_COMPUTE = 281,
    TOK_NAME = 282,
    TOK_PSLSPEC = 283,
    TOK_CONSTANTS = 284,
    TOK_INVARSPEC = 285,
    TOK_FAIRNESS = 286,
    TOK_COMPASSION = 287,
    TOK_JUSTICE = 288,
    TOK_ISA = 289,
    TOK_ASSIGN = 290,
    TOK_OF = 291,
    TOK_CONS = 292,
    TOK_SEMI = 293,
    TOK_LP = 294,
    TOK_RP = 295,
    TOK_RB = 296,
    TOK_LCB = 297,
    TOK_RCB = 298,
    TOK_EQDEF = 299,
    TOK_TWODOTS = 300,
    TOK_SELF = 301,
    TOK_CASE = 302,
    TOK_ESAC = 303,
    TOK_COLON = 304,
    TOK_INCONTEXT = 305,
    TOK_SIMPWFF = 306,
    TOK_NEXTWFF = 307,
    TOK_LTLWFF = 308,
    TOK_LTLPSL = 309,
    TOK_CTLWFF = 310,
    TOK_COMPWFF = 311,
    TOK_COMPID = 312,
    TOK_ARRAY = 313,
    TOK_BOOLEAN = 314,
    TOK_WORD = 315,
    TOK_BOOL = 316,
    TOK_WORD1 = 317,
    TOK_CONST_ARRAY = 318,
    TOK_WAREAD = 319,
    TOK_WAWRITE = 320,
    TOK_SIGNED = 321,
    TOK_UNSIGNED = 322,
    TOK_EXTEND = 323,
    TOK_UWCONST = 324,
    TOK_SWCONST = 325,
    TOK_WRESIZE = 326,
    TOK_WSIZEOF = 327,
    TOK_WTOINT = 328,
    TOK_COUNT = 329,
    TOK_TYPEOF = 330,
    TOK_ATOM = 331,
    TOK_FALSEEXP = 332,
    TOK_TRUEEXP = 333,
    TOK_NUMBER = 334,
    TOK_NUMBER_FRAC = 335,
    TOK_NUMBER_REAL = 336,
    TOK_NUMBER_EXP = 337,
    TOK_NUMBER_WORD = 338,
    TOK_ABS = 339,
    TOK_MIN = 340,
    TOK_MAX = 341,
    TOK_COMMA = 342,
    TOK_IMPLIES = 343,
    TOK_IFF = 344,
    TOK_OR = 345,
    TOK_XOR = 346,
    TOK_XNOR = 347,
    TOK_AND = 348,
    TOK_NOT = 349,
    TOK_QUESTIONMARK = 350,
    TOK_EX = 351,
    TOK_AX = 352,
    TOK_EF = 353,
    TOK_AF = 354,
    TOK_EG = 355,
    TOK_AG = 356,
    TOK_EE = 357,
    TOK_AA = 358,
    TOK_SINCE = 359,
    TOK_UNTIL = 360,
    TOK_TRIGGERED = 361,
    TOK_RELEASES = 362,
    TOK_EBF = 363,
    TOK_EBG = 364,
    TOK_ABF = 365,
    TOK_ABG = 366,
    TOK_BUNTIL = 367,
    TOK_MMIN = 368,
    TOK_MMAX = 369,
    TOK_OP_NEXT = 370,
    TOK_OP_GLOBAL = 371,
    TOK_OP_FUTURE = 372,
    TOK_OP_PREC = 373,
    TOK_OP_NOTPRECNOT = 374,
    TOK_OP_HISTORICAL = 375,
    TOK_OP_ONCE = 376,
    TOK_EQUAL = 377,
    TOK_NOTEQUAL = 378,
    TOK_LT = 379,
    TOK_GT = 380,
    TOK_LE = 381,
    TOK_GE = 382,
    TOK_UNION = 383,
    TOK_SETIN = 384,
    TOK_LSHIFT = 385,
    TOK_RSHIFT = 386,
    TOK_LROTATE = 387,
    TOK_RROTATE = 388,
    TOK_MOD = 389,
    TOK_PLUS = 390,
    TOK_MINUS = 391,
    TOK_TIMES = 392,
    TOK_DIVIDE = 393,
    TOK_NEXT = 394,
    TOK_SMALLINIT = 395,
    TOK_CONCATENATION = 396,
    TOK_LB = 397,
    TOK_DOT = 398,
    TOK_BIT = 399,
    TOK_GAME = 400,
    TOK_PLAYER_1 = 401,
    TOK_PLAYER_2 = 402,
    TOK_REACHTARGET = 403,
    TOK_AVOIDTARGET = 404,
    TOK_REACHDEADLOCK = 405,
    TOK_AVOIDDEADLOCK = 406,
    TOK_BUCHIGAME = 407,
    TOK_LTLGAME = 408,
    TOK_GENREACTIVITY = 409
  };
#endif
/* Tokens.  */
#define TOK_CONSTRAINT 258
#define TOK_ITYPE 259
#define TOK_MODULE 260
#define TOK_PROCESS 261
#define TOK_CONTEXT 262
#define TOK_EU 263
#define TOK_AU 264
#define TOK_EBU 265
#define TOK_ABU 266
#define TOK_MINU 267
#define TOK_MAXU 268
#define TOK_VAR 269
#define TOK_FROZENVAR 270
#define TOK_IVAR 271
#define TOK_FUN 272
#define TOK_DEFINE 273
#define TOK_ARRAY_DEFINE 274
#define TOK_INIT 275
#define TOK_TRANS 276
#define TOK_INVAR 277
#define TOK_SPEC 278
#define TOK_CTLSPEC 279
#define TOK_LTLSPEC 280
#define TOK_COMPUTE 281
#define TOK_NAME 282
#define TOK_PSLSPEC 283
#define TOK_CONSTANTS 284
#define TOK_INVARSPEC 285
#define TOK_FAIRNESS 286
#define TOK_COMPASSION 287
#define TOK_JUSTICE 288
#define TOK_ISA 289
#define TOK_ASSIGN 290
#define TOK_OF 291
#define TOK_CONS 292
#define TOK_SEMI 293
#define TOK_LP 294
#define TOK_RP 295
#define TOK_RB 296
#define TOK_LCB 297
#define TOK_RCB 298
#define TOK_EQDEF 299
#define TOK_TWODOTS 300
#define TOK_SELF 301
#define TOK_CASE 302
#define TOK_ESAC 303
#define TOK_COLON 304
#define TOK_INCONTEXT 305
#define TOK_SIMPWFF 306
#define TOK_NEXTWFF 307
#define TOK_LTLWFF 308
#define TOK_LTLPSL 309
#define TOK_CTLWFF 310
#define TOK_COMPWFF 311
#define TOK_COMPID 312
#define TOK_ARRAY 313
#define TOK_BOOLEAN 314
#define TOK_WORD 315
#define TOK_BOOL 316
#define TOK_WORD1 317
#define TOK_CONST_ARRAY 318
#define TOK_WAREAD 319
#define TOK_WAWRITE 320
#define TOK_SIGNED 321
#define TOK_UNSIGNED 322
#define TOK_EXTEND 323
#define TOK_UWCONST 324
#define TOK_SWCONST 325
#define TOK_WRESIZE 326
#define TOK_WSIZEOF 327
#define TOK_WTOINT 328
#define TOK_COUNT 329
#define TOK_TYPEOF 330
#define TOK_ATOM 331
#define TOK_FALSEEXP 332
#define TOK_TRUEEXP 333
#define TOK_NUMBER 334
#define TOK_NUMBER_FRAC 335
#define TOK_NUMBER_REAL 336
#define TOK_NUMBER_EXP 337
#define TOK_NUMBER_WORD 338
#define TOK_ABS 339
#define TOK_MIN 340
#define TOK_MAX 341
#define TOK_COMMA 342
#define TOK_IMPLIES 343
#define TOK_IFF 344
#define TOK_OR 345
#define TOK_XOR 346
#define TOK_XNOR 347
#define TOK_AND 348
#define TOK_NOT 349
#define TOK_QUESTIONMARK 350
#define TOK_EX 351
#define TOK_AX 352
#define TOK_EF 353
#define TOK_AF 354
#define TOK_EG 355
#define TOK_AG 356
#define TOK_EE 357
#define TOK_AA 358
#define TOK_SINCE 359
#define TOK_UNTIL 360
#define TOK_TRIGGERED 361
#define TOK_RELEASES 362
#define TOK_EBF 363
#define TOK_EBG 364
#define TOK_ABF 365
#define TOK_ABG 366
#define TOK_BUNTIL 367
#define TOK_MMIN 368
#define TOK_MMAX 369
#define TOK_OP_NEXT 370
#define TOK_OP_GLOBAL 371
#define TOK_OP_FUTURE 372
#define TOK_OP_PREC 373
#define TOK_OP_NOTPRECNOT 374
#define TOK_OP_HISTORICAL 375
#define TOK_OP_ONCE 376
#define TOK_EQUAL 377
#define TOK_NOTEQUAL 378
#define TOK_LT 379
#define TOK_GT 380
#define TOK_LE 381
#define TOK_GE 382
#define TOK_UNION 383
#define TOK_SETIN 384
#define TOK_LSHIFT 385
#define TOK_RSHIFT 386
#define TOK_LROTATE 387
#define TOK_RROTATE 388
#define TOK_MOD 389
#define TOK_PLUS 390
#define TOK_MINUS 391
#define TOK_TIMES 392
#define TOK_DIVIDE 393
#define TOK_NEXT 394
#define TOK_SMALLINIT 395
#define TOK_CONCATENATION 396
#define TOK_LB 397
#define TOK_DOT 398
#define TOK_BIT 399
#define TOK_GAME 400
#define TOK_PLAYER_1 401
#define TOK_PLAYER_2 402
#define TOK_REACHTARGET 403
#define TOK_AVOIDTARGET 404
#define TOK_REACHDEADLOCK 405
#define TOK_AVOIDDEADLOCK 406
#define TOK_BUCHIGAME 407
#define TOK_LTLGAME 408
#define TOK_GENREACTIVITY 409

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 98 "grammar.y" /* yacc.c:355  */

  node_ptr node;
  int lineno;

#line 522 "grammar.c" /* yacc.c:355  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE nusmv_yylval;

int nusmv_yyparse (void);

#endif /* !YY_NUSMV_YY_Y_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */
#line 205 "grammar.y" /* yacc.c:358  */

#include "config.h"
#if HAVE_GAME
#include "addons/game/parser/game_symbols.h"
#include "addons/game/game.h"
#endif

  /* below vars are used if input file contains game definition */
  static node_ptr game_parser_spec_list = Nil;
  static node_ptr game_parser_player_1 = Nil;
  static node_ptr game_parser_player_2 = Nil;

#line 549 "grammar.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  5
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   2861

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  155
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  132
/* YYNRULES -- Number of rules.  */
#define YYNRULES  372
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  788

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   409

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   142,   143,   144,
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   243,   243,   244,   247,   248,   249,   253,   255,   257,
     259,   262,   266,   270,   271,   272,   274,   276,   278,   280,
     281,   282,   287,   292,   301,   302,   309,   328,   329,   330,
     331,   332,   341,   350,   356,   361,   362,   367,   370,   373,
     374,   375,   376,   377,   378,   379,   380,   381,   383,   386,
     389,   391,   396,   397,   401,   412,   416,   422,   423,   428,
     429,   434,   435,   436,   437,   441,   442,   443,   444,   449,
     450,   451,   456,   457,   458,   461,   462,   463,   466,   467,
     468,   474,   475,   476,   479,   480,   484,   485,   488,   489,
     493,   494,   495,   496,   497,   498,   499,   502,   503,   507,
     508,   509,   510,   511,   512,   513,   515,   517,   519,   521,
     522,   523,   524,   527,   533,   534,   537,   538,   539,   540,
     543,   544,   548,   549,   552,   556,   557,   562,   563,   564,
     565,   566,   568,   569,   571,   572,   574,   575,   578,   585,
     586,   588,   590,   597,   607,   608,   612,   613,   614,   615,
     619,   620,   624,   625,   629,   630,   634,   641,   644,   647,
     650,   654,   656,   665,   666,   668,   670,   672,   673,   675,
     677,   679,   685,   686,   687,   691,   692,   695,   696,   697,
     698,   701,   702,   705,   706,   707,   709,   721,   722,   734,
     735,   738,   741,   742,   743,   746,   747,   752,   753,   754,
     757,   758,   759,   760,   761,   762,   763,   764,   765,   766,
     767,   768,   769,   770,   771,   772,   773,   774,   775,   776,
     785,   786,   789,   790,   793,   794,   796,   800,   806,   807,
     808,   810,   811,   812,   814,   815,   816,   818,   819,   820,
     823,   825,   827,   829,   832,   836,   837,   841,   844,   845,
     846,   849,   851,   864,   868,   869,   870,   874,   875,   879,
     880,   884,   885,   889,   891,   892,   893,   895,   897,   902,
     910,   912,   914,   918,   921,   924,   930,   931,   933,   934,
     937,   938,   940,   941,   942,   943,   946,   947,   950,   951,
     954,   955,   957,   958,   962,   972,   977,   978,   979,   986,
     990,   990,   998,   999,  1000,  1001,  1002,  1011,  1012,  1013,
    1014,  1015,  1022,  1023,  1024,  1027,  1029,  1031,  1033,  1035,
    1039,  1040,  1041,  1042,  1043,  1044,  1048,  1049,  1050,  1053,
    1054,  1060,  1060,  1099,  1099,  1106,  1106,  1120,  1121,  1136,
    1137,  1138,  1139,  1149,  1172,  1173,  1181,  1197,  1218,  1219,
    1220,  1221,  1222,  1223,  1224,  1230,  1231,  1235,  1236,  1238,
    1239,  1240,  1241,  1242,  1248,  1249,  1251,  1258,  1265,  1272,
    1279,  1290,  1297
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TOK_CONSTRAINT", "TOK_ITYPE",
  "TOK_MODULE", "TOK_PROCESS", "TOK_CONTEXT", "TOK_EU", "TOK_AU",
  "TOK_EBU", "TOK_ABU", "TOK_MINU", "TOK_MAXU", "TOK_VAR", "TOK_FROZENVAR",
  "TOK_IVAR", "TOK_FUN", "TOK_DEFINE", "TOK_ARRAY_DEFINE", "TOK_INIT",
  "TOK_TRANS", "TOK_INVAR", "TOK_SPEC", "TOK_CTLSPEC", "TOK_LTLSPEC",
  "TOK_COMPUTE", "TOK_NAME", "TOK_PSLSPEC", "TOK_CONSTANTS",
  "TOK_INVARSPEC", "TOK_FAIRNESS", "TOK_COMPASSION", "TOK_JUSTICE",
  "TOK_ISA", "TOK_ASSIGN", "TOK_OF", "TOK_CONS", "TOK_SEMI", "TOK_LP",
  "TOK_RP", "TOK_RB", "TOK_LCB", "TOK_RCB", "TOK_EQDEF", "TOK_TWODOTS",
  "TOK_SELF", "TOK_CASE", "TOK_ESAC", "TOK_COLON", "TOK_INCONTEXT",
  "TOK_SIMPWFF", "TOK_NEXTWFF", "TOK_LTLWFF", "TOK_LTLPSL", "TOK_CTLWFF",
  "TOK_COMPWFF", "TOK_COMPID", "TOK_ARRAY", "TOK_BOOLEAN", "TOK_WORD",
  "TOK_BOOL", "TOK_WORD1", "TOK_CONST_ARRAY", "TOK_WAREAD", "TOK_WAWRITE",
  "TOK_SIGNED", "TOK_UNSIGNED", "TOK_EXTEND", "TOK_UWCONST", "TOK_SWCONST",
  "TOK_WRESIZE", "TOK_WSIZEOF", "TOK_WTOINT", "TOK_COUNT", "TOK_TYPEOF",
  "TOK_ATOM", "TOK_FALSEEXP", "TOK_TRUEEXP", "TOK_NUMBER",
  "TOK_NUMBER_FRAC", "TOK_NUMBER_REAL", "TOK_NUMBER_EXP",
  "TOK_NUMBER_WORD", "TOK_ABS", "TOK_MIN", "TOK_MAX", "TOK_COMMA",
  "TOK_IMPLIES", "TOK_IFF", "TOK_OR", "TOK_XOR", "TOK_XNOR", "TOK_AND",
  "TOK_NOT", "TOK_QUESTIONMARK", "TOK_EX", "TOK_AX", "TOK_EF", "TOK_AF",
  "TOK_EG", "TOK_AG", "TOK_EE", "TOK_AA", "TOK_SINCE", "TOK_UNTIL",
  "TOK_TRIGGERED", "TOK_RELEASES", "TOK_EBF", "TOK_EBG", "TOK_ABF",
  "TOK_ABG", "TOK_BUNTIL", "TOK_MMIN", "TOK_MMAX", "TOK_OP_NEXT",
  "TOK_OP_GLOBAL", "TOK_OP_FUTURE", "TOK_OP_PREC", "TOK_OP_NOTPRECNOT",
  "TOK_OP_HISTORICAL", "TOK_OP_ONCE", "TOK_EQUAL", "TOK_NOTEQUAL",
  "TOK_LT", "TOK_GT", "TOK_LE", "TOK_GE", "TOK_UNION", "TOK_SETIN",
  "TOK_LSHIFT", "TOK_RSHIFT", "TOK_LROTATE", "TOK_RROTATE", "TOK_MOD",
  "TOK_PLUS", "TOK_MINUS", "TOK_TIMES", "TOK_DIVIDE", "TOK_NEXT",
  "TOK_SMALLINIT", "TOK_CONCATENATION", "TOK_LB", "TOK_DOT", "TOK_BIT",
  "TOK_GAME", "TOK_PLAYER_1", "TOK_PLAYER_2", "TOK_REACHTARGET",
  "TOK_AVOIDTARGET", "TOK_REACHDEADLOCK", "TOK_AVOIDDEADLOCK",
  "TOK_BUCHIGAME", "TOK_LTLGAME", "TOK_GENREACTIVITY", "$accept", "number",
  "integer", "number_word", "number_frac", "number_real", "number_exp",
  "subrange", "subrangetype", "constant", "primary_expr", "nfunc_expr",
  "primary_expr_type", "count_param_list", "case_element_list_expr",
  "case_element_expr", "concatination_expr_type", "concatination_expr",
  "multiplicative_expr_type", "multiplicative_expr", "additive_expr_type",
  "additive_expr", "shift_expr_type", "shift_expr", "set_expr",
  "set_list_expr", "union_expr", "in_expr", "relational_expr", "ctl_expr",
  "pure_ctl_expr", "ctl_and_expr", "ctl_or_expr", "ctl_iff_expr",
  "ctl_implies_expr", "ctl_basic_expr", "ltl_unary_expr",
  "pure_ltl_unary_expr", "ltl_binary_expr", "and_expr", "or_expr",
  "ite_expr", "iff_expr", "implies_expr", "basic_expr",
  "simple_expression", "next_expression", "ctl_expression",
  "ltl_expression", "compute_expression", "itype", "type",
  "type_value_list", "type_value", "complex_atom", "module_type",
  "next_list_expression", "module_list", "module", "module_sign",
  "atom_list", "declarations", "declaration", "var", "frozen_var",
  "input_var", "fun_def", "var_decl_list", "fvar_decl_list",
  "ivar_decl_list", "fun_decl_list", "var_decl", "fvar_decl", "ivar_decl",
  "fun_decl", "nfun_type", "nfun_ftype", "define_decls", "define_list",
  "define", "array_define", "array_define_list", "array_expression",
  "array_expression_list", "array_contents", "assign", "assign_list",
  "one_assign", "init", "invar", "trans", "fairness", "justice",
  "compassion", "_invarspec", "invarspec", "_ctlspec", "ctlspec",
  "_ltlspec", "ltlspec", "_compute", "compute", "pslspec", "constants",
  "constants_expression", "isa", "optsemi", "decl_var_id", "var_id",
  "command", "command_case", "context", "_simpwff", "game_begin", "$@1",
  "$@2", "$@3", "simple_list_expression", "game_module_list",
  "game_definition", "game_body", "game_body_element", "player_body",
  "player_body_element", "player_num", "reachtarget", "avoidtarget",
  "reachdeadlock", "avoiddeadlock", "buchigame", "ltlgame",
  "genreactivity", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,   340,   341,   342,   343,   344,
     345,   346,   347,   348,   349,   350,   351,   352,   353,   354,
     355,   356,   357,   358,   359,   360,   361,   362,   363,   364,
     365,   366,   367,   368,   369,   370,   371,   372,   373,   374,
     375,   376,   377,   378,   379,   380,   381,   382,   383,   384,
     385,   386,   387,   388,   389,   390,   391,   392,   393,   394,
     395,   396,   397,   398,   399,   400,   401,   402,   403,   404,
     405,   406,   407,   408,   409
};
# endif

#define YYPACT_NINF -559

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-559)))

#define YYTABLE_NINF -342

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     393,    98,    48,   536,  2076,  -559,    42,   329,    48,   143,
    -559,  -559,    26,  2076,  2403,  2076,  2076,  2076,  2076,  2076,
    2076,  2076,   184,    21,  -559,  -559,  2076,  2076,  -559,  2076,
     133,   175,   233,   242,   244,   249,   254,   280,   284,   286,
     288,   291,   295,   298,  -559,  -559,  -559,    81,  -559,  -559,
    -559,  -559,   346,   356,   360,  2159,  2242,  2242,  2242,  2242,
    2242,  2242,     3,    59,    32,    32,    32,    32,  2076,  1496,
    1579,  2076,  2076,  1662,  1745,   327,  2643,   371,  -559,   381,
    -559,  -559,  -559,  -559,  -559,  -559,   377,  -559,   219,   294,
     198,   235,   321,  -559,   309,   318,   217,  -559,  -559,  -559,
    -559,   335,   350,   221,  -559,   380,  -559,  -559,  -559,   421,
    -559,  -559,  -559,   325,   325,   325,   325,   325,   325,   325,
    -559,   329,  -559,  -559,  -559,  -559,  -559,  -559,  -559,   484,
    -559,  -559,  -559,   487,   186,  1914,  -559,   389,    70,   185,
    -559,  2722,   462,  2722,  -559,   219,   401,   274,   352,    10,
     505,   506,  -559,   508,   509,    86,  -559,    89,  -559,   205,
    -559,  -559,   230,  -559,   406,   407,   237,  -559,  -559,  -559,
       7,   510,    18,  -559,   504,  2076,   511,  2076,  2076,   479,
    2076,  2076,  2076,  2076,  2076,  2076,  2076,  2076,  2076,  2076,
    2076,  2076,  2076,  2076,   219,  -559,  -559,  2321,  -559,  -559,
    -559,  -559,  -559,  -559,  2242,  2242,  -559,   476,   482,  2242,
    2242,  2242,  2242,  -559,   483,  -559,   485,  -559,  -559,  -559,
     486,  -559,   490,  -559,   513,   514,   219,  2076,    32,  2076,
    2076,   171,  2722,  2722,  2722,  2722,  2722,  2722,  2722,  2722,
    2564,  2564,  2564,  2564,  2564,  2564,  2564,  2564,  2076,  2076,
    2076,  2076,  2076,  2076,  2076,  2076,  2076,  2076,  2076,    61,
    1049,   264,   264,  -559,  -559,  2076,  2076,   525,   525,   527,
    2076,   531,  -559,  -559,  -559,  -559,  -559,  -559,    51,  -559,
     428,  2403,   430,   537,  2076,   432,   433,  -559,  2722,  2722,
    2722,  2722,  2722,  2722,  2722,  2722,  2722,  -559,  -559,  -559,
    -559,  -559,   502,  -559,   502,  -559,   502,  -559,   502,  -559,
    2076,  2076,   502,  -559,  -559,  2076,   194,  -559,  -559,  2076,
    -559,  -559,  2076,   539,   540,   542,   495,   496,   544,   550,
     507,   512,   515,   516,   555,   556,   557,   517,   558,   519,
     520,  -559,   518,   328,   402,  -559,   141,   162,  -559,  -559,
    -559,  -559,  -559,  -559,   521,   522,   528,   530,   560,  -559,
    -559,    45,   571,   552,   573,  -559,  -559,   377,   294,   294,
     294,   198,   198,   235,   235,  -559,   309,   318,   318,   318,
     318,   318,   318,  -559,  -559,  -559,  -559,   335,   350,   350,
     350,   569,  -559,  -559,  -559,  -559,    82,  -559,   543,   543,
     543,   543,  -559,  -559,  2076,  2076,  2076,  1158,  1243,  1328,
      68,  -559,   545,  1413,  2076,   581,  2076,   546,  -559,  -559,
    -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,
    -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,
    -559,  -559,  -559,  -559,  -559,  -559,  -559,  -559,   525,   525,
    -559,  -559,  2076,   525,  2076,  -559,   186,   547,  -559,  2076,
    2403,   583,  2076,  2076,   219,   401,   401,   401,   -35,   -35,
     363,   352,   352,  -559,     9,     9,     9,     9,   538,   541,
       9,   585,  -559,  -559,  -559,   589,  -559,  -559,    21,  2076,
    2076,  -559,  -559,  2076,  2722,  2722,  2076,  -559,  -559,  -559,
    2076,  -559,  2076,  2076,  2242,  2242,  2242,  2242,  2242,  2242,
    2242,    32,  2242,    32,   551,   553,   554,   561,  -559,  -559,
    2076,  2076,  -559,  2076,  -559,   563,  -559,   358,  -559,    93,
     795,  -559,    95,    58,  -559,    97,   950,  -559,   106,   882,
     986,   525,   525,   525,    21,  -559,    21,  -559,    21,  -559,
      21,  -559,   428,    27,    21,  -559,   525,  2076,   525,  -559,
     727,  -559,  -559,  -559,    88,  -559,   155,  -559,  -559,   588,
    -559,  -559,   590,   593,  2076,   565,  -559,  -559,  -559,  -559,
    2076,  2076,  -559,  -559,  -559,    14,   602,   559,   603,   126,
     130,   605,  -559,   607,   608,  -559,   518,   518,   518,  -559,
     328,   609,  2242,   610,  2242,   611,   612,   613,   614,  -559,
     615,  -559,  -559,  -559,  -559,  1079,   -23,   241,  -559,  -559,
    2403,  -559,  -559,  2403,  -559,  -559,  2403,  -559,  -559,    64,
    -559,    73,  -559,  -559,  -559,    75,    77,    79,    85,  -559,
     545,    87,  -559,   562,  -559,  -559,   618,   620,  -559,    91,
     525,  2076,   575,   625,  -559,  -559,   623,  -559,   624,   626,
     579,  -559,  2076,  -559,  -559,  -559,  -559,  -559,  -559,  -559,
     627,  -559,   628,  2076,  2076,  2076,  2076,  -559,    49,  1914,
     480,  -559,   632,  -559,   630,   594,  -559,  -559,   636,   637,
    -559,   638,   -22,  1828,   548,  2076,  2076,  2076,   184,   428,
    2076,  2076,    21,    21,  2076,  -559,  -559,   639,  2403,  -559,
    -559,  -559,  2076,   641,  -559,  -559,  -559,  -559,  -559,  -559,
    2722,   640,  -559,   646,  1993,  -559,  -559,   643,  -559,  -559,
    -559,  2403,  2403,  1828,   647,   648,   649,  -559,  -559,  -559,
    -559,  -559,   654,    20,    22,   650,  2076,  -559,   657,  -559,
     663,  2485,  -559,   164,  -559,  -559,  -559,   616,   617,   659,
     660,  -559,  -559,  -559,   525,   658,   661,  -559,   204,  -559,
      49,  -559,  -559,  2076,   548,  -559,  -559,  -559,  2076,  2076,
     525,  -559,  -559,   668,   669,  -559,  -559,  -559
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
     335,     0,     0,     0,     0,     1,     0,   344,     0,   189,
     332,   340,   314,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   334,   312,     0,     0,    30,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    29,    13,    14,     2,     8,     9,
      10,     7,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    19,     0,
      20,    21,    23,    22,    82,    27,    59,    25,    24,    65,
      72,    78,    81,    86,    88,    90,    97,   125,    98,   139,
     126,   144,   146,   150,   152,   154,   156,   160,   336,   192,
     197,   355,   355,     0,     0,     0,     0,     0,     0,     0,
     343,   344,   348,   349,   350,   351,   352,   353,   354,   190,
     342,   313,   157,     0,     0,     0,   163,     0,     0,     0,
       2,     0,     0,     0,   167,    57,    61,    69,    75,     0,
       0,     0,   158,     0,     0,   300,   320,   300,   321,   300,
     323,   159,   300,   322,     0,     0,   300,   324,   308,   307,
       0,     0,     0,    84,     0,    54,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    39,   113,   138,     0,    99,   100,
     101,   102,   103,   104,     0,     0,     4,     0,     0,     0,
       0,     0,     0,   127,     0,   130,     0,   134,   128,   129,
       0,   132,     0,   136,     3,     2,    28,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   346,   347,   364,   365,     0,     0,   300,   300,     0,
       0,     0,   345,   318,   181,   179,   180,   178,     0,   175,
     177,     0,     0,     0,     0,     0,     0,     3,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   319,   315,   317,
     316,   301,     0,   329,     0,   276,     0,   286,     0,   280,
       0,     0,     0,   290,   325,     0,     0,    35,    83,     0,
      47,    55,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    52,     0,     0,
       0,   114,   116,   120,   122,   124,     0,     0,     5,     6,
     109,   111,   110,   112,     0,     0,     0,     0,     0,    11,
     187,     0,   157,     0,     0,    31,    32,    60,    68,    66,
      67,    73,    74,    79,    80,    87,    89,    91,    92,    93,
      94,    95,    96,   141,   140,   143,   142,   145,   147,   148,
     149,     0,   155,   153,   193,   195,     0,   199,   220,   222,
     224,   226,   248,   254,     0,     0,     0,     0,     0,     0,
       0,   294,   296,     0,     0,     0,     0,     0,   264,   198,
     201,   202,   203,   204,   209,   210,   205,   206,   207,   208,
     211,   212,   213,   214,   215,   216,   218,   217,   219,   200,
     357,   358,   363,   359,   360,   361,   362,   356,   300,   300,
     368,   369,     0,   300,     0,   168,     0,     0,   171,     0,
       0,     0,     0,     0,    58,    64,    62,    63,    70,    71,
      12,    76,    77,   326,   300,   300,   300,   300,     0,     0,
     300,     0,   309,   310,    85,     0,    40,    41,     0,     0,
       0,    43,    44,     0,     0,     0,     0,    17,    18,    51,
       0,    36,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    42,    26,
       0,     0,    33,     0,   194,     0,   302,     0,   228,     0,
       0,   231,     0,     0,   234,     0,     0,   237,     0,     0,
       0,   300,   300,   300,     0,   282,     0,   283,     0,   288,
       0,   292,   297,     0,     0,   278,   300,     0,   300,   299,
       0,   366,   367,   337,     0,   371,     0,   176,   182,     0,
     170,   164,     0,     0,     0,     0,   330,   277,   287,   281,
       0,     0,   291,   311,    56,     0,     0,     0,     0,     0,
       0,     0,    53,     0,     0,   115,   117,   118,   119,   123,
     121,     0,     0,     0,     0,     0,     0,     0,     0,   188,
       0,   151,   196,   230,   229,     0,     0,     0,   233,   232,
       0,   236,   235,     0,   239,   238,     0,   250,   249,     0,
     256,     0,   270,   272,   271,     0,     0,     0,     0,   295,
       0,     0,   273,     0,   274,   266,     0,     0,   265,     0,
     300,     0,     0,     0,   166,   165,     0,   327,     0,     0,
       0,    48,     0,    45,    15,    16,    46,    37,    38,   106,
       0,   105,     0,     0,     0,     0,     0,    34,     0,     0,
      29,   172,     0,   173,     0,     0,   303,   304,     0,     0,
     245,     0,     0,     0,     0,     0,     0,     0,     0,   298,
       0,     0,     0,     0,     0,   370,   338,     0,     0,   328,
     161,   162,     0,     0,   108,   107,   131,   135,   133,   137,
       0,   183,   174,     0,     0,   240,   305,     0,   241,   242,
     243,     0,     0,     0,     0,     0,     0,   284,   285,   289,
     293,   279,     0,     0,     0,     0,     0,   169,     0,    49,
       0,     0,   184,     0,   306,   244,   246,   262,   259,     0,
       0,   251,   252,   255,   300,     0,     0,   267,     0,    50,
       0,   186,   185,     0,     0,   258,   257,   275,     0,     0,
     300,   261,   260,     0,     0,   372,   269,   268
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -559,  -559,  -132,  -559,  -559,  -559,  -559,   -16,  -134,  -559,
     477,  -559,    57,   210,   549,  -559,   173,   232,   228,   287,
     231,   290,   417,    39,   473,  -559,   475,   122,  -559,   -51,
      -3,    -5,   208,  -559,   206,  -202,   -38,   664,   466,   260,
    -559,  -218,  -559,   468,    -4,    11,     2,  -291,    34,  -559,
     -10,  -559,  -559,   267,  -371,  -558,     6,  -559,   723,  -559,
    -559,  -559,  -559,   474,   478,  -559,  -559,  -559,  -559,  -559,
    -559,   212,   203,   207,   201,  -559,  -559,   494,  -559,  -559,
    -559,  -559,  -158,   -11,    -9,   523,  -559,  -559,   524,   526,
     532,  -559,  -559,  -559,  -386,  -559,  -394,  -559,  -388,  -559,
    -367,  -559,  -559,  -559,  -559,  -559,  -120,  -331,  -444,  -559,
    -559,   -12,  -559,  -559,  -559,  -559,  -559,  -443,  -559,   758,
     651,  -559,   655,  -559,   314,  -559,  -559,  -559,  -559,  -559,
    -559,  -559
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    78,    79,    80,    81,    82,    83,    84,   144,    85,
      86,    87,    88,   336,   174,   175,   146,    89,   147,    90,
     148,    91,   149,    92,    93,   172,    94,    95,    96,    97,
      98,   342,   343,   344,   345,   346,    99,   100,   101,   102,
     103,   104,   105,   106,   132,   563,   157,   162,   159,   166,
     570,   682,   278,   279,   280,   771,   361,     8,     9,   110,
     396,   260,   419,   440,   441,   422,   423,   527,   530,   533,
     536,   528,   531,   534,   537,   691,   692,   442,   539,   628,
     425,   540,   758,   759,   760,   443,   560,   648,   444,   445,
     446,   430,   431,   432,   158,   433,   163,   434,   160,   435,
     167,   436,   437,   438,   553,   439,   303,   529,   170,    24,
      25,   474,   156,     1,     2,     3,     4,   564,    10,    11,
     120,   121,   261,   447,   265,   122,   123,   124,   125,   126,
     127,   128
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
     107,   283,   277,   347,   150,   198,   199,   200,   201,   202,
     203,   566,   152,   545,   547,   152,   107,   161,   153,   478,
     479,   549,   171,   173,   133,   176,   151,   555,   154,   155,
     213,   215,   217,   218,   219,   221,   223,   305,   108,   307,
     393,   552,   309,   551,   585,   314,   313,   301,   209,   210,
     211,   212,   195,     6,   660,   294,   684,   683,  -225,   621,
     765,   318,   766,  -225,   131,   639,   731,   168,   532,   535,
     538,   145,  -225,  -225,  -225,  -225,  -225,  -225,  -225,  -225,
    -225,  -225,  -225,  -225,  -225,   519,  -225,  -225,  -225,  -225,
    -225,  -225,  -225,  -225,   455,   550,   359,   169,     5,   289,
     635,   394,   636,   291,   637,   319,   638,   720,   693,   182,
     641,   206,   194,   685,   640,   732,   649,   694,   109,   695,
     722,   696,   524,   697,   301,   721,    -4,   301,   650,   698,
     285,   700,   520,   226,   526,   704,   302,   395,   456,   304,
     295,   296,   615,  -339,   620,   204,   623,   450,   451,   315,
     316,   574,   575,   341,   341,   626,   315,   316,   350,   351,
     352,   353,   315,   316,   315,   316,   664,   207,   208,   525,
     665,   176,   177,   323,   324,   651,   326,   327,   328,   329,
     330,   164,   165,   333,   152,   152,   337,   338,   339,   340,
     334,   335,   145,     7,   195,   652,   331,   332,   194,   532,
     226,   205,   535,  -225,   772,   538,   616,   617,   629,   631,
     383,   384,   385,   386,   178,   616,   617,   315,   316,   315,
     316,   315,   316,   358,   183,   152,   362,   315,   316,   315,
     316,   360,   364,   315,   316,   616,   617,   616,   617,   616,
     617,   363,   651,   301,   780,   286,   510,   365,   616,   617,
     366,   520,   391,   511,   194,   306,   238,   239,   743,   744,
     238,   239,   274,   275,   276,   206,   107,   512,   301,   699,
     482,   458,   179,   483,   513,   301,   448,   449,   398,   399,
     308,   180,   402,   181,   404,   405,   406,   312,   182,   658,
     659,   651,   475,   183,   476,   461,   477,   164,   165,   418,
     480,   737,   738,   768,   453,   611,   161,   161,   601,   739,
     603,   253,   254,   255,   741,   484,   256,   686,   485,   184,
     687,   207,   208,   185,   277,   186,   481,   187,   561,   562,
     188,   740,   233,   565,   189,   234,   235,   190,   145,   242,
     243,   244,   245,   246,   247,   464,   145,   145,   145,   145,
     145,   145,   145,   145,   576,   577,   578,   579,  -221,   613,
     582,   230,   231,  -221,   377,   378,   379,   380,   381,   382,
     236,   237,  -221,  -221,  -221,  -221,  -221,  -221,  -221,  -221,
    -221,  -221,  -221,  -221,  -221,   191,  -221,  -221,  -221,  -221,
    -221,  -221,  -221,  -221,  -333,   192,  -333,  -333,  -331,   193,
     670,   152,   672,   161,   161,   107,   224,   542,   289,   152,
     227,   290,   291,  -333,  -333,   541,   229,   543,   505,   506,
     507,   632,   633,   634,  -333,   556,   228,   558,   266,   267,
     268,   269,   270,   271,   526,   232,   642,   240,   644,   248,
     249,   250,   251,   252,  -333,  -333,  -333,   241,  -333,  -333,
    -333,   238,   239,   595,   341,   341,   341,   341,   341,   341,
     259,   341,   465,   466,   467,   368,   369,   370,   257,   258,
     569,   263,   264,   572,   573,   111,   112,   113,   114,   115,
     116,   117,   118,   119,  -341,   586,   587,   292,   293,   588,
     508,   509,   591,   295,   296,   602,   337,   604,   593,   594,
     596,   597,   598,  -221,  -221,  -221,  -221,  -221,  -221,  -221,
    -221,  -221,  -221,   388,   389,   390,   152,   145,  -183,   724,
     468,   469,   609,   371,   372,   273,   471,   472,   373,   374,
     705,   284,   610,   589,   590,   735,   736,    12,  -331,    13,
      14,   287,   288,   297,   298,   723,   299,   300,   310,   311,
     317,   341,   320,   341,   325,   348,    15,    16,    -5,    -6,
     322,   349,   354,   301,   355,   356,   452,    17,   643,   357,
     454,   457,   459,   460,   462,   463,   161,   161,   473,   486,
     487,   488,   489,   490,   491,   656,   750,    18,    19,    20,
     492,    21,    22,    23,   493,   497,   498,   499,   501,   494,
     518,   521,   495,   496,   500,   681,   502,   503,   514,   515,
     688,   504,  -158,   689,   522,   516,   690,   517,   523,   526,
     557,   274,   559,   568,   571,   580,   583,   584,   581,   653,
     605,   654,   606,   607,   655,   716,   717,   718,   719,   612,
     608,   657,   661,   663,   777,   666,   662,   667,   668,   701,
     669,   671,   673,   674,   675,   676,   677,   702,   713,   703,
     785,   708,   706,   707,   709,   710,   712,   711,   714,   715,
     725,   726,   145,   727,   728,   729,   730,   145,   746,   724,
     145,   749,   751,   145,   754,   761,   762,   763,   767,   152,
     733,   161,   161,   107,   764,   734,   152,   769,   747,   770,
     775,   776,   778,   773,   774,   779,   786,   787,   748,   367,
     592,   470,   742,   375,   599,   745,   376,   600,   387,   196,
     152,   755,   756,   567,   321,   392,   360,  -263,   645,   152,
     753,   129,  -263,   619,   420,   757,   145,   625,   421,   614,
     622,  -263,  -263,  -263,  -263,  -263,  -263,  -263,  -263,  -263,
    -263,  -263,  -263,  -263,   424,  -263,  -263,  -263,  -263,  -263,
    -263,  -263,  -263,   782,   781,   145,   130,   262,     0,   152,
       0,     0,   272,   168,   152,   757,     0,   145,     0,     0,
     783,     0,     0,   426,   427,     0,   428,     0,   145,   145,
     784,     0,   429,     0,     0,  -223,   618,     0,     0,     0,
    -223,     0,     0,   169,     0,     0,     0,     0,   145,  -223,
    -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
    -223,  -223,     0,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
    -223,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   646,   647,     0,     0,
       0,   526,  -263,  -263,  -263,  -263,  -263,  -263,  -263,  -263,
    -263,  -263,  -247,   627,     0,     0,     0,  -247,     0,     0,
       0,     0,     0,     0,     0,     0,  -247,  -247,  -247,  -247,
    -247,  -247,  -247,  -247,  -247,  -247,  -247,  -247,  -247,     0,
    -247,  -247,  -247,  -247,  -247,  -247,  -247,  -247,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
    -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
    -227,   624,     0,     0,     0,  -227,     0,     0,   526,     0,
       0,     0,     0,     0,  -227,  -227,  -227,  -227,  -227,  -227,
    -227,  -227,  -227,  -227,  -227,  -227,  -227,     0,  -227,  -227,
    -227,  -227,  -227,  -227,  -227,  -227,  -253,   630,     0,     0,
       0,  -253,     0,     0,     0,     0,     0,     0,     0,     0,
    -253,  -253,  -253,  -253,  -253,  -253,  -253,  -253,  -253,  -253,
    -253,  -253,  -253,     0,  -253,  -253,  -253,  -253,  -253,  -253,
    -253,  -253,     0,     0,     0,     0,   526,  -247,  -247,  -247,
    -247,  -247,  -247,  -247,  -247,  -247,  -247,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,  -191,
     397,     0,     0,     0,  -191,     0,     0,     0,     0,     0,
       0,     0,   526,   398,   399,   400,   401,   402,   403,   404,
     405,   406,   407,   408,   409,   410,     0,   411,   412,   413,
     414,   415,   416,   417,   418,   678,     0,     0,     0,     0,
       0,     0,     0,     0,     0,  -227,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    26,     0,
       0,   134,     0,     0,     0,    28,    29,     0,     0,     0,
       0,  -253,     0,     0,     0,     0,     0,   679,   136,   137,
      30,    31,    32,    33,    34,   138,   139,    37,    38,    39,
      40,    41,    42,    43,     0,   680,    45,    46,   140,    48,
      49,    50,    51,    52,    53,    54,     0,     0,     0,     0,
       0,     0,     0,   141,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   544,     0,     0,     0,     0,
       0,     0,     0,     0,  -191,     0,     0,    26,     0,     0,
      27,     0,     0,     0,    28,    29,     0,     0,     0,     0,
       0,     0,     0,     0,   142,   143,     0,     0,    77,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,     0,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,     0,     0,     0,     0,     0,
       0,     0,    55,     0,    56,    57,    58,    59,    60,    61,
      62,    63,     0,     0,     0,     0,    64,    65,    66,    67,
     546,     0,     0,    68,    69,    70,    71,    72,    73,    74,
       0,     0,    26,     0,     0,    27,     0,     0,     0,    28,
      29,     0,     0,    75,    76,     0,     0,    77,     0,     0,
       0,     0,     0,     0,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,     0,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
       0,     0,     0,     0,     0,     0,     0,    55,     0,    56,
      57,    58,    59,    60,    61,    62,    63,     0,     0,     0,
       0,    64,    65,    66,    67,   548,     0,     0,    68,    69,
      70,    71,    72,    73,    74,     0,     0,    26,     0,     0,
      27,     0,     0,     0,    28,    29,     0,     0,    75,    76,
       0,     0,    77,     0,     0,     0,     0,     0,     0,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,     0,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,     0,     0,     0,     0,     0,
       0,     0,    55,     0,    56,    57,    58,    59,    60,    61,
      62,    63,     0,     0,     0,     0,    64,    65,    66,    67,
     554,     0,     0,    68,    69,    70,    71,    72,    73,    74,
       0,     0,    26,     0,     0,    27,     0,     0,     0,    28,
      29,     0,     0,    75,    76,     0,     0,    77,     0,     0,
       0,     0,     0,     0,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,     0,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
       0,     0,     0,     0,     0,     0,     0,    55,     0,    56,
      57,    58,    59,    60,    61,    62,    63,     0,     0,     0,
       0,    64,    65,    66,    67,     0,     0,     0,    68,    69,
      70,    71,    72,    73,    74,    26,     0,     0,    27,     0,
       0,     0,    28,    29,     0,     0,     0,     0,    75,    76,
       0,     0,    77,     0,     0,     0,     0,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,     0,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,     0,     0,     0,     0,     0,     0,     0,
      55,     0,    56,    57,    58,    59,    60,    61,    62,    63,
       0,     0,     0,     0,    64,    65,    66,    67,     0,     0,
       0,    68,    69,    70,    71,    72,    73,    74,    26,     0,
       0,    27,     0,     0,     0,    28,    29,     0,     0,     0,
       0,    75,    76,     0,     0,    77,     0,     0,   214,     0,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,     0,    44,    45,    46,    47,    48,
      49,    50,    51,    52,    53,    54,     0,     0,     0,     0,
       0,     0,     0,    55,     0,    56,    57,    58,    59,    60,
      61,    62,    63,     0,     0,     0,     0,    64,    65,    66,
      67,     0,     0,     0,    68,    69,    70,    71,    72,    73,
      74,    26,     0,     0,    27,     0,     0,     0,    28,    29,
       0,     0,     0,     0,    75,    76,     0,     0,    77,     0,
       0,   216,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,     0,    44,    45,
      46,    47,    48,    49,    50,    51,    52,    53,    54,     0,
       0,     0,     0,     0,     0,     0,    55,     0,    56,    57,
      58,    59,    60,    61,    62,    63,     0,     0,     0,     0,
      64,    65,    66,    67,     0,     0,     0,    68,    69,    70,
      71,    72,    73,    74,    26,     0,     0,    27,     0,     0,
       0,    28,    29,     0,     0,     0,     0,    75,    76,     0,
       0,    77,     0,     0,   220,     0,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
       0,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,     0,     0,     0,     0,     0,     0,     0,    55,
       0,    56,    57,    58,    59,    60,    61,    62,    63,     0,
       0,     0,     0,    64,    65,    66,    67,     0,     0,     0,
      68,    69,    70,    71,    72,    73,    74,    26,     0,     0,
      27,     0,     0,     0,    28,    29,     0,     0,     0,     0,
      75,    76,     0,     0,    77,     0,     0,   222,     0,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,     0,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,     0,     0,     0,     0,     0,
       0,     0,    55,     0,    56,    57,    58,    59,    60,    61,
      62,    63,     0,     0,     0,     0,    64,    65,    66,    67,
       0,     0,     0,    68,    69,    70,    71,    72,    73,    74,
     281,     0,     0,    26,     0,     0,     0,     0,     0,     0,
      28,    29,     0,    75,    76,     0,     0,    77,     0,     0,
     733,     0,     0,     0,   282,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,     0,
      44,    45,    46,   140,    48,    49,    50,    51,    52,    53,
      54,     0,     0,     0,     0,     0,     0,     0,   141,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    26,   752,     0,    27,     0,     0,     0,    28,
      29,     0,     0,     0,     0,     0,     0,     0,     0,   142,
     143,     0,     0,    77,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,     0,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
       0,     0,     0,     0,     0,     0,     0,    55,     0,    56,
      57,    58,    59,    60,    61,    62,    63,     0,     0,     0,
       0,    64,    65,    66,    67,     0,     0,     0,    68,    69,
      70,    71,    72,    73,    74,    26,     0,     0,    27,     0,
       0,     0,    28,    29,     0,     0,     0,     0,    75,    76,
       0,     0,    77,     0,     0,     0,     0,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,     0,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,     0,     0,     0,     0,     0,     0,     0,
      55,     0,    56,    57,    58,    59,    60,    61,    62,    63,
       0,     0,     0,     0,    64,    65,    66,    67,     0,     0,
       0,    68,    69,    70,    71,    72,    73,    74,    26,     0,
       0,     0,     0,     0,     0,    28,    29,     0,     0,     0,
       0,    75,    76,     0,     0,    77,     0,     0,     0,     0,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,     0,    44,    45,    46,   140,    48,
      49,    50,    51,    52,    53,    54,     0,     0,     0,     0,
       0,     0,     0,    55,     0,    56,    57,    58,    59,    60,
      61,    62,    63,     0,     0,     0,     0,    64,    65,    66,
      67,     0,     0,     0,    68,    69,    70,    71,    72,    73,
      74,    26,     0,     0,    27,     0,     0,     0,    28,    29,
       0,     0,     0,     0,   142,   143,     0,     0,    77,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,     0,    44,    45,
      46,    47,    48,    49,    50,    51,    52,    53,    54,     0,
       0,     0,     0,     0,     0,     0,   197,     0,    56,    57,
      58,    59,    60,    61,    62,    63,     0,     0,     0,     0,
      64,    65,    66,    67,     0,     0,     0,     0,     0,     0,
      26,     0,     0,     0,     0,     0,     0,    28,    29,     0,
       0,     0,     0,     0,     0,     0,     0,    75,    76,     0,
       0,    77,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    42,    43,     0,    44,    45,    46,
     140,    48,    49,    50,    51,    52,    53,    54,     0,     0,
       0,     0,     0,     0,     0,   197,     0,    56,    57,    58,
      59,    60,    61,    62,    63,     0,     0,     0,     0,    64,
      65,    66,    67,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    26,     0,     0,   134,     0,     0,     0,    28,
      29,     0,     0,     0,     0,     0,   142,   143,     0,     0,
      77,   135,   136,   137,    30,    31,    32,    33,    34,   138,
     139,    37,    38,    39,    40,    41,    42,    43,     0,    44,
      45,    46,   140,    48,    49,    50,    51,    52,    53,    54,
       0,     0,     0,     0,     0,     0,     0,   141,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    26,     0,     0,   134,     0,     0,
       0,    28,    29,     0,     0,     0,     0,     0,   142,   143,
       0,     0,    77,   679,   136,   137,    30,    31,    32,    33,
      34,   138,   139,    37,    38,    39,    40,    41,    42,    43,
       0,   680,    45,    46,   140,    48,    49,    50,    51,    52,
      53,    54,     0,     0,     0,     0,     0,     0,     0,   141,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    26,     0,     0,    27,     0,     0,     0,
      28,    29,     0,     0,     0,     0,     0,     0,     0,     0,
     142,   143,     0,     0,    77,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,     0,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,     0,     0,     0,     0,     0,     0,     0,   141,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    26,     0,     0,     0,     0,     0,     0,    28,
      29,     0,     0,     0,     0,     0,     0,     0,     0,    75,
      76,     0,     0,    77,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,     0,    44,
      45,    46,   225,    48,    49,    50,    51,    52,    53,    54,
       0,     0,     0,     0,     0,     0,     0,   141,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    26,     0,     0,     0,     0,     0,     0,    28,    29,
       0,     0,     0,     0,     0,     0,     0,     0,   142,   143,
       0,     0,    77,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,     0,    44,    45,
      46,   140,    48,    49,    50,    51,    52,    53,    54,     0,
       0,     0,     0,     0,     0,     0,   141,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   142,   143,     0,
       0,    77
};

static const yytype_int16 yycheck[] =
{
       4,   135,   134,   205,    14,    56,    57,    58,    59,    60,
      61,   454,    16,   407,   408,    19,    20,    21,    16,   310,
     311,   409,    26,    27,    13,    29,    15,   413,    17,    18,
      68,    69,    70,    71,    72,    73,    74,   157,     4,   159,
     258,   412,   162,   410,   488,    38,   166,    38,    64,    65,
      66,    67,    55,     5,    40,    45,    79,   615,     0,     1,
      40,    43,    40,     5,    38,    38,    88,    46,   399,   400,
     401,    14,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    40,    28,    29,    30,    31,
      32,    33,    34,    35,    43,    27,   228,    76,     0,   134,
     544,    40,   546,   138,   548,    87,   550,    58,    44,    39,
     554,    79,    55,   136,    87,   137,   560,    44,    76,    44,
     678,    44,    40,    44,    38,    76,    45,    38,    40,    44,
      60,    44,    87,    76,    76,    44,    50,    76,    87,    50,
     130,   131,    49,     0,    49,   142,    49,   267,   268,   142,
     143,   142,   143,   204,   205,    49,   142,   143,   209,   210,
     211,   212,   142,   143,   142,   143,    40,   135,   136,    87,
      40,   175,    39,   177,   178,    87,   180,   181,   182,   183,
     184,   113,   114,   187,   188,   189,   190,   191,   192,   193,
     188,   189,   135,   145,   197,    40,   185,   186,   141,   530,
     143,   142,   533,   145,    40,   536,   142,   143,   539,   540,
     248,   249,   250,   251,    39,   142,   143,   142,   143,   142,
     143,   142,   143,   227,    39,   229,   230,   142,   143,   142,
     143,   229,   230,   142,   143,   142,   143,   142,   143,   142,
     143,   230,    87,    38,    40,    60,   105,    76,   142,   143,
      79,    87,   256,   112,   197,    50,   130,   131,   702,   703,
     130,   131,    76,    77,    78,    79,   270,   105,    38,   640,
      76,   281,    39,    79,   112,    38,   265,   266,    14,    15,
      50,    39,    18,    39,    20,    21,    22,    50,    39,   580,
     581,    87,   304,    39,   306,   284,   308,   113,   114,    35,
     312,   695,   696,   746,   270,   523,   310,   311,   510,   697,
     512,    90,    91,    92,   700,   319,    95,    76,   322,    39,
      79,   135,   136,    39,   456,    39,   315,    39,   448,   449,
      39,   698,   134,   453,    39,   137,   138,    39,   281,   122,
     123,   124,   125,   126,   127,   288,   289,   290,   291,   292,
     293,   294,   295,   296,   474,   475,   476,   477,     0,     1,
     480,   142,   143,     5,   242,   243,   244,   245,   246,   247,
     135,   136,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    39,    28,    29,    30,    31,
      32,    33,    34,    35,     1,    39,     3,     4,     5,    39,
     602,   405,   604,   407,   408,   409,    79,   405,   134,   413,
      39,   137,   138,    20,    21,   404,    39,   406,    90,    91,
      92,   541,   542,   543,    31,   414,    45,   416,   114,   115,
     116,   117,   118,   119,    76,   141,   556,   128,   558,   104,
     105,   106,   107,    93,    51,    52,    53,   129,    55,    56,
      57,   130,   131,   504,   505,   506,   507,   508,   509,   510,
      39,   512,   289,   290,   291,   233,   234,   235,    88,    89,
     459,   146,   147,   462,   463,   146,   147,   148,   149,   150,
     151,   152,   153,   154,     0,   489,   490,   135,   136,   493,
      88,    89,   496,   130,   131,   511,   500,   513,   502,   503,
     505,   506,   507,   145,   146,   147,   148,   149,   150,   151,
     152,   153,   154,   253,   254,   255,   520,   460,    38,    39,
     292,   293,   520,   236,   237,    38,   295,   296,   238,   239,
     650,   142,   521,   494,   495,   693,   694,     1,   145,     3,
       4,    79,   141,    38,    38,   679,    38,    38,   142,   142,
      40,   602,    48,   604,    75,    79,    20,    21,    45,    45,
      49,    79,    79,    38,    79,    79,    39,    31,   557,    79,
      39,   143,   142,    36,   142,   142,   580,   581,    76,    40,
      40,    39,    87,    87,    40,   574,   720,    51,    52,    53,
      40,    55,    56,    57,    87,    40,    40,    40,    40,    87,
      40,    49,    87,    87,    87,   615,    87,    87,    87,    87,
     620,    93,    41,   623,    41,    87,   626,    87,    49,    76,
      39,    76,    76,    76,    41,    87,    41,    38,    87,    41,
      79,    41,    79,    79,    41,   673,   674,   675,   676,    76,
      79,    76,    40,    40,   764,    40,    87,    40,    40,    87,
      41,    41,    41,    41,    41,    41,    41,    39,   662,    39,
     780,    36,   651,    88,    41,    41,    87,    41,    41,    41,
      38,    41,   615,    79,    38,    38,    38,   620,    39,    39,
     623,    40,    36,   626,    41,    38,    38,    38,    38,   693,
     142,   695,   696,   697,    40,   693,   700,    40,   708,    36,
      41,    41,    44,    87,    87,    44,    38,    38,   712,   232,
     500,   294,   701,   240,   508,   704,   241,   509,   252,    55,
     724,   731,   732,   456,   175,   257,   724,     0,     1,   733,
     724,     8,     5,   530,   260,   733,   679,   536,   260,   527,
     533,    14,    15,    16,    17,    18,    19,    20,    21,    22,
      23,    24,    25,    26,   260,    28,    29,    30,    31,    32,
      33,    34,    35,   774,   773,   708,     8,   112,    -1,   773,
      -1,    -1,   121,    46,   778,   773,    -1,   720,    -1,    -1,
     778,    -1,    -1,   260,   260,    -1,   260,    -1,   731,   732,
     779,    -1,   260,    -1,    -1,     0,     1,    -1,    -1,    -1,
       5,    -1,    -1,    76,    -1,    -1,    -1,    -1,   751,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    -1,    28,    29,    30,    31,    32,    33,    34,
      35,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   139,   140,    -1,    -1,
      -1,    76,   145,   146,   147,   148,   149,   150,   151,   152,
     153,   154,     0,     1,    -1,    -1,    -1,     5,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    -1,
      28,    29,    30,    31,    32,    33,    34,    35,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154,
       0,     1,    -1,    -1,    -1,     5,    -1,    -1,    76,    -1,
      -1,    -1,    -1,    -1,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    -1,    28,    29,
      30,    31,    32,    33,    34,    35,     0,     1,    -1,    -1,
      -1,     5,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    -1,    28,    29,    30,    31,    32,    33,
      34,    35,    -1,    -1,    -1,    -1,    76,   145,   146,   147,
     148,   149,   150,   151,   152,   153,   154,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     0,
       1,    -1,    -1,    -1,     5,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    76,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    -1,    28,    29,    30,
      31,    32,    33,    34,    35,     6,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   145,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    39,    -1,
      -1,    42,    -1,    -1,    -1,    46,    47,    -1,    -1,    -1,
      -1,   145,    -1,    -1,    -1,    -1,    -1,    58,    59,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    -1,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    94,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    27,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   145,    -1,    -1,    39,    -1,    -1,
      42,    -1,    -1,    -1,    46,    47,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   135,   136,    -1,    -1,   139,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
      72,    73,    74,    -1,    76,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    94,    -1,    96,    97,    98,    99,   100,   101,
     102,   103,    -1,    -1,    -1,    -1,   108,   109,   110,   111,
      27,    -1,    -1,   115,   116,   117,   118,   119,   120,   121,
      -1,    -1,    39,    -1,    -1,    42,    -1,    -1,    -1,    46,
      47,    -1,    -1,   135,   136,    -1,    -1,   139,    -1,    -1,
      -1,    -1,    -1,    -1,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    -1,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    96,
      97,    98,    99,   100,   101,   102,   103,    -1,    -1,    -1,
      -1,   108,   109,   110,   111,    27,    -1,    -1,   115,   116,
     117,   118,   119,   120,   121,    -1,    -1,    39,    -1,    -1,
      42,    -1,    -1,    -1,    46,    47,    -1,    -1,   135,   136,
      -1,    -1,   139,    -1,    -1,    -1,    -1,    -1,    -1,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
      72,    73,    74,    -1,    76,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    94,    -1,    96,    97,    98,    99,   100,   101,
     102,   103,    -1,    -1,    -1,    -1,   108,   109,   110,   111,
      27,    -1,    -1,   115,   116,   117,   118,   119,   120,   121,
      -1,    -1,    39,    -1,    -1,    42,    -1,    -1,    -1,    46,
      47,    -1,    -1,   135,   136,    -1,    -1,   139,    -1,    -1,
      -1,    -1,    -1,    -1,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    -1,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    96,
      97,    98,    99,   100,   101,   102,   103,    -1,    -1,    -1,
      -1,   108,   109,   110,   111,    -1,    -1,    -1,   115,   116,
     117,   118,   119,   120,   121,    39,    -1,    -1,    42,    -1,
      -1,    -1,    46,    47,    -1,    -1,    -1,    -1,   135,   136,
      -1,    -1,   139,    -1,    -1,    -1,    -1,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    -1,    76,    77,    78,    79,    80,    81,    82,    83,
      84,    85,    86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      94,    -1,    96,    97,    98,    99,   100,   101,   102,   103,
      -1,    -1,    -1,    -1,   108,   109,   110,   111,    -1,    -1,
      -1,   115,   116,   117,   118,   119,   120,   121,    39,    -1,
      -1,    42,    -1,    -1,    -1,    46,    47,    -1,    -1,    -1,
      -1,   135,   136,    -1,    -1,   139,    -1,    -1,   142,    -1,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    -1,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    94,    -1,    96,    97,    98,    99,   100,
     101,   102,   103,    -1,    -1,    -1,    -1,   108,   109,   110,
     111,    -1,    -1,    -1,   115,   116,   117,   118,   119,   120,
     121,    39,    -1,    -1,    42,    -1,    -1,    -1,    46,    47,
      -1,    -1,    -1,    -1,   135,   136,    -1,    -1,   139,    -1,
      -1,   142,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    -1,    76,    77,
      78,    79,    80,    81,    82,    83,    84,    85,    86,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    96,    97,
      98,    99,   100,   101,   102,   103,    -1,    -1,    -1,    -1,
     108,   109,   110,   111,    -1,    -1,    -1,   115,   116,   117,
     118,   119,   120,   121,    39,    -1,    -1,    42,    -1,    -1,
      -1,    46,    47,    -1,    -1,    -1,    -1,   135,   136,    -1,
      -1,   139,    -1,    -1,   142,    -1,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      -1,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,
      -1,    96,    97,    98,    99,   100,   101,   102,   103,    -1,
      -1,    -1,    -1,   108,   109,   110,   111,    -1,    -1,    -1,
     115,   116,   117,   118,   119,   120,   121,    39,    -1,    -1,
      42,    -1,    -1,    -1,    46,    47,    -1,    -1,    -1,    -1,
     135,   136,    -1,    -1,   139,    -1,    -1,   142,    -1,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
      72,    73,    74,    -1,    76,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    94,    -1,    96,    97,    98,    99,   100,   101,
     102,   103,    -1,    -1,    -1,    -1,   108,   109,   110,   111,
      -1,    -1,    -1,   115,   116,   117,   118,   119,   120,   121,
      36,    -1,    -1,    39,    -1,    -1,    -1,    -1,    -1,    -1,
      46,    47,    -1,   135,   136,    -1,    -1,   139,    -1,    -1,
     142,    -1,    -1,    -1,    60,    61,    62,    63,    64,    65,
      66,    67,    68,    69,    70,    71,    72,    73,    74,    -1,
      76,    77,    78,    79,    80,    81,    82,    83,    84,    85,
      86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    39,    40,    -1,    42,    -1,    -1,    -1,    46,
      47,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   135,
     136,    -1,    -1,   139,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    -1,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    96,
      97,    98,    99,   100,   101,   102,   103,    -1,    -1,    -1,
      -1,   108,   109,   110,   111,    -1,    -1,    -1,   115,   116,
     117,   118,   119,   120,   121,    39,    -1,    -1,    42,    -1,
      -1,    -1,    46,    47,    -1,    -1,    -1,    -1,   135,   136,
      -1,    -1,   139,    -1,    -1,    -1,    -1,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    -1,    76,    77,    78,    79,    80,    81,    82,    83,
      84,    85,    86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      94,    -1,    96,    97,    98,    99,   100,   101,   102,   103,
      -1,    -1,    -1,    -1,   108,   109,   110,   111,    -1,    -1,
      -1,   115,   116,   117,   118,   119,   120,   121,    39,    -1,
      -1,    -1,    -1,    -1,    -1,    46,    47,    -1,    -1,    -1,
      -1,   135,   136,    -1,    -1,   139,    -1,    -1,    -1,    -1,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    -1,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    94,    -1,    96,    97,    98,    99,   100,
     101,   102,   103,    -1,    -1,    -1,    -1,   108,   109,   110,
     111,    -1,    -1,    -1,   115,   116,   117,   118,   119,   120,
     121,    39,    -1,    -1,    42,    -1,    -1,    -1,    46,    47,
      -1,    -1,    -1,    -1,   135,   136,    -1,    -1,   139,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    -1,    76,    77,
      78,    79,    80,    81,    82,    83,    84,    85,    86,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    96,    97,
      98,    99,   100,   101,   102,   103,    -1,    -1,    -1,    -1,
     108,   109,   110,   111,    -1,    -1,    -1,    -1,    -1,    -1,
      39,    -1,    -1,    -1,    -1,    -1,    -1,    46,    47,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   135,   136,    -1,
      -1,   139,    61,    62,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    73,    74,    -1,    76,    77,    78,
      79,    80,    81,    82,    83,    84,    85,    86,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    94,    -1,    96,    97,    98,
      99,   100,   101,   102,   103,    -1,    -1,    -1,    -1,   108,
     109,   110,   111,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    39,    -1,    -1,    42,    -1,    -1,    -1,    46,
      47,    -1,    -1,    -1,    -1,    -1,   135,   136,    -1,    -1,
     139,    58,    59,    60,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    -1,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    39,    -1,    -1,    42,    -1,    -1,
      -1,    46,    47,    -1,    -1,    -1,    -1,    -1,   135,   136,
      -1,    -1,   139,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      -1,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    39,    -1,    -1,    42,    -1,    -1,    -1,
      46,    47,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     135,   136,    -1,    -1,   139,    61,    62,    63,    64,    65,
      66,    67,    68,    69,    70,    71,    72,    73,    74,    -1,
      76,    77,    78,    79,    80,    81,    82,    83,    84,    85,
      86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    39,    -1,    -1,    -1,    -1,    -1,    -1,    46,
      47,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   135,
     136,    -1,    -1,   139,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    -1,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    39,    -1,    -1,    -1,    -1,    -1,    -1,    46,    47,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   135,   136,
      -1,    -1,   139,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    -1,    76,    77,
      78,    79,    80,    81,    82,    83,    84,    85,    86,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    94,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   135,   136,    -1,
      -1,   139
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint16 yystos[] =
{
       0,   268,   269,   270,   271,     0,     5,   145,   212,   213,
     273,   274,     1,     3,     4,    20,    21,    31,    51,    52,
      53,    55,    56,    57,   264,   265,    39,    42,    46,    47,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    76,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    94,    96,    97,    98,    99,
     100,   101,   102,   103,   108,   109,   110,   111,   115,   116,
     117,   118,   119,   120,   121,   135,   136,   139,   156,   157,
     158,   159,   160,   161,   162,   164,   165,   166,   167,   172,
     174,   176,   178,   179,   181,   182,   183,   184,   185,   191,
     192,   193,   194,   195,   196,   197,   198,   199,   203,    76,
     214,   146,   147,   148,   149,   150,   151,   152,   153,   154,
     275,   276,   280,   281,   282,   283,   284,   285,   286,   213,
     274,    38,   199,   200,    42,    58,    59,    60,    66,    67,
      79,    94,   135,   136,   163,   167,   171,   173,   175,   177,
     205,   200,   199,   201,   200,   200,   267,   201,   249,   203,
     253,   199,   202,   251,   113,   114,   204,   255,    46,    76,
     263,   199,   180,   199,   169,   170,   199,    39,    39,    39,
      39,    39,    39,    39,    39,    39,    39,    39,    39,    39,
      39,    39,    39,    39,   167,   185,   192,    94,   184,   184,
     184,   184,   184,   184,   142,   142,    79,   135,   136,   162,
     162,   162,   162,   191,   142,   191,   142,   191,   191,   191,
     142,   191,   142,   191,    79,    79,   167,    39,    45,    39,
     142,   143,   141,   134,   137,   138,   135,   136,   130,   131,
     128,   129,   122,   123,   124,   125,   126,   127,   104,   105,
     106,   107,    93,    90,    91,    92,    95,    88,    89,    39,
     216,   277,   277,   146,   147,   279,   279,   279,   279,   279,
     279,   279,   275,    38,    76,    77,    78,   157,   207,   208,
     209,    36,    60,   163,   142,    60,    60,    79,   141,   134,
     137,   138,   135,   136,    45,   130,   131,    38,    38,    38,
      38,    38,    50,   261,    50,   261,    50,   261,    50,   261,
     142,   142,    50,   261,    38,   142,   143,    40,    43,    87,
      48,   169,    49,   199,   199,    75,   199,   199,   199,   199,
     199,   200,   200,   199,   201,   201,   168,   199,   199,   199,
     199,   184,   186,   187,   188,   189,   190,   190,    79,    79,
     184,   184,   184,   184,    79,    79,    79,    79,   199,   157,
     201,   211,   199,   200,   201,    76,    79,   165,   172,   172,
     172,   174,   174,   176,   176,   179,   181,   182,   182,   182,
     182,   182,   182,   191,   191,   191,   191,   193,   194,   194,
     194,   199,   198,   196,    40,    76,   215,     1,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    28,    29,    30,    31,    32,    33,    34,    35,   217,
     218,   219,   220,   221,   232,   235,   240,   243,   244,   245,
     246,   247,   248,   250,   252,   254,   256,   257,   258,   260,
     218,   219,   232,   240,   243,   244,   245,   278,   200,   200,
     261,   261,    39,   203,    39,    43,    87,   143,   205,   142,
      36,   200,   142,   142,   167,   171,   171,   171,   173,   173,
     177,   175,   175,    76,   266,   266,   266,   266,   202,   202,
     266,   200,    76,    79,   199,   199,    40,    40,    39,    87,
      87,    40,    40,    87,    87,    87,    87,    40,    40,    40,
      87,    40,    87,    87,    93,    90,    91,    92,    88,    89,
     105,   112,   105,   112,    87,    87,    87,    87,    40,    40,
      87,    49,    41,    49,    40,    87,    76,   222,   226,   262,
     223,   227,   262,   224,   228,   262,   225,   229,   262,   233,
     236,   200,   201,   200,    27,   251,    27,   251,    27,   253,
      27,   255,   209,   259,    27,   249,   200,    39,   200,    76,
     241,   261,   261,   200,   272,   261,   272,   208,    76,   200,
     205,    41,   200,   200,   142,   143,   261,   261,   261,   261,
      87,    87,   261,    41,    38,   263,   199,   199,   199,   178,
     178,   199,   168,   199,   199,   184,   186,   186,   186,   189,
     187,   190,   162,   190,   162,    79,    79,    79,    79,   201,
     200,   196,    76,     1,   226,    49,   142,   143,     1,   227,
      49,     1,   228,    49,     1,   229,    49,     1,   234,   262,
       1,   262,   261,   261,   261,   263,   263,   263,   263,    38,
      87,   263,   261,   200,   261,     1,   139,   140,   242,   263,
      40,    87,    40,    41,    41,    41,   200,    76,   202,   202,
      40,    40,    87,    40,    40,    40,    40,    40,    40,    41,
     190,    41,   190,    41,    41,    41,    41,    41,     6,    58,
      76,   205,   206,   210,    79,   136,    76,    79,   205,   205,
     205,   230,   231,    44,    44,    44,    44,    44,    44,   209,
      44,    87,    39,    39,    44,   261,   200,    88,    36,    41,
      41,    41,    87,   199,    41,    41,   191,   191,   191,   191,
      58,    76,   210,   163,    39,    38,    41,    79,    38,    38,
      38,    88,   137,   142,   201,   237,   237,   251,   251,   253,
     255,   249,   200,   263,   263,   200,    39,   205,   199,    40,
     163,    36,    40,   211,    41,   205,   205,   201,   237,   238,
     239,    38,    38,    38,    40,    40,    40,    38,   272,    40,
      36,   210,    40,    87,    87,    41,    41,   261,    44,    44,
      40,   239,   238,   201,   200,   261,    38,    38
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint16 yyr1[] =
{
       0,   155,   156,   156,   157,   157,   157,   158,   159,   160,
     161,   162,   163,   164,   164,   164,   164,   164,   164,   164,
     164,   164,   164,   164,   165,   165,   166,   167,   167,   167,
     167,   167,   167,   167,   167,   167,   167,   167,   167,   167,
     167,   167,   167,   167,   167,   167,   167,   167,   167,   167,
     167,   167,   168,   168,   169,   169,   170,   171,   171,   172,
     172,   173,   173,   173,   173,   174,   174,   174,   174,   175,
     175,   175,   176,   176,   176,   177,   177,   177,   178,   178,
     178,   179,   179,   179,   180,   180,   181,   181,   182,   182,
     183,   183,   183,   183,   183,   183,   183,   184,   184,   185,
     185,   185,   185,   185,   185,   185,   185,   185,   185,   185,
     185,   185,   185,   185,   186,   186,   187,   187,   187,   187,
     188,   188,   189,   189,   190,   191,   191,   192,   192,   192,
     192,   192,   192,   192,   192,   192,   192,   192,   192,   193,
     193,   193,   193,   193,   194,   194,   195,   195,   195,   195,
     196,   196,   197,   197,   198,   198,   199,   200,   201,   202,
     203,   204,   204,   205,   205,   205,   205,   205,   205,   205,
     205,   205,   206,   206,   206,   207,   207,   208,   208,   208,
     208,   209,   209,   210,   210,   210,   210,   211,   211,   212,
     212,   213,   214,   214,   214,   215,   215,   216,   216,   216,
     217,   217,   217,   217,   217,   217,   217,   217,   217,   217,
     217,   217,   217,   217,   217,   217,   217,   217,   217,   217,
     218,   218,   219,   219,   220,   220,   221,   221,   222,   222,
     222,   223,   223,   223,   224,   224,   224,   225,   225,   225,
     226,   227,   228,   229,   230,   231,   231,   232,   233,   233,
     233,   234,   234,   235,   236,   236,   236,   237,   237,   238,
     238,   239,   239,   240,   241,   241,   241,   242,   242,   242,
     243,   244,   245,   246,   247,   248,   249,   249,   250,   250,
     251,   251,   252,   252,   252,   252,   253,   253,   254,   254,
     255,   255,   256,   256,   257,   258,   259,   259,   259,   260,
     261,   261,   262,   262,   262,   262,   262,   263,   263,   263,
     263,   263,   264,   264,   264,   265,   265,   265,   265,   265,
     265,   265,   265,   265,   265,   265,   266,   266,   266,   267,
     267,   269,   268,   270,   268,   271,   268,   272,   272,   273,
     273,   273,   273,   274,   275,   275,   276,   276,   276,   276,
     276,   276,   276,   276,   276,   277,   277,   278,   278,   278,
     278,   278,   278,   278,   279,   279,   280,   281,   282,   283,
     284,   285,   286
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     1,     2,     2,     1,     1,     1,
       1,     3,     3,     1,     1,     6,     6,     4,     4,     1,
       1,     1,     1,     1,     1,     1,     4,     1,     2,     1,
       1,     3,     3,     4,     6,     3,     4,     6,     6,     2,
       4,     4,     4,     4,     4,     6,     6,     3,     6,     8,
       9,     4,     1,     3,     1,     2,     4,     1,     3,     1,
       3,     1,     3,     3,     3,     1,     3,     3,     3,     1,
       3,     3,     1,     3,     3,     1,     3,     3,     1,     3,
       3,     1,     1,     3,     1,     3,     1,     3,     1,     3,
       1,     3,     3,     3,     3,     3,     3,     1,     1,     2,
       2,     2,     2,     2,     2,     6,     6,     7,     7,     3,
       3,     3,     3,     2,     1,     3,     1,     3,     3,     3,
       1,     3,     1,     3,     1,     1,     1,     2,     2,     2,
       2,     7,     2,     7,     2,     7,     2,     7,     2,     1,
       3,     3,     3,     3,     1,     3,     1,     3,     3,     3,
       1,     5,     1,     3,     1,     3,     1,     1,     1,     1,
       1,     6,     6,     1,     4,     5,     5,     1,     3,     7,
       4,     3,     1,     1,     2,     1,     3,     1,     1,     1,
       1,     1,     3,     1,     3,     4,     4,     1,     3,     1,
       2,     3,     1,     3,     4,     1,     3,     0,     2,     2,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     2,     1,     2,     1,     2,     1,     2,     1,     2,
       2,     1,     2,     2,     1,     2,     2,     1,     2,     2,
       4,     4,     4,     4,     3,     1,     3,     2,     0,     2,
       2,     4,     4,     2,     0,     5,     2,     3,     3,     1,
       3,     3,     1,     2,     0,     2,     2,     4,     7,     7,
       3,     3,     3,     3,     3,     7,     2,     4,     2,     5,
       2,     4,     2,     2,     5,     5,     2,     4,     2,     5,
       2,     4,     2,     5,     1,     3,     0,     1,     3,     2,
       0,     1,     1,     3,     3,     4,     5,     1,     1,     3,
       3,     4,     1,     2,     1,     3,     3,     3,     3,     3,
       2,     2,     2,     2,     2,     3,     1,     3,     4,     2,
       4,     0,     2,     0,     2,     0,     2,     1,     3,     1,
       1,     2,     2,     2,     0,     2,     2,     2,     1,     1,
       1,     1,     1,     1,     1,     0,     2,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     4,     4,     3,     3,
       6,     4,    10
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 3:
#line 244 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2648 "grammar.c" /* yacc.c:1646  */
    break;

  case 5:
#line 248 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2654 "grammar.c" /* yacc.c:1646  */
    break;

  case 6:
#line 250 "grammar.y" /* yacc.c:1646  */
    {node_int_setcar((yyvsp[0].node), -(node_get_int((yyvsp[0].node)))); (yyval.node) = (yyvsp[0].node);}
#line 2660 "grammar.c" /* yacc.c:1646  */
    break;

  case 11:
#line 263 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, TWODOTS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 2666 "grammar.c" /* yacc.c:1646  */
    break;

  case 12:
#line 267 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, TWODOTS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 2672 "grammar.c" /* yacc.c:1646  */
    break;

  case 15:
#line 273 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, UWCONST, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2678 "grammar.c" /* yacc.c:1646  */
    break;

  case 16:
#line 275 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SWCONST, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2684 "grammar.c" /* yacc.c:1646  */
    break;

  case 17:
#line 277 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, WSIZEOF, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2690 "grammar.c" /* yacc.c:1646  */
    break;

  case 18:
#line 279 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, CAST_TOINT, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2696 "grammar.c" /* yacc.c:1646  */
    break;

  case 21:
#line 283 "grammar.y" /* yacc.c:1646  */
    {
                 nusmv_yyerror("fractional constants are not supported.");
                 YYABORT;
               }
#line 2705 "grammar.c" /* yacc.c:1646  */
    break;

  case 22:
#line 288 "grammar.y" /* yacc.c:1646  */
    {
                 nusmv_yyerror("exponential constants are not supported.");
                 YYABORT;
               }
#line 2714 "grammar.c" /* yacc.c:1646  */
    break;

  case 23:
#line 293 "grammar.y" /* yacc.c:1646  */
    {
                 nusmv_yyerror("real constants are not supported.");
                 YYABORT;
               }
#line 2723 "grammar.c" /* yacc.c:1646  */
    break;

  case 25:
#line 302 "grammar.y" /* yacc.c:1646  */
    {
                 nusmv_yyerror("functions are not supported.");
                 YYABORT;
               }
#line 2732 "grammar.c" /* yacc.c:1646  */
    break;

  case 26:
#line 309 "grammar.y" /* yacc.c:1646  */
    {
                    int ntype = node_get_type((yyvsp[-3].node));
                    if (ATOM != ntype && DOT != ntype && SELF != ntype) {
                      nusmv_yyerror_lined("incorrect DOT expression", (yyvsp[-2].lineno));
                      YYABORT;
                    }
                (yyval.node) = new_lined_node(NODEMGR, NFUNCTION, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));
               }
#line 2745 "grammar.c" /* yacc.c:1646  */
    break;

  case 28:
#line 329 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, UMINUS, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2751 "grammar.c" /* yacc.c:1646  */
    break;

  case 30:
#line 331 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, SELF,Nil,Nil);}
#line 2757 "grammar.c" /* yacc.c:1646  */
    break;

  case 31:
#line 333 "grammar.y" /* yacc.c:1646  */
    {
                    int ntype = node_get_type((yyvsp[-2].node));
                    if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                      nusmv_yyerror_lined("incorrect DOT expression", (yyvsp[-1].lineno));
                      YYABORT;
                    }
                    (yyval.node) = new_lined_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)) ;
                  }
#line 2770 "grammar.c" /* yacc.c:1646  */
    break;

  case 32:
#line 342 "grammar.y" /* yacc.c:1646  */
    {
                   int ntype = node_get_type((yyvsp[-2].node));
                   if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                     nusmv_yyerror_lined("incorrect DOT expression", (yyvsp[-1].lineno));
                     YYABORT;
                   }
                   (yyval.node) = new_lined_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)) ;
                  }
#line 2783 "grammar.c" /* yacc.c:1646  */
    break;

  case 33:
#line 351 "grammar.y" /* yacc.c:1646  */
    {
                   /* array may have any expression on the left.
                      The type check will detect any problems */
                   (yyval.node) = new_lined_node(NODEMGR, ARRAY, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));
                  }
#line 2793 "grammar.c" /* yacc.c:1646  */
    break;

  case 34:
#line 357 "grammar.y" /* yacc.c:1646  */
    {
                    (yyval.node) = new_lined_node(NODEMGR, BIT_SELECTION, (yyvsp[-5].node),
                                        new_lined_node(NODEMGR, COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno)), (yyvsp[-4].lineno));
                  }
#line 2802 "grammar.c" /* yacc.c:1646  */
    break;

  case 35:
#line 361 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2808 "grammar.c" /* yacc.c:1646  */
    break;

  case 36:
#line 362 "grammar.y" /* yacc.c:1646  */
    { /* abs(a) := (a >= 0) ? a : - a */
                                                      node_ptr zero = new_lined_node(NODEMGR, NUMBER, NODE_FROM_INT((int)(0)), Nil, (yyvsp[-3].lineno));
                                                      node_ptr cond = new_lined_node(NODEMGR, GE, (yyvsp[-1].node), zero, (yyvsp[-3].lineno));
                                                      node_ptr minus_a = new_lined_node(NODEMGR, UMINUS, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno));
                                                      (yyval.node) = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, cond, (yyvsp[-1].node), (yyvsp[-3].lineno)), minus_a, (yyvsp[-3].lineno)); ; }
#line 2818 "grammar.c" /* yacc.c:1646  */
    break;

  case 37:
#line 367 "grammar.y" /* yacc.c:1646  */
    { /* MIN(a,b) := a < b ? a : b */
                                                                           node_ptr cond = new_lined_node(NODEMGR, LT, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno));
                                                                           (yyval.node) = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, cond, (yyvsp[-3].node), (yyvsp[-5].lineno)), (yyvsp[-1].node), (yyvsp[-5].lineno)); ; }
#line 2826 "grammar.c" /* yacc.c:1646  */
    break;

  case 38:
#line 370 "grammar.y" /* yacc.c:1646  */
    { /* MAX(a,b) := a < b ? b : a */
                                                                           node_ptr cond = new_lined_node(NODEMGR, LT, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno));
                                                                           (yyval.node) = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, cond, (yyvsp[-1].node), (yyvsp[-5].lineno)), (yyvsp[-3].node), (yyvsp[-5].lineno)); ;}
#line 2834 "grammar.c" /* yacc.c:1646  */
    break;

  case 39:
#line 373 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, NOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2840 "grammar.c" /* yacc.c:1646  */
    break;

  case 40:
#line 374 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CAST_BOOL, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2846 "grammar.c" /* yacc.c:1646  */
    break;

  case 41:
#line 375 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CAST_WORD1, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2852 "grammar.c" /* yacc.c:1646  */
    break;

  case 42:
#line 376 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, NEXT, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2858 "grammar.c" /* yacc.c:1646  */
    break;

  case 43:
#line 377 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CAST_SIGNED, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2864 "grammar.c" /* yacc.c:1646  */
    break;

  case 44:
#line 378 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CAST_UNSIGNED, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2870 "grammar.c" /* yacc.c:1646  */
    break;

  case 45:
#line 379 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EXTEND, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2876 "grammar.c" /* yacc.c:1646  */
    break;

  case 46:
#line 380 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, WRESIZE, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2882 "grammar.c" /* yacc.c:1646  */
    break;

  case 47:
#line 381 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2888 "grammar.c" /* yacc.c:1646  */
    break;

  case 48:
#line 385 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, WAREAD, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2894 "grammar.c" /* yacc.c:1646  */
    break;

  case 49:
#line 388 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, WAWRITE, (yyvsp[-5].node), new_node(NODEMGR, WAWRITE, (yyvsp[-3].node), (yyvsp[-1].node)), (yyvsp[-6].lineno)); }
#line 2900 "grammar.c" /* yacc.c:1646  */
    break;

  case 50:
#line 390 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CONST_ARRAY, new_node(NODEMGR, TYPEOF, (yyvsp[-4].node), Nil), (yyvsp[-1].node), (yyvsp[-8].lineno)); }
#line 2906 "grammar.c" /* yacc.c:1646  */
    break;

  case 51:
#line 392 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, COUNT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 2912 "grammar.c" /* yacc.c:1646  */
    break;

  case 52:
#line 396 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil); }
#line 2918 "grammar.c" /* yacc.c:1646  */
    break;

  case 53:
#line 397 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons(NODEMGR, (yyvsp[-2].node), (yyvsp[0].node)); }
#line 2924 "grammar.c" /* yacc.c:1646  */
    break;

  case 54:
#line 402 "grammar.y" /* yacc.c:1646  */
    {
               const ErrorMgr_ptr errmgr =
                 ERROR_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_ERROR_MANAGER));
               node_ptr fail =
                 ErrorMgr_failure_make(errmgr,
                                       "case conditions are not exhaustive",
                                       FAILURE_CASE_NOT_EXHAUSTIVE,
                                       nusmv_yylineno);
               (yyval.node) = new_node(NODEMGR, CASE, (yyvsp[0].node), fail);
             }
#line 2939 "grammar.c" /* yacc.c:1646  */
    break;

  case 55:
#line 412 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_node(NODEMGR, CASE, (yyvsp[-1].node), (yyvsp[0].node)); }
#line 2945 "grammar.c" /* yacc.c:1646  */
    break;

  case 56:
#line 417 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = build_case_colon_node((yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 2951 "grammar.c" /* yacc.c:1646  */
    break;

  case 58:
#line 423 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CONCATENATION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2957 "grammar.c" /* yacc.c:1646  */
    break;

  case 60:
#line 429 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, CONCATENATION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2963 "grammar.c" /* yacc.c:1646  */
    break;

  case 62:
#line 435 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, TIMES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2969 "grammar.c" /* yacc.c:1646  */
    break;

  case 63:
#line 436 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, DIVIDE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2975 "grammar.c" /* yacc.c:1646  */
    break;

  case 64:
#line 437 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, MOD, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2981 "grammar.c" /* yacc.c:1646  */
    break;

  case 66:
#line 442 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, TIMES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2987 "grammar.c" /* yacc.c:1646  */
    break;

  case 67:
#line 443 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, DIVIDE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2993 "grammar.c" /* yacc.c:1646  */
    break;

  case 68:
#line 444 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, MOD, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2999 "grammar.c" /* yacc.c:1646  */
    break;

  case 70:
#line 450 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, PLUS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3005 "grammar.c" /* yacc.c:1646  */
    break;

  case 71:
#line 451 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, MINUS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3011 "grammar.c" /* yacc.c:1646  */
    break;

  case 73:
#line 457 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, PLUS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3017 "grammar.c" /* yacc.c:1646  */
    break;

  case 74:
#line 458 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, MINUS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3023 "grammar.c" /* yacc.c:1646  */
    break;

  case 76:
#line 462 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, LSHIFT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3029 "grammar.c" /* yacc.c:1646  */
    break;

  case 77:
#line 463 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, RSHIFT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3035 "grammar.c" /* yacc.c:1646  */
    break;

  case 79:
#line 467 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, LSHIFT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3041 "grammar.c" /* yacc.c:1646  */
    break;

  case 80:
#line 468 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, RSHIFT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3047 "grammar.c" /* yacc.c:1646  */
    break;

  case 83:
#line 476 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3053 "grammar.c" /* yacc.c:1646  */
    break;

  case 85:
#line 480 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, UNION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3059 "grammar.c" /* yacc.c:1646  */
    break;

  case 87:
#line 485 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, UNION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3065 "grammar.c" /* yacc.c:1646  */
    break;

  case 89:
#line 489 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, SETIN, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3071 "grammar.c" /* yacc.c:1646  */
    break;

  case 91:
#line 494 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EQUAL, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3077 "grammar.c" /* yacc.c:1646  */
    break;

  case 92:
#line 495 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, NOTEQUAL, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3083 "grammar.c" /* yacc.c:1646  */
    break;

  case 93:
#line 496 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, LT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3089 "grammar.c" /* yacc.c:1646  */
    break;

  case 94:
#line 497 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, GT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3095 "grammar.c" /* yacc.c:1646  */
    break;

  case 95:
#line 498 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, LE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3101 "grammar.c" /* yacc.c:1646  */
    break;

  case 96:
#line 499 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, GE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3107 "grammar.c" /* yacc.c:1646  */
    break;

  case 99:
#line 507 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EX, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3113 "grammar.c" /* yacc.c:1646  */
    break;

  case 100:
#line 508 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, AX, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3119 "grammar.c" /* yacc.c:1646  */
    break;

  case 101:
#line 509 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EF, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3125 "grammar.c" /* yacc.c:1646  */
    break;

  case 102:
#line 510 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, AF, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3131 "grammar.c" /* yacc.c:1646  */
    break;

  case 103:
#line 511 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EG, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3137 "grammar.c" /* yacc.c:1646  */
    break;

  case 104:
#line 512 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, AG, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3143 "grammar.c" /* yacc.c:1646  */
    break;

  case 105:
#line 514 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, AU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 3149 "grammar.c" /* yacc.c:1646  */
    break;

  case 106:
#line 516 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 3155 "grammar.c" /* yacc.c:1646  */
    break;

  case 107:
#line 518 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, ABU, new_lined_node(NODEMGR, AU, (yyvsp[-4].node), (yyvsp[-1].node), (yyvsp[-6].lineno)), (yyvsp[-2].node), (yyvsp[-6].lineno)); }
#line 3161 "grammar.c" /* yacc.c:1646  */
    break;

  case 108:
#line 520 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EBU, new_lined_node(NODEMGR, EU, (yyvsp[-4].node), (yyvsp[-1].node), (yyvsp[-6].lineno)), (yyvsp[-2].node), (yyvsp[-6].lineno)); }
#line 3167 "grammar.c" /* yacc.c:1646  */
    break;

  case 109:
#line 521 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EBF, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 3173 "grammar.c" /* yacc.c:1646  */
    break;

  case 110:
#line 522 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, ABF, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 3179 "grammar.c" /* yacc.c:1646  */
    break;

  case 111:
#line 523 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EBG, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 3185 "grammar.c" /* yacc.c:1646  */
    break;

  case 112:
#line 524 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, ABG, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 3191 "grammar.c" /* yacc.c:1646  */
    break;

  case 113:
#line 527 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, NOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3197 "grammar.c" /* yacc.c:1646  */
    break;

  case 115:
#line 534 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, AND, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3203 "grammar.c" /* yacc.c:1646  */
    break;

  case 117:
#line 538 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, OR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3209 "grammar.c" /* yacc.c:1646  */
    break;

  case 118:
#line 539 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, XOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3215 "grammar.c" /* yacc.c:1646  */
    break;

  case 119:
#line 540 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, XNOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3221 "grammar.c" /* yacc.c:1646  */
    break;

  case 121:
#line 544 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, IFF, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3227 "grammar.c" /* yacc.c:1646  */
    break;

  case 123:
#line 549 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, IMPLIES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3233 "grammar.c" /* yacc.c:1646  */
    break;

  case 127:
#line 562 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_NEXT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3239 "grammar.c" /* yacc.c:1646  */
    break;

  case 128:
#line 563 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_PREC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3245 "grammar.c" /* yacc.c:1646  */
    break;

  case 129:
#line 564 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_NOTPRECNOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3251 "grammar.c" /* yacc.c:1646  */
    break;

  case 130:
#line 565 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_GLOBAL, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3257 "grammar.c" /* yacc.c:1646  */
    break;

  case 131:
#line 567 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_GLOBAL, (yyvsp[0].node), new_lined_node(NODEMGR, TWODOTS, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-6].lineno)), (yyvsp[-6].lineno));}
#line 3263 "grammar.c" /* yacc.c:1646  */
    break;

  case 132:
#line 568 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_HISTORICAL, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3269 "grammar.c" /* yacc.c:1646  */
    break;

  case 133:
#line 570 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_HISTORICAL, (yyvsp[0].node), new_lined_node(NODEMGR, TWODOTS, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-6].lineno)), (yyvsp[-6].lineno));}
#line 3275 "grammar.c" /* yacc.c:1646  */
    break;

  case 134:
#line 571 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_FUTURE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3281 "grammar.c" /* yacc.c:1646  */
    break;

  case 135:
#line 573 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_FUTURE, (yyvsp[0].node), new_lined_node(NODEMGR, TWODOTS, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-6].lineno)), (yyvsp[-6].lineno));}
#line 3287 "grammar.c" /* yacc.c:1646  */
    break;

  case 136:
#line 574 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_ONCE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3293 "grammar.c" /* yacc.c:1646  */
    break;

  case 137:
#line 576 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, OP_ONCE, (yyvsp[0].node), new_lined_node(NODEMGR, TWODOTS, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-6].lineno)), (yyvsp[-6].lineno));}
#line 3299 "grammar.c" /* yacc.c:1646  */
    break;

  case 138:
#line 578 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, NOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3305 "grammar.c" /* yacc.c:1646  */
    break;

  case 140:
#line 587 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, UNTIL, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3311 "grammar.c" /* yacc.c:1646  */
    break;

  case 141:
#line 589 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SINCE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3317 "grammar.c" /* yacc.c:1646  */
    break;

  case 142:
#line 591 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, NOT,
                           new_lined_node(NODEMGR, UNTIL,
                             new_lined_node(NODEMGR, NOT, (yyvsp[-2].node), Nil, node_get_lineno((yyvsp[-2].node))),
                             new_lined_node(NODEMGR, NOT, (yyvsp[0].node), Nil, node_get_lineno((yyvsp[0].node))),
                             (yyvsp[-1].lineno)), Nil, (yyvsp[-1].lineno));
                  }
#line 3328 "grammar.c" /* yacc.c:1646  */
    break;

  case 143:
#line 598 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, NOT,
                          new_lined_node(NODEMGR, SINCE,
                              new_lined_node(NODEMGR, NOT, (yyvsp[-2].node), Nil, node_get_lineno((yyvsp[-2].node))),
                              new_lined_node(NODEMGR, NOT, (yyvsp[0].node), Nil, node_get_lineno((yyvsp[0].node))),
                              (yyvsp[-1].lineno)), Nil, (yyvsp[-1].lineno));
                  }
#line 3339 "grammar.c" /* yacc.c:1646  */
    break;

  case 145:
#line 608 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, AND, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3345 "grammar.c" /* yacc.c:1646  */
    break;

  case 147:
#line 613 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, OR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3351 "grammar.c" /* yacc.c:1646  */
    break;

  case 148:
#line 614 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, XOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3357 "grammar.c" /* yacc.c:1646  */
    break;

  case 149:
#line 615 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, XNOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3363 "grammar.c" /* yacc.c:1646  */
    break;

  case 151:
#line 620 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-3].lineno)), (yyvsp[0].node), (yyvsp[-3].lineno)); }
#line 3369 "grammar.c" /* yacc.c:1646  */
    break;

  case 153:
#line 625 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, IFF, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3375 "grammar.c" /* yacc.c:1646  */
    break;

  case 155:
#line 630 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, IMPLIES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3381 "grammar.c" /* yacc.c:1646  */
    break;

  case 157:
#line 641 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_SIMPLE)) YYABORT;}
#line 3387 "grammar.c" /* yacc.c:1646  */
    break;

  case 158:
#line 644 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_NEXT)) YYABORT;}
#line 3393 "grammar.c" /* yacc.c:1646  */
    break;

  case 159:
#line 647 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_CTL)) YYABORT;}
#line 3399 "grammar.c" /* yacc.c:1646  */
    break;

  case 160:
#line 650 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_LTL)) YYABORT;}
#line 3405 "grammar.c" /* yacc.c:1646  */
    break;

  case 161:
#line 655 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, MINU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 3411 "grammar.c" /* yacc.c:1646  */
    break;

  case 162:
#line 657 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, MAXU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 3417 "grammar.c" /* yacc.c:1646  */
    break;

  case 163:
#line 665 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, BOOLEAN, Nil, Nil);}
#line 3423 "grammar.c" /* yacc.c:1646  */
    break;

  case 164:
#line 667 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, UNSIGNED_WORD, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno));}
#line 3429 "grammar.c" /* yacc.c:1646  */
    break;

  case 165:
#line 669 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, UNSIGNED_WORD, (yyvsp[-1].node), Nil, (yyvsp[-4].lineno));}
#line 3435 "grammar.c" /* yacc.c:1646  */
    break;

  case 166:
#line 671 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SIGNED_WORD, (yyvsp[-1].node), Nil, (yyvsp[-4].lineno));}
#line 3441 "grammar.c" /* yacc.c:1646  */
    break;

  case 168:
#line 674 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SCALAR, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3447 "grammar.c" /* yacc.c:1646  */
    break;

  case 169:
#line 676 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, WORDARRAY_TYPE, (yyvsp[-3].node), (yyvsp[0].node), (yyvsp[-6].lineno));}
#line 3453 "grammar.c" /* yacc.c:1646  */
    break;

  case 170:
#line 678 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, ARRAY_TYPE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-3].lineno));}
#line 3459 "grammar.c" /* yacc.c:1646  */
    break;

  case 171:
#line 680 "grammar.y" /* yacc.c:1646  */
    {nusmv_yyerror("unbounded arrays are not supported.");
                   YYABORT;
                  }
#line 3467 "grammar.c" /* yacc.c:1646  */
    break;

  case 174:
#line 688 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, PROCESS, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3473 "grammar.c" /* yacc.c:1646  */
    break;

  case 175:
#line 691 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, find_atom(NODEMGR, (yyvsp[0].node)), Nil); free_node(NODEMGR, (yyvsp[0].node));}
#line 3479 "grammar.c" /* yacc.c:1646  */
    break;

  case 176:
#line 692 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, find_atom(NODEMGR, (yyvsp[0].node)), (yyvsp[-2].node)); free_node(NODEMGR, (yyvsp[0].node));}
#line 3485 "grammar.c" /* yacc.c:1646  */
    break;

  case 182:
#line 702 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3491 "grammar.c" /* yacc.c:1646  */
    break;

  case 183:
#line 705 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, MODTYPE, (yyvsp[0].node), Nil);}
#line 3497 "grammar.c" /* yacc.c:1646  */
    break;

  case 184:
#line 706 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, MODTYPE, (yyvsp[-2].node), Nil);}
#line 3503 "grammar.c" /* yacc.c:1646  */
    break;

  case 185:
#line 708 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, MODTYPE, (yyvsp[-3].node), (yyvsp[-1].node), node_get_lineno((yyvsp[-3].node)));}
#line 3509 "grammar.c" /* yacc.c:1646  */
    break;

  case 186:
#line 710 "grammar.y" /* yacc.c:1646  */
    {
                    /* $$ = new_lined_node(NODEMGR, ARRAY, $2, $4, $1); */
                    /* array of modules is not supported any more.
                       NOTE: In future if there are some syntact conflicts
                       this case can be removed */
                    nusmv_yyerror_lined("array of modules is no supported", (yyvsp[-3].lineno));
                    YYABORT;
                  }
#line 3522 "grammar.c" /* yacc.c:1646  */
    break;

  case 187:
#line 721 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node),Nil);}
#line 3528 "grammar.c" /* yacc.c:1646  */
    break;

  case 188:
#line 722 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-2].node));}
#line 3534 "grammar.c" /* yacc.c:1646  */
    break;

  case 189:
#line 734 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 3540 "grammar.c" /* yacc.c:1646  */
    break;

  case 190:
#line 735 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3546 "grammar.c" /* yacc.c:1646  */
    break;

  case 191:
#line 739 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, MODULE, (yyvsp[-1].node), (yyvsp[0].node), (yyvsp[-2].lineno));}
#line 3552 "grammar.c" /* yacc.c:1646  */
    break;

  case 192:
#line 741 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, MODTYPE, (yyvsp[0].node), Nil);}
#line 3558 "grammar.c" /* yacc.c:1646  */
    break;

  case 193:
#line 742 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, MODTYPE, (yyvsp[-2].node), Nil);}
#line 3564 "grammar.c" /* yacc.c:1646  */
    break;

  case 194:
#line 744 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, MODTYPE, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 3570 "grammar.c" /* yacc.c:1646  */
    break;

  case 195:
#line 746 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, find_atom(NODEMGR, (yyvsp[0].node)), Nil); free_node(NODEMGR, (yyvsp[0].node));}
#line 3576 "grammar.c" /* yacc.c:1646  */
    break;

  case 196:
#line 747 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, find_atom(NODEMGR, (yyvsp[0].node)), (yyvsp[-2].node)); free_node(NODEMGR, (yyvsp[0].node));}
#line 3582 "grammar.c" /* yacc.c:1646  */
    break;

  case 197:
#line 752 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3588 "grammar.c" /* yacc.c:1646  */
    break;

  case 198:
#line 753 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3594 "grammar.c" /* yacc.c:1646  */
    break;

  case 199:
#line 754 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3600 "grammar.c" /* yacc.c:1646  */
    break;

  case 220:
#line 785 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, VAR, Nil, Nil, (yyvsp[0].lineno));}
#line 3606 "grammar.c" /* yacc.c:1646  */
    break;

  case 221:
#line 786 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, VAR, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3612 "grammar.c" /* yacc.c:1646  */
    break;

  case 222:
#line 789 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, FROZENVAR, Nil, Nil, (yyvsp[0].lineno));}
#line 3618 "grammar.c" /* yacc.c:1646  */
    break;

  case 223:
#line 790 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, FROZENVAR, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3624 "grammar.c" /* yacc.c:1646  */
    break;

  case 224:
#line 793 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, IVAR, Nil, Nil, (yyvsp[0].lineno));}
#line 3630 "grammar.c" /* yacc.c:1646  */
    break;

  case 225:
#line 794 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, IVAR, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3636 "grammar.c" /* yacc.c:1646  */
    break;

  case 226:
#line 796 "grammar.y" /* yacc.c:1646  */
    {
                 nusmv_yyerror("functions definitions are not supported.");
                 YYABORT;
               }
#line 3645 "grammar.c" /* yacc.c:1646  */
    break;

  case 227:
#line 800 "grammar.y" /* yacc.c:1646  */
    {
                 nusmv_yyerror("functions definitions are not supported.");
                 YYABORT;
               }
#line 3654 "grammar.c" /* yacc.c:1646  */
    break;

  case 228:
#line 806 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 3660 "grammar.c" /* yacc.c:1646  */
    break;

  case 229:
#line 807 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3666 "grammar.c" /* yacc.c:1646  */
    break;

  case 230:
#line 808 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3672 "grammar.c" /* yacc.c:1646  */
    break;

  case 231:
#line 810 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 3678 "grammar.c" /* yacc.c:1646  */
    break;

  case 232:
#line 811 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3684 "grammar.c" /* yacc.c:1646  */
    break;

  case 233:
#line 812 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3690 "grammar.c" /* yacc.c:1646  */
    break;

  case 234:
#line 814 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 3696 "grammar.c" /* yacc.c:1646  */
    break;

  case 235:
#line 815 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3702 "grammar.c" /* yacc.c:1646  */
    break;

  case 236:
#line 816 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3708 "grammar.c" /* yacc.c:1646  */
    break;

  case 237:
#line 818 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 3714 "grammar.c" /* yacc.c:1646  */
    break;

  case 238:
#line 819 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3720 "grammar.c" /* yacc.c:1646  */
    break;

  case 239:
#line 820 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3726 "grammar.c" /* yacc.c:1646  */
    break;

  case 240:
#line 823 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3732 "grammar.c" /* yacc.c:1646  */
    break;

  case 241:
#line 825 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3738 "grammar.c" /* yacc.c:1646  */
    break;

  case 242:
#line 827 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3744 "grammar.c" /* yacc.c:1646  */
    break;

  case 243:
#line 829 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3750 "grammar.c" /* yacc.c:1646  */
    break;

  case 244:
#line 832 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, NFUNCTION_TYPE, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3756 "grammar.c" /* yacc.c:1646  */
    break;

  case 245:
#line 836 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil); }
#line 3762 "grammar.c" /* yacc.c:1646  */
    break;

  case 246:
#line 837 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-2].node)); }
#line 3768 "grammar.c" /* yacc.c:1646  */
    break;

  case 247:
#line 842 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, DEFINE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3774 "grammar.c" /* yacc.c:1646  */
    break;

  case 248:
#line 844 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3780 "grammar.c" /* yacc.c:1646  */
    break;

  case 249:
#line 845 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-1].node));}
#line 3786 "grammar.c" /* yacc.c:1646  */
    break;

  case 250:
#line 846 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3792 "grammar.c" /* yacc.c:1646  */
    break;

  case 251:
#line 850 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3798 "grammar.c" /* yacc.c:1646  */
    break;

  case 252:
#line 852 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));
                                 /* Note that array-define is declared
                                    as normal define.
                                    Then compile_instantiate in compileFlatten.c
                                    distinguish them by detecting
                                    ARRAY_DEF on right hand side.
                                   */
                                 }
#line 3811 "grammar.c" /* yacc.c:1646  */
    break;

  case 253:
#line 864 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, DEFINE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3817 "grammar.c" /* yacc.c:1646  */
    break;

  case 254:
#line 868 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3823 "grammar.c" /* yacc.c:1646  */
    break;

  case 255:
#line 869 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, new_lined_node(NODEMGR, EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno)), (yyvsp[-4].node));}
#line 3829 "grammar.c" /* yacc.c:1646  */
    break;

  case 256:
#line 870 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3835 "grammar.c" /* yacc.c:1646  */
    break;

  case 257:
#line 874 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) =  new_lined_node(NODEMGR, ARRAY_DEF, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3841 "grammar.c" /* yacc.c:1646  */
    break;

  case 258:
#line 875 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) =  new_lined_node(NODEMGR, ARRAY_DEF, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3847 "grammar.c" /* yacc.c:1646  */
    break;

  case 259:
#line 879 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 3853 "grammar.c" /* yacc.c:1646  */
    break;

  case 260:
#line 880 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3859 "grammar.c" /* yacc.c:1646  */
    break;

  case 261:
#line 884 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3865 "grammar.c" /* yacc.c:1646  */
    break;

  case 262:
#line 885 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node),Nil);}
#line 3871 "grammar.c" /* yacc.c:1646  */
    break;

  case 263:
#line 889 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, ASSIGN, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3877 "grammar.c" /* yacc.c:1646  */
    break;

  case 264:
#line 891 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3883 "grammar.c" /* yacc.c:1646  */
    break;

  case 265:
#line 892 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, AND, (yyvsp[-1].node), (yyvsp[0].node));}
#line 3889 "grammar.c" /* yacc.c:1646  */
    break;

  case 266:
#line 893 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3895 "grammar.c" /* yacc.c:1646  */
    break;

  case 267:
#line 896 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3901 "grammar.c" /* yacc.c:1646  */
    break;

  case 268:
#line 898 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EQDEF,
                                        new_lined_node(NODEMGR, SMALLINIT, (yyvsp[-4].node), Nil, (yyvsp[-6].lineno)),
                                        (yyvsp[-1].node), (yyvsp[-2].lineno));
                  }
#line 3910 "grammar.c" /* yacc.c:1646  */
    break;

  case 269:
#line 903 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NODEMGR, EQDEF,
                                        new_lined_node(NODEMGR, NEXT, (yyvsp[-4].node), Nil, (yyvsp[-6].lineno)),
                                        (yyvsp[-1].node), (yyvsp[-2].lineno));
                  }
#line 3919 "grammar.c" /* yacc.c:1646  */
    break;

  case 270:
#line 910 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, INIT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3925 "grammar.c" /* yacc.c:1646  */
    break;

  case 271:
#line 912 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, INVAR, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3931 "grammar.c" /* yacc.c:1646  */
    break;

  case 272:
#line 914 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, TRANS, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3937 "grammar.c" /* yacc.c:1646  */
    break;

  case 273:
#line 918 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, JUSTICE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3943 "grammar.c" /* yacc.c:1646  */
    break;

  case 274:
#line 921 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, JUSTICE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3949 "grammar.c" /* yacc.c:1646  */
    break;

  case 275:
#line 926 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COMPASSION, cons(NODEMGR, (yyvsp[-4].node),(yyvsp[-2].node)), Nil, (yyvsp[-6].lineno));}
#line 3955 "grammar.c" /* yacc.c:1646  */
    break;

  case 276:
#line 930 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3961 "grammar.c" /* yacc.c:1646  */
    break;

  case 277:
#line 931 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 3967 "grammar.c" /* yacc.c:1646  */
    break;

  case 278:
#line 933 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, INVARSPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3973 "grammar.c" /* yacc.c:1646  */
    break;

  case 279:
#line 934 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, INVARSPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 3979 "grammar.c" /* yacc.c:1646  */
    break;

  case 280:
#line 937 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3985 "grammar.c" /* yacc.c:1646  */
    break;

  case 281:
#line 938 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 3991 "grammar.c" /* yacc.c:1646  */
    break;

  case 282:
#line 940 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3997 "grammar.c" /* yacc.c:1646  */
    break;

  case 283:
#line 941 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 4003 "grammar.c" /* yacc.c:1646  */
    break;

  case 284:
#line 942 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 4009 "grammar.c" /* yacc.c:1646  */
    break;

  case 285:
#line 943 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 4015 "grammar.c" /* yacc.c:1646  */
    break;

  case 286:
#line 946 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 4021 "grammar.c" /* yacc.c:1646  */
    break;

  case 287:
#line 947 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 4027 "grammar.c" /* yacc.c:1646  */
    break;

  case 288:
#line 950 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, LTLSPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 4033 "grammar.c" /* yacc.c:1646  */
    break;

  case 289:
#line 951 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, LTLSPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 4039 "grammar.c" /* yacc.c:1646  */
    break;

  case 290:
#line 954 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 4045 "grammar.c" /* yacc.c:1646  */
    break;

  case 291:
#line 955 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 4051 "grammar.c" /* yacc.c:1646  */
    break;

  case 292:
#line 957 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COMPUTE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 4057 "grammar.c" /* yacc.c:1646  */
    break;

  case 293:
#line 958 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COMPUTE, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 4063 "grammar.c" /* yacc.c:1646  */
    break;

  case 294:
#line 963 "grammar.y" /* yacc.c:1646  */
    {
  if (nusmv_parse_psl() != 0) {
    YYABORT;
  }
  (yyval.node) = new_lined_node(NODEMGR, PSLSPEC, psl_parsed_tree, psl_property_name, (yyvsp[0].lineno));
  psl_property_name = Nil;
}
#line 4075 "grammar.c" /* yacc.c:1646  */
    break;

  case 295:
#line 973 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, CONSTANTS, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4081 "grammar.c" /* yacc.c:1646  */
    break;

  case 296:
#line 977 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 4087 "grammar.c" /* yacc.c:1646  */
    break;

  case 297:
#line 978 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons(NODEMGR, (yyvsp[0].node), Nil);}
#line 4093 "grammar.c" /* yacc.c:1646  */
    break;

  case 298:
#line 979 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR, (yyvsp[0].node), (yyvsp[-2].node));}
#line 4099 "grammar.c" /* yacc.c:1646  */
    break;

  case 299:
#line 986 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, ISA, (yyvsp[0].node), Nil);}
#line 4105 "grammar.c" /* yacc.c:1646  */
    break;

  case 301:
#line 990 "grammar.y" /* yacc.c:1646  */
    {}
#line 4111 "grammar.c" /* yacc.c:1646  */
    break;

  case 303:
#line 999 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 4117 "grammar.c" /* yacc.c:1646  */
    break;

  case 304:
#line 1000 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 4123 "grammar.c" /* yacc.c:1646  */
    break;

  case 305:
#line 1001 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, ARRAY, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 4129 "grammar.c" /* yacc.c:1646  */
    break;

  case 306:
#line 1003 "grammar.y" /* yacc.c:1646  */
    { node_ptr tmp = new_lined_node(NODEMGR, NUMBER,
                                                      PTR_FROM_INT(node_ptr, -node_get_int((yyvsp[-1].node))),
                                                      Nil,
                                                      (yyvsp[-2].lineno));
                        (yyval.node) = new_node(NODEMGR, ARRAY, (yyvsp[-4].node), tmp);
                      }
#line 4140 "grammar.c" /* yacc.c:1646  */
    break;

  case 308:
#line 1012 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, SELF,Nil,Nil);}
#line 4146 "grammar.c" /* yacc.c:1646  */
    break;

  case 309:
#line 1013 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 4152 "grammar.c" /* yacc.c:1646  */
    break;

  case 310:
#line 1014 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 4158 "grammar.c" /* yacc.c:1646  */
    break;

  case 311:
#line 1015 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, ARRAY, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 4164 "grammar.c" /* yacc.c:1646  */
    break;

  case 312:
#line 1022 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = (yyvsp[0].node);}
#line 4170 "grammar.c" /* yacc.c:1646  */
    break;

  case 313:
#line 1023 "grammar.y" /* yacc.c:1646  */
    {return(1);}
#line 4176 "grammar.c" /* yacc.c:1646  */
    break;

  case 314:
#line 1024 "grammar.y" /* yacc.c:1646  */
    {return(1);}
#line 4182 "grammar.c" /* yacc.c:1646  */
    break;

  case 315:
#line 1028 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, INIT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4188 "grammar.c" /* yacc.c:1646  */
    break;

  case 316:
#line 1030 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, JUSTICE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4194 "grammar.c" /* yacc.c:1646  */
    break;

  case 317:
#line 1032 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, TRANS, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4200 "grammar.c" /* yacc.c:1646  */
    break;

  case 318:
#line 1034 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, CONSTRAINT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4206 "grammar.c" /* yacc.c:1646  */
    break;

  case 319:
#line 1036 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, ITYPE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4212 "grammar.c" /* yacc.c:1646  */
    break;

  case 320:
#line 1039 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, SIMPWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 4218 "grammar.c" /* yacc.c:1646  */
    break;

  case 321:
#line 1040 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, NEXTWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 4224 "grammar.c" /* yacc.c:1646  */
    break;

  case 322:
#line 1041 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, CTLWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 4230 "grammar.c" /* yacc.c:1646  */
    break;

  case 323:
#line 1042 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, LTLWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 4236 "grammar.c" /* yacc.c:1646  */
    break;

  case 324:
#line 1043 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COMPWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 4242 "grammar.c" /* yacc.c:1646  */
    break;

  case 325:
#line 1044 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NODEMGR, COMPID, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 4248 "grammar.c" /* yacc.c:1646  */
    break;

  case 326:
#line 1048 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = find_atom(NODEMGR, (yyvsp[0].node)); free_node(NODEMGR, (yyvsp[0].node)); }
#line 4254 "grammar.c" /* yacc.c:1646  */
    break;

  case 327:
#line 1049 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = find_node(NODEMGR, DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 4260 "grammar.c" /* yacc.c:1646  */
    break;

  case 328:
#line 1050 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = find_node(NODEMGR, ARRAY, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 4266 "grammar.c" /* yacc.c:1646  */
    break;

  case 329:
#line 1053 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 4272 "grammar.c" /* yacc.c:1646  */
    break;

  case 330:
#line 1054 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(NODEMGR, CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 4278 "grammar.c" /* yacc.c:1646  */
    break;

  case 331:
#line 1060 "grammar.y" /* yacc.c:1646  */
    {
  if (PARSE_MODULES != parse_mode_flag) {
    yyerror("unexpected MODULE definition encountered during parsing");
    YYABORT;
  }
#if HAVE_GAME
  if (opt_game_game(OptsHandler_create())) {
    Game_Mode_Exit();
  }
  game_parser_spec_list = Nil;
  game_parser_player_1 = Nil;
  game_parser_player_2 = Nil;
#endif
}
#line 4297 "grammar.c" /* yacc.c:1646  */
    break;

  case 332:
#line 1075 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                  if (!opt_game_game(OptsHandler_create())) {
                    /*this is a usual SMV file*/
                    parsed_tree = (yyvsp[0].node);
                  }
                  else {
                    /* this is a game (realizability problem) .
                       Return a Game with spec list on the left and a
                       module list on the right. This module list
                       contains two special modules (with names
                       PLAYER_1 and PLAYER_2) created from player
                       declarations.
                    */
                    parsed_tree = new_node(NODEMGR,GAME,
                                           game_parser_spec_list,
                                           cons(NODEMGR,game_parser_player_1,
                                                cons(NODEMGR,game_parser_player_2,
                                                     (yyvsp[0].node))));
                  }
#else /* no GAME */
                  parsed_tree = (yyvsp[0].node);            
#endif
                }
#line 4326 "grammar.c" /* yacc.c:1646  */
    break;

  case 333:
#line 1099 "grammar.y" /* yacc.c:1646  */
    {
                  if (PARSE_COMMAND != parse_mode_flag) {
                    yyerror("unexpected command encountered during parsing");
                    YYABORT;
                  }
                }
#line 4337 "grammar.c" /* yacc.c:1646  */
    break;

  case 334:
#line 1105 "grammar.y" /* yacc.c:1646  */
    {parsed_tree = (yyvsp[0].node);}
#line 4343 "grammar.c" /* yacc.c:1646  */
    break;

  case 335:
#line 1106 "grammar.y" /* yacc.c:1646  */
    {
                  if (PARSE_LTL_EXPR != parse_mode_flag){
                    yyerror("unexpected expression encountered during parsing");
                    YYABORT;
                  }
                }
#line 4354 "grammar.c" /* yacc.c:1646  */
    break;

  case 336:
#line 1112 "grammar.y" /* yacc.c:1646  */
    {parsed_tree = (yyvsp[0].node);}
#line 4360 "grammar.c" /* yacc.c:1646  */
    break;

  case 337:
#line 1120 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR,(yyvsp[0].node),Nil);}
#line 4366 "grammar.c" /* yacc.c:1646  */
    break;

  case 338:
#line 1121 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR,(yyvsp[0].node), (yyvsp[-2].node));}
#line 4372 "grammar.c" /* yacc.c:1646  */
    break;

  case 339:
#line 1136 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR,(yyvsp[0].node), Nil);}
#line 4378 "grammar.c" /* yacc.c:1646  */
    break;

  case 340:
#line 1137 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 4384 "grammar.c" /* yacc.c:1646  */
    break;

  case 341:
#line 1138 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(NODEMGR,(yyvsp[0].node), (yyvsp[-1].node));}
#line 4390 "grammar.c" /* yacc.c:1646  */
    break;

  case 342:
#line 1139 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = (yyvsp[-1].node);}
#line 4396 "grammar.c" /* yacc.c:1646  */
    break;

  case 343:
#line 1150 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                       /* check that the game is not redeclared */
                       if (opt_game_game(OptsHandler_create())) {
                         nusmv_yyerror_lined("redefinition of a GAME", (yyvsp[-1].lineno));
                       }
                       else {
                         Game_Mode_Enter();
                       }
#else
                       nusmv_yyerror_lined("GAME declaration cannot be processes "
                                     "because GAME package is not set up\n"
                                     "Check --enable-addons=game option of "
                                     "the configure script\n", (yyvsp[-1].lineno));
                       YYABORT;
#endif
                       game_parser_spec_list = (yyvsp[0].node);
                       (yyval.node) = Nil;
                     }
#line 4420 "grammar.c" /* yacc.c:1646  */
    break;

  case 344:
#line 1172 "grammar.y" /* yacc.c:1646  */
    {(yyval.node)=Nil;}
#line 4426 "grammar.c" /* yacc.c:1646  */
    break;

  case 345:
#line 1174 "grammar.y" /* yacc.c:1646  */
    {if (Nil != (yyvsp[-1].node)) (yyval.node) = cons(NODEMGR,(yyvsp[-1].node),(yyvsp[0].node)); else (yyval.node) = (yyvsp[0].node);}
#line 4432 "grammar.c" /* yacc.c:1646  */
    break;

  case 346:
#line 1182 "grammar.y" /* yacc.c:1646  */
    {
                       /* a player definition is converted to a module
                          definitino with a special name. This is done
                          to simplify the further flattening
                       */
                       if (game_parser_player_1 != Nil) {
                         nusmv_yyerror_lined("redefinition of a PLAYER_1", (yyvsp[-1].lineno));
                         YYABORT;
                       }
                       game_parser_player_1 = new_lined_node(NODEMGR,MODULE,
                           new_node(NODEMGR,MODTYPE,
                             new_node(NODEMGR,ATOM,(node_ptr)UStringMgr_find_string(USTRING_MGR(NULL),"PLAYER_1"),
                                      Nil), Nil),  (yyvsp[0].node), (yyvsp[-1].lineno));
                       (yyval.node)=Nil;
                     }
#line 4452 "grammar.c" /* yacc.c:1646  */
    break;

  case 347:
#line 1198 "grammar.y" /* yacc.c:1646  */
    {
                       /* a player definition is converted to a module
                          definitino with a special name. This is done
                          to simplify the further flattening
                       */
                       if (game_parser_player_2 != Nil) {
                         nusmv_yyerror_lined("redefinition of a PLAYER_2", (yyvsp[-1].lineno));
                         YYABORT;
                       }
                       game_parser_player_2 = new_lined_node(NODEMGR,MODULE,
                           new_node(NODEMGR,MODTYPE,
                             new_node(NODEMGR,ATOM,(node_ptr)UStringMgr_find_string(USTRING_MGR(NULL),"PLAYER_2"),
                                      Nil), Nil), (yyvsp[0].node), (yyvsp[-1].lineno));
                       (yyval.node)=Nil;
                     }
#line 4472 "grammar.c" /* yacc.c:1646  */
    break;

  case 355:
#line 1230 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = Nil; }
#line 4478 "grammar.c" /* yacc.c:1646  */
    break;

  case 356:
#line 1231 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons(NODEMGR,(yyvsp[0].node), (yyvsp[-1].node)); }
#line 4484 "grammar.c" /* yacc.c:1646  */
    break;

  case 364:
#line 1248 "grammar.y" /* yacc.c:1646  */
    {(yyval.lineno)=1;}
#line 4490 "grammar.c" /* yacc.c:1646  */
    break;

  case 365:
#line 1249 "grammar.y" /* yacc.c:1646  */
    {(yyval.lineno)=2;}
#line 4496 "grammar.c" /* yacc.c:1646  */
    break;

  case 366:
#line 1252 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,REACHTARGET, NODE_FROM_INT((yyvsp[-2].lineno)), (yyvsp[-1].node), (yyvsp[-3].lineno));
#endif
                       }
#line 4506 "grammar.c" /* yacc.c:1646  */
    break;

  case 367:
#line 1259 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,AVOIDTARGET, NODE_FROM_INT((yyvsp[-2].lineno)), (yyvsp[-1].node), (yyvsp[-3].lineno));
#endif
                       }
#line 4516 "grammar.c" /* yacc.c:1646  */
    break;

  case 368:
#line 1266 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,REACHDEADLOCK, NODE_FROM_INT((yyvsp[-1].lineno)), Nil, (yyvsp[-2].lineno));
#endif
                       }
#line 4526 "grammar.c" /* yacc.c:1646  */
    break;

  case 369:
#line 1273 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,AVOIDDEADLOCK, NODE_FROM_INT((yyvsp[-1].lineno)), Nil, (yyvsp[-2].lineno));
#endif
}
#line 4536 "grammar.c" /* yacc.c:1646  */
    break;

  case 370:
#line 1281 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,BUCHIGAME, NODE_FROM_INT((yyvsp[-4].lineno)),
                                             new_lined_node(NODEMGR,GAME_EXP_LIST,
                                                            reverse((yyvsp[-2].node)), Nil, (yyvsp[-3].lineno)),
                                             (yyvsp[-5].lineno));
#endif
}
#line 4549 "grammar.c" /* yacc.c:1646  */
    break;

  case 371:
#line 1291 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,LTLGAME, NODE_FROM_INT((yyvsp[-2].lineno)), (yyvsp[-1].node), (yyvsp[-3].lineno));
#endif
                       }
#line 4559 "grammar.c" /* yacc.c:1646  */
    break;

  case 372:
#line 1300 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(NODEMGR,GENREACTIVITY, NODE_FROM_INT((yyvsp[-8].lineno)),
                                             new_lined_node(NODEMGR,GAME_TWO_EXP_LISTS,
                                                            reverse((yyvsp[-6].node)), reverse((yyvsp[-2].node)), (yyvsp[-4].lineno)),
                                             (yyvsp[-9].lineno));
#endif
                       }
#line 4572 "grammar.c" /* yacc.c:1646  */
    break;


#line 4576 "grammar.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 1310 "grammar.y" /* yacc.c:1906  */

  /* BEGINS: /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/parser/grammar.y.3.50 */
/***************************************************************  -*-C-*-  ***/

/* Additional source code */

/* outputs the current token with the provided string and then may terminate */
void nusmv_yyerror(char *s)
{
  /* In the input.l file we explicity tell flex that we want a pointer
     (see man flex -> %pointer). So we don't need to check if nusmv_yytext
     is declared as pointer or as array  */
  extern char* nusmv_yytext;
  extern int nusmv_yylineno;
  const OptsHandler_ptr opmgr = GET_OPTS;
  const ErrorMgr_ptr errmgr =
    ERROR_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_ERROR_MANAGER));
  const StreamMgr_ptr streams =
    STREAM_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STREAM_MANAGER));

  parser_add_syntax_error(__nusmv_parser_env__, get_input_file(opmgr), nusmv_yylineno, nusmv_yytext, s);
  if (!OptsHandler_get_bool_option_value(opmgr, OPT_PARSER_IS_LAX)) {
    ErrorMgr_start_parsing_err(errmgr);
    StreamMgr_print_error(streams,  "at token \"%s\": %s\n", nusmv_yytext, s);
    if (opt_batch(opmgr)) { ErrorMgr_finish_parsing_err(errmgr); }
  }
}

/* the same as yyerror, except at first it sets the line number and does
 not output the current token
*/
void nusmv_yyerror_lined(const char *s, int line)
{
  extern char* nusmv_yytext;
  extern int nusmv_yylineno;
  const OptsHandler_ptr opmgr = GET_OPTS;
  const ErrorMgr_ptr errmgr =
    ERROR_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_ERROR_MANAGER));
  const StreamMgr_ptr streams =
    STREAM_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STREAM_MANAGER));

  /*set the line number */
  nusmv_yylineno = line;

  parser_add_syntax_error(__nusmv_parser_env__, get_input_file(opmgr), line, nusmv_yytext, s);
  if (!OptsHandler_get_bool_option_value(opmgr, OPT_PARSER_IS_LAX)) {
    ErrorMgr_start_parsing_err(errmgr);
    StreamMgr_print_error(streams,  ": %s\n", s);
    if (opt_batch(opmgr)) { ErrorMgr_finish_parsing_err(errmgr); }
  }
}

int nusmv_yywrap()
{
  return(1);
}


/* Given a node (possibly a relative or absolute context)
   constructs a node that is contextualized absolutely
   (i.e. relatively to main module). This is used to construct
   context of properties that have to be instatiated in main
   module */
static node_ptr node2maincontext(node_ptr node)
{
  node_ptr ctx;

  if (node_get_type(node) == CONTEXT) {
    /* already a context */
    ctx = CompileFlatten_concat_contexts(__nusmv_parser_env__, Nil, car(node));
    return find_node(NODEMGR, CONTEXT, ctx, cdr(node));
  }

  /* an atom, array or dot */
  return find_node(NODEMGR, CONTEXT, Nil, node);
}

/* This functions build the COLON node for case expressions.  If
   backward compatibility is enabled, and the condition expression is
   found to be the constant "1", then a warning is printed and the
   condition is replaced with TRUE. */
static node_ptr build_case_colon_node(node_ptr l,
                                      node_ptr r,
                                      int linum)
{
  const OptsHandler_ptr opts = GET_OPTS;
  const StreamMgr_ptr streams =
    STREAM_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_STREAM_MANAGER));

  node_ptr res;

  static int user_warned = 0;

  if (opt_backward_comp(opts) &&
      (NUMBER == node_get_type(l)) && (1 == NODE_TO_INT(car(l)))) {

    /* Print this warning only once. */
    if (!user_warned) {
      StreamMgr_print_error(streams,
              "\nWARNING *** Option backward_compatibility (-old) is deprecate ***\n");
      StreamMgr_print_error(streams,
              "WARNING *** and will no longer be supported in future NuSMV versions. ***\n\n");
      user_warned = 1;
    }

    StreamMgr_print_error(streams,  "WARNING (");

    if (get_input_file(opts)) {
      StreamMgr_print_error(streams,  "file %s", get_input_file(opts));
    }
    else StreamMgr_print_error(streams,  "file stdin");

    StreamMgr_print_error(streams,
            ", line %d) : Deprecated use of \"1\" for case condition\n", linum);

    res = new_lined_node(NODEMGR, COLON, new_node(NODEMGR, TRUEEXP, Nil, Nil), r, linum);
  }
  else {
    res = new_lined_node(NODEMGR, COLON, l, r, linum);
  }

  return res;
}

/* this functions checks that the expression is formed syntactically correct.
   Takes the expression to be checked, the expected kind of the
   expression. Returns true if the expression is formed correctly, and
   false otherwise.
   See enum EXP_KIND for more info about syntactic well-formedness.
*/
static boolean isCorrectExp(node_ptr exp, enum EXP_KIND expectedKind)
{
  switch(node_get_type(exp))
    {
      /* atomic expression (or thier operands have been checked earlier) */
    case FAILURE:
    case FALSEEXP:
    case TRUEEXP:
    case NUMBER:
    case NUMBER_UNSIGNED_WORD:
    case NUMBER_SIGNED_WORD:
    case NUMBER_FRAC:
    case NUMBER_REAL:
    case NUMBER_EXP:
    case UWCONST:
    case SWCONST:
    case TWODOTS:
    case DOT:
    case ATOM:
    case SELF:
    case ARRAY:
    case COUNT:
      return true;

      /* unary operators incompatible with LTL and CTL operator */
    case CAST_BOOL:
    case CAST_WORD1:
    case CAST_SIGNED:
    case CAST_UNSIGNED:
    case WSIZEOF:
    case CAST_TOINT:
    case TYPEOF:
      if (EXP_CTL == expectedKind) {
        return isCorrectExp(car(exp), EXP_SIMPLE);
      }
      else if (EXP_LTL == expectedKind) {
        return isCorrectExp(car(exp), EXP_NEXT);
      }

      FALLTHROUGH

      /* unary operators compatible with LTL and CTL operator */
    case NOT:
    case UMINUS:
      return isCorrectExp(car(exp), expectedKind);

      /* binary opertors incompatible with LTL and CTL operator */
    case BIT_SELECTION:
    case CASE: case COLON:
    case CONCATENATION:
    case TIMES: case DIVIDE: case PLUS :case MINUS: case MOD:
    case LSHIFT: case RSHIFT: case LROTATE: case RROTATE:
    case WAREAD: case WAWRITE: /* AC ADDED THESE */
    case UNION: case SETIN:
    case EQUAL: case NOTEQUAL: case LT: case GT: case LE: case GE:
    case IFTHENELSE:
    case EXTEND:
    case WRESIZE:
    case CONST_ARRAY: /* AI ADDED */
      if (EXP_CTL == expectedKind) {
        return isCorrectExp(car(exp), EXP_SIMPLE)
          && isCorrectExp(cdr(exp), EXP_SIMPLE);
      }
      else if (EXP_LTL == expectedKind) {
        return isCorrectExp(car(exp), EXP_NEXT)
          && isCorrectExp(cdr(exp), EXP_NEXT);
      }

      FALLTHROUGH

      /* binary opertors compatible LTL and CTL operator */
    case AND: case OR: case XOR: case XNOR: case IFF: case IMPLIES:
      return isCorrectExp(car(exp), expectedKind)
        && isCorrectExp(cdr(exp), expectedKind);

      /* next expression (LTL is allowed to contain next) */
    case NEXT:
      if (EXP_NEXT != expectedKind &&
          EXP_LTL != expectedKind) {
        nusmv_yyerror_lined("unexpected 'next' operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_SIMPLE); /* NEXT cannot contain NEXT */

      /* CTL unary expressions */
    case EX: case AX: case EF: case AF: case EG: case AG:
    case ABU: case EBU:
    case EBF: case ABF: case EBG: case ABG:
      if (EXP_CTL != expectedKind) {
        nusmv_yyerror_lined("unexpected CTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_CTL); /* continue to check CTL */

      /* CTL binary expressions */
    case AU: case EU:
      if (EXP_CTL != expectedKind) {
        nusmv_yyerror_lined("unexpected CTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_CTL)
        && isCorrectExp(cdr(exp), EXP_CTL); /* continue to check CTL */


      /* LTL unary expressions */
    case OP_NEXT: case OP_PREC: case OP_NOTPRECNOT: case OP_GLOBAL:
    case OP_HISTORICAL: case OP_FUTURE: case OP_ONCE:
      if (EXP_LTL != expectedKind) {
        nusmv_yyerror_lined("unexpected LTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_LTL); /* continue to check LTL */


      /* LTL binary expressions */
    case UNTIL: case SINCE:
      if (EXP_LTL != expectedKind) {
        nusmv_yyerror_lined("unexpected LTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_LTL)
        && isCorrectExp(cdr(exp), EXP_LTL); /* continue to check LTL */

    default: nusmv_assert(false); /* unknown expression */
    }
  return false; /* should never be invoked */
}


static int nusmv_parse_psl()
{
  int res;
  res = psl_yyparse();
  return res;
}
  /* ENDS: /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/parser/grammar.y.3.50 */
