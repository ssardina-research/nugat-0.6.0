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




/* Copy the first part of user declarations.  */
#line 3 "grammar.y" /* yacc.c:339  */

/**CFile***********************************************************************

  FileName    [grammar.y]

  PackageName [parser]

  Synopsis    [Grammar (for Yacc and Bison) of NuSMV input language]

  SeeAlso     [input.l]

  Author      [Andrei Tchaltsev, Marco Roveri]

  Copyright   [
  This file is part of the ``parser'' package of NuSMV version 2.
  Copyright (C) 1998-2005 by CMU and FBK-irst.

  NuSMV version 2 is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2 of the License, or (at your option) any later version.

  NuSMV version 2 is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  For more information on NuSMV see <http://nusmv.fbk.eu>
  or email to <nusmv-users@fbk.eu>.
  Please report bugs to <nusmv-users@fbk.eu>.

  To contact the NuSMV development board, email to <nusmv@fbk.eu>. ]

******************************************************************************/

#if HAVE_CONFIG_H
# include "nusmv-config.h"
#endif
#include "config.h"
#include <setjmp.h>

#if NUSMV_HAVE_MALLOC_H
# if NUSMV_HAVE_SYS_TYPES_H
#  include <sys/types.h>
# endif
# include <malloc.h>
#elif NUSMV_HAVE_SYS_MALLOC_H
# if NUSMV_HAVE_SYS_TYPES_H
#  include <sys/types.h>
# endif
# include <sys/malloc.h>
#elif NUSMV_HAVE_STDLIB_H
# include <stdlib.h>
#endif

#include <limits.h>

#include "parser/parserInt.h"
#include "utils/utils.h"
#include "utils/ustring.h"
#include "node/node.h"
#include "opt/opt.h"
#include "prop/propPkg.h"
#include "utils/error.h"

#include "parser/symbols.h"

static char rcsid[] UTIL_UNUSED = "$Id: grammar.y,v 1.19.4.10.4.46.4.45 2010-02-17 15:13:41 nusmv Exp $";

#define YYMAXDEPTH INT_MAX

#define SYNTAX_ERROR_HANDLING(dest, src) \
  {                                      \
    if (OptsHandler_get_bool_option_value(OptsHandler_get_instance(), \
                                          OPT_PARSER_IS_LAX)) {       \
      dest = src;                                                     \
    }                                                                 \
    else {                                                            \
      YYABORT;                                                        \
    }                                                                 \
 }


node_ptr parsed_tree; /* the returned value of parsing */

enum PARSE_MODE parse_mode_flag; /* the flag what should be parsed */

extern FILE * nusmv_stderr;

void yyerror ARGS((char *s));
void yyerror_lined ARGS((const char *s, int line));
static node_ptr node2maincontext ARGS((node_ptr node));

/* this enum is used to distinguish
   different kinds of expressions: SIMPLE, NEXT, CTL and LTL.
   Since syntactically only one global kind of expressions exists,
   we have to invoke a special function which checks that an expression
   complies to the additional syntactic constrains.
   So, if an ltl-expression is expected then occurrences of NEXT or EBF
   operators will cause the termination of parsing.

   NB: An alternative to invoking a checking function would be to write quite
   intricate syntactic rules to distinguish all the cases.

   NB: This checking function could also be a part of the type checker,
   but it is more straightforward to write a separate function.
*/
  enum EXP_KIND {EXP_SIMPLE, EXP_NEXT, EXP_LTL, EXP_CTL};

  static boolean isCorrectExp ARGS((node_ptr exp, enum EXP_KIND expectedKind));

  static node_ptr build_case_colon_node ARGS((node_ptr l,
                                              node_ptr r,
                                              int linum));

  static int nusmv_parse_psl ARGS((void));

#line 188 "grammar.c" /* yacc.c:339  */

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
#ifndef YY_YY_Y_TAB_H_INCLUDED
# define YY_YY_Y_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TOK_CONSTRAINT = 258,
    TOK_MODULE = 259,
    TOK_PROCESS = 260,
    TOK_CONTEXT = 261,
    TOK_EU = 262,
    TOK_AU = 263,
    TOK_EBU = 264,
    TOK_ABU = 265,
    TOK_MINU = 266,
    TOK_MAXU = 267,
    TOK_VAR = 268,
    TOK_FROZENVAR = 269,
    TOK_IVAR = 270,
    TOK_DEFINE = 271,
    TOK_ARRAY_DEFINE = 272,
    TOK_INIT = 273,
    TOK_TRANS = 274,
    TOK_INVAR = 275,
    TOK_SPEC = 276,
    TOK_CTLSPEC = 277,
    TOK_LTLSPEC = 278,
    TOK_COMPUTE = 279,
    TOK_NAME = 280,
    TOK_PSLSPEC = 281,
    TOK_CONSTANTS = 282,
    TOK_INVARSPEC = 283,
    TOK_FAIRNESS = 284,
    TOK_COMPASSION = 285,
    TOK_JUSTICE = 286,
    TOK_ISA = 287,
    TOK_ASSIGN = 288,
    TOK_OF = 289,
    TOK_CONS = 290,
    TOK_SEMI = 291,
    TOK_LP = 292,
    TOK_RP = 293,
    TOK_RB = 294,
    TOK_LCB = 295,
    TOK_RCB = 296,
    TOK_EQDEF = 297,
    TOK_TWODOTS = 298,
    TOK_SELF = 299,
    TOK_CASE = 300,
    TOK_ESAC = 301,
    TOK_COLON = 302,
    TOK_INCONTEXT = 303,
    TOK_SIMPWFF = 304,
    TOK_NEXTWFF = 305,
    TOK_LTLWFF = 306,
    TOK_LTLPSL = 307,
    TOK_CTLWFF = 308,
    TOK_COMPWFF = 309,
    TOK_COMPID = 310,
    TOK_ARRAY = 311,
    TOK_BOOLEAN = 312,
    TOK_INTEGER = 313,
    TOK_REAL = 314,
    TOK_WORD = 315,
    TOK_BOOL = 316,
    TOK_WORD1 = 317,
    TOK_WAREAD = 318,
    TOK_WAWRITE = 319,
    TOK_SIGNED = 320,
    TOK_UNSIGNED = 321,
    TOK_EXTEND = 322,
    TOK_UWCONST = 323,
    TOK_SWCONST = 324,
    TOK_WRESIZE = 325,
    TOK_WSIZEOF = 326,
    TOK_WTOINT = 327,
    TOK_COUNT = 328,
    TOK_ATOM = 329,
    TOK_FALSEEXP = 330,
    TOK_TRUEEXP = 331,
    TOK_NUMBER = 332,
    TOK_NUMBER_FRAC = 333,
    TOK_NUMBER_REAL = 334,
    TOK_NUMBER_EXP = 335,
    TOK_NUMBER_WORD = 336,
    TOK_COMMA = 337,
    TOK_IMPLIES = 338,
    TOK_IFF = 339,
    TOK_OR = 340,
    TOK_XOR = 341,
    TOK_XNOR = 342,
    TOK_AND = 343,
    TOK_NOT = 344,
    TOK_QUESTIONMARK = 345,
    TOK_EX = 346,
    TOK_AX = 347,
    TOK_EF = 348,
    TOK_AF = 349,
    TOK_EG = 350,
    TOK_AG = 351,
    TOK_EE = 352,
    TOK_AA = 353,
    TOK_SINCE = 354,
    TOK_UNTIL = 355,
    TOK_TRIGGERED = 356,
    TOK_RELEASES = 357,
    TOK_EBF = 358,
    TOK_EBG = 359,
    TOK_ABF = 360,
    TOK_ABG = 361,
    TOK_BUNTIL = 362,
    TOK_MMIN = 363,
    TOK_MMAX = 364,
    TOK_OP_NEXT = 365,
    TOK_OP_GLOBAL = 366,
    TOK_OP_FUTURE = 367,
    TOK_OP_PREC = 368,
    TOK_OP_NOTPRECNOT = 369,
    TOK_OP_HISTORICAL = 370,
    TOK_OP_ONCE = 371,
    TOK_EQUAL = 372,
    TOK_NOTEQUAL = 373,
    TOK_LT = 374,
    TOK_GT = 375,
    TOK_LE = 376,
    TOK_GE = 377,
    TOK_UNION = 378,
    TOK_SETIN = 379,
    TOK_LSHIFT = 380,
    TOK_RSHIFT = 381,
    TOK_LROTATE = 382,
    TOK_RROTATE = 383,
    TOK_MOD = 384,
    TOK_PLUS = 385,
    TOK_MINUS = 386,
    TOK_TIMES = 387,
    TOK_DIVIDE = 388,
    TOK_NEXT = 389,
    TOK_SMALLINIT = 390,
    TOK_CONCATENATION = 391,
    TOK_LB = 392,
    TOK_DOT = 393,
    TOK_BIT = 394,
    TOK_PRED = 395,
    TOK_PREDSLIST = 396,
    TOK_MIRROR = 397,
    TOK_GAME = 398,
    TOK_PLAYER_1 = 399,
    TOK_PLAYER_2 = 400,
    TOK_REACHTARGET = 401,
    TOK_AVOIDTARGET = 402,
    TOK_REACHDEADLOCK = 403,
    TOK_AVOIDDEADLOCK = 404,
    TOK_BUCHIGAME = 405,
    TOK_LTLGAME = 406,
    TOK_GENREACTIVITY = 407
  };
#endif
/* Tokens.  */
#define TOK_CONSTRAINT 258
#define TOK_MODULE 259
#define TOK_PROCESS 260
#define TOK_CONTEXT 261
#define TOK_EU 262
#define TOK_AU 263
#define TOK_EBU 264
#define TOK_ABU 265
#define TOK_MINU 266
#define TOK_MAXU 267
#define TOK_VAR 268
#define TOK_FROZENVAR 269
#define TOK_IVAR 270
#define TOK_DEFINE 271
#define TOK_ARRAY_DEFINE 272
#define TOK_INIT 273
#define TOK_TRANS 274
#define TOK_INVAR 275
#define TOK_SPEC 276
#define TOK_CTLSPEC 277
#define TOK_LTLSPEC 278
#define TOK_COMPUTE 279
#define TOK_NAME 280
#define TOK_PSLSPEC 281
#define TOK_CONSTANTS 282
#define TOK_INVARSPEC 283
#define TOK_FAIRNESS 284
#define TOK_COMPASSION 285
#define TOK_JUSTICE 286
#define TOK_ISA 287
#define TOK_ASSIGN 288
#define TOK_OF 289
#define TOK_CONS 290
#define TOK_SEMI 291
#define TOK_LP 292
#define TOK_RP 293
#define TOK_RB 294
#define TOK_LCB 295
#define TOK_RCB 296
#define TOK_EQDEF 297
#define TOK_TWODOTS 298
#define TOK_SELF 299
#define TOK_CASE 300
#define TOK_ESAC 301
#define TOK_COLON 302
#define TOK_INCONTEXT 303
#define TOK_SIMPWFF 304
#define TOK_NEXTWFF 305
#define TOK_LTLWFF 306
#define TOK_LTLPSL 307
#define TOK_CTLWFF 308
#define TOK_COMPWFF 309
#define TOK_COMPID 310
#define TOK_ARRAY 311
#define TOK_BOOLEAN 312
#define TOK_INTEGER 313
#define TOK_REAL 314
#define TOK_WORD 315
#define TOK_BOOL 316
#define TOK_WORD1 317
#define TOK_WAREAD 318
#define TOK_WAWRITE 319
#define TOK_SIGNED 320
#define TOK_UNSIGNED 321
#define TOK_EXTEND 322
#define TOK_UWCONST 323
#define TOK_SWCONST 324
#define TOK_WRESIZE 325
#define TOK_WSIZEOF 326
#define TOK_WTOINT 327
#define TOK_COUNT 328
#define TOK_ATOM 329
#define TOK_FALSEEXP 330
#define TOK_TRUEEXP 331
#define TOK_NUMBER 332
#define TOK_NUMBER_FRAC 333
#define TOK_NUMBER_REAL 334
#define TOK_NUMBER_EXP 335
#define TOK_NUMBER_WORD 336
#define TOK_COMMA 337
#define TOK_IMPLIES 338
#define TOK_IFF 339
#define TOK_OR 340
#define TOK_XOR 341
#define TOK_XNOR 342
#define TOK_AND 343
#define TOK_NOT 344
#define TOK_QUESTIONMARK 345
#define TOK_EX 346
#define TOK_AX 347
#define TOK_EF 348
#define TOK_AF 349
#define TOK_EG 350
#define TOK_AG 351
#define TOK_EE 352
#define TOK_AA 353
#define TOK_SINCE 354
#define TOK_UNTIL 355
#define TOK_TRIGGERED 356
#define TOK_RELEASES 357
#define TOK_EBF 358
#define TOK_EBG 359
#define TOK_ABF 360
#define TOK_ABG 361
#define TOK_BUNTIL 362
#define TOK_MMIN 363
#define TOK_MMAX 364
#define TOK_OP_NEXT 365
#define TOK_OP_GLOBAL 366
#define TOK_OP_FUTURE 367
#define TOK_OP_PREC 368
#define TOK_OP_NOTPRECNOT 369
#define TOK_OP_HISTORICAL 370
#define TOK_OP_ONCE 371
#define TOK_EQUAL 372
#define TOK_NOTEQUAL 373
#define TOK_LT 374
#define TOK_GT 375
#define TOK_LE 376
#define TOK_GE 377
#define TOK_UNION 378
#define TOK_SETIN 379
#define TOK_LSHIFT 380
#define TOK_RSHIFT 381
#define TOK_LROTATE 382
#define TOK_RROTATE 383
#define TOK_MOD 384
#define TOK_PLUS 385
#define TOK_MINUS 386
#define TOK_TIMES 387
#define TOK_DIVIDE 388
#define TOK_NEXT 389
#define TOK_SMALLINIT 390
#define TOK_CONCATENATION 391
#define TOK_LB 392
#define TOK_DOT 393
#define TOK_BIT 394
#define TOK_PRED 395
#define TOK_PREDSLIST 396
#define TOK_MIRROR 397
#define TOK_GAME 398
#define TOK_PLAYER_1 399
#define TOK_PLAYER_2 400
#define TOK_REACHTARGET 401
#define TOK_AVOIDTARGET 402
#define TOK_REACHDEADLOCK 403
#define TOK_AVOIDDEADLOCK 404
#define TOK_BUCHIGAME 405
#define TOK_LTLGAME 406
#define TOK_GENREACTIVITY 407

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 125 "grammar.y" /* yacc.c:355  */

  node_ptr node;
  int lineno;

#line 537 "grammar.c" /* yacc.c:355  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */
#line 225 "grammar.y" /* yacc.c:358  */

#if HAVE_GAME
#include "addons/game/parser/game_symbols.h"
#include "addons/game/game.h"
#endif

  /* below vars are used if input file contains game definition */
  static node_ptr game_parser_spec_list = Nil;
  static node_ptr game_parser_player_1 = Nil;
  static node_ptr game_parser_player_2 = Nil;

#line 563 "grammar.c" /* yacc.c:358  */

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
#define YYLAST   2329

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  153
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  124
/* YYNRULES -- Number of rules.  */
#define YYNRULES  349
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  727

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   407

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
     145,   146,   147,   148,   149,   150,   151,   152
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   262,   262,   263,   266,   267,   268,   272,   274,   276,
     278,   281,   285,   289,   290,   291,   293,   295,   297,   299,
     300,   301,   306,   311,   325,   326,   327,   328,   329,   338,
     347,   353,   358,   359,   360,   361,   362,   363,   364,   365,
     366,   367,   369,   372,   375,   380,   381,   385,   387,   391,
     396,   397,   401,   402,   403,   404,   408,   409,   410,   413,
     414,   415,   421,   422,   423,   426,   427,   431,   432,   435,
     436,   440,   441,   442,   443,   444,   445,   446,   449,   450,
     454,   455,   456,   457,   458,   459,   460,   462,   464,   466,
     468,   469,   470,   471,   474,   480,   481,   484,   485,   486,
     487,   490,   491,   495,   496,   499,   503,   504,   509,   510,
     511,   512,   513,   514,   515,   517,   524,   525,   527,   529,
     536,   546,   547,   551,   552,   553,   554,   558,   559,   563,
     564,   568,   569,   573,   580,   583,   586,   589,   593,   595,
     604,   605,   609,   613,   615,   617,   619,   620,   622,   624,
     628,   629,   630,   634,   635,   638,   639,   640,   641,   644,
     645,   648,   649,   650,   652,   664,   665,   677,   678,   681,
     684,   685,   686,   689,   690,   695,   696,   697,   700,   701,
     702,   703,   704,   705,   706,   707,   708,   709,   710,   711,
     712,   713,   714,   715,   716,   717,   718,   719,   720,   729,
     730,   733,   734,   737,   738,   741,   742,   743,   745,   746,
     747,   749,   750,   751,   754,   756,   758,   762,   765,   766,
     767,   770,   772,   785,   789,   790,   791,   795,   796,   800,
     801,   805,   806,   810,   812,   813,   814,   816,   818,   823,
     831,   833,   835,   839,   842,   845,   851,   852,   854,   855,
     858,   859,   861,   862,   863,   864,   867,   868,   871,   872,
     875,   876,   878,   879,   883,   893,   898,   899,   900,   904,
     905,   909,   914,   920,   926,   934,   942,   946,   946,   954,
     955,   956,   957,   958,   967,   968,   969,   970,   971,   978,
     979,   980,   983,   985,   987,   989,   993,   994,   995,   996,
     997,   998,   999,  1007,  1008,  1009,  1012,  1013,  1019,  1019,
    1058,  1058,  1065,  1065,  1079,  1080,  1095,  1096,  1097,  1098,
    1108,  1131,  1132,  1140,  1156,  1177,  1178,  1179,  1180,  1181,
    1182,  1183,  1189,  1190,  1194,  1195,  1197,  1198,  1199,  1200,
    1201,  1207,  1208,  1210,  1217,  1224,  1231,  1238,  1249,  1256
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TOK_CONSTRAINT", "TOK_MODULE",
  "TOK_PROCESS", "TOK_CONTEXT", "TOK_EU", "TOK_AU", "TOK_EBU", "TOK_ABU",
  "TOK_MINU", "TOK_MAXU", "TOK_VAR", "TOK_FROZENVAR", "TOK_IVAR",
  "TOK_DEFINE", "TOK_ARRAY_DEFINE", "TOK_INIT", "TOK_TRANS", "TOK_INVAR",
  "TOK_SPEC", "TOK_CTLSPEC", "TOK_LTLSPEC", "TOK_COMPUTE", "TOK_NAME",
  "TOK_PSLSPEC", "TOK_CONSTANTS", "TOK_INVARSPEC", "TOK_FAIRNESS",
  "TOK_COMPASSION", "TOK_JUSTICE", "TOK_ISA", "TOK_ASSIGN", "TOK_OF",
  "TOK_CONS", "TOK_SEMI", "TOK_LP", "TOK_RP", "TOK_RB", "TOK_LCB",
  "TOK_RCB", "TOK_EQDEF", "TOK_TWODOTS", "TOK_SELF", "TOK_CASE",
  "TOK_ESAC", "TOK_COLON", "TOK_INCONTEXT", "TOK_SIMPWFF", "TOK_NEXTWFF",
  "TOK_LTLWFF", "TOK_LTLPSL", "TOK_CTLWFF", "TOK_COMPWFF", "TOK_COMPID",
  "TOK_ARRAY", "TOK_BOOLEAN", "TOK_INTEGER", "TOK_REAL", "TOK_WORD",
  "TOK_BOOL", "TOK_WORD1", "TOK_WAREAD", "TOK_WAWRITE", "TOK_SIGNED",
  "TOK_UNSIGNED", "TOK_EXTEND", "TOK_UWCONST", "TOK_SWCONST",
  "TOK_WRESIZE", "TOK_WSIZEOF", "TOK_WTOINT", "TOK_COUNT", "TOK_ATOM",
  "TOK_FALSEEXP", "TOK_TRUEEXP", "TOK_NUMBER", "TOK_NUMBER_FRAC",
  "TOK_NUMBER_REAL", "TOK_NUMBER_EXP", "TOK_NUMBER_WORD", "TOK_COMMA",
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
  "TOK_PRED", "TOK_PREDSLIST", "TOK_MIRROR", "TOK_GAME", "TOK_PLAYER_1",
  "TOK_PLAYER_2", "TOK_REACHTARGET", "TOK_AVOIDTARGET",
  "TOK_REACHDEADLOCK", "TOK_AVOIDDEADLOCK", "TOK_BUCHIGAME", "TOK_LTLGAME",
  "TOK_GENREACTIVITY", "$accept", "number", "integer", "number_word",
  "number_frac", "number_real", "number_exp", "subrange", "subrangetype",
  "constant", "primary_expr", "count_param_list", "case_element_list_expr",
  "case_element_expr", "concatination_expr", "multiplicative_expr",
  "additive_expr", "shift_expr", "set_expr", "set_list_expr", "union_expr",
  "in_expr", "relational_expr", "ctl_expr", "pure_ctl_expr",
  "ctl_and_expr", "ctl_or_expr", "ctl_iff_expr", "ctl_implies_expr",
  "ctl_basic_expr", "ltl_unary_expr", "pure_ltl_unary_expr",
  "ltl_binary_expr", "and_expr", "or_expr", "ite_expr", "iff_expr",
  "implies_expr", "basic_expr", "simple_expression", "next_expression",
  "ctl_expression", "ltl_expression", "compute_expression", "itype",
  "type", "type_value_list", "type_value", "complex_atom", "module_type",
  "next_list_expression", "module_list", "module", "module_sign",
  "atom_list", "declarations", "declaration", "var", "frozen_var",
  "input_var", "var_decl_list", "fvar_decl_list", "ivar_decl_list",
  "var_decl", "fvar_decl", "ivar_decl", "define_decls", "define_list",
  "define", "array_define", "array_define_list", "array_expression",
  "array_expression_list", "array_contents", "assign", "assign_list",
  "one_assign", "init", "invar", "trans", "fairness", "justice",
  "compassion", "_invarspec", "invarspec", "_ctlspec", "ctlspec",
  "_ltlspec", "ltlspec", "_compute", "compute", "pslspec", "constants",
  "constants_expression", "predicate_list", "predicate", "mirror", "isa",
  "optsemi", "decl_var_id", "var_id", "command", "command_case", "context",
  "_simpwff", "game_begin", "$@1", "$@2", "$@3", "simple_list_expression",
  "game_module_list", "game_definition", "game_body", "game_body_element",
  "player_body", "player_body_element", "player_num", "reachtarget",
  "avoidtarget", "reachdeadlock", "avoiddeadlock", "buchigame", "ltlgame",
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
     405,   406,   407
};
# endif

#define YYPACT_NINF -502

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-502)))

#define YYTABLE_NINF -319

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
      66,    76,    11,   367,  1652,  -502,     6,   332,    11,    89,
    -502,  -502,    74,  1652,  1652,  1652,  1652,  1652,  1652,  1652,
    1652,   201,    30,   -49,  -502,  -502,  1652,  1652,  -502,  1652,
      97,   102,   140,   158,   189,   194,   215,   229,   236,   250,
     266,   275,   297,  -502,  -502,  -502,   193,  -502,  -502,  -502,
    -502,  1732,  1812,  1812,  1812,  1812,  1812,  1812,   200,   224,
     -28,   -28,   -28,   -28,  1652,  1652,  1652,  1652,  1652,  1652,
    1652,   279,  2149,   329,  -502,   336,  -502,  -502,  -502,  -502,
    -502,  -502,   238,   245,   126,   260,   298,  -502,   249,   264,
     283,  -502,  -502,  -502,  -502,   361,   296,   324,  -502,   343,
    -502,  -502,  -502,   357,  -502,  -502,  -502,   306,   306,   306,
     306,   306,   306,   306,  -502,   332,  -502,  -502,  -502,  -502,
    -502,  -502,  -502,   406,  -502,  -502,  -502,   377,   383,  -502,
     393,   402,   164,  -502,   169,  -502,   199,  -502,  -502,   241,
    -502,   278,   304,   299,  -502,  -502,  -502,     3,  1332,   -49,
    -502,   447,    17,  -502,   448,  1652,   455,  1652,  1652,  1652,
    1652,  1652,  1652,  1652,  1652,  1652,  1652,  1652,  1652,  2195,
    -502,   424,  2195,   238,  -502,  -502,  1886,  -502,  -502,  -502,
    -502,  -502,  -502,  1812,  1812,  -502,   426,   427,  1812,  1812,
    1812,  1812,  -502,  -502,  -502,  -502,  -502,  -502,  -502,   462,
     463,  2195,   238,  1652,   -28,  1652,    31,  2195,  2195,  2195,
    2195,  2195,  2195,  2195,  2195,  2057,  2057,  2057,  2057,  2057,
    2057,  2057,  2057,  1652,  1652,  1652,  1652,  1652,  1652,  1652,
    1652,  1652,  1652,  1652,    44,   902,   379,   379,  -502,  -502,
    1652,  1652,   471,   471,   472,  1652,   473,  -502,  -502,  -502,
    -502,  -502,  -502,   437,  -502,   437,  -502,   437,  -502,   437,
    -502,  1652,  1652,   437,  -502,  -502,  1652,   168,    30,   435,
     471,  -502,  -502,  -502,  1652,  -502,  -502,  1652,   475,   477,
     436,   438,   479,   481,   440,   441,   442,   443,   488,   489,
     -45,   490,  -502,  -502,   444,   254,   390,  -502,   -19,     7,
    -502,  -502,  -502,  -502,  -502,  -502,   491,  -502,   492,   483,
     494,  -502,  -502,   238,   245,   245,   245,   126,   126,   260,
     260,  -502,   249,   264,   264,   264,   264,   264,   264,  -502,
    -502,  -502,  -502,   361,   296,   296,   296,   487,  -502,  -502,
    -502,  -502,    19,  -502,   461,   461,   461,  -502,  -502,  1652,
    1652,  1652,  1006,  1088,  1170,   132,  -502,   464,  1252,  1652,
     499,  1652,   465,  -502,   461,  -502,  -502,  -502,  -502,  -502,
    -502,  -502,  -502,  -502,  -502,  -502,  -502,  -502,  -502,  -502,
    -502,  -502,  -502,  -502,  -502,  -502,  -502,  -502,  -502,  -502,
    -502,  -502,  -502,  -502,  -502,   471,   471,  -502,  -502,  1652,
     471,  1652,  -502,    12,    12,    12,    12,   458,   459,    12,
     498,  -502,  -502,   154,   503,  -502,  -502,   507,  -502,  -502,
    1652,  1652,  -502,  -502,  1652,  2195,  2195,  1652,  -502,  -502,
    2195,  -502,  1812,  1812,  1812,  1812,  1812,  1812,  1812,   -28,
    1812,   -28,  -502,  1652,  -502,  1652,  -502,   470,  -502,   715,
    -502,   -12,   749,  -502,   119,   300,  -502,   133,   811,   546,
     471,   471,   471,    30,  -502,    30,  -502,    30,  -502,    30,
    -502,  -502,   410,     4,    30,  -502,   471,  1652,   471,  -502,
     652,    23,  -502,  -502,  -502,    49,  -502,   148,  1652,   478,
    -502,  -502,  -502,  -502,  1652,  1652,  -502,  -502,   511,  1492,
    -502,   516,   467,   518,    85,    90,   519,  -502,  -502,   444,
     444,   444,  -502,   254,   532,  1812,   541,  1812,   542,  -502,
    -502,  -502,  -502,   931,   -33,   209,  -502,  -502,  1965,  -502,
    -502,  1965,  -502,  -502,   -25,  -502,    33,  -502,  -502,  -502,
      36,    96,   106,   111,   484,  -502,   464,   113,  -502,   500,
    -502,  -502,   547,   548,  -502,   123,  -502,   471,  1652,   505,
     544,  -502,   550,   551,  1652,    30,   471,  -502,  1652,  -502,
    -502,  -502,  -502,  -502,   552,  -502,   553,  -502,    55,   219,
    2103,  -502,  -502,  -502,   449,    40,    46,   454,  -502,   159,
    -502,   557,  -502,   555,   520,  -502,  -502,  2103,   559,   562,
    1412,   469,  1652,  1652,  1652,   201,  -502,   410,  1652,  1652,
      30,    30,  1652,  -502,  -502,   563,  -502,  -502,  -502,   471,
     205,  -502,   564,  -502,  -502,  2195,   570,  -502,  -502,  -502,
    -502,    27,  -502,   410,   476,   578,  1652,   480,   482,  1572,
    2195,  -502,  -502,   575,   581,  -502,  -502,  1412,   580,   582,
     585,  -502,  -502,  -502,  -502,  -502,   584,    -5,     5,   588,
    1652,  -502,   583,  -502,   592,  -502,   219,  1652,  2011,   589,
    1652,  1652,  -502,  -502,   155,   298,  -502,  1965,   545,   549,
     590,   591,  -502,  -502,  -502,   471,   593,   594,  -502,   187,
    1652,    55,  -502,   595,  -502,  -502,  -502,   598,   599,  -502,
    1652,  1652,   469,  -502,  -502,  -502,  1652,  1652,   471,   471,
     605,  -502,  -502,  -502,  -502,  -502,   596,   597,  -502,  -502,
     586,  -502,  -502,   504,  1652,   603,  -502
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
     312,     0,     0,     0,     0,     1,     0,   321,     0,   167,
     309,   317,   291,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   311,   289,     0,     0,    27,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    26,    13,    14,     2,     8,     9,    10,
       7,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    19,     0,    20,    21,    23,    22,
      63,    24,    50,    52,    56,    59,    62,    67,    69,    71,
      78,   106,    79,   116,   107,   121,   123,   127,   129,   131,
     133,   137,   313,   170,   175,   332,   332,     0,     0,     0,
       0,     0,     0,     0,   320,   321,   325,   326,   327,   328,
     329,   330,   331,   168,   319,   290,   134,     0,     0,   135,
       0,     0,   277,   296,   277,   297,   277,   299,   136,   277,
     298,     0,     0,   277,   300,   285,   284,     0,     0,   302,
     269,     0,     0,    65,     0,    47,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       2,     0,     0,    33,    94,   115,     0,    80,    81,    82,
      83,    84,    85,     0,     0,     4,     0,     0,     0,     0,
       0,     0,   108,   111,   113,   109,   110,   112,   114,     3,
       2,     0,    25,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   323,   324,   341,   342,
       0,     0,   277,   277,     0,     0,     0,   322,   295,   292,
     294,   293,   278,     0,   306,     0,   246,     0,   256,     0,
     250,     0,     0,     0,   260,   301,     0,     0,     0,     0,
     277,   270,    32,    64,     0,    41,    48,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      45,     0,     3,    95,    97,   101,   103,   105,     0,     0,
       5,     6,    90,    92,    91,    93,     0,    11,   134,     0,
       0,    28,    29,    51,    55,    53,    54,    57,    58,    60,
      61,    68,    70,    72,    73,    74,    75,    76,    77,   118,
     117,   120,   119,   122,   124,   125,   126,     0,   132,   130,
     171,   173,     0,   177,   199,   201,   203,   218,   224,     0,
       0,     0,     0,     0,     0,     0,   264,   266,     0,     0,
       0,     0,     0,   234,     0,   176,   179,   180,   181,   186,
     187,   182,   183,   184,   185,   188,   189,   190,   191,   192,
     193,   195,   194,   196,   197,   198,   178,   334,   335,   340,
     336,   337,   338,   339,   333,   277,   277,   345,   346,     0,
     277,     0,   303,   277,   277,   277,   277,     0,     0,   277,
       0,   286,   287,     0,     0,   271,    66,     0,    34,    35,
       0,     0,    37,    38,     0,     0,     0,     0,    17,    18,
       0,    44,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    36,     0,    30,     0,   172,     0,   279,     0,
     205,     0,     0,   208,     0,     0,   211,     0,     0,     0,
     277,   277,   277,     0,   252,     0,   253,     0,   258,     0,
     262,   159,   267,     0,     0,   248,   277,     0,   277,   276,
       0,   277,   343,   344,   314,     0,   348,     0,     0,     0,
     307,   247,   257,   251,     0,     0,   261,   288,     0,     0,
      49,     0,     0,     0,     0,     0,     0,    46,    96,    98,
      99,   100,   104,   102,     0,     0,     0,     0,     0,   128,
     174,   207,   206,     0,     0,     0,   210,   209,     0,   213,
     212,     0,   220,   219,     0,   226,     0,   240,   242,   241,
       0,     0,     0,     0,     0,   265,     0,     0,   243,     0,
     244,   236,     0,     0,   235,     0,   275,   277,     0,     0,
       0,   304,     0,     0,     0,     0,   277,    42,     0,    39,
      15,    16,    40,    87,     0,    86,     0,    31,     0,     0,
       0,   140,   141,   142,     0,     0,     0,    26,   146,     0,
     150,     0,   151,     0,     0,   280,   281,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   160,   268,     0,     0,
       0,     0,     0,   347,   315,     0,   305,   138,   139,   277,
       0,   272,     0,    89,    88,     0,   161,   152,   157,   158,
     156,     0,   153,   155,     0,     0,     0,     0,     0,     0,
       0,   214,   282,     0,     0,   215,   216,     0,     0,     0,
       0,   254,   255,   259,   263,   249,     0,     0,     0,     0,
       0,   273,     0,    43,     0,   147,     0,     0,     0,     0,
       0,     0,   162,   165,     0,    12,   283,     0,   232,   229,
       0,     0,   221,   222,   225,   277,     0,     0,   237,     0,
       0,     0,   154,     0,   149,   164,   143,     0,     0,   163,
       0,     0,     0,   228,   227,   245,     0,     0,   277,   277,
       0,   145,   144,   166,   231,   230,     0,     0,   349,   274,
       0,   239,   238,     0,     0,     0,   148
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -502,  -502,  -197,  -502,  -502,  -502,  -502,   -52,  -501,  -502,
      22,   213,   495,  -502,   257,   281,   284,  -401,   429,  -502,
     433,   227,  -502,    -1,   -39,    37,   208,  -502,   223,  -150,
      -4,   600,   434,   259,  -502,  -207,  -502,   428,     1,   -13,
       8,  -215,     9,  -502,  -171,  -502,  -502,    -3,  -328,  -481,
    -502,  -502,   654,  -502,  -502,  -502,  -502,   452,   456,  -502,
    -502,  -502,  -502,   243,   212,   235,   460,  -502,  -502,  -502,
    -502,  -101,    -9,    -2,   468,  -502,  -502,   485,   486,   517,
    -502,  -502,  -502,  -344,  -502,  -321,  -502,  -336,  -502,  -333,
    -502,  -502,  -502,  -502,  -502,   -99,  -502,  -502,   -98,  -274,
    -266,  -502,  -502,   114,  -502,  -502,  -502,  -502,  -502,  -395,
    -502,   689,   602,  -502,   604,  -502,   345,  -502,  -502,  -502,
    -502,  -502,  -502,  -502
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    74,    75,    76,    77,    78,    79,    80,   588,    81,
      82,   291,   154,   155,    83,    84,    85,    86,    87,   152,
      88,    89,    90,    91,    92,   294,   295,   296,   297,   298,
      93,    94,    95,    96,    97,    98,    99,   100,   126,   484,
     134,   139,   136,   143,   694,   591,   631,   632,   633,   695,
     674,     8,     9,   104,   342,   235,   365,   387,   388,   368,
     449,   452,   455,   450,   453,   456,   389,   458,   533,   370,
     459,   679,   680,   681,   390,   480,   554,   391,   392,   393,
     375,   376,   377,   135,   378,   140,   379,   137,   380,   144,
     381,   382,   383,   473,   149,   150,   385,   386,   254,   451,
     147,    24,    25,   403,   133,     1,     2,     3,     4,   485,
      10,    11,   114,   115,   236,   394,   240,   116,   117,   118,
     119,   120,   121,   122
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
     127,   128,   413,   131,   132,   101,   487,   307,   188,   189,
     190,   191,   174,   102,   475,     6,   129,   600,   468,   129,
     101,   138,   470,   130,   504,   505,   339,   151,   153,   472,
     156,   464,   466,   686,   299,   523,   256,   430,   258,   265,
     545,   260,   592,   687,   593,   264,   407,   408,   252,   185,
     271,   177,   178,   179,   180,   181,   182,   446,   273,   252,
     192,   193,   194,   195,   196,   197,   198,  -310,   665,  -310,
    -308,   454,   457,   173,   145,   601,     5,   161,   602,   635,
     103,   438,   340,   162,  -310,  -310,   546,   557,   439,  -316,
     481,   148,   205,   206,   202,  -310,   644,   627,   594,   274,
     637,   447,   186,   187,   146,   311,   638,   440,   312,   666,
     125,   625,   524,   525,   441,  -310,  -310,  -310,   341,  -310,
    -310,  -310,   589,   570,   664,   524,   525,   589,   571,   626,
     589,   558,   266,   267,   157,   270,   384,   174,   603,   158,
     266,   267,   266,   267,   397,   398,   280,   281,   604,   488,
     489,   285,   286,   605,     7,   608,   156,   469,   278,   279,
     524,   525,   282,   283,   284,   612,   528,   287,   129,   129,
     524,   525,   415,   266,   267,   288,   289,   159,   454,   589,
     531,   457,   293,   293,   534,   536,   559,   302,   303,   304,
     305,   290,   309,   699,   202,   160,   589,   540,   173,   541,
     252,   542,   640,   543,   306,   252,   308,  -310,   547,  -308,
     213,   214,   253,   310,   555,   213,   214,   255,   607,   329,
     330,   331,   332,   173,   589,   708,   161,   395,   396,   313,
     558,   162,   337,   266,   267,   252,    -4,   700,   519,   675,
     141,   142,   411,   266,   267,   412,   101,   257,   266,   267,
     266,   267,   163,   410,   400,   208,   524,   525,   209,   210,
     266,   267,   138,   138,   655,   689,   164,   589,   653,   558,
     524,   525,   654,   165,   498,   416,   589,   252,   417,   562,
     563,   651,   652,   595,   213,   214,   596,   166,   514,   259,
     516,   266,   267,   471,   628,   629,   185,   482,   483,   620,
    -204,   529,   486,   167,  -204,   490,   491,   492,   493,   141,
     142,   496,   168,  -204,  -204,  -204,  -204,  -204,  -204,  -204,
    -204,  -204,  -204,  -204,  -204,   662,  -204,  -204,  -204,  -204,
    -204,  -204,  -204,  -204,   169,   252,   460,   183,   462,   433,
     434,   435,   266,   267,   657,   658,   476,   263,   478,   186,
     187,   129,   590,   138,   138,   101,   199,   598,   461,   129,
     599,   184,   537,   538,   539,   574,   203,   576,    12,   404,
      13,   405,   215,   406,   448,   205,   206,   409,   548,   204,
     550,   207,   630,   556,   227,    14,    15,   515,   216,   517,
     211,   212,   344,   345,   234,   347,    16,   349,   350,   351,
     217,   218,   219,   220,   221,   222,  -318,   501,   502,   228,
     229,   230,   363,   248,   231,   261,    17,    18,    19,   249,
      20,    21,    22,   213,   214,   503,   232,   233,   506,   250,
     518,   508,   293,   293,   293,   293,   293,   293,   251,   293,
    -204,   262,  -204,  -204,   323,   324,   325,   326,   327,   328,
     238,   239,   290,   241,   242,   243,   244,   245,   246,   613,
     223,   224,   225,   226,   549,   314,   315,   316,   621,   630,
     509,   510,   511,   436,   437,   560,   105,   106,   107,   108,
     109,   110,   111,   112,   113,   272,   566,   334,   335,   336,
    -161,   639,   317,   318,   275,   138,   138,   319,   320,   649,
     650,   292,   277,   300,   301,    -5,    -6,   252,    23,   399,
     401,   402,   414,   418,   293,   419,   293,   422,   420,   423,
     421,   661,   424,   425,   426,   427,   428,   429,   431,   442,
     443,  -135,   432,   444,   445,   448,   477,   497,   471,   479,
     494,   495,   499,   500,   520,   614,  -223,   535,   544,   568,
    -223,   619,   561,   564,   567,   622,   569,   572,   606,  -223,
    -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
    -223,   573,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
     575,   577,   609,   616,   610,   611,   636,   705,   615,   617,
     618,   623,   624,   641,   642,   645,   656,   643,   646,   659,
     660,   129,   663,   138,   138,   101,   647,   639,   648,   129,
     718,   719,   668,   667,   676,   677,   682,   670,   683,   671,
     448,   684,   685,   669,   688,   690,   691,   701,   696,   703,
     704,   702,   721,   722,   710,   706,   707,   711,   712,   720,
     129,   724,   726,   507,   321,   513,   723,   673,   129,   322,
     276,   175,  -233,   551,   693,   678,  -233,   697,   698,   512,
     338,   333,   123,   692,   527,  -233,  -233,  -233,  -233,  -233,
    -233,  -233,  -233,  -233,  -233,  -233,  -233,   709,  -233,  -233,
    -233,  -233,  -233,  -233,  -233,  -233,  -223,   366,  -223,  -223,
     530,   367,   522,   715,   717,   369,   145,   124,     0,   714,
       0,   129,   129,   371,     0,     0,     0,   129,   713,   678,
     237,   725,     0,     0,   716,  -200,   521,   247,     0,  -200,
     372,   373,     0,     0,     0,     0,   146,     0,  -200,  -200,
    -200,  -200,  -200,  -200,  -200,  -200,  -200,  -200,  -200,  -200,
       0,  -200,  -200,  -200,  -200,  -200,  -200,  -200,  -200,  -202,
     526,     0,   374,  -202,     0,     0,     0,     0,     0,     0,
       0,     0,  -202,  -202,  -202,  -202,  -202,  -202,  -202,  -202,
    -202,  -202,  -202,  -202,     0,  -202,  -202,  -202,  -202,  -202,
    -202,  -202,  -202,     0,     0,     0,   552,   553,     0,   448,
       0,     0,  -233,     0,  -233,  -233,  -233,  -233,  -233,  -233,
    -233,  -233,  -233,  -233,  -233,     0,     0,     0,     0,     0,
       0,  -217,   532,     0,     0,  -217,     0,     0,     0,     0,
       0,     0,     0,   448,  -217,  -217,  -217,  -217,  -217,  -217,
    -217,  -217,  -217,  -217,  -217,  -217,     0,  -217,  -217,  -217,
    -217,  -217,  -217,  -217,  -217,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,  -200,     0,  -200,  -200,  -200,
    -200,  -200,  -200,  -200,  -200,  -200,  -200,  -200,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   448,     0,     0,     0,  -202,
       0,  -202,  -202,  -202,  -202,  -202,  -202,  -202,  -202,  -202,
    -202,  -202,  -169,   343,     0,     0,  -169,     0,     0,     0,
       0,     0,     0,     0,     0,   344,   345,   346,   347,   348,
     349,   350,   351,   352,   353,   354,   355,     0,   356,   357,
     358,   359,   360,   361,   362,   363,   578,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,  -217,     0,  -217,  -217,  -217,  -217,  -217,  -217,  -217,
    -217,  -217,  -217,  -217,     0,     0,     0,     0,    26,     0,
       0,   579,     0,     0,     0,    28,    29,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   580,   581,   582,
     583,   584,    30,    31,    32,    33,   585,   586,    36,    37,
      38,    39,    40,    41,    42,   587,    44,    45,   170,    47,
      48,    49,    50,     0,     0,     0,     0,     0,     0,     0,
     201,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   463,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   148,    26,   364,  -169,    27,     0,     0,     0,
      28,    29,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   171,   172,     0,     0,    73,     0,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,     0,     0,
       0,     0,     0,     0,     0,    51,     0,    52,    53,    54,
      55,    56,    57,    58,    59,     0,     0,     0,     0,    60,
      61,    62,    63,   465,     0,     0,    64,    65,    66,    67,
      68,    69,    70,     0,     0,    26,     0,     0,    27,     0,
       0,     0,    28,    29,     0,     0,    71,    72,     0,     0,
      73,     0,     0,     0,     0,     0,     0,     0,     0,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
       0,     0,     0,     0,     0,     0,     0,    51,     0,    52,
      53,    54,    55,    56,    57,    58,    59,     0,     0,     0,
       0,    60,    61,    62,    63,   467,     0,     0,    64,    65,
      66,    67,    68,    69,    70,     0,     0,    26,     0,     0,
      27,     0,     0,     0,    28,    29,     0,     0,    71,    72,
       0,     0,    73,     0,     0,     0,     0,     0,     0,     0,
       0,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    47,    48,
      49,    50,     0,     0,     0,     0,     0,     0,     0,    51,
       0,    52,    53,    54,    55,    56,    57,    58,    59,     0,
       0,     0,     0,    60,    61,    62,    63,   474,     0,     0,
      64,    65,    66,    67,    68,    69,    70,     0,     0,    26,
       0,     0,    27,     0,     0,     0,    28,    29,     0,     0,
      71,    72,     0,     0,    73,     0,     0,     0,     0,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
       0,     0,    27,     0,     0,     0,    28,    29,     0,     0,
       0,     0,    71,    72,     0,     0,    73,     0,     0,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
       0,   268,    27,     0,     0,     0,    28,    29,     0,     0,
       0,     0,    71,    72,     0,     0,    73,     0,     0,   269,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
       0,     0,    27,     0,     0,     0,    28,    29,     0,     0,
       0,     0,    71,    72,     0,     0,    73,     0,     0,   647,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
     672,   565,    27,     0,     0,     0,    28,    29,     0,     0,
       0,     0,    71,    72,     0,     0,    73,     0,     0,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
       0,     0,    27,     0,     0,     0,    28,    29,     0,     0,
       0,     0,    71,    72,     0,     0,    73,     0,     0,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
       0,     0,     0,     0,     0,     0,    28,    29,     0,     0,
       0,     0,    71,    72,     0,     0,    73,     0,     0,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,   170,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,    51,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,    64,    65,    66,    67,    68,    69,    70,    26,
       0,     0,    27,     0,     0,     0,    28,    29,     0,     0,
       0,     0,   171,   172,     0,     0,    73,     0,     0,     0,
       0,     0,     0,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,     0,     0,     0,     0,     0,     0,
       0,   176,     0,    52,    53,    54,    55,    56,    57,    58,
      59,     0,     0,     0,     0,    60,    61,    62,    63,     0,
       0,     0,     0,    26,     0,     0,     0,     0,     0,     0,
      28,    29,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    71,    72,     0,     0,    73,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,    44,    45,   170,    47,    48,    49,    50,     0,     0,
       0,     0,     0,     0,     0,   176,     0,    52,    53,    54,
      55,    56,    57,    58,    59,     0,     0,     0,     0,    60,
      61,    62,    63,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    26,     0,     0,   579,     0,     0,     0,    28,
      29,     0,     0,     0,     0,     0,   171,   172,     0,     0,
      73,   597,   581,   582,   583,   584,    30,    31,    32,    33,
     585,   586,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    45,   170,    47,    48,    49,    50,     0,    26,     0,
       0,   579,     0,     0,   201,    28,    29,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   580,   581,   582,
     583,   584,    30,    31,    32,    33,   585,   586,    36,    37,
      38,    39,    40,    41,    42,   587,    44,    45,   170,    47,
      48,    49,    50,     0,    26,   171,   172,    27,     0,    73,
     201,    28,    29,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    48,    49,    50,     0,
      26,   171,   172,     0,     0,    73,   201,    28,    29,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   634,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
     170,    47,    48,    49,    50,     0,    26,    71,    72,     0,
       0,    73,   201,    28,    29,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,    44,    45,   200,    47,    48,    49,
      50,     0,    26,   171,   172,     0,     0,    73,   201,    28,
      29,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    45,   170,    47,    48,    49,    50,     0,     0,   171,
     172,     0,     0,    73,   201,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   171,   172,     0,     0,    73
};

static const yytype_int16 yycheck[] =
{
      13,    14,   268,    16,    17,     4,   401,   204,    60,    61,
      62,    63,    51,     4,   358,     4,    15,    42,   354,    18,
      19,    20,   355,    15,   425,   426,   233,    26,    27,   357,
      29,   352,   353,    38,   184,    47,   134,    82,   136,    36,
      36,   139,   523,    38,    77,   143,   261,   262,    36,    77,
     149,    52,    53,    54,    55,    56,    57,    38,    41,    36,
      64,    65,    66,    67,    68,    69,    70,     1,    41,     3,
       4,   345,   346,    51,    44,    42,     0,    37,    42,   580,
      74,   100,    38,    37,    18,    19,    82,    38,   107,     0,
     364,   140,   137,   138,    72,    29,   597,   578,   131,    82,
      60,    82,   130,   131,    74,    74,    60,   100,    77,    82,
      36,    56,   137,   138,   107,    49,    50,    51,    74,    53,
      54,    55,   523,    38,   625,   137,   138,   528,    38,    74,
     531,    82,   137,   138,    37,   148,   235,   176,    42,    37,
     137,   138,   137,   138,   242,   243,   159,   160,    42,   137,
     138,   164,   165,    42,   143,    42,   155,    25,   157,   158,
     137,   138,   161,   162,   163,    42,    47,   166,   167,   168,
     137,   138,   270,   137,   138,   167,   168,    37,   452,   580,
      47,   455,   183,   184,   458,   459,    38,   188,   189,   190,
     191,   169,   205,    38,   172,    37,   597,   463,   176,   465,
      36,   467,    43,   469,   203,    36,   205,   141,   474,   143,
     125,   126,    48,   205,   480,   125,   126,    48,   546,   223,
     224,   225,   226,   201,   625,    38,    37,   240,   241,   207,
      82,    37,   231,   137,   138,    36,    43,    82,   445,   640,
     108,   109,    74,   137,   138,    77,   245,    48,   137,   138,
     137,   138,    37,   266,   245,   129,   137,   138,   132,   133,
     137,   138,   261,   262,   608,   660,    37,   668,   604,    82,
     137,   138,   605,    37,   120,   274,   677,    36,   277,   494,
     495,   602,   603,    74,   125,   126,    77,    37,   438,    48,
     440,   137,   138,    74,    75,    76,    77,   395,   396,   565,
       0,     1,   400,    37,     4,   403,   404,   405,   406,   108,
     109,   409,    37,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,   120,    26,    27,    28,    29,
      30,    31,    32,    33,    37,    36,   349,   137,   351,    85,
      86,    87,   137,   138,   610,   611,   359,    48,   361,   130,
     131,   350,   523,   352,   353,   354,    77,   528,   350,   358,
     531,   137,   460,   461,   462,   515,    37,   517,     1,   255,
       3,   257,   123,   259,    74,   137,   138,   263,   476,    43,
     478,   136,   579,   481,    88,    18,    19,   439,   124,   441,
     130,   131,    13,    14,    37,    16,    29,    18,    19,    20,
     117,   118,   119,   120,   121,   122,     0,   420,   421,    85,
      86,    87,    33,    36,    90,   137,    49,    50,    51,    36,
      53,    54,    55,   125,   126,   424,    83,    84,   427,    36,
     443,   432,   433,   434,   435,   436,   437,   438,    36,   440,
     140,   137,   142,   143,   217,   218,   219,   220,   221,   222,
     144,   145,   430,   108,   109,   110,   111,   112,   113,   557,
      99,   100,   101,   102,   477,   208,   209,   210,   566,   666,
     433,   434,   435,    83,    84,   488,   144,   145,   146,   147,
     148,   149,   150,   151,   152,    38,   499,   228,   229,   230,
      36,    37,   211,   212,    46,   494,   495,   213,   214,   600,
     601,    77,    47,    77,    77,    43,    43,    36,   141,    37,
      37,    74,    77,    38,   515,    38,   517,    38,    82,    38,
      82,   619,    82,    82,    82,    82,    38,    38,    38,    38,
      47,    39,    88,    39,    47,    74,    37,    39,    74,    74,
      82,    82,    39,    36,    74,   558,     0,     1,   138,    82,
       4,   564,    74,    42,    38,   568,    38,    38,    74,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    39,    26,    27,    28,    29,    30,    31,    32,    33,
      39,    39,    82,    39,    37,    37,   137,   685,    83,    39,
      39,    39,    39,    36,    39,    36,   609,    77,    36,   612,
      37,   600,    38,   602,   603,   604,   137,    37,   600,   608,
     708,   709,    34,   137,    39,    34,    36,   137,    36,   137,
      74,    36,    38,   636,    36,    42,    34,    82,    39,    39,
      39,    82,    36,    36,    39,    42,    42,    39,    39,    34,
     639,   137,    39,   430,   215,   437,    60,   639,   647,   216,
     155,    51,     0,     1,   667,   647,     4,   670,   671,   436,
     232,   227,     8,   666,   452,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,   690,    26,    27,
      28,    29,    30,    31,    32,    33,   140,   235,   142,   143,
     455,   235,   449,   702,   707,   235,    44,     8,    -1,   701,
      -1,   700,   701,   235,    -1,    -1,    -1,   706,   700,   701,
     106,   724,    -1,    -1,   706,     0,     1,   115,    -1,     4,
     235,   235,    -1,    -1,    -1,    -1,    74,    -1,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      -1,    26,    27,    28,    29,    30,    31,    32,    33,     0,
       1,    -1,   235,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    -1,    26,    27,    28,    29,    30,
      31,    32,    33,    -1,    -1,    -1,   134,   135,    -1,    74,
      -1,    -1,   140,    -1,   142,   143,   144,   145,   146,   147,
     148,   149,   150,   151,   152,    -1,    -1,    -1,    -1,    -1,
      -1,     0,     1,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,    24,    -1,    26,    27,    28,
      29,    30,    31,    32,    33,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   140,    -1,   142,   143,   144,
     145,   146,   147,   148,   149,   150,   151,   152,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    -1,    -1,    -1,   140,
      -1,   142,   143,   144,   145,   146,   147,   148,   149,   150,
     151,   152,     0,     1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    -1,    26,    27,
      28,    29,    30,    31,    32,    33,     5,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   140,    -1,   142,   143,   144,   145,   146,   147,   148,
     149,   150,   151,   152,    -1,    -1,    -1,    -1,    37,    -1,
      -1,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    56,    57,    58,
      59,    60,    61,    62,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      89,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    25,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   140,    37,   142,   143,    40,    -1,    -1,    -1,
      44,    45,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   130,   131,    -1,    -1,   134,    -1,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    89,    -1,    91,    92,    93,
      94,    95,    96,    97,    98,    -1,    -1,    -1,    -1,   103,
     104,   105,   106,    25,    -1,    -1,   110,   111,   112,   113,
     114,   115,   116,    -1,    -1,    37,    -1,    -1,    40,    -1,
      -1,    -1,    44,    45,    -1,    -1,   130,   131,    -1,    -1,
     134,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    89,    -1,    91,
      92,    93,    94,    95,    96,    97,    98,    -1,    -1,    -1,
      -1,   103,   104,   105,   106,    25,    -1,    -1,   110,   111,
     112,   113,   114,   115,   116,    -1,    -1,    37,    -1,    -1,
      40,    -1,    -1,    -1,    44,    45,    -1,    -1,   130,   131,
      -1,    -1,   134,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    71,    72,    73,    74,    75,    76,    77,    78,    79,
      80,    81,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    89,
      -1,    91,    92,    93,    94,    95,    96,    97,    98,    -1,
      -1,    -1,    -1,   103,   104,   105,   106,    25,    -1,    -1,
     110,   111,   112,   113,   114,   115,   116,    -1,    -1,    37,
      -1,    -1,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
     130,   131,    -1,    -1,   134,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      -1,    -1,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      -1,   119,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,   137,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      -1,    -1,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,   137,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      38,   119,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      -1,    -1,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      -1,    -1,    -1,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,   110,   111,   112,   113,   114,   115,   116,    37,
      -1,    -1,    40,    -1,    -1,    -1,    44,    45,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    91,    92,    93,    94,    95,    96,    97,
      98,    -1,    -1,    -1,    -1,   103,   104,   105,   106,    -1,
      -1,    -1,    -1,    37,    -1,    -1,    -1,    -1,    -1,    -1,
      44,    45,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   130,   131,    -1,    -1,   134,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    89,    -1,    91,    92,    93,
      94,    95,    96,    97,    98,    -1,    -1,    -1,    -1,   103,
     104,   105,   106,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    37,    -1,    -1,    40,    -1,    -1,    -1,    44,
      45,    -1,    -1,    -1,    -1,    -1,   130,   131,    -1,    -1,
     134,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    -1,    37,    -1,
      -1,    40,    -1,    -1,    89,    44,    45,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    56,    57,    58,
      59,    60,    61,    62,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    -1,    37,   130,   131,    40,    -1,   134,
      89,    44,    45,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    61,    62,
      63,    64,    65,    66,    67,    68,    69,    70,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    80,    81,    -1,
      37,   130,   131,    -1,    -1,   134,    89,    44,    45,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    60,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    75,    76,
      77,    78,    79,    80,    81,    -1,    37,   130,   131,    -1,
      -1,   134,    89,    44,    45,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      81,    -1,    37,   130,   131,    -1,    -1,   134,    89,    44,
      45,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    -1,    -1,   130,
     131,    -1,    -1,   134,    89,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   130,   131,    -1,    -1,   134
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint16 yystos[] =
{
       0,   258,   259,   260,   261,     0,     4,   143,   204,   205,
     263,   264,     1,     3,    18,    19,    29,    49,    50,    51,
      53,    54,    55,   141,   254,   255,    37,    40,    44,    45,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      81,    89,    91,    92,    93,    94,    95,    96,    97,    98,
     103,   104,   105,   106,   110,   111,   112,   113,   114,   115,
     116,   130,   131,   134,   154,   155,   156,   157,   158,   159,
     160,   162,   163,   167,   168,   169,   170,   171,   173,   174,
     175,   176,   177,   183,   184,   185,   186,   187,   188,   189,
     190,   191,   195,    74,   206,   144,   145,   146,   147,   148,
     149,   150,   151,   152,   265,   266,   270,   271,   272,   273,
     274,   275,   276,   205,   264,    36,   191,   192,   192,   191,
     193,   192,   192,   257,   193,   236,   195,   240,   191,   194,
     238,   108,   109,   196,   242,    44,    74,   253,   140,   247,
     248,   191,   172,   191,   165,   166,   191,    37,    37,    37,
      37,    37,    37,    37,    37,    37,    37,    37,    37,    37,
      77,   130,   131,   163,   177,   184,    89,   176,   176,   176,
     176,   176,   176,   137,   137,    77,   130,   131,   160,   160,
     160,   160,   183,   183,   183,   183,   183,   183,   183,    77,
      77,    89,   163,    37,    43,   137,   138,   136,   129,   132,
     133,   130,   131,   125,   126,   123,   124,   117,   118,   119,
     120,   121,   122,    99,   100,   101,   102,    88,    85,    86,
      87,    90,    83,    84,    37,   208,   267,   267,   144,   145,
     269,   269,   269,   269,   269,   269,   269,   265,    36,    36,
      36,    36,    36,    48,   251,    48,   251,    48,   251,    48,
     251,   137,   137,    48,   251,    36,   137,   138,   119,   137,
     192,   248,    38,    41,    82,    46,   165,    47,   191,   191,
     192,   192,   191,   191,   191,   192,   192,   191,   193,   193,
     163,   164,    77,   176,   178,   179,   180,   181,   182,   182,
      77,    77,   176,   176,   176,   176,   191,   155,   191,   192,
     193,    74,    77,   163,   167,   167,   167,   168,   168,   169,
     169,   171,   173,   174,   174,   174,   174,   174,   174,   183,
     183,   183,   183,   185,   186,   186,   186,   191,   190,   188,
      38,    74,   207,     1,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,    24,    26,    27,    28,    29,
      30,    31,    32,    33,   142,   209,   210,   211,   212,   219,
     222,   227,   230,   231,   232,   233,   234,   235,   237,   239,
     241,   243,   244,   245,   248,   249,   250,   210,   211,   219,
     227,   230,   231,   232,   268,   192,   192,   251,   251,    37,
     195,    37,    74,   256,   256,   256,   256,   194,   194,   256,
     192,    74,    77,   253,    77,   251,   191,   191,    38,    38,
      82,    82,    38,    38,    82,    82,    82,    82,    38,    38,
      82,    38,    88,    85,    86,    87,    83,    84,   100,   107,
     100,   107,    38,    47,    39,    47,    38,    82,    74,   213,
     216,   252,   214,   217,   252,   215,   218,   252,   220,   223,
     192,   193,   192,    25,   238,    25,   238,    25,   240,    25,
     242,    74,   201,   246,    25,   236,   192,    37,   192,    74,
     228,   252,   251,   251,   192,   262,   251,   262,   137,   138,
     251,   251,   251,   251,    82,    82,   251,    39,   120,    39,
      36,   192,   192,   191,   170,   170,   191,   164,   176,   178,
     178,   178,   181,   179,   182,   160,   182,   160,   192,   188,
      74,     1,   216,    47,   137,   138,     1,   217,    47,     1,
     218,    47,     1,   221,   252,     1,   252,   251,   251,   251,
     253,   253,   253,   253,   138,    36,    82,   253,   251,   192,
     251,     1,   134,   135,   229,   253,   251,    38,    82,    38,
     192,    74,   194,   194,    42,   119,   192,    38,    82,    38,
      38,    38,    38,    39,   182,    39,   182,    39,     5,    40,
      56,    57,    58,    59,    60,    65,    66,    74,   161,   170,
     197,   198,   202,    77,   131,    74,    77,    56,   197,   197,
      42,    42,    42,    42,    42,    42,    74,   201,    42,    82,
      37,    37,    42,   251,   192,    83,    39,    39,    39,   192,
     253,   251,   192,    39,    39,    56,    74,   202,    75,    76,
     155,   199,   200,   201,    60,   161,   137,    60,    60,    37,
      43,    36,    39,    77,   161,    36,    36,   137,   193,   224,
     224,   238,   238,   240,   242,   236,   192,   253,   253,   192,
      37,   251,   120,    38,   161,    41,    82,   137,    34,   192,
     137,   137,    38,   193,   203,   170,    39,    34,   193,   224,
     225,   226,    36,    36,    36,    38,    38,    38,    36,   262,
      42,    34,   200,   192,   197,   202,    39,   192,   192,    38,
      82,    82,    82,    39,    39,   251,    42,    42,    38,   192,
      39,    39,    39,   193,   226,   225,   193,   192,   251,   251,
      34,    36,    36,    60,   137,   192,    39
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint16 yyr1[] =
{
       0,   153,   154,   154,   155,   155,   155,   156,   157,   158,
     159,   160,   161,   162,   162,   162,   162,   162,   162,   162,
     162,   162,   162,   162,   163,   163,   163,   163,   163,   163,
     163,   163,   163,   163,   163,   163,   163,   163,   163,   163,
     163,   163,   163,   163,   163,   164,   164,   165,   165,   166,
     167,   167,   168,   168,   168,   168,   169,   169,   169,   170,
     170,   170,   171,   171,   171,   172,   172,   173,   173,   174,
     174,   175,   175,   175,   175,   175,   175,   175,   176,   176,
     177,   177,   177,   177,   177,   177,   177,   177,   177,   177,
     177,   177,   177,   177,   177,   178,   178,   179,   179,   179,
     179,   180,   180,   181,   181,   182,   183,   183,   184,   184,
     184,   184,   184,   184,   184,   184,   185,   185,   185,   185,
     185,   186,   186,   187,   187,   187,   187,   188,   188,   189,
     189,   190,   190,   191,   192,   193,   194,   195,   196,   196,
     197,   197,   197,   197,   197,   197,   197,   197,   197,   197,
     198,   198,   198,   199,   199,   200,   200,   200,   200,   201,
     201,   202,   202,   202,   202,   203,   203,   204,   204,   205,
     206,   206,   206,   207,   207,   208,   208,   208,   209,   209,
     209,   209,   209,   209,   209,   209,   209,   209,   209,   209,
     209,   209,   209,   209,   209,   209,   209,   209,   209,   210,
     210,   211,   211,   212,   212,   213,   213,   213,   214,   214,
     214,   215,   215,   215,   216,   217,   218,   219,   220,   220,
     220,   221,   221,   222,   223,   223,   223,   224,   224,   225,
     225,   226,   226,   227,   228,   228,   228,   229,   229,   229,
     230,   231,   232,   233,   234,   235,   236,   236,   237,   237,
     238,   238,   239,   239,   239,   239,   240,   240,   241,   241,
     242,   242,   243,   243,   244,   245,   246,   246,   246,   247,
     247,   248,   248,   248,   248,   249,   250,   251,   251,   252,
     252,   252,   252,   252,   253,   253,   253,   253,   253,   254,
     254,   254,   255,   255,   255,   255,   255,   255,   255,   255,
     255,   255,   255,   256,   256,   256,   257,   257,   259,   258,
     260,   258,   261,   258,   262,   262,   263,   263,   263,   263,
     264,   265,   265,   266,   266,   266,   266,   266,   266,   266,
     266,   266,   267,   267,   268,   268,   268,   268,   268,   268,
     268,   269,   269,   270,   271,   272,   273,   274,   275,   276
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     1,     2,     2,     1,     1,     1,
       1,     3,     3,     1,     1,     6,     6,     4,     4,     1,
       1,     1,     1,     1,     1,     2,     1,     1,     3,     3,
       4,     6,     3,     2,     4,     4,     4,     4,     4,     6,
       6,     3,     6,     8,     4,     1,     3,     1,     2,     4,
       1,     3,     1,     3,     3,     3,     1,     3,     3,     1,
       3,     3,     1,     1,     3,     1,     3,     1,     3,     1,
       3,     1,     3,     3,     3,     3,     3,     3,     1,     1,
       2,     2,     2,     2,     2,     2,     6,     6,     7,     7,
       3,     3,     3,     3,     2,     1,     3,     1,     3,     3,
       3,     1,     3,     1,     3,     1,     1,     1,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     3,     3,     3,
       3,     1,     3,     1,     3,     3,     3,     1,     5,     1,
       3,     1,     3,     1,     1,     1,     1,     1,     6,     6,
       1,     1,     1,     4,     5,     5,     1,     3,    10,     4,
       1,     1,     2,     1,     3,     1,     1,     1,     1,     1,
       3,     1,     3,     4,     4,     1,     3,     1,     2,     3,
       1,     3,     4,     1,     3,     0,     2,     2,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       2,     1,     2,     1,     2,     1,     2,     2,     1,     2,
       2,     1,     2,     2,     4,     4,     4,     2,     0,     2,
       2,     4,     4,     2,     0,     5,     2,     3,     3,     1,
       3,     3,     1,     2,     0,     2,     2,     4,     7,     7,
       3,     3,     3,     3,     3,     7,     2,     4,     2,     5,
       2,     4,     2,     2,     5,     5,     2,     4,     2,     5,
       2,     4,     2,     5,     1,     3,     0,     1,     3,     1,
       2,     3,     6,     7,    10,     3,     2,     0,     1,     1,
       3,     3,     4,     5,     1,     1,     3,     3,     4,     1,
       2,     1,     3,     3,     3,     3,     2,     2,     2,     2,
       2,     3,     2,     1,     3,     4,     2,     4,     0,     2,
       0,     2,     0,     2,     1,     3,     1,     1,     2,     2,
       2,     0,     2,     2,     2,     1,     1,     1,     1,     1,
       1,     1,     0,     2,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     4,     4,     3,     3,     6,     4,    10
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
#line 263 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2521 "grammar.c" /* yacc.c:1646  */
    break;

  case 5:
#line 267 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2527 "grammar.c" /* yacc.c:1646  */
    break;

  case 6:
#line 269 "grammar.y" /* yacc.c:1646  */
    {node_int_setcar((yyvsp[0].node), -(node_get_int((yyvsp[0].node)))); (yyval.node) = (yyvsp[0].node);}
#line 2533 "grammar.c" /* yacc.c:1646  */
    break;

  case 11:
#line 282 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(TWODOTS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 2539 "grammar.c" /* yacc.c:1646  */
    break;

  case 12:
#line 286 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(TWODOTS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 2545 "grammar.c" /* yacc.c:1646  */
    break;

  case 15:
#line 292 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(UWCONST, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2551 "grammar.c" /* yacc.c:1646  */
    break;

  case 16:
#line 294 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SWCONST, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2557 "grammar.c" /* yacc.c:1646  */
    break;

  case 17:
#line 296 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(WSIZEOF, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2563 "grammar.c" /* yacc.c:1646  */
    break;

  case 18:
#line 298 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(CAST_TOINT, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2569 "grammar.c" /* yacc.c:1646  */
    break;

  case 21:
#line 302 "grammar.y" /* yacc.c:1646  */
    {
                 yyerror("fractional constants are not supported.");
                 YYABORT;
               }
#line 2578 "grammar.c" /* yacc.c:1646  */
    break;

  case 22:
#line 307 "grammar.y" /* yacc.c:1646  */
    {
                 yyerror("exponential constants are not supported.");
                 YYABORT;
               }
#line 2587 "grammar.c" /* yacc.c:1646  */
    break;

  case 23:
#line 312 "grammar.y" /* yacc.c:1646  */
    {
                 yyerror("real constants are not supported.");
                 YYABORT;
               }
#line 2596 "grammar.c" /* yacc.c:1646  */
    break;

  case 25:
#line 326 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(UMINUS, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2602 "grammar.c" /* yacc.c:1646  */
    break;

  case 27:
#line 328 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(SELF,Nil,Nil);}
#line 2608 "grammar.c" /* yacc.c:1646  */
    break;

  case 28:
#line 330 "grammar.y" /* yacc.c:1646  */
    {
                    int ntype = node_get_type((yyvsp[-2].node));
                    if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                      yyerror_lined("incorrect DOT expression", (yyvsp[-1].lineno));
                      YYABORT;
                    }
                    (yyval.node) = new_lined_node(DOT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)) ;
                  }
#line 2621 "grammar.c" /* yacc.c:1646  */
    break;

  case 29:
#line 339 "grammar.y" /* yacc.c:1646  */
    {
                   int ntype = node_get_type((yyvsp[-2].node));
                   if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                     yyerror_lined("incorrect DOT expression", (yyvsp[-1].lineno));
                     YYABORT;
                   }
                   (yyval.node) = new_lined_node(DOT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)) ;
                  }
#line 2634 "grammar.c" /* yacc.c:1646  */
    break;

  case 30:
#line 348 "grammar.y" /* yacc.c:1646  */
    {
                   /* array may have any expression on the left.
                      The type check will detect any problems */
                   (yyval.node) = new_lined_node(ARRAY, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));
                  }
#line 2644 "grammar.c" /* yacc.c:1646  */
    break;

  case 31:
#line 354 "grammar.y" /* yacc.c:1646  */
    {
                    (yyval.node) = new_lined_node(BIT_SELECTION, (yyvsp[-5].node),
                                        new_lined_node(COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno)), (yyvsp[-4].lineno));
                  }
#line 2653 "grammar.c" /* yacc.c:1646  */
    break;

  case 32:
#line 358 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2659 "grammar.c" /* yacc.c:1646  */
    break;

  case 33:
#line 359 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2665 "grammar.c" /* yacc.c:1646  */
    break;

  case 34:
#line 360 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(CAST_BOOL, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2671 "grammar.c" /* yacc.c:1646  */
    break;

  case 35:
#line 361 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(CAST_WORD1, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2677 "grammar.c" /* yacc.c:1646  */
    break;

  case 36:
#line 362 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NEXT, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2683 "grammar.c" /* yacc.c:1646  */
    break;

  case 37:
#line 363 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(CAST_SIGNED, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2689 "grammar.c" /* yacc.c:1646  */
    break;

  case 38:
#line 364 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(CAST_UNSIGNED, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno)); }
#line 2695 "grammar.c" /* yacc.c:1646  */
    break;

  case 39:
#line 365 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EXTEND, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2701 "grammar.c" /* yacc.c:1646  */
    break;

  case 40:
#line 366 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(WRESIZE, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2707 "grammar.c" /* yacc.c:1646  */
    break;

  case 41:
#line 367 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2713 "grammar.c" /* yacc.c:1646  */
    break;

  case 42:
#line 371 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(WAREAD, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2719 "grammar.c" /* yacc.c:1646  */
    break;

  case 43:
#line 374 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(WAWRITE, (yyvsp[-5].node), new_node(WAWRITE, (yyvsp[-3].node), (yyvsp[-1].node)), (yyvsp[-6].lineno)); }
#line 2725 "grammar.c" /* yacc.c:1646  */
    break;

  case 44:
#line 376 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(COUNT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno)); }
#line 2731 "grammar.c" /* yacc.c:1646  */
    break;

  case 45:
#line 380 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons((yyvsp[0].node), Nil); }
#line 2737 "grammar.c" /* yacc.c:1646  */
    break;

  case 46:
#line 381 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons((yyvsp[-2].node), (yyvsp[0].node)); }
#line 2743 "grammar.c" /* yacc.c:1646  */
    break;

  case 47:
#line 386 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_node(CASE, (yyvsp[0].node), failure_make("case conditions are not exhaustive", FAILURE_CASE_NOT_EXHAUSTIVE, yylineno));}
#line 2749 "grammar.c" /* yacc.c:1646  */
    break;

  case 48:
#line 387 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_node(CASE, (yyvsp[-1].node), (yyvsp[0].node)); }
#line 2755 "grammar.c" /* yacc.c:1646  */
    break;

  case 49:
#line 392 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = build_case_colon_node((yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 2761 "grammar.c" /* yacc.c:1646  */
    break;

  case 51:
#line 397 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(CONCATENATION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2767 "grammar.c" /* yacc.c:1646  */
    break;

  case 53:
#line 402 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(TIMES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2773 "grammar.c" /* yacc.c:1646  */
    break;

  case 54:
#line 403 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(DIVIDE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2779 "grammar.c" /* yacc.c:1646  */
    break;

  case 55:
#line 404 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(MOD, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2785 "grammar.c" /* yacc.c:1646  */
    break;

  case 57:
#line 409 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(PLUS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2791 "grammar.c" /* yacc.c:1646  */
    break;

  case 58:
#line 410 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(MINUS, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2797 "grammar.c" /* yacc.c:1646  */
    break;

  case 60:
#line 414 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(LSHIFT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2803 "grammar.c" /* yacc.c:1646  */
    break;

  case 61:
#line 415 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(RSHIFT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2809 "grammar.c" /* yacc.c:1646  */
    break;

  case 64:
#line 423 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2815 "grammar.c" /* yacc.c:1646  */
    break;

  case 66:
#line 427 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(UNION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 2821 "grammar.c" /* yacc.c:1646  */
    break;

  case 68:
#line 432 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(UNION, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2827 "grammar.c" /* yacc.c:1646  */
    break;

  case 70:
#line 436 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(SETIN, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2833 "grammar.c" /* yacc.c:1646  */
    break;

  case 72:
#line 441 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EQUAL, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2839 "grammar.c" /* yacc.c:1646  */
    break;

  case 73:
#line 442 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NOTEQUAL, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2845 "grammar.c" /* yacc.c:1646  */
    break;

  case 74:
#line 443 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(LT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2851 "grammar.c" /* yacc.c:1646  */
    break;

  case 75:
#line 444 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(GT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2857 "grammar.c" /* yacc.c:1646  */
    break;

  case 76:
#line 445 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(LE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2863 "grammar.c" /* yacc.c:1646  */
    break;

  case 77:
#line 446 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(GE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2869 "grammar.c" /* yacc.c:1646  */
    break;

  case 80:
#line 454 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EX, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2875 "grammar.c" /* yacc.c:1646  */
    break;

  case 81:
#line 455 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(AX, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2881 "grammar.c" /* yacc.c:1646  */
    break;

  case 82:
#line 456 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EF, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2887 "grammar.c" /* yacc.c:1646  */
    break;

  case 83:
#line 457 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(AF, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2893 "grammar.c" /* yacc.c:1646  */
    break;

  case 84:
#line 458 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EG, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2899 "grammar.c" /* yacc.c:1646  */
    break;

  case 85:
#line 459 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(AG, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2905 "grammar.c" /* yacc.c:1646  */
    break;

  case 86:
#line 461 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(AU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2911 "grammar.c" /* yacc.c:1646  */
    break;

  case 87:
#line 463 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 2917 "grammar.c" /* yacc.c:1646  */
    break;

  case 88:
#line 465 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(ABU, new_lined_node(AU, (yyvsp[-4].node), (yyvsp[-1].node), (yyvsp[-6].lineno)), (yyvsp[-2].node), (yyvsp[-6].lineno)); }
#line 2923 "grammar.c" /* yacc.c:1646  */
    break;

  case 89:
#line 467 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EBU, new_lined_node(EU, (yyvsp[-4].node), (yyvsp[-1].node), (yyvsp[-6].lineno)), (yyvsp[-2].node), (yyvsp[-6].lineno)); }
#line 2929 "grammar.c" /* yacc.c:1646  */
    break;

  case 90:
#line 468 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EBF, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 2935 "grammar.c" /* yacc.c:1646  */
    break;

  case 91:
#line 469 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(ABF, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 2941 "grammar.c" /* yacc.c:1646  */
    break;

  case 92:
#line 470 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EBG, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 2947 "grammar.c" /* yacc.c:1646  */
    break;

  case 93:
#line 471 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(ABG, (yyvsp[0].node), (yyvsp[-1].node), (yyvsp[-2].lineno)); }
#line 2953 "grammar.c" /* yacc.c:1646  */
    break;

  case 94:
#line 474 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 2959 "grammar.c" /* yacc.c:1646  */
    break;

  case 96:
#line 481 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(AND, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2965 "grammar.c" /* yacc.c:1646  */
    break;

  case 98:
#line 485 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(OR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2971 "grammar.c" /* yacc.c:1646  */
    break;

  case 99:
#line 486 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(XOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2977 "grammar.c" /* yacc.c:1646  */
    break;

  case 100:
#line 487 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(XNOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2983 "grammar.c" /* yacc.c:1646  */
    break;

  case 102:
#line 491 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(IFF, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2989 "grammar.c" /* yacc.c:1646  */
    break;

  case 104:
#line 496 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(IMPLIES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 2995 "grammar.c" /* yacc.c:1646  */
    break;

  case 108:
#line 509 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_NEXT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3001 "grammar.c" /* yacc.c:1646  */
    break;

  case 109:
#line 510 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_PREC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3007 "grammar.c" /* yacc.c:1646  */
    break;

  case 110:
#line 511 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_NOTPRECNOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3013 "grammar.c" /* yacc.c:1646  */
    break;

  case 111:
#line 512 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_GLOBAL, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3019 "grammar.c" /* yacc.c:1646  */
    break;

  case 112:
#line 513 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_HISTORICAL, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3025 "grammar.c" /* yacc.c:1646  */
    break;

  case 113:
#line 514 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_FUTURE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3031 "grammar.c" /* yacc.c:1646  */
    break;

  case 114:
#line 515 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(OP_ONCE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3037 "grammar.c" /* yacc.c:1646  */
    break;

  case 115:
#line 517 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(NOT, (yyvsp[0].node), Nil, (yyvsp[-1].lineno)); }
#line 3043 "grammar.c" /* yacc.c:1646  */
    break;

  case 117:
#line 526 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(UNTIL, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3049 "grammar.c" /* yacc.c:1646  */
    break;

  case 118:
#line 528 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SINCE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3055 "grammar.c" /* yacc.c:1646  */
    break;

  case 119:
#line 530 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NOT,
                           new_lined_node(UNTIL,
                             new_lined_node(NOT, (yyvsp[-2].node), Nil, node_get_lineno((yyvsp[-2].node))),
                             new_lined_node(NOT, (yyvsp[0].node), Nil, node_get_lineno((yyvsp[0].node))),
                             (yyvsp[-1].lineno)), Nil, (yyvsp[-1].lineno));
                  }
#line 3066 "grammar.c" /* yacc.c:1646  */
    break;

  case 120:
#line 537 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NOT,
                          new_lined_node(SINCE,
                              new_lined_node(NOT, (yyvsp[-2].node), Nil, node_get_lineno((yyvsp[-2].node))),
                              new_lined_node(NOT, (yyvsp[0].node), Nil, node_get_lineno((yyvsp[0].node))),
                              (yyvsp[-1].lineno)), Nil, (yyvsp[-1].lineno));
                  }
#line 3077 "grammar.c" /* yacc.c:1646  */
    break;

  case 122:
#line 547 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(AND, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3083 "grammar.c" /* yacc.c:1646  */
    break;

  case 124:
#line 552 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(OR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3089 "grammar.c" /* yacc.c:1646  */
    break;

  case 125:
#line 553 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(XOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3095 "grammar.c" /* yacc.c:1646  */
    break;

  case 126:
#line 554 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(XNOR,(yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3101 "grammar.c" /* yacc.c:1646  */
    break;

  case 128:
#line 559 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(IFTHENELSE, new_lined_node(COLON, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[-3].lineno)), (yyvsp[0].node), (yyvsp[-3].lineno)); }
#line 3107 "grammar.c" /* yacc.c:1646  */
    break;

  case 130:
#line 564 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(IFF, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3113 "grammar.c" /* yacc.c:1646  */
    break;

  case 132:
#line 569 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(IMPLIES, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno)); }
#line 3119 "grammar.c" /* yacc.c:1646  */
    break;

  case 134:
#line 580 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_SIMPLE)) YYABORT;}
#line 3125 "grammar.c" /* yacc.c:1646  */
    break;

  case 135:
#line 583 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_NEXT)) YYABORT;}
#line 3131 "grammar.c" /* yacc.c:1646  */
    break;

  case 136:
#line 586 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_CTL)) YYABORT;}
#line 3137 "grammar.c" /* yacc.c:1646  */
    break;

  case 137:
#line 589 "grammar.y" /* yacc.c:1646  */
    {if (!isCorrectExp((yyval.node), EXP_LTL)) YYABORT;}
#line 3143 "grammar.c" /* yacc.c:1646  */
    break;

  case 138:
#line 594 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(MINU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 3149 "grammar.c" /* yacc.c:1646  */
    break;

  case 139:
#line 596 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(MAXU, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-5].lineno)); }
#line 3155 "grammar.c" /* yacc.c:1646  */
    break;

  case 140:
#line 604 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(BOOLEAN, Nil, Nil);}
#line 3161 "grammar.c" /* yacc.c:1646  */
    break;

  case 141:
#line 605 "grammar.y" /* yacc.c:1646  */
    {
                yyerror("given token is not supported.");
                YYABORT;
              }
#line 3170 "grammar.c" /* yacc.c:1646  */
    break;

  case 142:
#line 609 "grammar.y" /* yacc.c:1646  */
    {
                yyerror("given token is not supported.");
                YYABORT;
              }
#line 3179 "grammar.c" /* yacc.c:1646  */
    break;

  case 143:
#line 614 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(UNSIGNED_WORD, (yyvsp[-1].node), Nil, (yyvsp[-3].lineno));}
#line 3185 "grammar.c" /* yacc.c:1646  */
    break;

  case 144:
#line 616 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(UNSIGNED_WORD, (yyvsp[-1].node), Nil, (yyvsp[-4].lineno));}
#line 3191 "grammar.c" /* yacc.c:1646  */
    break;

  case 145:
#line 618 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SIGNED_WORD, (yyvsp[-1].node), Nil, (yyvsp[-4].lineno));}
#line 3197 "grammar.c" /* yacc.c:1646  */
    break;

  case 147:
#line 621 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SCALAR, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3203 "grammar.c" /* yacc.c:1646  */
    break;

  case 148:
#line 623 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(WORDARRAY, (yyvsp[-6].node), (yyvsp[-1].node), (yyvsp[-9].lineno));}
#line 3209 "grammar.c" /* yacc.c:1646  */
    break;

  case 149:
#line 625 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(ARRAY_TYPE, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-3].lineno));}
#line 3215 "grammar.c" /* yacc.c:1646  */
    break;

  case 152:
#line 631 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(PROCESS, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3221 "grammar.c" /* yacc.c:1646  */
    break;

  case 153:
#line 634 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(find_atom((yyvsp[0].node)), Nil); free_node((yyvsp[0].node));}
#line 3227 "grammar.c" /* yacc.c:1646  */
    break;

  case 154:
#line 635 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(find_atom((yyvsp[0].node)), (yyvsp[-2].node)); free_node((yyvsp[0].node));}
#line 3233 "grammar.c" /* yacc.c:1646  */
    break;

  case 160:
#line 645 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(DOT, (yyvsp[-2].node), (yyvsp[0].node), (yyvsp[-1].lineno));}
#line 3239 "grammar.c" /* yacc.c:1646  */
    break;

  case 161:
#line 648 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(MODTYPE, (yyvsp[0].node), Nil);}
#line 3245 "grammar.c" /* yacc.c:1646  */
    break;

  case 162:
#line 649 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(MODTYPE, (yyvsp[-2].node), Nil);}
#line 3251 "grammar.c" /* yacc.c:1646  */
    break;

  case 163:
#line 651 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(MODTYPE, (yyvsp[-3].node), (yyvsp[-1].node), node_get_lineno((yyvsp[-3].node)));}
#line 3257 "grammar.c" /* yacc.c:1646  */
    break;

  case 164:
#line 653 "grammar.y" /* yacc.c:1646  */
    {
                    /* $$ = new_lined_node(ARRAY, $2, $4, $1); */
                    /* array of modules is not supported any more.
                       NOTE: In future if there are some syntact conflicts
                       this case can be removed */
                    yyerror_lined("array of modules is no supported", (yyvsp[-3].lineno));
                    YYABORT;
                  }
#line 3270 "grammar.c" /* yacc.c:1646  */
    break;

  case 165:
#line 664 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node),Nil);}
#line 3276 "grammar.c" /* yacc.c:1646  */
    break;

  case 166:
#line 665 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-2].node));}
#line 3282 "grammar.c" /* yacc.c:1646  */
    break;

  case 167:
#line 677 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3288 "grammar.c" /* yacc.c:1646  */
    break;

  case 168:
#line 678 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3294 "grammar.c" /* yacc.c:1646  */
    break;

  case 169:
#line 682 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(MODULE, (yyvsp[-1].node), (yyvsp[0].node), (yyvsp[-2].lineno));}
#line 3300 "grammar.c" /* yacc.c:1646  */
    break;

  case 170:
#line 684 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(MODTYPE, (yyvsp[0].node), Nil);}
#line 3306 "grammar.c" /* yacc.c:1646  */
    break;

  case 171:
#line 685 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(MODTYPE, (yyvsp[-2].node), Nil);}
#line 3312 "grammar.c" /* yacc.c:1646  */
    break;

  case 172:
#line 687 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(MODTYPE, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 3318 "grammar.c" /* yacc.c:1646  */
    break;

  case 173:
#line 689 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(find_atom((yyvsp[0].node)), Nil); free_node((yyvsp[0].node));}
#line 3324 "grammar.c" /* yacc.c:1646  */
    break;

  case 174:
#line 690 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(find_atom((yyvsp[0].node)), (yyvsp[-2].node)); free_node((yyvsp[0].node));}
#line 3330 "grammar.c" /* yacc.c:1646  */
    break;

  case 175:
#line 695 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3336 "grammar.c" /* yacc.c:1646  */
    break;

  case 176:
#line 696 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3342 "grammar.c" /* yacc.c:1646  */
    break;

  case 177:
#line 697 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3348 "grammar.c" /* yacc.c:1646  */
    break;

  case 199:
#line 729 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(VAR, Nil, Nil, (yyvsp[0].lineno));}
#line 3354 "grammar.c" /* yacc.c:1646  */
    break;

  case 200:
#line 730 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(VAR, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3360 "grammar.c" /* yacc.c:1646  */
    break;

  case 201:
#line 733 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(FROZENVAR, Nil, Nil, (yyvsp[0].lineno));}
#line 3366 "grammar.c" /* yacc.c:1646  */
    break;

  case 202:
#line 734 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(FROZENVAR, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3372 "grammar.c" /* yacc.c:1646  */
    break;

  case 203:
#line 737 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(IVAR, Nil, Nil, (yyvsp[0].lineno));}
#line 3378 "grammar.c" /* yacc.c:1646  */
    break;

  case 204:
#line 738 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(IVAR, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3384 "grammar.c" /* yacc.c:1646  */
    break;

  case 205:
#line 741 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3390 "grammar.c" /* yacc.c:1646  */
    break;

  case 206:
#line 742 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3396 "grammar.c" /* yacc.c:1646  */
    break;

  case 207:
#line 743 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3402 "grammar.c" /* yacc.c:1646  */
    break;

  case 208:
#line 745 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3408 "grammar.c" /* yacc.c:1646  */
    break;

  case 209:
#line 746 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3414 "grammar.c" /* yacc.c:1646  */
    break;

  case 210:
#line 747 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3420 "grammar.c" /* yacc.c:1646  */
    break;

  case 211:
#line 749 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3426 "grammar.c" /* yacc.c:1646  */
    break;

  case 212:
#line 750 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3432 "grammar.c" /* yacc.c:1646  */
    break;

  case 213:
#line 751 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3438 "grammar.c" /* yacc.c:1646  */
    break;

  case 214:
#line 754 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3444 "grammar.c" /* yacc.c:1646  */
    break;

  case 215:
#line 756 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3450 "grammar.c" /* yacc.c:1646  */
    break;

  case 216:
#line 758 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COLON, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3456 "grammar.c" /* yacc.c:1646  */
    break;

  case 217:
#line 763 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(DEFINE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3462 "grammar.c" /* yacc.c:1646  */
    break;

  case 218:
#line 765 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3468 "grammar.c" /* yacc.c:1646  */
    break;

  case 219:
#line 766 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3474 "grammar.c" /* yacc.c:1646  */
    break;

  case 220:
#line 767 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3480 "grammar.c" /* yacc.c:1646  */
    break;

  case 221:
#line 771 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3486 "grammar.c" /* yacc.c:1646  */
    break;

  case 222:
#line 773 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));
                                 /* Note that array-define is declared
                                    as normal define.
                                    Then compile_instantiate in compileFlatten.c
                                    distinguish them by detecting
                                    ARRAY_DEF on right hand side.
                                   */
                                 }
#line 3499 "grammar.c" /* yacc.c:1646  */
    break;

  case 223:
#line 785 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(DEFINE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3505 "grammar.c" /* yacc.c:1646  */
    break;

  case 224:
#line 789 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3511 "grammar.c" /* yacc.c:1646  */
    break;

  case 225:
#line 790 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons(new_lined_node(EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno)), (yyvsp[-4].node));}
#line 3517 "grammar.c" /* yacc.c:1646  */
    break;

  case 226:
#line 791 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3523 "grammar.c" /* yacc.c:1646  */
    break;

  case 227:
#line 795 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) =  new_lined_node(ARRAY_DEF, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3529 "grammar.c" /* yacc.c:1646  */
    break;

  case 228:
#line 796 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) =  new_lined_node(ARRAY_DEF, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3535 "grammar.c" /* yacc.c:1646  */
    break;

  case 229:
#line 800 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3541 "grammar.c" /* yacc.c:1646  */
    break;

  case 230:
#line 801 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[-2].node), (yyvsp[0].node));}
#line 3547 "grammar.c" /* yacc.c:1646  */
    break;

  case 231:
#line 805 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[-2].node), (yyvsp[0].node));}
#line 3553 "grammar.c" /* yacc.c:1646  */
    break;

  case 232:
#line 806 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node),Nil);}
#line 3559 "grammar.c" /* yacc.c:1646  */
    break;

  case 233:
#line 810 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(ASSIGN, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3565 "grammar.c" /* yacc.c:1646  */
    break;

  case 234:
#line 812 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3571 "grammar.c" /* yacc.c:1646  */
    break;

  case 235:
#line 813 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(AND, (yyvsp[-1].node), (yyvsp[0].node));}
#line 3577 "grammar.c" /* yacc.c:1646  */
    break;

  case 236:
#line 814 "grammar.y" /* yacc.c:1646  */
    { SYNTAX_ERROR_HANDLING((yyval.node), (yyvsp[-1].node)); }
#line 3583 "grammar.c" /* yacc.c:1646  */
    break;

  case 237:
#line 817 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(EQDEF, (yyvsp[-3].node), (yyvsp[-1].node), (yyvsp[-2].lineno));}
#line 3589 "grammar.c" /* yacc.c:1646  */
    break;

  case 238:
#line 819 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EQDEF,
                                        new_lined_node(SMALLINIT, (yyvsp[-4].node), Nil, (yyvsp[-6].lineno)),
                                        (yyvsp[-1].node), (yyvsp[-2].lineno));
                  }
#line 3598 "grammar.c" /* yacc.c:1646  */
    break;

  case 239:
#line 824 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = new_lined_node(EQDEF,
                                        new_lined_node(NEXT, (yyvsp[-4].node), Nil, (yyvsp[-6].lineno)),
                                        (yyvsp[-1].node), (yyvsp[-2].lineno));
                  }
#line 3607 "grammar.c" /* yacc.c:1646  */
    break;

  case 240:
#line 831 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(INIT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3613 "grammar.c" /* yacc.c:1646  */
    break;

  case 241:
#line 833 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(INVAR, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3619 "grammar.c" /* yacc.c:1646  */
    break;

  case 242:
#line 835 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(TRANS, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3625 "grammar.c" /* yacc.c:1646  */
    break;

  case 243:
#line 839 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(JUSTICE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3631 "grammar.c" /* yacc.c:1646  */
    break;

  case 244:
#line 842 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(JUSTICE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3637 "grammar.c" /* yacc.c:1646  */
    break;

  case 245:
#line 847 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COMPASSION, cons((yyvsp[-4].node),(yyvsp[-2].node)), Nil, (yyvsp[-6].lineno));}
#line 3643 "grammar.c" /* yacc.c:1646  */
    break;

  case 246:
#line 851 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3649 "grammar.c" /* yacc.c:1646  */
    break;

  case 247:
#line 852 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 3655 "grammar.c" /* yacc.c:1646  */
    break;

  case 248:
#line 854 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(INVARSPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3661 "grammar.c" /* yacc.c:1646  */
    break;

  case 249:
#line 855 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(INVARSPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 3667 "grammar.c" /* yacc.c:1646  */
    break;

  case 250:
#line 858 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3673 "grammar.c" /* yacc.c:1646  */
    break;

  case 251:
#line 859 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 3679 "grammar.c" /* yacc.c:1646  */
    break;

  case 252:
#line 861 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3685 "grammar.c" /* yacc.c:1646  */
    break;

  case 253:
#line 862 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3691 "grammar.c" /* yacc.c:1646  */
    break;

  case 254:
#line 863 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 3697 "grammar.c" /* yacc.c:1646  */
    break;

  case 255:
#line 864 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 3703 "grammar.c" /* yacc.c:1646  */
    break;

  case 256:
#line 867 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3709 "grammar.c" /* yacc.c:1646  */
    break;

  case 257:
#line 868 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 3715 "grammar.c" /* yacc.c:1646  */
    break;

  case 258:
#line 871 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(LTLSPEC, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3721 "grammar.c" /* yacc.c:1646  */
    break;

  case 259:
#line 872 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(LTLSPEC, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 3727 "grammar.c" /* yacc.c:1646  */
    break;

  case 260:
#line 875 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 3733 "grammar.c" /* yacc.c:1646  */
    break;

  case 261:
#line 876 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 3739 "grammar.c" /* yacc.c:1646  */
    break;

  case 262:
#line 878 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COMPUTE, (yyvsp[0].node), Nil, (yyvsp[-1].lineno));}
#line 3745 "grammar.c" /* yacc.c:1646  */
    break;

  case 263:
#line 879 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COMPUTE, (yyvsp[0].node), (yyvsp[-2].node), (yyvsp[-4].lineno));}
#line 3751 "grammar.c" /* yacc.c:1646  */
    break;

  case 264:
#line 884 "grammar.y" /* yacc.c:1646  */
    {
  if (nusmv_parse_psl() != 0) {
    YYABORT;
  }
  (yyval.node) = new_lined_node(PSLSPEC, psl_parsed_tree, psl_property_name, (yyvsp[0].lineno));
  psl_property_name = Nil;
}
#line 3763 "grammar.c" /* yacc.c:1646  */
    break;

  case 265:
#line 894 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(CONSTANTS, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3769 "grammar.c" /* yacc.c:1646  */
    break;

  case 266:
#line 898 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 3775 "grammar.c" /* yacc.c:1646  */
    break;

  case 267:
#line 899 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3781 "grammar.c" /* yacc.c:1646  */
    break;

  case 268:
#line 900 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-2].node));}
#line 3787 "grammar.c" /* yacc.c:1646  */
    break;

  case 269:
#line 904 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons((yyvsp[0].node), Nil);}
#line 3793 "grammar.c" /* yacc.c:1646  */
    break;

  case 270:
#line 905 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 3799 "grammar.c" /* yacc.c:1646  */
    break;

  case 271:
#line 910 "grammar.y" /* yacc.c:1646  */
    {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }
#line 3808 "grammar.c" /* yacc.c:1646  */
    break;

  case 272:
#line 915 "grammar.y" /* yacc.c:1646  */
    {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }
#line 3817 "grammar.c" /* yacc.c:1646  */
    break;

  case 273:
#line 921 "grammar.y" /* yacc.c:1646  */
    {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }
#line 3826 "grammar.c" /* yacc.c:1646  */
    break;

  case 274:
#line 928 "grammar.y" /* yacc.c:1646  */
    {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }
#line 3835 "grammar.c" /* yacc.c:1646  */
    break;

  case 275:
#line 935 "grammar.y" /* yacc.c:1646  */
    {
                    yyerror("given token is not supported.");
                    YYABORT;
                  }
#line 3844 "grammar.c" /* yacc.c:1646  */
    break;

  case 276:
#line 942 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(ISA, (yyvsp[0].node), Nil);}
#line 3850 "grammar.c" /* yacc.c:1646  */
    break;

  case 278:
#line 946 "grammar.y" /* yacc.c:1646  */
    {}
#line 3856 "grammar.c" /* yacc.c:1646  */
    break;

  case 280:
#line 955 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3862 "grammar.c" /* yacc.c:1646  */
    break;

  case 281:
#line 956 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3868 "grammar.c" /* yacc.c:1646  */
    break;

  case 282:
#line 957 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(ARRAY, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 3874 "grammar.c" /* yacc.c:1646  */
    break;

  case 283:
#line 959 "grammar.y" /* yacc.c:1646  */
    { node_ptr tmp = new_lined_node(NUMBER,
                                                      PTR_FROM_INT(node_ptr, -node_get_int((yyvsp[-1].node))),
                                                      Nil,
                                                      (yyvsp[-2].lineno));
                        (yyval.node) = new_node(ARRAY, (yyvsp[-4].node), tmp);
                      }
#line 3885 "grammar.c" /* yacc.c:1646  */
    break;

  case 285:
#line 968 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(SELF,Nil,Nil);}
#line 3891 "grammar.c" /* yacc.c:1646  */
    break;

  case 286:
#line 969 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3897 "grammar.c" /* yacc.c:1646  */
    break;

  case 287:
#line 970 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 3903 "grammar.c" /* yacc.c:1646  */
    break;

  case 288:
#line 971 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(ARRAY, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 3909 "grammar.c" /* yacc.c:1646  */
    break;

  case 289:
#line 978 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = (yyvsp[0].node);}
#line 3915 "grammar.c" /* yacc.c:1646  */
    break;

  case 290:
#line 979 "grammar.y" /* yacc.c:1646  */
    {return(1);}
#line 3921 "grammar.c" /* yacc.c:1646  */
    break;

  case 291:
#line 980 "grammar.y" /* yacc.c:1646  */
    {return(1);}
#line 3927 "grammar.c" /* yacc.c:1646  */
    break;

  case 292:
#line 984 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(INIT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3933 "grammar.c" /* yacc.c:1646  */
    break;

  case 293:
#line 986 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(JUSTICE, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3939 "grammar.c" /* yacc.c:1646  */
    break;

  case 294:
#line 988 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(TRANS, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3945 "grammar.c" /* yacc.c:1646  */
    break;

  case 295:
#line 990 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(CONSTRAINT, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3951 "grammar.c" /* yacc.c:1646  */
    break;

  case 296:
#line 993 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(SIMPWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 3957 "grammar.c" /* yacc.c:1646  */
    break;

  case 297:
#line 994 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(NEXTWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 3963 "grammar.c" /* yacc.c:1646  */
    break;

  case 298:
#line 995 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(CTLWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 3969 "grammar.c" /* yacc.c:1646  */
    break;

  case 299:
#line 996 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(LTLWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 3975 "grammar.c" /* yacc.c:1646  */
    break;

  case 300:
#line 997 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COMPWFF, node2maincontext((yyvsp[0].node)), Nil, (yyvsp[-1].lineno));}
#line 3981 "grammar.c" /* yacc.c:1646  */
    break;

  case 301:
#line 998 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_lined_node(COMPID, (yyvsp[-1].node), Nil, (yyvsp[-2].lineno));}
#line 3987 "grammar.c" /* yacc.c:1646  */
    break;

  case 302:
#line 1000 "grammar.y" /* yacc.c:1646  */
    {
                  yyerror("given token is not supported.");
                  YYABORT;
                }
#line 3996 "grammar.c" /* yacc.c:1646  */
    break;

  case 303:
#line 1007 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = find_atom((yyvsp[0].node)); free_node((yyvsp[0].node)); }
#line 4002 "grammar.c" /* yacc.c:1646  */
    break;

  case 304:
#line 1008 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = find_node(DOT, (yyvsp[-2].node), (yyvsp[0].node));}
#line 4008 "grammar.c" /* yacc.c:1646  */
    break;

  case 305:
#line 1009 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = find_node(ARRAY, (yyvsp[-3].node), (yyvsp[-1].node));}
#line 4014 "grammar.c" /* yacc.c:1646  */
    break;

  case 306:
#line 1012 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 4020 "grammar.c" /* yacc.c:1646  */
    break;

  case 307:
#line 1013 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = new_node(CONTEXT, (yyvsp[-1].node), (yyvsp[-3].node));}
#line 4026 "grammar.c" /* yacc.c:1646  */
    break;

  case 308:
#line 1019 "grammar.y" /* yacc.c:1646  */
    {
  if (PARSE_MODULES != parse_mode_flag) {
    yyerror("unexpected MODULE definition encountered during parsing");
    YYABORT;
  }
#if HAVE_GAME
  if (opt_game_game(OptsHandler_get_instance())) {
    Game_Mode_Exit();
  }
  game_parser_spec_list = Nil;
  game_parser_player_1 = Nil;
  game_parser_player_2 = Nil;
#endif
}
#line 4045 "grammar.c" /* yacc.c:1646  */
    break;

  case 309:
#line 1034 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                  if (!opt_game_game(OptsHandler_get_instance())) {
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
                    parsed_tree = new_node(GAME,
                                           game_parser_spec_list,
                                           cons(game_parser_player_1,
                                                cons(game_parser_player_2, 
                                                     (yyvsp[0].node))));
                  }
#else /* no GAME */
                  parsed_tree = (yyvsp[0].node);            
#endif
                }
#line 4074 "grammar.c" /* yacc.c:1646  */
    break;

  case 310:
#line 1058 "grammar.y" /* yacc.c:1646  */
    {
                  if (PARSE_COMMAND != parse_mode_flag) {
                    yyerror("unexpected command encountered during parsing");
                    YYABORT;
                  }
                }
#line 4085 "grammar.c" /* yacc.c:1646  */
    break;

  case 311:
#line 1064 "grammar.y" /* yacc.c:1646  */
    {parsed_tree = (yyvsp[0].node);}
#line 4091 "grammar.c" /* yacc.c:1646  */
    break;

  case 312:
#line 1065 "grammar.y" /* yacc.c:1646  */
    {
                  if (PARSE_LTL_EXPR != parse_mode_flag){
                    yyerror("unexpected expression encountered during parsing");
                    YYABORT;
                  }
                }
#line 4102 "grammar.c" /* yacc.c:1646  */
    break;

  case 313:
#line 1071 "grammar.y" /* yacc.c:1646  */
    {parsed_tree = (yyvsp[0].node);}
#line 4108 "grammar.c" /* yacc.c:1646  */
    break;

  case 314:
#line 1079 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node),Nil);}
#line 4114 "grammar.c" /* yacc.c:1646  */
    break;

  case 315:
#line 1080 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-2].node));}
#line 4120 "grammar.c" /* yacc.c:1646  */
    break;

  case 316:
#line 1095 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), Nil);}
#line 4126 "grammar.c" /* yacc.c:1646  */
    break;

  case 317:
#line 1096 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = Nil;}
#line 4132 "grammar.c" /* yacc.c:1646  */
    break;

  case 318:
#line 1097 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node));}
#line 4138 "grammar.c" /* yacc.c:1646  */
    break;

  case 319:
#line 1098 "grammar.y" /* yacc.c:1646  */
    {(yyval.node) = (yyvsp[-1].node);}
#line 4144 "grammar.c" /* yacc.c:1646  */
    break;

  case 320:
#line 1109 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                       /* check that the game is not redeclared */
                       if (opt_game_game(OptsHandler_get_instance())) {
                         yyerror_lined("redefinition of a GAME", (yyvsp[-1].lineno));
                       }
                       else {
                         Game_Mode_Enter();
                       }
#else
                       yyerror_lined("GAME declaration cannot be processes "
                                     "because GAME package is not set up\n"
                                     "Check --enable-addons=game option of "
                                     "the configure script\n", (yyvsp[-1].lineno));
                       YYABORT;
#endif
                       game_parser_spec_list = (yyvsp[0].node);
                       (yyval.node) = Nil;
                     }
#line 4168 "grammar.c" /* yacc.c:1646  */
    break;

  case 321:
#line 1131 "grammar.y" /* yacc.c:1646  */
    {(yyval.node)=Nil;}
#line 4174 "grammar.c" /* yacc.c:1646  */
    break;

  case 322:
#line 1133 "grammar.y" /* yacc.c:1646  */
    {if (Nil != (yyvsp[-1].node)) (yyval.node) = cons((yyvsp[-1].node),(yyvsp[0].node)); else (yyval.node) = (yyvsp[0].node);}
#line 4180 "grammar.c" /* yacc.c:1646  */
    break;

  case 323:
#line 1141 "grammar.y" /* yacc.c:1646  */
    {
                       /* a player definition is converted to a module
                          definitino with a special name. This is done
                          to simplify the further flattening
                       */
                       if (game_parser_player_1 != Nil) {
                         yyerror_lined("redefinition of a PLAYER_1", (yyvsp[-1].lineno));
                         YYABORT;
                       }
                       game_parser_player_1 = new_lined_node(MODULE,
                           new_node(MODTYPE,
                             new_node(ATOM,(node_ptr)find_string("PLAYER_1"),
                                      Nil), Nil),  (yyvsp[0].node), (yyvsp[-1].lineno));
                       (yyval.node)=Nil;
                     }
#line 4200 "grammar.c" /* yacc.c:1646  */
    break;

  case 324:
#line 1157 "grammar.y" /* yacc.c:1646  */
    {
                       /* a player definition is converted to a module
                          definitino with a special name. This is done
                          to simplify the further flattening
                       */
                       if (game_parser_player_2 != Nil) {
                         yyerror_lined("redefinition of a PLAYER_2", (yyvsp[-1].lineno));
                         YYABORT;
                       }
                       game_parser_player_2 = new_lined_node(MODULE,
                           new_node(MODTYPE,
                             new_node(ATOM,(node_ptr)find_string("PLAYER_2"),
                                      Nil), Nil), (yyvsp[0].node), (yyvsp[-1].lineno));
                       (yyval.node)=Nil;
                     }
#line 4220 "grammar.c" /* yacc.c:1646  */
    break;

  case 332:
#line 1189 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = Nil; }
#line 4226 "grammar.c" /* yacc.c:1646  */
    break;

  case 333:
#line 1190 "grammar.y" /* yacc.c:1646  */
    { (yyval.node) = cons((yyvsp[0].node), (yyvsp[-1].node)); }
#line 4232 "grammar.c" /* yacc.c:1646  */
    break;

  case 341:
#line 1207 "grammar.y" /* yacc.c:1646  */
    {(yyval.lineno)=1;}
#line 4238 "grammar.c" /* yacc.c:1646  */
    break;

  case 342:
#line 1208 "grammar.y" /* yacc.c:1646  */
    {(yyval.lineno)=2;}
#line 4244 "grammar.c" /* yacc.c:1646  */
    break;

  case 343:
#line 1211 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(REACHTARGET, NODE_FROM_INT((yyvsp[-2].lineno)), (yyvsp[-1].node), (yyvsp[-3].lineno));
#endif
                       }
#line 4254 "grammar.c" /* yacc.c:1646  */
    break;

  case 344:
#line 1218 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(AVOIDTARGET, NODE_FROM_INT((yyvsp[-2].lineno)), (yyvsp[-1].node), (yyvsp[-3].lineno));
#endif
                       }
#line 4264 "grammar.c" /* yacc.c:1646  */
    break;

  case 345:
#line 1225 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(REACHDEADLOCK, NODE_FROM_INT((yyvsp[-1].lineno)), Nil, (yyvsp[-2].lineno));
#endif
                       }
#line 4274 "grammar.c" /* yacc.c:1646  */
    break;

  case 346:
#line 1232 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(AVOIDDEADLOCK, NODE_FROM_INT((yyvsp[-1].lineno)), Nil, (yyvsp[-2].lineno));
#endif
}
#line 4284 "grammar.c" /* yacc.c:1646  */
    break;

  case 347:
#line 1240 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(BUCHIGAME, NODE_FROM_INT((yyvsp[-4].lineno)),
                                             new_lined_node(GAME_EXP_LIST,
                                                            reverse((yyvsp[-2].node)), Nil, (yyvsp[-3].lineno)),
                                             (yyvsp[-5].lineno));
#endif
}
#line 4297 "grammar.c" /* yacc.c:1646  */
    break;

  case 348:
#line 1250 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(LTLGAME, NODE_FROM_INT((yyvsp[-2].lineno)), (yyvsp[-1].node), (yyvsp[-3].lineno));
#endif
                       }
#line 4307 "grammar.c" /* yacc.c:1646  */
    break;

  case 349:
#line 1259 "grammar.y" /* yacc.c:1646  */
    {
#if HAVE_GAME
                         (yyval.node) = new_lined_node(GENREACTIVITY, NODE_FROM_INT((yyvsp[-8].lineno)),
                                             new_lined_node(GAME_TWO_EXP_LISTS,
                                                            reverse((yyvsp[-6].node)), reverse((yyvsp[-2].node)), (yyvsp[-4].lineno)),
                                             (yyvsp[-9].lineno));
#endif
                       }
#line 4320 "grammar.c" /* yacc.c:1646  */
    break;


#line 4324 "grammar.c" /* yacc.c:1646  */
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
#line 1269 "grammar.y" /* yacc.c:1906  */

  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/grammar.y.3.50 */
/***************************************************************  -*-C-*-  ***/

/* Additional source code */

/* outputs the current token with the provided string and then may terminate */
void yyerror(char *s)
{
  /* In the input.l file we explicity tell flex that we want a pointer
     (see man flex -> %pointer). So we don't need to check if yytext
     is declared as pointer or as array  */
  extern char* yytext;
  extern int yylineno;
  OptsHandler_ptr opmgr = OptsHandler_get_instance();
  
  if (OptsHandler_get_bool_option_value(opmgr, OPT_PARSER_IS_LAX)) {
    parser_add_syntax_error(get_input_file(opmgr), yylineno, yytext, s);
  }
  else {
    start_parsing_err();
    fprintf(nusmv_stderr, "at token \"%s\": %s\n", yytext, s);
    if (opt_batch(opmgr)) { finish_parsing_err(); }
  }
}

/* the same as yyerror, except at first it sets the line number and does
 not output the current token
*/
void yyerror_lined(const char *s, int line)
{
  extern char* yytext;
  extern int yylineno;
  OptsHandler_ptr opmgr = OptsHandler_get_instance();

  /*set the line number */
  yylineno = line;

  if (OptsHandler_get_bool_option_value(opmgr, OPT_PARSER_IS_LAX)) {
    parser_add_syntax_error(get_input_file(opmgr), line, yytext, s);
  }
  else {
    start_parsing_err();
    fprintf(nusmv_stderr, ": %s\n", s);
    if (opt_batch(opmgr)) { finish_parsing_err(); }
  }
}

int yywrap()
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
    ctx = CompileFlatten_concat_contexts(Nil, car(node));
    return find_node(CONTEXT, ctx, cdr(node));
  }

  /* an atom, array or dot */
  return find_node(CONTEXT, Nil, node);
}

/* This functions build the COLON node for case expressions.  If
   backward compatibility is enabled, and the condition expression is
   found to be the constant "1", then a warning is printed and the
   condition is replaced with TRUE. */
static node_ptr build_case_colon_node(node_ptr l,
                                      node_ptr r,
                                      int linum)
{
  node_ptr res;

  static int user_warned = 0;

  if (opt_backward_comp(OptsHandler_get_instance()) &&
      (NUMBER == node_get_type(l)) && (1 == NODE_TO_INT(car(l)))) {

    /* Print this warning only once. */
    if (!user_warned) {
      fprintf(nusmv_stderr,
              "\nWARNING *** Option backward_compatibility (-old) is deprecate ***\n");
      fprintf(nusmv_stderr,
              "WARNING *** and will no longer be supported in future NuSMV versions. ***\n\n");
      user_warned = 1;
    }

    fprintf(nusmv_stderr, "WARNING (");

    if (get_input_file(OptsHandler_get_instance())) {
      fprintf(nusmv_stderr, "file %s", get_input_file(OptsHandler_get_instance()));
    }
    else fprintf(nusmv_stderr, "file stdin");

    fprintf(nusmv_stderr,
            ", line %d) : Deprecated use of \"1\" for case condition\n", linum);

    res = new_lined_node(COLON, new_node(TRUEEXP, Nil, Nil), r, linum);
  }
  else {
    res = new_lined_node(COLON, l, r, linum);
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
      if (EXP_LTL == expectedKind || EXP_CTL == expectedKind) {
        return isCorrectExp(car(exp), EXP_SIMPLE);
      }
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
      if (EXP_LTL == expectedKind || EXP_CTL == expectedKind) {
        return isCorrectExp(car(exp), EXP_SIMPLE)
          && isCorrectExp(cdr(exp), EXP_SIMPLE);
      }
      /* binary opertors compatible LTL and CTL operator */
    case AND: case OR: case XOR: case XNOR: case IFF: case IMPLIES:
      return isCorrectExp(car(exp), expectedKind)
        && isCorrectExp(cdr(exp), expectedKind);

      /* next expression */
    case NEXT:
      if (EXP_NEXT != expectedKind) {
        yyerror_lined("unexpected 'next' operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_SIMPLE); /* NEXT cannot contain NEXT */

      /* CTL unary expressions */
    case EX: case AX: case EF: case AF: case EG: case AG:
    case ABU: case EBU:
    case EBF: case ABF: case EBG: case ABG:
      if (EXP_CTL != expectedKind) {
        yyerror_lined("unexpected CTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_CTL); /* continue to check CTL */

      /* CTL binary expressions */
    case AU: case EU:
      if (EXP_CTL != expectedKind) {
        yyerror_lined("unexpected CTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_CTL)
        && isCorrectExp(cdr(exp), EXP_CTL); /* continue to check CTL */


      /* LTL unary expressions */
    case OP_NEXT: case OP_PREC: case OP_NOTPRECNOT: case OP_GLOBAL:
    case OP_HISTORICAL: case OP_FUTURE: case OP_ONCE:
      if (EXP_LTL != expectedKind) {
        yyerror_lined("unexpected LTL operator", node_get_lineno(exp));
        return false;
      }
      return isCorrectExp(car(exp), EXP_LTL); /* continue to check LTL */


      /* LTL binary expressions */
    case UNTIL: case SINCE:
      if (EXP_LTL != expectedKind) {
        yyerror_lined("unexpected LTL operator", node_get_lineno(exp));
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

  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/grammar.y.3.50 */
