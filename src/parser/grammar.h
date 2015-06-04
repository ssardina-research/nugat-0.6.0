/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison interface for Yacc-like parsers in C

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

#ifndef YY_YY_GRAMMAR_H_INCLUDED
# define YY_YY_GRAMMAR_H_INCLUDED
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
#line 125 "grammar.y" /* yacc.c:1909  */

  node_ptr node;
  int lineno;

#line 363 "grammar.h" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_GRAMMAR_H_INCLUDED  */
