  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/grammar.y.1.50 */
/***************************************************************  -*-C-*-  ***/
%{
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
%}

%union {
  node_ptr node;
  int lineno;
}

/*
  All of the terminal grammar symbols (tokens recognized by the
  lexical analyzer) Note: all binary operators associate from left to
  right. The priority of operators is coded into the syntax rules,
  i.e. the priority of operators in the token declarations below is
  of not importance.

  Note: The following token are not used inside the grammar, but are
  used by other modules inside the system (i.e. the compiler, mc).
  TOK_CONTEXT TOK_EU TOK_AU TOK_EBU TOK_ABU TOK_MINU TOK_MAXU
  TOK_CONS TOK_BIT
*/

%left <lineno> TOK_CONSTRAINT
%left <lineno> TOK_MODULE TOK_PROCESS TOK_CONTEXT TOK_EU TOK_AU TOK_EBU TOK_ABU TOK_MINU TOK_MAXU
%left <lineno> TOK_VAR TOK_FROZENVAR TOK_IVAR TOK_DEFINE TOK_ARRAY_DEFINE TOK_INIT TOK_TRANS TOK_INVAR TOK_SPEC TOK_CTLSPEC TOK_LTLSPEC TOK_COMPUTE TOK_NAME
%left <lineno> TOK_PSLSPEC
%left <lineno> TOK_CONSTANTS
%left <lineno> TOK_INVARSPEC TOK_FAIRNESS TOK_COMPASSION TOK_JUSTICE
%left <lineno> TOK_ISA TOK_ASSIGN
%left <lineno> TOK_OF TOK_CONS TOK_SEMI
%left <lineno> TOK_LP TOK_RP TOK_RB TOK_LCB TOK_RCB
%left <lineno> TOK_EQDEF TOK_TWODOTS
%left <lineno> TOK_SELF
%left <lineno> TOK_CASE TOK_ESAC TOK_COLON
%left <lineno> TOK_INCONTEXT TOK_SIMPWFF TOK_NEXTWFF TOK_LTLWFF TOK_LTLPSL TOK_CTLWFF TOK_COMPWFF TOK_COMPID
%left <lineno> TOK_ARRAY  TOK_BOOLEAN TOK_INTEGER TOK_REAL TOK_WORD
%left <lineno> TOK_BOOL TOK_WORD1
%left <lineno> TOK_WAREAD TOK_WAWRITE
%left <lineno> TOK_SIGNED TOK_UNSIGNED TOK_EXTEND TOK_UWCONST TOK_SWCONST TOK_WRESIZE TOK_WSIZEOF TOK_WTOINT TOK_COUNT

%left <node> TOK_ATOM TOK_FALSEEXP TOK_TRUEEXP
%left <node> TOK_NUMBER TOK_NUMBER_FRAC TOK_NUMBER_REAL TOK_NUMBER_EXP
%left <node> TOK_NUMBER_WORD

%left  <lineno> TOK_COMMA TOK_IMPLIES TOK_IFF TOK_OR TOK_XOR TOK_XNOR TOK_AND TOK_NOT TOK_QUESTIONMARK
%left  <lineno> TOK_EX TOK_AX TOK_EF TOK_AF TOK_EG TOK_AG TOK_EE TOK_AA
%left  <lineno> TOK_SINCE TOK_UNTIL TOK_TRIGGERED TOK_RELEASES
%left  <lineno> TOK_EBF TOK_EBG TOK_ABF TOK_ABG TOK_BUNTIL TOK_MMIN TOK_MMAX
%left  <lineno> TOK_OP_NEXT TOK_OP_GLOBAL TOK_OP_FUTURE
%left  <lineno> TOK_OP_PREC TOK_OP_NOTPRECNOT TOK_OP_HISTORICAL TOK_OP_ONCE
%left  <lineno> TOK_EQUAL TOK_NOTEQUAL TOK_LT TOK_GT TOK_LE TOK_GE
%left  <lineno> TOK_UNION TOK_SETIN TOK_LSHIFT TOK_RSHIFT TOK_LROTATE TOK_RROTATE
%left  <lineno> TOK_MOD TOK_PLUS TOK_MINUS TOK_TIMES TOK_DIVIDE
%left  <lineno> TOK_NEXT TOK_SMALLINIT TOK_CONCATENATION
%left  <lineno> TOK_LB TOK_DOT TOK_BIT


%nonassoc <lineno> TOK_PRED TOK_PREDSLIST TOK_MIRROR

/* all nonterminals return a parse tree node */
%type <node> number integer number_word number_frac number_real number_exp subrange subrangetype

%type <node> constant primary_expr case_element_expr case_element_list_expr count_param_list
%type <node> concatination_expr multiplicative_expr
%type <node> additive_expr shift_expr
%type <node> set_expr set_list_expr union_expr in_expr relational_expr
%type <node> ctl_expr pure_ctl_expr ctl_and_expr
%type <node> ctl_or_expr ctl_iff_expr ctl_implies_expr ctl_basic_expr
%type <node> ltl_binary_expr ltl_unary_expr pure_ltl_unary_expr
%type <node> and_expr or_expr iff_expr implies_expr basic_expr ite_expr
%type <node> simple_expression next_expression ctl_expression ltl_expression

%type <node> itype type module_type
%type <node> type_value_list type_value complex_atom next_list_expression

%type <node> module_list module module_sign atom_list
%type <node> declarations declaration
%type <node> var frozen_var var_decl var_decl_list
%type <node> input_var ivar_decl fvar_decl ivar_decl_list fvar_decl_list
%type <node> define_decls define_list define

%type <node> array_contents array_expression_list array_expression
%type <node> array_define_list array_define

%type <node> assign assign_list one_assign
%type <node> init invar trans
%type <node> fairness justice compassion
%type <node> invarspec ctlspec ltlspec pslspec compute
%type <node> _invarspec _ctlspec _ltlspec _compute
%type <node> constants constants_expression
%type <node> compute_expression
%type <node> isa
%type <node> predicate predicate_list mirror


%type <node> decl_var_id var_id

%type <node> command command_case context _simpwff


%start game_begin 
  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/grammar.y.1.50 */
  /* BEGINS: grammar.y.1.55 */
/***************************************************************  -*-C-*-  ***/
%{
#if HAVE_GAME
#include "addons/game/parser/game_symbols.h"
#include "addons/game/game.h"
#endif

  /* below vars are used if input file contains game definition */
  static node_ptr game_parser_spec_list = Nil;
  static node_ptr game_parser_player_1 = Nil;
  static node_ptr game_parser_player_2 = Nil;
%}

%nonassoc <lineno> TOK_GAME TOK_PLAYER_1 TOK_PLAYER_2
%nonassoc <lineno> TOK_REACHTARGET TOK_AVOIDTARGET
%nonassoc <lineno> TOK_REACHDEADLOCK TOK_AVOIDDEADLOCK
%nonassoc <lineno> TOK_BUCHIGAME TOK_LTLGAME TOK_GENREACTIVITY

%type <node> simple_list_expression

%type <node> game_module_list

%type <node> game_definition
%type <node> game_body game_body_element player_body player_body_element
%type <lineno> player_num
%type <node> reachtarget avoidtarget reachdeadlock avoiddeadlock
%type <node> buchigame ltlgame genreactivity
  /* ENDS: grammar.y.1.55 */
%%
  /* BEGINS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/grammar.y.2.50 */
/***************************************************************  -*-C-*-  ***/

/* --------------------------------------------------------------------- */
/* ---------------------------- EXPRESSION ----------------------------- */
/* --------------------------------------------------------------------- */
/* Later on unary plus must be implemented as a usual unary operator
   (as unary minus now)
*/
number        : TOK_NUMBER
              | TOK_PLUS TOK_NUMBER { $$ = $2; }
              ;

integer       : TOK_NUMBER
              | TOK_PLUS TOK_NUMBER { $$ = $2; }
              | TOK_MINUS TOK_NUMBER
                {node_int_setcar($2, -(node_get_int($2))); $$ = $2;}
              ;

number_word   : TOK_NUMBER_WORD
              ;
number_frac   : TOK_NUMBER_FRAC
              ;
number_real   : TOK_NUMBER_REAL
              ;
number_exp    : TOK_NUMBER_EXP
              ;

subrange      : integer TOK_TWODOTS integer
                  {$$ = new_lined_node(TWODOTS, $1, $3, $2);}
              ;

subrangetype  : shift_expr TOK_TWODOTS shift_expr
                  {$$ = new_lined_node(TWODOTS, $1, $3, $2);}
              ;

constant     : TOK_FALSEEXP
             | TOK_TRUEEXP
             | TOK_UWCONST TOK_LP simple_expression TOK_COMMA shift_expr TOK_RP
               {$$ = new_lined_node(UWCONST, $3, $5, $1); }
             | TOK_SWCONST TOK_LP simple_expression TOK_COMMA shift_expr TOK_RP
               {$$ = new_lined_node(SWCONST, $3, $5, $1); }
             | TOK_WSIZEOF TOK_LP next_expression TOK_RP
               {$$ = new_lined_node(WSIZEOF, $3, Nil, $1); }
             | TOK_WTOINT TOK_LP next_expression TOK_RP
               {$$ = new_lined_node(CAST_TOINT, $3, Nil, $1); }
             | number
             | number_word
             | number_frac
               {
                 yyerror("fractional constants are not supported.");
                 YYABORT;
               }
             | number_exp
               {
                 yyerror("exponential constants are not supported.");
                 YYABORT;
               }
             | number_real
               {
                 yyerror("real constants are not supported.");
                 YYABORT;
               }
             ;

/* expression has to have "var_identifier", but it is ambiguous with
   bit-selection (the problem is with "left-bracket" (TOK_LB)).
   So they are put in one place and "var_idenitifier" alternatives have
   additional assertions to check that array's and
   dot's rules are applied to var_idintifier only.
*/
primary_expr :
               constant
             | TOK_MINUS primary_expr { $$ = new_lined_node(UMINUS, $2, Nil, $1); }
             | TOK_ATOM
             | TOK_SELF         {$$ = new_node(SELF,Nil,Nil);}
             | primary_expr TOK_DOT TOK_ATOM
                  {
                    int ntype = node_get_type($1);
                    if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                      yyerror_lined("incorrect DOT expression", $2);
                      YYABORT;
                    }
                    $$ = new_lined_node(DOT, $1, $3, $2) ;
                  }
             | primary_expr TOK_DOT TOK_NUMBER
                  {
                   int ntype = node_get_type($1);
                   if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                     yyerror_lined("incorrect DOT expression", $2);
                     YYABORT;
                   }
                   $$ = new_lined_node(DOT, $1, $3, $2) ;
                  }
             | primary_expr TOK_LB next_expression TOK_RB
                  {
                   /* array may have any expression on the left.
                      The type check will detect any problems */
                   $$ = new_lined_node(ARRAY, $1, $3, $2);
                  }
             | primary_expr TOK_LB simple_expression TOK_COLON simple_expression TOK_RB
                  {
                    $$ = new_lined_node(BIT_SELECTION, $1,
                                        new_lined_node(COLON, $3, $5, $4), $2);
                  }
             | TOK_LP basic_expr TOK_RP             { $$ = $2; }
             | TOK_NOT primary_expr                 { $$ = new_lined_node(NOT, $2, Nil, $1); }
             | TOK_BOOL  TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(CAST_BOOL, $3, Nil, $1); }
             | TOK_WORD1 TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(CAST_WORD1, $3, Nil, $1); }
             | TOK_NEXT  TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(NEXT, $3, Nil, $1); }
             | TOK_SIGNED   TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(CAST_SIGNED, $3, Nil, $1); }
             | TOK_UNSIGNED TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(CAST_UNSIGNED, $3, Nil, $1); }
             | TOK_EXTEND   TOK_LP basic_expr TOK_COMMA basic_expr TOK_RP   { $$ = new_lined_node(EXTEND, $3, $5, $1); }
             | TOK_WRESIZE TOK_LP basic_expr TOK_COMMA  basic_expr TOK_RP   { $$ = new_lined_node(WRESIZE, $3, $5, $1); }
             | TOK_CASE case_element_list_expr TOK_ESAC { $$ = $2; }

             | TOK_WAREAD TOK_LP
                   simple_expression TOK_COMMA simple_expression TOK_RP
                { $$ = new_lined_node(WAREAD, $3, $5, $1); }
             | TOK_WAWRITE TOK_LP
                   simple_expression TOK_COMMA simple_expression TOK_COMMA simple_expression TOK_RP
                { $$ = new_lined_node(WAWRITE, $3, new_node(WAWRITE, $5, $7), $2); }
             | TOK_COUNT TOK_LP count_param_list TOK_RP 
                { $$ = new_lined_node(COUNT, $3, Nil, $2); }
             ;

count_param_list:
               primary_expr { $$ = cons($1, Nil); }
             | primary_expr TOK_COMMA count_param_list { $$ = cons($1, $3); }
             ;

case_element_list_expr
             : case_element_expr /* last element in the list. Add FAILURE node */
                   { $$ = new_node(CASE, $1, failure_make("case conditions are not exhaustive", FAILURE_CASE_NOT_EXHAUSTIVE, yylineno));}
             | case_element_expr case_element_list_expr { $$ = new_node(CASE, $1, $2); }
             ;

case_element_expr
             : basic_expr TOK_COLON basic_expr TOK_SEMI
                 { $$ = build_case_colon_node($1, $3, $2); }
             ;

concatination_expr :
               primary_expr
             | concatination_expr TOK_CONCATENATION primary_expr { $$ = new_lined_node(CONCATENATION, $1, $3, $2); }
             ;

multiplicative_expr :
               concatination_expr
             | multiplicative_expr TOK_TIMES concatination_expr  { $$ = new_lined_node(TIMES, $1, $3, $2); }
             | multiplicative_expr TOK_DIVIDE concatination_expr { $$ = new_lined_node(DIVIDE, $1, $3, $2); }
             | multiplicative_expr TOK_MOD concatination_expr    { $$ = new_lined_node(MOD, $1, $3, $2); }
             ;

additive_expr :
               multiplicative_expr
             | additive_expr TOK_PLUS multiplicative_expr  { $$ = new_lined_node(PLUS, $1, $3, $2); }
             | additive_expr TOK_MINUS multiplicative_expr { $$ = new_lined_node(MINUS, $1, $3, $2); }
             ;

shift_expr :   additive_expr
             | shift_expr TOK_LSHIFT additive_expr   { $$ = new_lined_node(LSHIFT, $1, $3, $2); }
             | shift_expr TOK_RSHIFT additive_expr   { $$ = new_lined_node(RSHIFT, $1, $3, $2); }
/*
             | shift_expr TOK_LROTATE additive_expr  { $$ = new_lined_node(LROTATE, $1, $3, $2); }
             | shift_expr TOK_RROTATE additive_expr  { $$ = new_lined_node(RROTATE, $1, $3, $2); } */
             ;

set_expr     : shift_expr
             | subrange
             | TOK_LCB set_list_expr TOK_RCB   { $$ = $2; }
             ;

set_list_expr: basic_expr
             | set_list_expr TOK_COMMA basic_expr {$$ = new_lined_node(UNION, $1, $3, $2);}
             ;


union_expr   : set_expr
             | union_expr TOK_UNION set_expr { $$ = new_lined_node(UNION, $1, $3, $2); }
             ;

in_expr :      union_expr
             | in_expr TOK_SETIN union_expr { $$ = new_lined_node(SETIN, $1, $3, $2); }
             ;

relational_expr :
               in_expr
             | relational_expr TOK_EQUAL in_expr { $$ = new_lined_node(EQUAL, $1, $3, $2); }
             | relational_expr TOK_NOTEQUAL in_expr { $$ = new_lined_node(NOTEQUAL, $1, $3, $2); }
             | relational_expr TOK_LT in_expr { $$ = new_lined_node(LT, $1, $3, $2); }
             | relational_expr TOK_GT in_expr { $$ = new_lined_node(GT, $1, $3, $2); }
             | relational_expr TOK_LE in_expr { $$ = new_lined_node(LE, $1, $3, $2); }
             | relational_expr TOK_GE in_expr { $$ = new_lined_node(GE, $1, $3, $2); }
             ;

ctl_expr     : relational_expr
             | pure_ctl_expr /* all CTL operators */
             ;
/* pure ctl_expr is introduced to allow NOT before the ctl expressions */
pure_ctl_expr
             : TOK_EX ctl_expr       { $$ = new_lined_node(EX, $2, Nil, $1); }
             | TOK_AX ctl_expr       { $$ = new_lined_node(AX, $2, Nil, $1); }
             | TOK_EF ctl_expr       { $$ = new_lined_node(EF, $2, Nil, $1); }
             | TOK_AF ctl_expr       { $$ = new_lined_node(AF, $2, Nil, $1); }
             | TOK_EG ctl_expr       { $$ = new_lined_node(EG, $2, Nil, $1); }
             | TOK_AG ctl_expr       { $$ = new_lined_node(AG, $2, Nil, $1); }
             | TOK_AA TOK_LB ctl_basic_expr TOK_UNTIL ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(AU, $3, $5, $1); }
             | TOK_EE TOK_LB ctl_basic_expr TOK_UNTIL ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(EU, $3, $5, $1); }
             | TOK_AA TOK_LB ctl_basic_expr TOK_BUNTIL subrange ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(ABU, new_lined_node(AU, $3, $6, $1), $5, $1); }
             | TOK_EE TOK_LB ctl_basic_expr TOK_BUNTIL subrange ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(EBU, new_lined_node(EU, $3, $6, $1), $5, $1); }
             | TOK_EBF subrange ctl_expr { $$ = new_lined_node(EBF, $3, $2, $1); }
             | TOK_ABF subrange ctl_expr { $$ = new_lined_node(ABF, $3, $2, $1); }
             | TOK_EBG subrange ctl_expr { $$ = new_lined_node(EBG, $3, $2, $1); }
             | TOK_ABG subrange ctl_expr { $$ = new_lined_node(ABG, $3, $2, $1); }

             /* NOT is required here to allow such expr as "! EX a" */
             | TOK_NOT pure_ctl_expr { $$ = new_lined_node(NOT, $2, Nil, $1); }
             ;
/* there are separate CTL rules for propositional expressions
   to avoid ambiguity related to TOK_UNTIL token in LTL and CTL.
*/
ctl_and_expr :
               ctl_expr
             | ctl_and_expr TOK_AND ctl_expr  { $$ = new_lined_node(AND, $1, $3, $2); }
             ;
ctl_or_expr :
               ctl_and_expr
             | ctl_or_expr TOK_OR ctl_and_expr    { $$ = new_lined_node(OR,$1, $3, $2); }
             | ctl_or_expr TOK_XOR ctl_and_expr   { $$ = new_lined_node(XOR,$1, $3, $2); }
             | ctl_or_expr TOK_XNOR ctl_and_expr  { $$ = new_lined_node(XNOR,$1, $3, $2); }
             ;
ctl_iff_expr :
               ctl_or_expr
             | ctl_iff_expr TOK_IFF ctl_or_expr   { $$ = new_lined_node(IFF, $1, $3, $2); }
             ;

ctl_implies_expr : /* right association */
               ctl_iff_expr
             | ctl_iff_expr TOK_IMPLIES ctl_implies_expr { $$ = new_lined_node(IMPLIES, $1, $3, $2); }
             ;

ctl_basic_expr : ctl_implies_expr;

/* LTL has to include CTL to allow paranthesis around CTL (and everything) */
ltl_unary_expr
             : ctl_expr
             | pure_ltl_unary_expr /* all unary LTL operators */
             ;

/* pure ltl_unary_expr is introduced to allow NOT before the ltl expressions */
pure_ltl_unary_expr
             : TOK_OP_NEXT ltl_unary_expr  {$$ = new_lined_node(OP_NEXT, $2, Nil, $1);}
             | TOK_OP_PREC ltl_unary_expr  {$$ = new_lined_node(OP_PREC, $2, Nil, $1);}
             | TOK_OP_NOTPRECNOT ltl_unary_expr {$$ = new_lined_node(OP_NOTPRECNOT, $2, Nil, $1);}
             | TOK_OP_GLOBAL ltl_unary_expr {$$ = new_lined_node(OP_GLOBAL, $2, Nil, $1);}
             | TOK_OP_HISTORICAL ltl_unary_expr {$$ = new_lined_node(OP_HISTORICAL, $2, Nil, $1);}
             | TOK_OP_FUTURE ltl_unary_expr {$$ = new_lined_node(OP_FUTURE, $2, Nil, $1);}
             | TOK_OP_ONCE ltl_unary_expr {$$ = new_lined_node(OP_ONCE, $2, Nil, $1);}
             /* NOT is required here to allow such expr as "! X a" */
             | TOK_NOT pure_ltl_unary_expr { $$ = new_lined_node(NOT, $2, Nil, $1); }
             ;

/*  a & b U c & d */

/* all LTL binary operators */
ltl_binary_expr :
                ltl_unary_expr
              | ltl_binary_expr TOK_UNTIL ltl_unary_expr
                                {$$ = new_lined_node(UNTIL, $1, $3, $2);}
              | ltl_binary_expr TOK_SINCE ltl_unary_expr
                                {$$ = new_lined_node(SINCE, $1, $3, $2);}
              | ltl_binary_expr TOK_RELEASES ltl_unary_expr
                  {$$ = new_lined_node(NOT,
                           new_lined_node(UNTIL,
                             new_lined_node(NOT, $1, Nil, node_get_lineno($1)),
                             new_lined_node(NOT, $3, Nil, node_get_lineno($3)),
                             $2), Nil, $2);
                  }
              | ltl_binary_expr TOK_TRIGGERED ltl_unary_expr
                  {$$ = new_lined_node(NOT,
                          new_lined_node(SINCE,
                              new_lined_node(NOT, $1, Nil, node_get_lineno($1)),
                              new_lined_node(NOT, $3, Nil, node_get_lineno($3)),
                              $2), Nil, $2);
                  }
              ;

and_expr :
               ltl_binary_expr
             | and_expr TOK_AND ltl_binary_expr  { $$ = new_lined_node(AND, $1, $3, $2); }
             ;

or_expr :
               and_expr
             | or_expr TOK_OR and_expr    { $$ = new_lined_node(OR,$1, $3, $2); }
             | or_expr TOK_XOR and_expr   { $$ = new_lined_node(XOR,$1, $3, $2); }
             | or_expr TOK_XNOR and_expr  { $$ = new_lined_node(XNOR,$1, $3, $2); }
             ;

ite_expr :
               or_expr
             | or_expr TOK_QUESTIONMARK basic_expr TOK_COLON ite_expr { $$ = new_lined_node(IFTHENELSE, new_lined_node(COLON, $1, $3, $2), $5, $2); }


iff_expr :
               ite_expr
             | iff_expr TOK_IFF ite_expr   { $$ = new_lined_node(IFF, $1, $3, $2); }
             ;

implies_expr : /* right association */
               iff_expr
             | iff_expr TOK_IMPLIES implies_expr { $$ = new_lined_node(IMPLIES, $1, $3, $2); }
             ;

basic_expr :
             implies_expr
           ;

/* every expression below, at first, remembers the current kind of
   the parsed expression and then sets its own kind.
   After parsing the kind of expression is restoreed
*/
simple_expression : basic_expr   {if (!isCorrectExp($$, EXP_SIMPLE)) YYABORT;}
                  ;

next_expression   : basic_expr   {if (!isCorrectExp($$, EXP_NEXT)) YYABORT;}
                  ;

ctl_expression    : basic_expr   {if (!isCorrectExp($$, EXP_CTL)) YYABORT;}
                  ;

ltl_expression    : basic_expr   {if (!isCorrectExp($$, EXP_LTL)) YYABORT;}
                  ;


compute_expression : TOK_MMIN TOK_LB ctl_expression TOK_COMMA ctl_expression TOK_RB
                  { $$ = new_lined_node(MINU, $3, $5, $1); }
              | TOK_MMAX TOK_LB ctl_expression TOK_COMMA ctl_expression TOK_RB
                  { $$ = new_lined_node(MAXU, $3, $5, $1); }
              ;


/* ------------------------------------------------------------------------ */
/* ----------------------------  TYPES ------------------------------------ */
/* ------------------------------------------------------------------------ */

itype         : TOK_BOOLEAN {$$ = new_node(BOOLEAN, Nil, Nil);}
              | TOK_INTEGER {
                yyerror("given token is not supported.");
                YYABORT;
              }
              | TOK_REAL {
                yyerror("given token is not supported.");
                YYABORT;
              }
              | TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(UNSIGNED_WORD, $3, Nil, $1);}
              | TOK_UNSIGNED TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(UNSIGNED_WORD, $4, Nil, $1);}
              | TOK_SIGNED TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(SIGNED_WORD, $4, Nil, $1);}
              | subrangetype
              | TOK_LCB type_value_list TOK_RCB
                  {$$ = new_lined_node(SCALAR, $2, Nil, $1);}
              | TOK_ARRAY TOK_WORD TOK_LB simple_expression TOK_RB TOK_OF TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(WORDARRAY, $4, $9, $1);}
              | TOK_ARRAY subrangetype TOK_OF itype
                  {$$ = new_lined_node(ARRAY_TYPE, $2, $4, $1);}
              ;

type          : itype
              | module_type
              | TOK_PROCESS module_type
                  {$$ = new_lined_node(PROCESS, $2, Nil, $1);}
              ;

type_value_list : type_value {$$ = cons(find_atom($1), Nil); free_node($1);}
                | type_value_list TOK_COMMA type_value {$$ = cons(find_atom($3), $1); free_node($3);}
                ;

type_value    : complex_atom /* actually only process_selector can be declared with complex constants */
              | integer
              | TOK_FALSEEXP
              | TOK_TRUEEXP
              ;

complex_atom  : TOK_ATOM
              | complex_atom TOK_DOT TOK_ATOM {$$ = new_lined_node(DOT, $1, $3, $2);}
              ;

module_type   : TOK_ATOM {$$ = new_node(MODTYPE, $1, Nil);}
              | TOK_ATOM TOK_LP TOK_RP {$$ = new_node(MODTYPE, $1, Nil);}
              | TOK_ATOM TOK_LP next_list_expression TOK_RP
                {$$ = new_lined_node(MODTYPE, $1, $3, node_get_lineno($1));}
              | TOK_ARRAY subrangetype TOK_OF module_type
                  {
                    /* $$ = new_lined_node(ARRAY, $2, $4, $1); */
                    /* array of modules is not supported any more.
                       NOTE: In future if there are some syntact conflicts
                       this case can be removed */
                    yyerror_lined("array of modules is no supported", $1);
                    YYABORT;
                  }
              ;

next_list_expression
              : next_expression {$$ = cons($1,Nil);}
              | next_list_expression TOK_COMMA next_expression {$$ = cons($3, $1);}
              ;

/* ------------------------------------------------------------------------ */
/* ---------------------------- DECLARATIONS  ----------------------------- */
/* ------------------------------------------------------------------------ */


/*
 An NuSMV program is a repetition of modules. Each module has a
 signature and a body.
*/
module_list  : module {$$ = cons($1, Nil);}
             | module_list module {$$ = cons($2, $1);}
             ;

module       : TOK_MODULE module_sign declarations
                    {$$ = new_lined_node(MODULE, $2, $3, $1);}
             ;
module_sign  : TOK_ATOM {$$ = new_node(MODTYPE, $1, Nil);}
             | TOK_ATOM TOK_LP TOK_RP {$$ = new_node(MODTYPE, $1, Nil);}
             | TOK_ATOM TOK_LP atom_list TOK_RP
                    {$$ = new_node(MODTYPE, $1, $3);}
             ;
atom_list    : TOK_ATOM {$$ = cons(find_atom($1), Nil); free_node($1);}
             | atom_list TOK_COMMA TOK_ATOM {$$ = cons(find_atom($3), $1); free_node($3);}
             ;


/* The body of a module */
declarations : {$$ = Nil;}
             | declarations declaration {$$ = cons($2, $1);}
             | declarations error     { SYNTAX_ERROR_HANDLING($$, $1); }
             ;

declaration  : isa
             | var
             | frozen_var
             | input_var
             | assign
             | init
             | invar
             | trans
             | define_decls
             | array_define
             | fairness
             | justice
             | compassion
             | invarspec
             | ctlspec
             | ltlspec
             | pslspec
             | compute
             | constants
             | predicate
             | mirror
             ;

/*
 Variable declarations:
 This includes also the instantiation of module
 (in synchronous and asynchronous product).
*/
/* Do we realy want to have empty VAR declarations? */
var           : TOK_VAR {$$ = new_lined_node(VAR, Nil, Nil, $1);}
              | TOK_VAR var_decl_list {$$ = new_lined_node(VAR, $2, Nil, $1);}
              ;

frozen_var    : TOK_FROZENVAR {$$ = new_lined_node(FROZENVAR, Nil, Nil, $1);}
              | TOK_FROZENVAR fvar_decl_list {$$ = new_lined_node(FROZENVAR, $2, Nil, $1);}
              ;

input_var     : TOK_IVAR {$$ = new_lined_node(IVAR, Nil, Nil, $1);}
              | TOK_IVAR ivar_decl_list {$$ = new_lined_node(IVAR, $2, Nil, $1);}
              ;

var_decl_list : var_decl                {$$ = cons($1, Nil);}
              | var_decl_list var_decl  {$$ = cons($2, $1);} /* oppositive direction chosen for some reason */
              | var_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
fvar_decl_list: fvar_decl                 {$$ = cons($1, Nil);}
              | fvar_decl_list fvar_decl  {$$ = cons($2, $1);} /* oppositive direction chosen for some reason */
              | fvar_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
ivar_decl_list: ivar_decl                 {$$ = cons($1, Nil);}
              | ivar_decl_list ivar_decl  {$$ = cons($2, $1);} /* oppositive direction chosen for some reason */
              | ivar_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;

var_decl      : decl_var_id TOK_COLON type TOK_SEMI {$$ = new_lined_node(COLON, $1, $3, $2);}
              ;
fvar_decl     : decl_var_id TOK_COLON itype TOK_SEMI {$$ = new_lined_node(COLON, $1, $3, $2);}
              ;
ivar_decl     : decl_var_id TOK_COLON itype TOK_SEMI {$$ = new_lined_node(COLON, $1, $3, $2);}
              ;

/* Definitions */
define_decls  : TOK_DEFINE define_list
                                  {$$ = new_lined_node(DEFINE, $2, Nil, $1);}
              ;
define_list   : {$$ = Nil;}
              | define_list define {$$ = cons($2, $1);}
              | define_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;

define        : decl_var_id TOK_EQDEF next_expression TOK_SEMI
                                 {$$ = new_lined_node(EQDEF, $1, $3, $2);}
              | decl_var_id TOK_EQDEF array_expression TOK_SEMI
                                 {$$ = new_lined_node(EQDEF, $1, $3, $2);
                                 /* Note that array-define is declared
                                    as normal define.
                                    Then compile_instantiate in compileFlatten.c
                                    distinguish them by detecting
                                    ARRAY_DEF on right hand side.
                                   */
                                 }
              ;

/* Array Definitions : Deprecated feature as DEFINE is enough.
   Remove array_define and array_define_list later.*/
array_define : TOK_ARRAY_DEFINE array_define_list     {$$ = new_lined_node(DEFINE, $2, Nil, $1);}
              ;

array_define_list
              : {$$ = Nil;}
              | array_define_list decl_var_id TOK_EQDEF array_expression TOK_SEMI  {$$ = cons(new_lined_node(EQDEF, $2, $4, $3), $1);}
              | array_define_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;

array_expression
              : TOK_LB array_contents TOK_RB {$$ =  new_lined_node(ARRAY_DEF, $2, Nil, $1);}
              | TOK_LB array_expression_list TOK_RB {$$ =  new_lined_node(ARRAY_DEF, $2, Nil, $1);}
              ;

array_expression_list
              : array_expression {$$ = cons($1, Nil);}
              | array_expression TOK_COMMA array_expression_list {$$ = cons($1, $3);}
              ;

array_contents
              : next_expression TOK_COMMA array_contents {$$ = cons($1, $3);}
              | next_expression {$$ = cons($1,Nil);}
              ;

/* Assignments of initial, current or next value of variables */
assign        : TOK_ASSIGN assign_list {$$ = new_lined_node(ASSIGN, $2, Nil, $1);}
              ;
assign_list   : {$$ = Nil;}
              | assign_list one_assign {$$ = new_node(AND, $1, $2);}
              | assign_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
one_assign   : var_id TOK_EQDEF simple_expression TOK_SEMI
                  {$$ = new_lined_node(EQDEF, $1, $3, $2);}
              | TOK_SMALLINIT TOK_LP var_id TOK_RP TOK_EQDEF simple_expression TOK_SEMI
                  { $$ = new_lined_node(EQDEF,
                                        new_lined_node(SMALLINIT, $3, Nil, $1),
                                        $6, $5);
                  }
              | TOK_NEXT TOK_LP var_id TOK_RP TOK_EQDEF next_expression TOK_SEMI
                  { $$ = new_lined_node(EQDEF,
                                        new_lined_node(NEXT, $3, Nil, $1),
                                        $6, $5);
                  }
              ;

/* Direct finite state machine definition (init, invar, trans) */
init          : TOK_INIT simple_expression optsemi   {$$ = new_lined_node(INIT, $2, Nil, $1);}
              ;
invar         : TOK_INVAR simple_expression optsemi {$$ = new_lined_node(INVAR, $2, Nil, $1);}
              ;
trans         : TOK_TRANS next_expression optsemi {$$ = new_lined_node(TRANS, $2, Nil, $1);}
              ;

/* Fairness declarations */
fairness      : TOK_FAIRNESS simple_expression optsemi  {$$ = new_lined_node(JUSTICE, $2, Nil, $1);}
              ;

justice       : TOK_JUSTICE simple_expression optsemi  {$$ = new_lined_node(JUSTICE, $2, Nil, $1);}
              ;

compassion    : TOK_COMPASSION
                TOK_LP simple_expression TOK_COMMA simple_expression TOK_RP
                optsemi  {$$ = new_lined_node(COMPASSION, cons($3,$5), Nil, $1);}
              ;

/* Specifications and computation of min and max distance */
_invarspec    : next_expression optsemi { $$ = $1; }
              | next_expression TOK_INCONTEXT context optsemi {$$ = new_node(CONTEXT, $3, $1);}
;
invarspec     : TOK_INVARSPEC _invarspec {$$ = new_lined_node(INVARSPEC, $2, Nil, $1);}
              | TOK_INVARSPEC TOK_NAME var_id TOK_EQDEF _invarspec {$$ = new_lined_node(INVARSPEC, $5, $3, $1);}
;

_ctlspec      : ctl_expression optsemi { $$ = $1; }
              | ctl_expression TOK_INCONTEXT context optsemi {$$ = new_node(CONTEXT, $3, $1);}
;
ctlspec       : TOK_SPEC _ctlspec {$$ = new_lined_node(SPEC, $2, Nil, $1);}
              | TOK_CTLSPEC _ctlspec {$$ = new_lined_node(SPEC, $2, Nil, $1);}
              | TOK_SPEC TOK_NAME var_id TOK_EQDEF  _ctlspec {$$ = new_lined_node(SPEC, $5, $3, $1);}
              | TOK_CTLSPEC TOK_NAME var_id TOK_EQDEF _ctlspec {$$ = new_lined_node(SPEC, $5, $3, $1);}
;

_ltlspec      : ltl_expression optsemi { $$ = $1; }
              | ltl_expression TOK_INCONTEXT context optsemi {$$ = new_node(CONTEXT, $3, $1);}
;

ltlspec       : TOK_LTLSPEC _ltlspec {$$ = new_lined_node(LTLSPEC, $2, Nil, $1);}
              | TOK_LTLSPEC TOK_NAME var_id TOK_EQDEF _ltlspec {$$ = new_lined_node(LTLSPEC, $5, $3, $1);}
;

_compute      : compute_expression optsemi { $$ = $1; }
              | compute_expression TOK_INCONTEXT context optsemi {$$ = new_node(CONTEXT, $3, $1);}
;
compute       : TOK_COMPUTE _compute {$$ = new_lined_node(COMPUTE, $2, Nil, $1);}
              | TOK_COMPUTE TOK_NAME var_id TOK_EQDEF _compute {$$ = new_lined_node(COMPUTE, $5, $3, $1);}
;


pslspec       : TOK_PSLSPEC
{
  if (nusmv_parse_psl() != 0) {
    YYABORT;
  }
  $$ = new_lined_node(PSLSPEC, psl_parsed_tree, psl_property_name, $1);
  psl_property_name = Nil;
}
              ;

constants     : TOK_CONSTANTS constants_expression TOK_SEMI
                  {$$ = new_lined_node(CONSTANTS, $2, Nil, $1);}
              ;

constants_expression
             : {$$ = Nil;}
             | complex_atom { $$ = cons($1, Nil);}
             | constants_expression TOK_COMMA complex_atom {$$ = cons($3, $1);}
             ;

predicate_list
             : predicate { $$ = cons($1, Nil);}
             | predicate_list predicate { $$ = cons($2, $1);}
             ;


predicate     : TOK_PRED simple_expression optsemi
                 {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }
              | TOK_PRED TOK_LB TOK_NUMBER TOK_RB simple_expression optsemi
                 {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }

              | TOK_PRED TOK_LT var_id TOK_GT TOK_EQDEF simple_expression optsemi
                 {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }

              | TOK_PRED TOK_LB TOK_NUMBER TOK_RB TOK_LT var_id TOK_GT TOK_EQDEF
                       simple_expression optsemi
                 {
                   yyerror("given token is not supported.");
                   YYABORT;
                 }
              ;

mirror        : TOK_MIRROR decl_var_id optsemi
                  {
                    yyerror("given token is not supported.");
                    YYABORT;
                  }
              ;

/* Module macro-expansion */
isa           : TOK_ISA TOK_ATOM {$$ = new_node(ISA, $2, Nil);}
              ;

/* parse an optional semicolon */
optsemi      : | TOK_SEMI {};


/* Variable identifiers.
   decl_var_id is used for declarations; self not allowed.
   var_id is used to reference variables in assignment, includes self.
 */

decl_var_id   : TOK_ATOM
              | decl_var_id TOK_DOT TOK_ATOM {$$ = new_node(DOT, $1, $3);}
              | decl_var_id TOK_DOT TOK_NUMBER {$$ = new_node(DOT, $1, $3);}
              | decl_var_id TOK_LB TOK_NUMBER TOK_RB  {$$ = new_node(ARRAY, $1, $3);}
              | decl_var_id TOK_LB TOK_MINUS TOK_NUMBER TOK_RB
                      { node_ptr tmp = new_lined_node(NUMBER,
                                                      PTR_FROM_INT(node_ptr, -node_get_int($4)),
                                                      Nil,
                                                      $3);
                        $$ = new_node(ARRAY, $1, tmp);
                      }
              ;

var_id        : TOK_ATOM
              | TOK_SELF {$$ = new_node(SELF,Nil,Nil);}
              | var_id TOK_DOT TOK_ATOM {$$ = new_node(DOT, $1, $3);}
              | var_id TOK_DOT TOK_NUMBER {$$ = new_node(DOT, $1, $3);}
              | var_id TOK_LB simple_expression TOK_RB {$$ = new_node(ARRAY, $1, $3);}
              ;

/* ------------------------------------------------------------------------ */
/* ----------------------------  COMMANDS  -------------------------------- */
/* ------------------------------------------------------------------------ */

command       : command_case {$$ = $1;}
              | error TOK_SEMI {return(1);}
              | error {return(1);}
              ;

command_case  : TOK_INIT simple_expression TOK_SEMI
                 {$$ = new_lined_node(INIT, $2, Nil, $1);}
              | TOK_FAIRNESS simple_expression TOK_SEMI
                 {$$ = new_lined_node(JUSTICE, $2, Nil, $1);}
              | TOK_TRANS next_expression TOK_SEMI
                 {$$ = new_lined_node(TRANS, $2, Nil, $1);}
              | TOK_CONSTRAINT simple_expression TOK_SEMI
                 {$$ = new_lined_node(CONSTRAINT, $2, Nil, $1);}

/* properties */
              | TOK_SIMPWFF _simpwff {$$ = new_lined_node(SIMPWFF, node2maincontext($2), Nil, $1);}
              | TOK_NEXTWFF _invarspec {$$ = new_lined_node(NEXTWFF, node2maincontext($2), Nil, $1);}
              | TOK_CTLWFF _ctlspec {$$ = new_lined_node(CTLWFF, node2maincontext($2), Nil, $1);}
              | TOK_LTLWFF _ltlspec {$$ = new_lined_node(LTLWFF, node2maincontext($2), Nil, $1);}
              | TOK_COMPWFF _compute {$$ = new_lined_node(COMPWFF, node2maincontext($2), Nil, $1);}
              | TOK_COMPID var_id TOK_SEMI  {$$ = new_lined_node(COMPID, $2, Nil, $1);}
              | TOK_PREDSLIST predicate_list
                {
                  yyerror("given token is not supported.");
                  YYABORT;
                }
              ;


context       : TOK_ATOM                          {$$ = find_atom($1); free_node($1); }
              | context TOK_DOT TOK_ATOM          {$$ = find_node(DOT, $1, $3);}
              | context TOK_LB simple_expression TOK_RB {$$ = find_node(ARRAY, $1, $3);}
              ;

_simpwff      : simple_expression optsemi { $$ = $1; }
              | simple_expression TOK_INCONTEXT context optsemi {$$ = new_node(CONTEXT, $3, $1);}

  /* ENDS: /home/nitin/Tools/mc/NuSMV-2.5.4/nusmv/src/parser/grammar.y.2.50 */
  /* BEGINS: grammar.y.2.55 */
/***************************************************************  -*-C-*-  ***/

game_begin    : {
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
               game_module_list
                {
#if HAVE_GAME
                  if (!opt_game_game(OptsHandler_get_instance())) {
                    /*this is a usual SMV file*/
                    parsed_tree = $2;
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
                                                     $2)));
                  }
#else /* no GAME */
                  parsed_tree = $2;            
#endif
                }
              | {
                  if (PARSE_COMMAND != parse_mode_flag) {
                    yyerror("unexpected command encountered during parsing");
                    YYABORT;
                  }
                }
               command {parsed_tree = $2;}
              | {
                  if (PARSE_LTL_EXPR != parse_mode_flag){
                    yyerror("unexpected expression encountered during parsing");
                    YYABORT;
                  }
                }
               ltl_expression  {parsed_tree = $2;}
              ;

/* ------------------------------------------------------------------------ */
/* ----------------------------  TYPES ------------------------------------ */
/* ------------------------------------------------------------------------ */

simple_list_expression
              : simple_expression {$$ = cons($1,Nil);}
              | simple_list_expression TOK_COMMA simple_expression {$$ = cons($3, $1);}
              ;

/* ------------------------------------------------------------------------ */
/* ---------------------------- DECLARATIONS  ----------------------------- */
/* ------------------------------------------------------------------------ */

/*
 An NuGaT program is a repetition of modules. Also there can be one
 game definition. Each module has a signature and a body. Game
 definition constructs are passed through variables
 game_parser_spec_list, game_parser_player_1 and game_parser_player_2
 and not returned by this rule.
*/
game_module_list
             : module {$$ = cons($1, Nil);}
             | game_definition {$$ = Nil;}
             | module_list module {$$ = cons($2, $1);}
             | module_list game_definition {$$ = $1;}
             ;

/* A game definition consists of GAME keyword, definitions of its two
   players and a list of usual and game specifications.
   NOTE: this rule returns value not by usual way
   but through variables game_parser_spec_list,
   game_parser_player_1 and game_parser_player_2.
*/
game_definition
             : TOK_GAME game_body
                     {
#if HAVE_GAME
                       /* check that the game is not redeclared */
                       if (opt_game_game(OptsHandler_get_instance())) {
                         yyerror_lined("redefinition of a GAME", $1);
                       }
                       else {
                         Game_Mode_Enter();
                       }
#else
                       yyerror_lined("GAME declaration cannot be processes "
                                     "because GAME package is not set up\n"
                                     "Check --enable-addons=game option of "
                                     "the configure script\n", $1);
                       YYABORT;
#endif
                       game_parser_spec_list = $2;
                       $$ = Nil;
                     }
             ;

game_body
             :       {$$=Nil;}
             | game_body_element game_body
                     {if (Nil != $1) $$ = cons($1,$2); else $$ = $2;}
             ;

/* a GAME definition consists of both players definitions,
   usual specifications and game specifications.
*/
game_body_element
             : TOK_PLAYER_1 player_body
                     {
                       /* a player definition is converted to a module
                          definitino with a special name. This is done
                          to simplify the further flattening
                       */
                       if (game_parser_player_1 != Nil) {
                         yyerror_lined("redefinition of a PLAYER_1", $1);
                         YYABORT;
                       }
                       game_parser_player_1 = new_lined_node(MODULE,
                           new_node(MODTYPE,
                             new_node(ATOM,(node_ptr)find_string("PLAYER_1"),
                                      Nil), Nil),  $2, $1);
                       $$=Nil;
                     }
             | TOK_PLAYER_2 player_body
                     {
                       /* a player definition is converted to a module
                          definitino with a special name. This is done
                          to simplify the further flattening
                       */
                       if (game_parser_player_2 != Nil) {
                         yyerror_lined("redefinition of a PLAYER_2", $1);
                         YYABORT;
                       }
                       game_parser_player_2 = new_lined_node(MODULE,
                           new_node(MODTYPE,
                             new_node(ATOM,(node_ptr)find_string("PLAYER_2"),
                                      Nil), Nil), $2, $1);
                       $$=Nil;
                     }
// not implemented    | invarspec
// not implemented    | ctlspec
// not implemented    | ltlspec
// not implemented    | pslspec
// not implemented    | compute
             | reachtarget
             | avoidtarget
             | reachdeadlock
             | avoiddeadlock
             | buchigame
             | ltlgame
             | genreactivity
             ;

/* a player's body is the same as module's body except the player
   cannot have ISA declaration and specifications
*/
player_body  : { $$ = Nil; }
             | player_body player_body_element{ $$ = cons($2, $1); }
             ;

player_body_element
             : var
             | frozen_var
// not implemented : | input_var
             | assign
             | init
             | invar
             | trans
             | define_decls
// not implemented :    | fairness
// not implemented :    | justice
// not implemented :    | compassion
             ;

player_num    : TOK_PLAYER_1 {$$=1;}
              | TOK_PLAYER_2 {$$=2;}
              ;
reachtarget   : TOK_REACHTARGET player_num simple_expression optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(REACHTARGET, NODE_FROM_INT($2), $3, $1);
#endif
                       }
              ;
avoidtarget   : TOK_AVOIDTARGET player_num simple_expression optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(AVOIDTARGET, NODE_FROM_INT($2), $3, $1);
#endif
                       }
              ;
reachdeadlock : TOK_REACHDEADLOCK player_num optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(REACHDEADLOCK, NODE_FROM_INT($2), Nil, $1);
#endif
                       }
              ;
avoiddeadlock : TOK_AVOIDDEADLOCK player_num optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(AVOIDDEADLOCK, NODE_FROM_INT($2), Nil, $1);
#endif
}
              ;
buchigame     : TOK_BUCHIGAME player_num
                TOK_LP simple_list_expression TOK_RP optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(BUCHIGAME, NODE_FROM_INT($2),
                                             new_lined_node(GAME_EXP_LIST,
                                                            reverse($4), Nil, $3),
                                             $1);
#endif
}
              ;
ltlgame       : TOK_LTLGAME player_num ltl_expression optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(LTLGAME, NODE_FROM_INT($2), $3, $1);
#endif
                       }
              ;
genreactivity : TOK_GENREACTIVITY player_num
                TOK_LP simple_list_expression TOK_RP TOK_IMPLIES
                TOK_LP simple_list_expression TOK_RP optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(GENREACTIVITY, NODE_FROM_INT($2),
                                             new_lined_node(GAME_TWO_EXP_LISTS,
                                                            reverse($4), reverse($8), $6),
                                             $1);
#endif
                       }
              ;
  /* ENDS: grammar.y.2.55 */
%%
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
