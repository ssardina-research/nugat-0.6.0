  /* BEGINS: /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/parser/grammar.y.1.50 */
/***************************************************************  -*-C-*-  ***/
%{

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


%left <lineno> TOK_CONSTRAINT TOK_ITYPE
%left <lineno> TOK_MODULE TOK_PROCESS TOK_CONTEXT TOK_EU TOK_AU TOK_EBU TOK_ABU TOK_MINU TOK_MAXU
%left <lineno> TOK_VAR TOK_FROZENVAR TOK_IVAR TOK_FUN TOK_DEFINE TOK_ARRAY_DEFINE TOK_INIT TOK_TRANS TOK_INVAR TOK_SPEC TOK_CTLSPEC TOK_LTLSPEC TOK_COMPUTE TOK_NAME
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
%left <lineno> TOK_ARRAY  TOK_BOOLEAN TOK_WORD
%left <lineno> TOK_BOOL TOK_WORD1
%left <lineno> TOK_CONST_ARRAY TOK_WAREAD TOK_WAWRITE
%left <lineno> TOK_SIGNED TOK_UNSIGNED TOK_EXTEND TOK_UWCONST TOK_SWCONST TOK_WRESIZE TOK_WSIZEOF TOK_WTOINT TOK_COUNT 
%left <lineno> TOK_TYPEOF

%left <node> TOK_ATOM TOK_FALSEEXP TOK_TRUEEXP
%left <node> TOK_NUMBER TOK_NUMBER_FRAC TOK_NUMBER_REAL TOK_NUMBER_EXP
%left <node> TOK_NUMBER_WORD

%left <lineno> TOK_ABS TOK_MIN TOK_MAX

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



/* all nonterminals return a parse tree node */
%type <node> number integer number_word number_frac number_real number_exp subrange subrangetype

%type <node> constant primary_expr case_element_expr case_element_list_expr count_param_list
%type <node> concatination_expr multiplicative_expr

%type <node> primary_expr_type concatination_expr_type multiplicative_expr_type additive_expr_type shift_expr_type

%type <node> additive_expr shift_expr
%type <node> set_expr set_list_expr union_expr in_expr relational_expr 
%type <node> ctl_expr pure_ctl_expr ctl_and_expr
%type <node> ctl_or_expr ctl_iff_expr ctl_implies_expr ctl_basic_expr
%type <node> ltl_binary_expr ltl_unary_expr pure_ltl_unary_expr
%type <node> and_expr or_expr iff_expr implies_expr basic_expr ite_expr
%type <node> simple_expression next_expression ctl_expression ltl_expression

%type <node> nfun_type nfun_ftype nfunc_expr 

%type <node> itype type module_type 
%type <node> type_value_list type_value complex_atom next_list_expression
%type <node> module_list module module_sign atom_list
%type <node> declarations declaration
%type <node> var frozen_var var_decl var_decl_list fun_decl fun_def
%type <node> input_var ivar_decl fvar_decl ivar_decl_list fvar_decl_list fun_decl_list
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


%type <node> decl_var_id var_id

%type <node> command command_case context _simpwff


%start game_begin 
  /* ENDS: /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/parser/grammar.y.1.50 */
  /* BEGINS: grammar.y.1.55 */
/***************************************************************  -*-C-*-  ***/

%{
#include "config.h"
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
  /* BEGINS: /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/parser/grammar.y.2.50 */
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
                  {$$ = new_lined_node(NODEMGR, TWODOTS, $1, $3, $2);}
              ;

subrangetype  : shift_expr_type TOK_TWODOTS shift_expr_type
                {$$ = new_lined_node(NODEMGR, TWODOTS, $1, $3, $2);}
              ;

constant     : TOK_FALSEEXP
             | TOK_TRUEEXP
             | TOK_UWCONST TOK_LP simple_expression TOK_COMMA shift_expr TOK_RP
               {$$ = new_lined_node(NODEMGR, UWCONST, $3, $5, $1); }
             | TOK_SWCONST TOK_LP simple_expression TOK_COMMA shift_expr TOK_RP
               {$$ = new_lined_node(NODEMGR, SWCONST, $3, $5, $1); }
             | TOK_WSIZEOF TOK_LP next_expression TOK_RP
               {$$ = new_lined_node(NODEMGR, WSIZEOF, $3, Nil, $1); }
             | TOK_WTOINT TOK_LP next_expression TOK_RP
               {$$ = new_lined_node(NODEMGR, CAST_TOINT, $3, Nil, $1); }
             | number
             | number_word
             | number_frac
               {
                 nusmv_yyerror("fractional constants are not supported.");
                 YYABORT;
               }
             | number_exp
               {
                 nusmv_yyerror("exponential constants are not supported.");
                 YYABORT;
               }
             | number_real
               {
                 nusmv_yyerror("real constants are not supported.");
                 YYABORT;
               }
             ;


primary_expr :
               primary_expr_type
             | nfunc_expr  {
                 nusmv_yyerror("functions are not supported.");
                 YYABORT;
               }

             ;

nfunc_expr   : primary_expr TOK_LP next_list_expression TOK_RP {
                    int ntype = node_get_type($1);
                    if (ATOM != ntype && DOT != ntype && SELF != ntype) {
                      nusmv_yyerror_lined("incorrect DOT expression", $2);
                      YYABORT;
                    }
                $$ = new_lined_node(NODEMGR, NFUNCTION, $1, $3, $2);
               }

             ;

/* expression has to have "var_identifier", but it is ambiguous with
   bit-selection (the problem is with "left-bracket" (TOK_LB)).
   So they are put in one place and "var_idenitifier" alternatives have
   additional assertions to check that array's and
   dot's rules are applied to var_idintifier only.
*/

primary_expr_type :
               constant
             | TOK_MINUS primary_expr_type { $$ = new_lined_node(NODEMGR, UMINUS, $2, Nil, $1); }
             | TOK_ATOM
             | TOK_SELF         {$$ = new_node(NODEMGR, SELF,Nil,Nil);}
             | primary_expr_type TOK_DOT TOK_ATOM
                  {
                    int ntype = node_get_type($1);
                    if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                      nusmv_yyerror_lined("incorrect DOT expression", $2);
                      YYABORT;
                    }
                    $$ = new_lined_node(NODEMGR, DOT, $1, $3, $2) ;
                  }
             | primary_expr_type TOK_DOT TOK_NUMBER
                  {
                   int ntype = node_get_type($1);
                   if (ATOM != ntype && DOT != ntype && ARRAY != ntype && SELF != ntype) {
                     nusmv_yyerror_lined("incorrect DOT expression", $2);
                     YYABORT;
                   }
                   $$ = new_lined_node(NODEMGR, DOT, $1, $3, $2) ;
                  }
             | primary_expr_type TOK_LB next_expression TOK_RB
                  {
                   /* array may have any expression on the left.
                      The type check will detect any problems */
                   $$ = new_lined_node(NODEMGR, ARRAY, $1, $3, $2);
                  }
             | primary_expr_type TOK_LB simple_expression TOK_COLON simple_expression TOK_RB
                  {
                    $$ = new_lined_node(NODEMGR, BIT_SELECTION, $1,
                                        new_lined_node(NODEMGR, COLON, $3, $5, $4), $2);
                  }
             | TOK_LP basic_expr TOK_RP             { $$ = $2; }
             | TOK_ABS TOK_LP basic_expr TOK_RP     { /* abs(a) := (a >= 0) ? a : - a */
                                                      node_ptr zero = new_lined_node(NODEMGR, NUMBER, NODE_FROM_INT((int)(0)), Nil, $1);
                                                      node_ptr cond = new_lined_node(NODEMGR, GE, $3, zero, $1);
                                                      node_ptr minus_a = new_lined_node(NODEMGR, UMINUS, $3, Nil, $1);
                                                      $$ = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, cond, $3, $1), minus_a, $1); ; }
             | TOK_MIN TOK_LP basic_expr TOK_COMMA basic_expr TOK_RP     { /* MIN(a,b) := a < b ? a : b */
                                                                           node_ptr cond = new_lined_node(NODEMGR, LT, $3, $5, $1);
                                                                           $$ = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, cond, $3, $1), $5, $1); ; }
             | TOK_MAX TOK_LP basic_expr TOK_COMMA basic_expr TOK_RP     { /* MAX(a,b) := a < b ? b : a */
                                                                           node_ptr cond = new_lined_node(NODEMGR, LT, $3, $5, $1);
                                                                           $$ = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, cond, $5, $1), $3, $1); ;}
             | TOK_NOT primary_expr_type                 { $$ = new_lined_node(NODEMGR, NOT, $2, Nil, $1); }
             | TOK_BOOL  TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, CAST_BOOL, $3, Nil, $1); }
             | TOK_WORD1 TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, CAST_WORD1, $3, Nil, $1); }
             | TOK_NEXT  TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, NEXT, $3, Nil, $1); }
             | TOK_SIGNED   TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, CAST_SIGNED, $3, Nil, $1); }
             | TOK_UNSIGNED TOK_LP basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, CAST_UNSIGNED, $3, Nil, $1); }
             | TOK_EXTEND   TOK_LP basic_expr TOK_COMMA basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, EXTEND, $3, $5, $1); }
             | TOK_WRESIZE TOK_LP basic_expr TOK_COMMA  basic_expr TOK_RP   { $$ = new_lined_node(NODEMGR, WRESIZE, $3, $5, $1); }
             | TOK_CASE case_element_list_expr TOK_ESAC { $$ = $2; }

             | TOK_WAREAD TOK_LP
                   basic_expr TOK_COMMA basic_expr TOK_RP
                { $$ = new_lined_node(NODEMGR, WAREAD, $3, $5, $1); }
             | TOK_WAWRITE TOK_LP
                   basic_expr TOK_COMMA basic_expr TOK_COMMA basic_expr TOK_RP
                { $$ = new_lined_node(NODEMGR, WAWRITE, $3, new_node(NODEMGR, WAWRITE, $5, $7), $2); }
             | TOK_CONST_ARRAY TOK_LP TOK_TYPEOF TOK_LP var_id TOK_RP TOK_COMMA basic_expr TOK_RP 
                { $$ = new_lined_node(NODEMGR, CONST_ARRAY, new_node(NODEMGR, TYPEOF, $5, Nil), $8, $1); }
             | TOK_COUNT TOK_LP count_param_list TOK_RP 
                { $$ = new_lined_node(NODEMGR, COUNT, $3, Nil, $2);}
             ;

count_param_list:
               basic_expr { $$ = cons(NODEMGR, $1, Nil); }
             | basic_expr TOK_COMMA count_param_list { $$ = cons(NODEMGR, $1, $3); }
             ;

case_element_list_expr
             : case_element_expr /* last element in the list. Add FAILURE node */
             {
               const ErrorMgr_ptr errmgr =
                 ERROR_MGR(NuSMVEnv_get_value(__nusmv_parser_env__, ENV_ERROR_MANAGER));
               node_ptr fail =
                 ErrorMgr_failure_make(errmgr,
                                       "case conditions are not exhaustive",
                                       FAILURE_CASE_NOT_EXHAUSTIVE,
                                       nusmv_yylineno);
               $$ = new_node(NODEMGR, CASE, $1, fail);
             }
             | case_element_expr case_element_list_expr { $$ = new_node(NODEMGR, CASE, $1, $2); }
             ;

case_element_expr
             : basic_expr TOK_COLON basic_expr TOK_SEMI
                 { $$ = build_case_colon_node($1, $3, $2); }
             ;


concatination_expr_type :
               primary_expr_type
             | concatination_expr_type TOK_CONCATENATION primary_expr_type { $$ = new_lined_node(NODEMGR, CONCATENATION, $1, $3, $2); }
             ;


concatination_expr :
               primary_expr
             | concatination_expr TOK_CONCATENATION primary_expr { $$ = new_lined_node(NODEMGR, CONCATENATION, $1, $3, $2); }
             ;


multiplicative_expr_type :
               concatination_expr_type
             | multiplicative_expr_type TOK_TIMES concatination_expr_type  { $$ = new_lined_node(NODEMGR, TIMES, $1, $3, $2); }
             | multiplicative_expr_type TOK_DIVIDE concatination_expr_type { $$ = new_lined_node(NODEMGR, DIVIDE, $1, $3, $2); }
             | multiplicative_expr_type TOK_MOD concatination_expr_type    { $$ = new_lined_node(NODEMGR, MOD, $1, $3, $2); }
             ;

multiplicative_expr :
               concatination_expr
             | multiplicative_expr TOK_TIMES concatination_expr  { $$ = new_lined_node(NODEMGR, TIMES, $1, $3, $2); }
             | multiplicative_expr TOK_DIVIDE concatination_expr { $$ = new_lined_node(NODEMGR, DIVIDE, $1, $3, $2); }
             | multiplicative_expr TOK_MOD concatination_expr    { $$ = new_lined_node(NODEMGR, MOD, $1, $3, $2); }
             ;


additive_expr_type :
               multiplicative_expr_type
             | additive_expr_type TOK_PLUS multiplicative_expr_type  { $$ = new_lined_node(NODEMGR, PLUS, $1, $3, $2); }
             | additive_expr_type TOK_MINUS multiplicative_expr_type { $$ = new_lined_node(NODEMGR, MINUS, $1, $3, $2); }
             ;


additive_expr :
               multiplicative_expr
             | additive_expr TOK_PLUS multiplicative_expr  { $$ = new_lined_node(NODEMGR, PLUS, $1, $3, $2); }
             | additive_expr TOK_MINUS multiplicative_expr { $$ = new_lined_node(NODEMGR, MINUS, $1, $3, $2); }
             ;

shift_expr_type :   additive_expr_type
                | shift_expr_type TOK_LSHIFT additive_expr_type   { $$ = new_lined_node(NODEMGR, LSHIFT, $1, $3, $2); }
                | shift_expr_type TOK_RSHIFT additive_expr_type   { $$ = new_lined_node(NODEMGR, RSHIFT, $1, $3, $2); }


shift_expr :   additive_expr
             | shift_expr TOK_LSHIFT additive_expr   { $$ = new_lined_node(NODEMGR, LSHIFT, $1, $3, $2); }
             | shift_expr TOK_RSHIFT additive_expr   { $$ = new_lined_node(NODEMGR, RSHIFT, $1, $3, $2); }
/*
             | shift_expr TOK_LROTATE additive_expr  { $$ = new_lined_node(NODEMGR, LROTATE, $1, $3, $2); }
             | shift_expr TOK_RROTATE additive_expr  { $$ = new_lined_node(NODEMGR, RROTATE, $1, $3, $2); } */
             ;

set_expr     : shift_expr
             | subrange
             | TOK_LCB set_list_expr TOK_RCB   { $$ = $2; }
             ;

set_list_expr: basic_expr
             | set_list_expr TOK_COMMA basic_expr {$$ = new_lined_node(NODEMGR, UNION, $1, $3, $2);}
             ;


union_expr   : set_expr
             | union_expr TOK_UNION set_expr { $$ = new_lined_node(NODEMGR, UNION, $1, $3, $2); }
             ;

in_expr :      union_expr
             | in_expr TOK_SETIN union_expr { $$ = new_lined_node(NODEMGR, SETIN, $1, $3, $2); }
             ;

relational_expr :
               in_expr
             | relational_expr TOK_EQUAL in_expr { $$ = new_lined_node(NODEMGR, EQUAL, $1, $3, $2); }
             | relational_expr TOK_NOTEQUAL in_expr { $$ = new_lined_node(NODEMGR, NOTEQUAL, $1, $3, $2); }
             | relational_expr TOK_LT in_expr { $$ = new_lined_node(NODEMGR, LT, $1, $3, $2); }
             | relational_expr TOK_GT in_expr { $$ = new_lined_node(NODEMGR, GT, $1, $3, $2); }
             | relational_expr TOK_LE in_expr { $$ = new_lined_node(NODEMGR, LE, $1, $3, $2); }
             | relational_expr TOK_GE in_expr { $$ = new_lined_node(NODEMGR, GE, $1, $3, $2); }
             ;

ctl_expr     : relational_expr
             | pure_ctl_expr /* all CTL operators */
             ;
/* pure ctl_expr is introduced to allow NOT before the ctl expressions */
pure_ctl_expr
             : TOK_EX ctl_expr       { $$ = new_lined_node(NODEMGR, EX, $2, Nil, $1); }
             | TOK_AX ctl_expr       { $$ = new_lined_node(NODEMGR, AX, $2, Nil, $1); }
             | TOK_EF ctl_expr       { $$ = new_lined_node(NODEMGR, EF, $2, Nil, $1); }
             | TOK_AF ctl_expr       { $$ = new_lined_node(NODEMGR, AF, $2, Nil, $1); }
             | TOK_EG ctl_expr       { $$ = new_lined_node(NODEMGR, EG, $2, Nil, $1); }
             | TOK_AG ctl_expr       { $$ = new_lined_node(NODEMGR, AG, $2, Nil, $1); }
             | TOK_AA TOK_LB ctl_basic_expr TOK_UNTIL ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(NODEMGR, AU, $3, $5, $1); }
             | TOK_EE TOK_LB ctl_basic_expr TOK_UNTIL ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(NODEMGR, EU, $3, $5, $1); }
             | TOK_AA TOK_LB ctl_basic_expr TOK_BUNTIL subrange ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(NODEMGR, ABU, new_lined_node(NODEMGR, AU, $3, $6, $1), $5, $1); }
             | TOK_EE TOK_LB ctl_basic_expr TOK_BUNTIL subrange ctl_basic_expr TOK_RB
                                     { $$ = new_lined_node(NODEMGR, EBU, new_lined_node(NODEMGR, EU, $3, $6, $1), $5, $1); }
             | TOK_EBF subrange ctl_expr { $$ = new_lined_node(NODEMGR, EBF, $3, $2, $1); }
             | TOK_ABF subrange ctl_expr { $$ = new_lined_node(NODEMGR, ABF, $3, $2, $1); }
             | TOK_EBG subrange ctl_expr { $$ = new_lined_node(NODEMGR, EBG, $3, $2, $1); }
             | TOK_ABG subrange ctl_expr { $$ = new_lined_node(NODEMGR, ABG, $3, $2, $1); }

             /* NOT is required here to allow such expr as "! EX a" */
             | TOK_NOT pure_ctl_expr { $$ = new_lined_node(NODEMGR, NOT, $2, Nil, $1); }
             ;
/* there are separate CTL rules for propositional expressions
   to avoid ambiguity related to TOK_UNTIL token in LTL and CTL.
*/
ctl_and_expr :
               ctl_expr
             | ctl_and_expr TOK_AND ctl_expr  { $$ = new_lined_node(NODEMGR, AND, $1, $3, $2); }
             ;
ctl_or_expr :
               ctl_and_expr
             | ctl_or_expr TOK_OR ctl_and_expr    { $$ = new_lined_node(NODEMGR, OR,$1, $3, $2); }
             | ctl_or_expr TOK_XOR ctl_and_expr   { $$ = new_lined_node(NODEMGR, XOR,$1, $3, $2); }
             | ctl_or_expr TOK_XNOR ctl_and_expr  { $$ = new_lined_node(NODEMGR, XNOR,$1, $3, $2); }
             ;
ctl_iff_expr :
               ctl_or_expr
             | ctl_iff_expr TOK_IFF ctl_or_expr   { $$ = new_lined_node(NODEMGR, IFF, $1, $3, $2); }
             ;

ctl_implies_expr : /* right association */
               ctl_iff_expr
             | ctl_iff_expr TOK_IMPLIES ctl_implies_expr { $$ = new_lined_node(NODEMGR, IMPLIES, $1, $3, $2); }
             ;

ctl_basic_expr : ctl_implies_expr;

/* LTL has to include CTL to allow paranthesis around CTL (and everything) */
ltl_unary_expr
             : ctl_expr
             | pure_ltl_unary_expr /* all unary LTL operators */
             ;

/* pure ltl_unary_expr is introduced to allow NOT before the ltl expressions */
pure_ltl_unary_expr
             : TOK_OP_NEXT ltl_unary_expr  {$$ = new_lined_node(NODEMGR, OP_NEXT, $2, Nil, $1);}
             | TOK_OP_PREC ltl_unary_expr  {$$ = new_lined_node(NODEMGR, OP_PREC, $2, Nil, $1);}
             | TOK_OP_NOTPRECNOT ltl_unary_expr {$$ = new_lined_node(NODEMGR, OP_NOTPRECNOT, $2, Nil, $1);}
             | TOK_OP_GLOBAL ltl_unary_expr {$$ = new_lined_node(NODEMGR, OP_GLOBAL, $2, Nil, $1);}
             | TOK_OP_GLOBAL TOK_LB TOK_NUMBER TOK_COMMA TOK_NUMBER TOK_RB ltl_unary_expr 
               {$$ = new_lined_node(NODEMGR, OP_GLOBAL, $7, new_lined_node(NODEMGR, TWODOTS, $3, $5, $1), $1);}
             | TOK_OP_HISTORICAL ltl_unary_expr {$$ = new_lined_node(NODEMGR, OP_HISTORICAL, $2, Nil, $1);}
             | TOK_OP_HISTORICAL TOK_LB TOK_NUMBER TOK_COMMA TOK_NUMBER TOK_RB ltl_unary_expr 
               {$$ = new_lined_node(NODEMGR, OP_HISTORICAL, $7, new_lined_node(NODEMGR, TWODOTS, $3, $5, $1), $1);}
             | TOK_OP_FUTURE ltl_unary_expr {$$ = new_lined_node(NODEMGR, OP_FUTURE, $2, Nil, $1);}
             | TOK_OP_FUTURE TOK_LB TOK_NUMBER TOK_COMMA TOK_NUMBER TOK_RB ltl_unary_expr 
               {$$ = new_lined_node(NODEMGR, OP_FUTURE, $7, new_lined_node(NODEMGR, TWODOTS, $3, $5, $1), $1);}
             | TOK_OP_ONCE ltl_unary_expr {$$ = new_lined_node(NODEMGR, OP_ONCE, $2, Nil, $1);}
             | TOK_OP_ONCE TOK_LB TOK_NUMBER TOK_COMMA TOK_NUMBER TOK_RB ltl_unary_expr 
               {$$ = new_lined_node(NODEMGR, OP_ONCE, $7, new_lined_node(NODEMGR, TWODOTS, $3, $5, $1), $1);}
             /* NOT is required here to allow such expr as "! X a" */
             | TOK_NOT pure_ltl_unary_expr { $$ = new_lined_node(NODEMGR, NOT, $2, Nil, $1); }
             ;

/*  a & b U c & d */

/* all LTL binary operators */
ltl_binary_expr :
                ltl_unary_expr
              | ltl_binary_expr TOK_UNTIL ltl_unary_expr
                                {$$ = new_lined_node(NODEMGR, UNTIL, $1, $3, $2);}
              | ltl_binary_expr TOK_SINCE ltl_unary_expr
                                {$$ = new_lined_node(NODEMGR, SINCE, $1, $3, $2);}
              | ltl_binary_expr TOK_RELEASES ltl_unary_expr
                  {$$ = new_lined_node(NODEMGR, NOT,
                           new_lined_node(NODEMGR, UNTIL,
                             new_lined_node(NODEMGR, NOT, $1, Nil, node_get_lineno($1)),
                             new_lined_node(NODEMGR, NOT, $3, Nil, node_get_lineno($3)),
                             $2), Nil, $2);
                  }
              | ltl_binary_expr TOK_TRIGGERED ltl_unary_expr
                  {$$ = new_lined_node(NODEMGR, NOT,
                          new_lined_node(NODEMGR, SINCE,
                              new_lined_node(NODEMGR, NOT, $1, Nil, node_get_lineno($1)),
                              new_lined_node(NODEMGR, NOT, $3, Nil, node_get_lineno($3)),
                              $2), Nil, $2);
                  }
              ;

and_expr :
               ltl_binary_expr
             | and_expr TOK_AND ltl_binary_expr  { $$ = new_lined_node(NODEMGR, AND, $1, $3, $2); }
             ;

or_expr :
               and_expr
             | or_expr TOK_OR and_expr    { $$ = new_lined_node(NODEMGR, OR,$1, $3, $2); }
             | or_expr TOK_XOR and_expr   { $$ = new_lined_node(NODEMGR, XOR,$1, $3, $2); }
             | or_expr TOK_XNOR and_expr  { $$ = new_lined_node(NODEMGR, XNOR,$1, $3, $2); }
             ;

ite_expr :
               or_expr
             | or_expr TOK_QUESTIONMARK basic_expr TOK_COLON ite_expr { $$ = new_lined_node(NODEMGR, IFTHENELSE, new_lined_node(NODEMGR, COLON, $1, $3, $2), $5, $2); }


iff_expr :
               ite_expr
             | iff_expr TOK_IFF ite_expr   { $$ = new_lined_node(NODEMGR, IFF, $1, $3, $2); }
             ;

implies_expr : /* right association */
               iff_expr
             | iff_expr TOK_IMPLIES implies_expr { $$ = new_lined_node(NODEMGR, IMPLIES, $1, $3, $2); }
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
                  { $$ = new_lined_node(NODEMGR, MINU, $3, $5, $1); }
              | TOK_MMAX TOK_LB ctl_expression TOK_COMMA ctl_expression TOK_RB
                  { $$ = new_lined_node(NODEMGR, MAXU, $3, $5, $1); }
              ;


/* ------------------------------------------------------------------------ */
/* ----------------------------  TYPES ------------------------------------ */
/* ------------------------------------------------------------------------ */

itype         : TOK_BOOLEAN {$$ = new_node(NODEMGR, BOOLEAN, Nil, Nil);}
              | TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(NODEMGR, UNSIGNED_WORD, $3, Nil, $1);}
              | TOK_UNSIGNED TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(NODEMGR, UNSIGNED_WORD, $4, Nil, $1);}
              | TOK_SIGNED TOK_WORD TOK_LB simple_expression TOK_RB
                  {$$ = new_lined_node(NODEMGR, SIGNED_WORD, $4, Nil, $1);}
              | subrangetype 
              | TOK_LCB type_value_list TOK_RCB
                  {$$ = new_lined_node(NODEMGR, SCALAR, $2, Nil, $1);}
              | TOK_ARRAY TOK_WORD TOK_LB simple_expression TOK_RB TOK_OF itype
                  {$$ = new_lined_node(NODEMGR, WORDARRAY_TYPE, $4, $7, $1);}
              | TOK_ARRAY subrangetype TOK_OF itype
                  {$$ = new_lined_node(NODEMGR, ARRAY_TYPE, $2, $4, $1);}
              | TOK_ARRAY TOK_OF itype
                  {nusmv_yyerror("unbounded arrays are not supported.");
                   YYABORT;
                  }
              ;

type          : itype 
              | module_type 
              | TOK_PROCESS module_type
                  {$$ = new_lined_node(NODEMGR, PROCESS, $2, Nil, $1);}
              ;

type_value_list : type_value {$$ = cons(NODEMGR, find_atom(NODEMGR, $1), Nil); free_node(NODEMGR, $1);}
                | type_value_list TOK_COMMA type_value {$$ = cons(NODEMGR, find_atom(NODEMGR, $3), $1); free_node(NODEMGR, $3);}
                ;

type_value    : complex_atom /* actually only process_selector can be declared with complex constants */
              | integer
              | TOK_FALSEEXP
              | TOK_TRUEEXP
              ;

complex_atom  : TOK_ATOM
              | complex_atom TOK_DOT TOK_ATOM {$$ = new_lined_node(NODEMGR, DOT, $1, $3, $2);}
              ;

module_type   : TOK_ATOM {$$ = new_node(NODEMGR, MODTYPE, $1, Nil);}
              | TOK_ATOM TOK_LP TOK_RP {$$ = new_node(NODEMGR, MODTYPE, $1, Nil);}
              | TOK_ATOM TOK_LP next_list_expression TOK_RP
                {$$ = new_lined_node(NODEMGR, MODTYPE, $1, $3, node_get_lineno($1));}
              | TOK_ARRAY subrangetype TOK_OF module_type
                  {
                    /* $$ = new_lined_node(NODEMGR, ARRAY, $2, $4, $1); */
                    /* array of modules is not supported any more.
                       NOTE: In future if there are some syntact conflicts
                       this case can be removed */
                    nusmv_yyerror_lined("array of modules is no supported", $1);
                    YYABORT;
                  }
              ;

next_list_expression
              : next_expression {$$ = cons(NODEMGR, $1,Nil);}
              | next_list_expression TOK_COMMA next_expression {$$ = cons(NODEMGR, $3, $1);}
              ;

/* ------------------------------------------------------------------------ */
/* ---------------------------- DECLARATIONS  ----------------------------- */
/* ------------------------------------------------------------------------ */


/*
 An NuSMV program is a repetition of modules. Each module has a
 signature and a body.
*/
module_list  : module {$$ = cons(NODEMGR, $1, Nil);}
             | module_list module {$$ = cons(NODEMGR, $2, $1);}
             ;

module       : TOK_MODULE module_sign declarations
                    {$$ = new_lined_node(NODEMGR, MODULE, $2, $3, $1);}
             ;
module_sign  : TOK_ATOM {$$ = new_node(NODEMGR, MODTYPE, $1, Nil);}
             | TOK_ATOM TOK_LP TOK_RP {$$ = new_node(NODEMGR, MODTYPE, $1, Nil);}
             | TOK_ATOM TOK_LP atom_list TOK_RP
                    {$$ = new_node(NODEMGR, MODTYPE, $1, $3);}
             ;
atom_list    : TOK_ATOM {$$ = cons(NODEMGR, find_atom(NODEMGR, $1), Nil); free_node(NODEMGR, $1);}
             | atom_list TOK_COMMA TOK_ATOM {$$ = cons(NODEMGR, find_atom(NODEMGR, $3), $1); free_node(NODEMGR, $3);}
             ;


/* The body of a module */
declarations : {$$ = Nil;}
             | declarations declaration {$$ = cons(NODEMGR, $2, $1);}
             | declarations error     { SYNTAX_ERROR_HANDLING($$, $1); }
             ;

declaration  : isa
             | var
             | frozen_var
             | input_var
             | fun_def
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
             ;

/*
 Variable declarations:
 This includes also the instantiation of module
 (in synchronous and asynchronous product).
*/
/* Do we realy want to have empty VAR declarations? */
var           : TOK_VAR {$$ = new_lined_node(NODEMGR, VAR, Nil, Nil, $1);}
              | TOK_VAR var_decl_list {$$ = new_lined_node(NODEMGR, VAR, $2, Nil, $1);}
              ;

frozen_var    : TOK_FROZENVAR {$$ = new_lined_node(NODEMGR, FROZENVAR, Nil, Nil, $1);}
              | TOK_FROZENVAR fvar_decl_list {$$ = new_lined_node(NODEMGR, FROZENVAR, $2, Nil, $1);}
              ;

input_var     : TOK_IVAR {$$ = new_lined_node(NODEMGR, IVAR, Nil, Nil, $1);}
              | TOK_IVAR ivar_decl_list {$$ = new_lined_node(NODEMGR, IVAR, $2, Nil, $1);}
              ;
fun_def       : TOK_FUN {
                 nusmv_yyerror("functions definitions are not supported.");
                 YYABORT;
               }
              | TOK_FUN fun_decl_list {
                 nusmv_yyerror("functions definitions are not supported.");
                 YYABORT;
               }
              ;

var_decl_list : var_decl                {$$ = cons(NODEMGR, $1, Nil);}
              | var_decl_list var_decl  {$$ = cons(NODEMGR, $2, $1);} /* oppositive direction chosen for some reason */
              | var_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
fvar_decl_list: fvar_decl                 {$$ = cons(NODEMGR, $1, Nil);}
              | fvar_decl_list fvar_decl  {$$ = cons(NODEMGR, $2, $1);} /* oppositive direction chosen for some reason */
              | fvar_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
ivar_decl_list: ivar_decl                 {$$ = cons(NODEMGR, $1, Nil);}
              | ivar_decl_list ivar_decl  {$$ = cons(NODEMGR, $2, $1);} /* oppositive direction chosen for some reason */
              | ivar_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
fun_decl_list : fun_decl                {$$ = cons(NODEMGR, $1, Nil);}
              | fun_decl_list fun_decl  {$$ = cons(NODEMGR, $2, $1);} /* oppositive direction chosen for some reason */
              | fun_decl_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;

var_decl      : decl_var_id TOK_COLON type TOK_SEMI {$$ = new_lined_node(NODEMGR, COLON, $1, $3, $2);}
              ;
fvar_decl     : decl_var_id TOK_COLON itype TOK_SEMI {$$ = new_lined_node(NODEMGR, COLON, $1, $3, $2);}
              ;
ivar_decl     : decl_var_id TOK_COLON itype TOK_SEMI {$$ = new_lined_node(NODEMGR, COLON, $1, $3, $2);}
              ;
fun_decl      : decl_var_id TOK_COLON nfun_type TOK_SEMI {$$ = new_lined_node(NODEMGR, COLON, $1, $3, $2);}
              ;

nfun_type     : nfun_ftype TOK_IMPLIES itype {$$ = new_node(NODEMGR, NFUNCTION_TYPE, $1, $3);}
              ;


nfun_ftype   : itype { $$ = cons(NODEMGR, $1, Nil); }
             | nfun_ftype TOK_TIMES itype { $$ = cons(NODEMGR, $3, $1); }
             ;

/* Definitions */
define_decls  : TOK_DEFINE define_list
                                  {$$ = new_lined_node(NODEMGR, DEFINE, $2, Nil, $1);}
              ;
define_list   : {$$ = Nil;}
              | define_list define {$$ = cons(NODEMGR, $2, $1);}
              | define_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;

define        : decl_var_id TOK_EQDEF next_expression TOK_SEMI
                                 {$$ = new_lined_node(NODEMGR, EQDEF, $1, $3, $2);}
              | decl_var_id TOK_EQDEF array_expression TOK_SEMI
                                 {$$ = new_lined_node(NODEMGR, EQDEF, $1, $3, $2);
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
array_define : TOK_ARRAY_DEFINE array_define_list     {$$ = new_lined_node(NODEMGR, DEFINE, $2, Nil, $1);}
              ;

array_define_list
              : {$$ = Nil;}
              | array_define_list decl_var_id TOK_EQDEF array_expression TOK_SEMI  {$$ = cons(NODEMGR, new_lined_node(NODEMGR, EQDEF, $2, $4, $3), $1);}
              | array_define_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;

array_expression
              : TOK_LB array_contents TOK_RB {$$ =  new_lined_node(NODEMGR, ARRAY_DEF, $2, Nil, $1);}
              | TOK_LB array_expression_list TOK_RB {$$ =  new_lined_node(NODEMGR, ARRAY_DEF, $2, Nil, $1);}
              ;

array_expression_list
              : array_expression {$$ = cons(NODEMGR, $1, Nil);}
              | array_expression TOK_COMMA array_expression_list {$$ = cons(NODEMGR, $1, $3);}
              ;

array_contents
              : next_expression TOK_COMMA array_contents {$$ = cons(NODEMGR, $1, $3);}
              | next_expression {$$ = cons(NODEMGR, $1,Nil);}
              ;

/* Assignments of initial, current or next value of variables */
assign        : TOK_ASSIGN assign_list {$$ = new_lined_node(NODEMGR, ASSIGN, $2, Nil, $1);}
              ;
assign_list   : {$$ = Nil;}
              | assign_list one_assign {$$ = new_node(NODEMGR, AND, $1, $2);}
              | assign_list error     { SYNTAX_ERROR_HANDLING($$, $1); }
              ;
one_assign   : var_id TOK_EQDEF simple_expression TOK_SEMI
                  {$$ = new_lined_node(NODEMGR, EQDEF, $1, $3, $2);}
              | TOK_SMALLINIT TOK_LP var_id TOK_RP TOK_EQDEF simple_expression TOK_SEMI
                  { $$ = new_lined_node(NODEMGR, EQDEF,
                                        new_lined_node(NODEMGR, SMALLINIT, $3, Nil, $1),
                                        $6, $5);
                  }
              | TOK_NEXT TOK_LP var_id TOK_RP TOK_EQDEF next_expression TOK_SEMI
                  { $$ = new_lined_node(NODEMGR, EQDEF,
                                        new_lined_node(NODEMGR, NEXT, $3, Nil, $1),
                                        $6, $5);
                  }
              ;

/* Direct finite state machine definition (init, invar, trans) */
init          : TOK_INIT simple_expression optsemi   {$$ = new_lined_node(NODEMGR, INIT, $2, Nil, $1);}
              ;
invar         : TOK_INVAR simple_expression optsemi {$$ = new_lined_node(NODEMGR, INVAR, $2, Nil, $1);}
              ;
trans         : TOK_TRANS next_expression optsemi {$$ = new_lined_node(NODEMGR, TRANS, $2, Nil, $1);}
              ;

/* Fairness declarations */
fairness      : TOK_FAIRNESS simple_expression optsemi  {$$ = new_lined_node(NODEMGR, JUSTICE, $2, Nil, $1);}
              ;

justice       : TOK_JUSTICE simple_expression optsemi  {$$ = new_lined_node(NODEMGR, JUSTICE, $2, Nil, $1);}
              ;

compassion    : TOK_COMPASSION
                TOK_LP simple_expression TOK_COMMA simple_expression TOK_RP
                optsemi  {$$ = new_lined_node(NODEMGR, COMPASSION, cons(NODEMGR, $3,$5), Nil, $1);}
              ;

/* Specifications and computation of min and max distance */
_invarspec    : next_expression optsemi { $$ = $1; }
              | next_expression TOK_INCONTEXT context optsemi {$$ = new_node(NODEMGR, CONTEXT, $3, $1);}
;
invarspec     : TOK_INVARSPEC _invarspec {$$ = new_lined_node(NODEMGR, INVARSPEC, $2, Nil, $1);}
              | TOK_INVARSPEC TOK_NAME var_id TOK_EQDEF _invarspec {$$ = new_lined_node(NODEMGR, INVARSPEC, $5, $3, $1);}
;

_ctlspec      : ctl_expression optsemi { $$ = $1; }
              | ctl_expression TOK_INCONTEXT context optsemi {$$ = new_node(NODEMGR, CONTEXT, $3, $1);}
;
ctlspec       : TOK_SPEC _ctlspec {$$ = new_lined_node(NODEMGR, SPEC, $2, Nil, $1);}
              | TOK_CTLSPEC _ctlspec {$$ = new_lined_node(NODEMGR, SPEC, $2, Nil, $1);}
              | TOK_SPEC TOK_NAME var_id TOK_EQDEF  _ctlspec {$$ = new_lined_node(NODEMGR, SPEC, $5, $3, $1);}
              | TOK_CTLSPEC TOK_NAME var_id TOK_EQDEF _ctlspec {$$ = new_lined_node(NODEMGR, SPEC, $5, $3, $1);}
;

_ltlspec      : ltl_expression optsemi { $$ = $1; }
              | ltl_expression TOK_INCONTEXT context optsemi {$$ = new_node(NODEMGR, CONTEXT, $3, $1);}
;

ltlspec       : TOK_LTLSPEC _ltlspec {$$ = new_lined_node(NODEMGR, LTLSPEC, $2, Nil, $1);}
              | TOK_LTLSPEC TOK_NAME var_id TOK_EQDEF _ltlspec {$$ = new_lined_node(NODEMGR, LTLSPEC, $5, $3, $1);}
;

_compute      : compute_expression optsemi { $$ = $1; }
              | compute_expression TOK_INCONTEXT context optsemi {$$ = new_node(NODEMGR, CONTEXT, $3, $1);}
;
compute       : TOK_COMPUTE _compute {$$ = new_lined_node(NODEMGR, COMPUTE, $2, Nil, $1);}
              | TOK_COMPUTE TOK_NAME var_id TOK_EQDEF _compute {$$ = new_lined_node(NODEMGR, COMPUTE, $5, $3, $1);}
;


pslspec       : TOK_PSLSPEC
{
  if (nusmv_parse_psl() != 0) {
    YYABORT;
  }
  $$ = new_lined_node(NODEMGR, PSLSPEC, psl_parsed_tree, psl_property_name, $1);
  psl_property_name = Nil;
}
              ;

constants     : TOK_CONSTANTS constants_expression TOK_SEMI
                  {$$ = new_lined_node(NODEMGR, CONSTANTS, $2, Nil, $1);}
              ;

constants_expression
             : {$$ = Nil;}
             | complex_atom { $$ = cons(NODEMGR, $1, Nil);}
             | constants_expression TOK_COMMA complex_atom {$$ = cons(NODEMGR, $3, $1);}

             ;



/* Module macro-expansion */
isa           : TOK_ISA TOK_ATOM {$$ = new_node(NODEMGR, ISA, $2, Nil);}
              ;

/* parse an optional semicolon */
optsemi      : | TOK_SEMI {};


/* Variable identifiers.
   decl_var_id is used for declarations; self not allowed.
   var_id is used to reference variables in assignment, includes self.
 */

decl_var_id   : TOK_ATOM
              | decl_var_id TOK_DOT TOK_ATOM {$$ = new_node(NODEMGR, DOT, $1, $3);}
              | decl_var_id TOK_DOT TOK_NUMBER {$$ = new_node(NODEMGR, DOT, $1, $3);}
              | decl_var_id TOK_LB TOK_NUMBER TOK_RB  {$$ = new_node(NODEMGR, ARRAY, $1, $3);}
              | decl_var_id TOK_LB TOK_MINUS TOK_NUMBER TOK_RB
                      { node_ptr tmp = new_lined_node(NODEMGR, NUMBER,
                                                      PTR_FROM_INT(node_ptr, -node_get_int($4)),
                                                      Nil,
                                                      $3);
                        $$ = new_node(NODEMGR, ARRAY, $1, tmp);
                      }
              ;

var_id        : TOK_ATOM
              | TOK_SELF {$$ = new_node(NODEMGR, SELF,Nil,Nil);}
              | var_id TOK_DOT TOK_ATOM {$$ = new_node(NODEMGR, DOT, $1, $3);}
              | var_id TOK_DOT TOK_NUMBER {$$ = new_node(NODEMGR, DOT, $1, $3);}
              | var_id TOK_LB simple_expression TOK_RB {$$ = new_node(NODEMGR, ARRAY, $1, $3);}
              ;

/* ------------------------------------------------------------------------ */
/* ----------------------------  COMMANDS  -------------------------------- */
/* ------------------------------------------------------------------------ */

command       : command_case {$$ = $1;}
              | error TOK_SEMI {return(1);}
              | error {return(1);}
              ;

command_case  : TOK_INIT simple_expression TOK_SEMI
                 {$$ = new_lined_node(NODEMGR, INIT, $2, Nil, $1);}
              | TOK_FAIRNESS simple_expression TOK_SEMI
                 {$$ = new_lined_node(NODEMGR, JUSTICE, $2, Nil, $1);}
              | TOK_TRANS next_expression TOK_SEMI
                 {$$ = new_lined_node(NODEMGR, TRANS, $2, Nil, $1);}
              | TOK_CONSTRAINT simple_expression TOK_SEMI
              {$$ = new_lined_node(NODEMGR, CONSTRAINT, $2, Nil, $1);}
              | TOK_ITYPE itype TOK_SEMI
                 {$$ = new_lined_node(NODEMGR, ITYPE, $2, Nil, $1);}

/* properties */
              | TOK_SIMPWFF _simpwff {$$ = new_lined_node(NODEMGR, SIMPWFF, node2maincontext($2), Nil, $1);}
              | TOK_NEXTWFF _invarspec {$$ = new_lined_node(NODEMGR, NEXTWFF, node2maincontext($2), Nil, $1);}
              | TOK_CTLWFF _ctlspec {$$ = new_lined_node(NODEMGR, CTLWFF, node2maincontext($2), Nil, $1);}
              | TOK_LTLWFF _ltlspec {$$ = new_lined_node(NODEMGR, LTLWFF, node2maincontext($2), Nil, $1);}
              | TOK_COMPWFF _compute {$$ = new_lined_node(NODEMGR, COMPWFF, node2maincontext($2), Nil, $1);}
              | TOK_COMPID var_id TOK_SEMI  {$$ = new_lined_node(NODEMGR, COMPID, $2, Nil, $1);}
              ;


context       : TOK_ATOM                          {$$ = find_atom(NODEMGR, $1); free_node(NODEMGR, $1); }
              | context TOK_DOT TOK_ATOM          {$$ = find_node(NODEMGR, DOT, $1, $3);}
              | context TOK_LB simple_expression TOK_RB {$$ = find_node(NODEMGR, ARRAY, $1, $3);}
              ;

_simpwff      : simple_expression optsemi { $$ = $1; }
              | simple_expression TOK_INCONTEXT context optsemi {$$ = new_node(NODEMGR, CONTEXT, $3, $1);}

  /* ENDS: /home/lorenzo/Documents/software/ClionProjects/NuSMV-2.6.0/NuSMV/code/nusmv/core/parser/grammar.y.2.50 */
  /* BEGINS: grammar.y.2.55 */
/***************************************************************  -*-C-*-  ***/

game_begin    : {
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
               game_module_list
                {
#if HAVE_GAME
                  if (!opt_game_game(OptsHandler_create())) {
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
                    parsed_tree = new_node(NODEMGR,GAME,
                                           game_parser_spec_list,
                                           cons(NODEMGR,game_parser_player_1,
                                                cons(NODEMGR,game_parser_player_2,
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
              : simple_expression {$$ = cons(NODEMGR,$1,Nil);}
              | simple_list_expression TOK_COMMA simple_expression {$$ = cons(NODEMGR,$3, $1);}
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
             : module {$$ = cons(NODEMGR,$1, Nil);}
             | game_definition {$$ = Nil;}
             | module_list module {$$ = cons(NODEMGR,$2, $1);}
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
                       if (opt_game_game(OptsHandler_create())) {
                         nusmv_yyerror_lined("redefinition of a GAME", $1);
                       }
                       else {
                         Game_Mode_Enter();
                       }
#else
                       nusmv_yyerror_lined("GAME declaration cannot be processes "
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
                     {if (Nil != $1) $$ = cons(NODEMGR,$1,$2); else $$ = $2;}
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
                         nusmv_yyerror_lined("redefinition of a PLAYER_1", $1);
                         YYABORT;
                       }
                       game_parser_player_1 = new_lined_node(NODEMGR,MODULE,
                           new_node(NODEMGR,MODTYPE,
                             new_node(NODEMGR,ATOM,(node_ptr)UStringMgr_find_string(USTRING_MGR(NULL),"PLAYER_1"),
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
                         nusmv_yyerror_lined("redefinition of a PLAYER_2", $1);
                         YYABORT;
                       }
                       game_parser_player_2 = new_lined_node(NODEMGR,MODULE,
                           new_node(NODEMGR,MODTYPE,
                             new_node(NODEMGR,ATOM,(node_ptr)UStringMgr_find_string(USTRING_MGR(NULL),"PLAYER_2"),
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
             | player_body player_body_element{ $$ = cons(NODEMGR,$2, $1); }
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
                         $$ = new_lined_node(NODEMGR,REACHTARGET, NODE_FROM_INT($2), $3, $1);
#endif
                       }
              ;
avoidtarget   : TOK_AVOIDTARGET player_num simple_expression optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(NODEMGR,AVOIDTARGET, NODE_FROM_INT($2), $3, $1);
#endif
                       }
              ;
reachdeadlock : TOK_REACHDEADLOCK player_num optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(NODEMGR,REACHDEADLOCK, NODE_FROM_INT($2), Nil, $1);
#endif
                       }
              ;
avoiddeadlock : TOK_AVOIDDEADLOCK player_num optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(NODEMGR,AVOIDDEADLOCK, NODE_FROM_INT($2), Nil, $1);
#endif
}
              ;
buchigame     : TOK_BUCHIGAME player_num
                TOK_LP simple_list_expression TOK_RP optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(NODEMGR,BUCHIGAME, NODE_FROM_INT($2),
                                             new_lined_node(NODEMGR,GAME_EXP_LIST,
                                                            reverse($4), Nil, $3),
                                             $1);
#endif
}
              ;
ltlgame       : TOK_LTLGAME player_num ltl_expression optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(NODEMGR,LTLGAME, NODE_FROM_INT($2), $3, $1);
#endif
                       }
              ;
genreactivity : TOK_GENREACTIVITY player_num
                TOK_LP simple_list_expression TOK_RP TOK_IMPLIES
                TOK_LP simple_list_expression TOK_RP optsemi
                       {
#if HAVE_GAME
                         $$ = new_lined_node(NODEMGR,GENREACTIVITY, NODE_FROM_INT($2),
                                             new_lined_node(NODEMGR,GAME_TWO_EXP_LISTS,
                                                            reverse($4), reverse($8), $6),
                                             $1);
#endif
                       }
              ;
  /* ENDS: grammar.y.2.55 */
%%
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
