/**CFile***********************************************************************

  FileName    [ CheckerGame.c ]

  PackageName [ game.walkers ]

  Synopsis    [ Implementaion of class 'CheckerGame'.  All thse functions
                are required to type check expressions and statements
                related to GAME package. This class is very small
                because GAME mostly uses usual NuSMV expressions. ]

  Description [ ]

  SeeAlso     [ CheckerGame.h ]

  Author      [ Andrei Tchaltsv ]

  Copyright   [
  This file is part of the ``game.walkers'' package of
  NuGaT. Copyright (C) 2010 by FBK-irst.

  NuGaT is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 2.1 of the License, or (at your option) any later version.

  NuGaT is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this library; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.

  For more information on NuGaT see <http://es.fbk.eu/tools/nugat>
  or email to <nugat-users@list.fbk.eu>.
  Please report bugs to <nugat-users@list.fbk.eu>.

  To contact the NuGaT development board, email to <nugat@list.fbk.eu>. ]

  Revision    [$Id: CheckerGame.c,v 1.1.2.3 2010-02-08 15:28:10 nusmv Exp $]

******************************************************************************/

#include "CheckerGame.h"
#include "CheckerGame_private.h"
#include "addons/game/parser/game_symbols.h"

#include "compile/compile.h"
#include "compile/symb_table/symb_table.h"

#include "parser/symbols.h"
#include "utils/utils.h"
#include "utils/error.h"

static char rcsid[] UTIL_UNUSED = "$Id: CheckerGame.c,v 1.1.2.3 2010-02-08 15:28:10 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void checker_game_finalize ARGS((Object_ptr object, void* dummy));

static SymbType_ptr checker_game_check_expr ARGS((CheckerBase_ptr self,
                                                  node_ptr e,
                                                  node_ptr ctx));

static boolean checker_game_viol_handler ARGS((CheckerBase_ptr self,
                                               TypeSystemViolation violation,
                                               node_ptr expression));

static void print_operator ARGS((FILE* output_stream, node_ptr expr));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The CheckerGame class constructor. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ NodeWalker_destroy ]

******************************************************************************/
CheckerGame_ptr CheckerGame_create()
{
  CheckerGame_ptr self = ALLOC(CheckerGame, 1);
  CHECKER_GAME_CHECK_INSTANCE(self);

  checker_game_init(self);

  return self;
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The CheckerGame class private initializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ CheckerGame_create ]

******************************************************************************/
void checker_game_init(CheckerGame_ptr self)
{
  /* base class initialization */
  checker_base_init(CHECKER_BASE(self), "GAME Type Checker",
                    NUSMV_GAME_SYMBOL_FIRST,
                    NUSMV_GAME_SYMBOL_LAST - NUSMV_GAME_SYMBOL_FIRST);

  /* members initialization */

  /* virtual methods settings */
  OVERRIDE(Object, finalize) = checker_game_finalize;
  OVERRIDE(CheckerBase, check_expr) = checker_game_check_expr;
  OVERRIDE(CheckerBase, viol_handler) = checker_game_viol_handler;
}

/**Function********************************************************************

  Synopsis    [ The CheckerGame class private deinitializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ CheckerGame_destroy ]

******************************************************************************/
void checker_game_deinit(CheckerGame_ptr self)
{
  /* members deinitialization */

  /* base class deinitialization */
  checker_base_deinit(CHECKER_BASE(self));
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The CheckerGame class virtual finalizer. ]

  Description [ Called by the class destructor. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void checker_game_finalize(Object_ptr object, void* dummy)
{
  CheckerGame_ptr self = CHECKER_GAME(object);

  checker_game_deinit(self);
  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Checks the given node. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ CheckerBase_check_expr ]

******************************************************************************/
static SymbType_ptr checker_game_check_expr(CheckerBase_ptr self,
                                            node_ptr expr,
                                            node_ptr context)
{
  /* Wrap expr into the context. This is required by the facilities
     which remembers the type of expressions and by the violation
     handler.
  */
  node_ptr ctx_expr;
  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  if (context != Nil) ctx_expr = find_node(nodemgr,CONTEXT, context, expr);
  else ctx_expr = expr;

  { /* checks memoizing */
    SymbType_ptr tmp = _GET_TYPE(ctx_expr);
    if (nullType != tmp) return tmp;
  }

  switch (node_get_type(expr)) {
  case GAME:
    /* statements and expressions are type checked, not
       the whole GAME
    */
    nusmv_assert(false);

    /* these are the usual specifications. Therefore the same code as
       in CheckerStatements.c for specification is used.
    */
  case REACHTARGET:
  case AVOIDTARGET:
  case REACHDEADLOCK:
  case AVOIDDEADLOCK:
  case BUCHIGAME:
  case LTLGAME:
  case GENREACTIVITY:
  {
    /* get the operand's type */
    SymbType_ptr type = _THROW(car(expr), Nil);

    if (SymbType_is_error(type)) {
      /* earlier error */
      return _SET_TYPE(ctx_expr, SymbTablePkg_error_type());
    }

    /* The operand must be boolean or statement-type (statements can
       be produced by predicate-normalisation in symbolic FSMs (when
       assignments are pushed into expressions). */
    if (SymbType_is_boolean(type) || SymbType_is_statement(type)) {
      return _SET_TYPE(ctx_expr, type);
    }

    /* there is violation */
    if (_VIOLATION(TC_VIOLATION_TYPE_MANDATORY, expr)) {
      return _SET_TYPE(ctx_expr, SymbTablePkg_error_type());
    }

    /* this is not an error after all -> keeps the current type */
    return _SET_TYPE(ctx_expr, type);
  }

  /* this exp is just wrapper. just return the type of operand */
  case GAME_SPEC_WRAPPER:
    return _SET_TYPE(ctx_expr, _THROW(cdr(expr), context));

  /* this exp is just wrapper. just return the type of operand */
  case GAME_EXP_LIST: /* CONS in CheckerCore.c will check the list */
    return _SET_TYPE(ctx_expr, _THROW(car(expr), context));

  /* CONS in CheckerCore.c will check the lists. Then behave the same
     way as CONS, i.e. return the least common type.
  */
  case GAME_TWO_EXP_LISTS: /* two exp lists */
  {
    SymbType_ptr returnType;

    /* get the operands' type */
    SymbType_ptr type1 = _THROW(car(expr), context);
    SymbType_ptr type2 = _THROW(cdr(expr), context);

    if (SymbType_is_error(type1) || SymbType_is_error(type2)) {
      /*earlier error*/
      return _SET_TYPE(ctx_expr, SymbTablePkg_error_type());
    }

    /* implicit conversion to the least common type of the operands */
    returnType = SymbType_get_minimal_common(type1, type2);

    /* types can be implicitily converted to one type */
    if (nullType != returnType) {
      return _SET_TYPE(ctx_expr, returnType);
    }
    /* is this a type error ? */
    if (_VIOLATION(TC_VIOLATION_TYPE_MANDATORY, ctx_expr)) {
      return _SET_TYPE(ctx_expr, SymbTablePkg_error_type());
    }

    /* this is not an error after all -> return left operand's type */
    return _SET_TYPE(ctx_expr, type1);
  }

  default:
    internal_error("checker_game_check_expr: not supported type");
  }

  nusmv_assert(false); /* impossible code */
  return nullType;
}

/**Function********************************************************************

  Synopsis    [ The type core violation handler. ]

  Description [ The violation handler is implemented as a virtual
                method, which is invoked by the checker when an
                expression being checked violates the type system.
                See the violation handler
                TypeCheckingViolationHandler_ptr for more
                explanations.

                The function elow is the default violation handler,
                and a user can potentially define its own violation
                handler, by deriving a new class from this class and
                by overriding this virtual method.

                This violation handler outputs only error messages (no
                warnings) and always returns true (indicating that
                this is an error, not a warning).

                NB: if the expression is checked in some context
                    (context is not Nil) then before providing the
                    expression to this function the expression should
                    be wrapped into context, i.e., with
                    find_node(nodemgr,CONEXT, context, expr). ]

  SideEffects [ ]

  SeeAlso     [ TypeSystemViolation

******************************************************************************/
static boolean checker_game_viol_handler(CheckerBase_ptr self,
                                         TypeSystemViolation violation,
                                         node_ptr expression)
{
  /* get rid of the context the expression may be wrapped in */
  node_ptr context = Nil;
  node_ptr expr = expression;
  if (node_get_type(expression) == CONTEXT) {
    context = car(expression);
    expr = cdr(expression);
  }

  _PRINT_ERROR_MSG(expr, true);

  /* this function is very simplified, because only one error situation is
     expected : TC_VIOLATION_TYPE_MANDATORY
  */
  nusmv_assert(TC_VIOLATION_TYPE_MANDATORY == violation);

  fprintf(nusmv_stderr, "illegal ");

  switch (node_get_type(expr)) {
  case GAME:
    nusmv_assert(false); /* this is impossible */

  case REACHTARGET:
  case AVOIDTARGET:
  case REACHDEADLOCK:
  case AVOIDDEADLOCK:
  case BUCHIGAME:
  case LTLGAME:
  case GENREACTIVITY:
    fprintf(nusmv_stderr,"type of ");
    print_operator(nusmv_stderr, expr);
    fprintf(nusmv_stderr," expression : ");
    checker_base_print_type(self, nusmv_stderr, car(expr), context);
    break;

  case GAME_SPEC_WRAPPER:
  case GAME_EXP_LIST:
    nusmv_assert(false);    /* this node cannot generate an error */

  case GAME_TWO_EXP_LISTS: /* two exp lists */
    fprintf(nusmv_stderr, "operand types of \"");
    print_operator(nusmv_stderr, expr);
    fprintf(nusmv_stderr,"\" : ");
    checker_base_print_type(self, nusmv_stderr, car(expr), context);
    fprintf(nusmv_stderr," and ");
    checker_base_print_type(self, nusmv_stderr, cdr(expr), context);
    break;

  default:
    nusmv_assert(false); /* unknown kind of exp */

  } /* switch (violation) */

  return true;
}

/**Function********************************************************************

  Synopsis    [ Just prints an expression's operator to output_stream. ]

  Description [ This function is the almost the same as print_sexp,
                except this function does not print the children of
                the node.  The expr must be a correct expression.  The
                function is used in printing of an error messages
                only. ]

  SideEffects [ ]

  SeeAlso     [ print_sexp ]

******************************************************************************/
static void print_operator(FILE* output_stream, node_ptr expr)
{
  nusmv_assert((FILE *) NULL != output_stream);
  nusmv_assert(expr != Nil);

  switch (node_get_type(expr)) {
  case GAME:               fprintf(output_stream, "\n(GAME "); return;

  case REACHTARGET:        fprintf(output_stream, "REACHTARGET"); return;
  case AVOIDTARGET:        fprintf(output_stream, "AVOIDTARGET"); return;
  case REACHDEADLOCK:      fprintf(output_stream, "REACHDEADLOCK"); return;
  case AVOIDDEADLOCK:      fprintf(output_stream, "AVOIDDEADLOCK"); return;
  case BUCHIGAME:          fprintf(output_stream, "BUCHIGAME"); return;
  case LTLGAME:            fprintf(output_stream, "LTLGAME"); return;
  case GENREACTIVITY:      fprintf(output_stream, "GENREACTIVITY"); return;
  case GAME_SPEC_WRAPPER:  fprintf(output_stream, "GAME_SPEC_WRAPPER"); return;
  case GAME_EXP_LIST:      fprintf(output_stream, "GAME_EXP_LIST"); return;
  case GAME_TWO_EXP_LISTS: fprintf(output_stream, "->"); return;

  default:
    fprintf(nusmv_stderr, "\n%d\n", node_get_type(expr));
    nusmv_assert(false);
  }
}

/**AutomaticEnd***************************************************************/
