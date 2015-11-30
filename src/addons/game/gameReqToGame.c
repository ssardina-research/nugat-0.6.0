/**CFile***********************************************************************

  FileName    [ gameReqToGame.c ]

  PackageName [ game ]

  Synopsis    [ The file contains functions to convert an arbitrary set
                of requirements (assumptions and guarantees) to a game
                structure. These functions are used by the XML
                reader. ]

  Description [ ]

  Author      [ Andrei Tchaltsev ]

  Copyright   [
  This file is part of the ``game'' package of NuGaT.
  Copyright (C) 2010 by FBK-irst.

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

******************************************************************************/

#include "parser/game_symbols.h"

#include "node/node.h"
#include "parser/symbols.h"
#include "parser/psl/pslNode.h"
#include "utils/utils.h"
#include "utils/assoc.h"
#include "utils/error.h"
#include "utils/ustring.h"
#include "gameInt.h"

#include <stdio.h>
#include <code/nusmv/core/compile/type_checking/checkers/CheckerBase.h>

static char rcsid[] UTIL_UNUSED = "$Id: gameReqToGame.c,v 1.1.2.9 2010/02/12 19:37:46 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/* undef to disable resorting to LTLGAME for cases that cannot be
   translated into GR(1). */
/* #undef GAME_REQ_TO_GAME_USE_LTLGAME */
#define GAME_REQ_TO_GAME_USE_LTLGAME

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Enum**********************************************************************

  Synopsis    [ This is a list of expectations of particular values of an
                expression. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
enum expected_value_TAG {
  TOP_LEVEL,          /* An expression is a top level expression (or
                         one of its conjuncts). As a result the
                         expression has to be TRUE. */
  DETERMINISTIC_TRUE, /* From a current state if required a player can
                         deterministically infer that the value of the
                         expression has to be TRUE. For example, "(G
                         a) OR b" where a and b are propositions. If b
                         is false then "G a" is true. Otherwise, the
                         value of "G a" is of no importance. If a
                         subexpression has this tag then this
                         subexpression can be substituted by a fresh
                         variable. */
  UNKNOWN_VALUE       /* All other expressions, i.e., a player cannot
                         infer for sure which value the expression has
                         to be. */
};
typedef enum expected_value_TAG expected_value;

/**Enum**********************************************************************

  Synopsis    [ This is a list of kinds of expressions. ]

  Description [ Values must be ordered from the simplest to the most
                complex. ]

  SeeAlso     [ ]

******************************************************************************/
enum exp_kind_TAG {
  PURE_PROPOSITIONAL, /* Expression without temporal operations. */
  ONCE_NEXT,          /* Expression containing applications of NEXT
                         without nesting. */
  TEMPORAL,           /* Expression with other temporal operators or
                         nested NEXT. */
};
typedef enum exp_kind_TAG exp_kind;

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/**Variable********************************************************************

  Synopsis    [ A hash table for all variables: name -> its type. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
static hash_ptr nameToType;

/**Variable********************************************************************

  Synopsis    [ A hash table: an expression -> its kind. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
static hash_ptr expToKind;

EXTERN int nusmv_yylineno;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static node_ptr game_and_exp ARGS((NodeMgr_ptr nodemgr, node_ptr exp1, node_ptr exp2));

static void game_fill_in_var_hash_table ARGS((NodeMgr_ptr nodemgr,node_ptr inVarList,
                                              node_ptr outVarList));

static node_ptr game_create_unique_name ARGS((NuSMVEnv_ptr env));

static node_ptr game_create_new_var ARGS((NuSMVEnv_ptr env, node_ptr* list, node_ptr type));

static exp_kind game_set_expression_kind ARGS((node_ptr exp,
                                               exp_kind kind));

static exp_kind game_get_expression_kind ARGS((node_ptr exp));

static node_ptr game_normalize_syntactically ARGS((node_ptr exp,
                                                   boolean negated));

static node_ptr game_concatenate_lists ARGS((node_ptr list,
                                             node_ptr exp,
                                             node_ptr reuse));

static node_ptr game_combine_two_next ARGS((node_ptr exp1,
                                            node_ptr exp2,
                                            int op));

static exp_kind game_property_to_game ARGS((NuSMVEnv_ptr env,
                                            node_ptr* exp,
                                            expected_value value,
                                            node_ptr* varList,
                                            node_ptr* init,
                                            node_ptr* trans,
                                            node_ptr* req));

/* ---------------------------------------------------------------------- */
/*     Definition of exported functions                                   */
/* ---------------------------------------------------------------------- */

/**Function********************************************************************

  Synopsis    [ The function takes two PSL expressions representing the
                specifications of the two players, respectively, and
                converts the expressions to the subparts of a game. ]

  Description [ The function tries to convert the PSL expressions into
                classes of games that are easier than arbitrary LTL
                games (REACHTARGET, AVOIDTARGET, BUCHIGAME,
                GENREACTIVITY). If that fails it resorts to an LTLGAME
                of the form (& assumptions) -> (& guarantees). Note
                that the semantics between the simplified classes and
                the LTLGAME are slightly different in their handling
                when both players violate their parts: the LTLGAME
                shape doesn't take into account who vioates first.

                The translation into the easier game classes works as
                follows:

                - Every given exp is converted and divided into 3
                  sets: initial conditions init (containing no
                  temporal operators), transition relations trans
                  (containing only next temporal operator and assumed
                  to be under Always), and remaining expressions (free
                  requirements).

                - Requirements of both expressions are then converted
                  to a realizability (game) property for the second
                  player.

                Parameters inputVars and outputVars are lists of
                (var,its-type) pairs of all input and output
                variables. During the conversions new vars may be
                added.

                Before processing PSL expression are converted to SMV
                (including "forall" expansion).

                The returned true means success, and false means an
                error (error messaged are printed in this case). ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
boolean Game_PropertyToGame(NuSMVEnv_ptr env,
                            node_ptr* inputVars,
                            node_ptr* outputVars,
                            node_ptr exp_1,
                            node_ptr* init_1,
                            node_ptr* trans_1,
                            node_ptr exp_2,
                            node_ptr* init_2,
                            node_ptr* trans_2,
                            node_ptr* property)
{
  node_ptr req_1 = Nil;
  node_ptr req_2 = Nil;
  node_ptr inputVars_orig;  /* Stores the original list of input
                               variables; this relies on new variables
                               being added to the front. */
  node_ptr outputVars_orig; /* Stores the original list of output
                               variables; this relies on new variables
                               being added to the front. */
  node_ptr exp_1_orig;      /* Stores the original unPSL-ed exp_1. */
  node_ptr exp_2_orig;      /* Stores the original unPSL-ed exp_2. */

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  nameToType = new_assoc();
  expToKind = new_assoc();

  game_fill_in_var_hash_table(nodemgr,*inputVars, *outputVars);

  /* Store inputVars, outputVars. */
  inputVars_orig = *inputVars;
  outputVars_orig = *outputVars;

  /* Get rid of all PSL operators, i.e., convert to usual SMV format. */
  exp_1 = PslNode_convert_psl_to_core(env,exp_1);
  exp_2 = PslNode_convert_psl_to_core(env,exp_2);

  /* Store exp_1, exp_2. */
  exp_1_orig = exp_1;
  exp_2_orig = exp_2;

  /* Perform at first syntactic transformations and then convert the
     exp to a game structure. */
  if (exp_1 != Nil) {
    exp_1 = game_normalize_syntactically(exp_1, false);

//    /* debugging printing */
//    fprintf(stderr,"\n-- SIMPLIFIED:"); print_node(nusmv_stderr, exp_1);

    game_property_to_game(env,
                          &exp_1,
                          TOP_LEVEL,
                          inputVars,
                          init_1,
                          trans_1,
                          &req_1);
  }

  if (exp_2 != Nil) {
    exp_2 = game_normalize_syntactically(exp_2, false);

//    /* debugging printing */
//    fprintf(stderr,"\n-- SIMPLIFIED:"); print_node(nusmv_stderr, exp_2);

    game_property_to_game(env,
                          &exp_2,
                          TOP_LEVEL,
                          outputVars,
                          init_2,
                          trans_2,
                          &req_2);
  }

//  fprintf(stderr,"\n\n");/* debugging printing */

  /* All the expressions were processed. */
  nusmv_assert(Nil == exp_1 && Nil == exp_2);


  /* --- Convert the requirements into a property. --- */

  /* Success is set to true if one of the special cases below
     succeeds. Otherwise resort to LTLGAME. */
  boolean success = false;

  {
    /* At first reset the value of game_get_expression_kind function. */
    free_assoc(expToKind);
    expToKind = new_assoc();

    /* Check if both reqs are Nil => create an avoid-deadlock game. */
    if (Nil == req_1 && Nil == req_2) {
      *property = new_node(nodemgr,AVOIDDEADLOCK, NODE_FROM_INT(2), Nil);
      success = true;
    }
    /* Check if this is a reachability game. */
    if ((!success) &&
        (Nil == req_1 && Nil != req_2 && OP_FUTURE == node_get_type(req_2) &&
         PURE_PROPOSITIONAL == game_get_expression_kind(car(req_2)))) {
      *property = new_node(nodemgr,REACHTARGET, NODE_FROM_INT(2), car(req_2));
      success = true;
    }
    /* Check if this is an avoidance game. */
    if ((!success) &&
        (Nil == req_2 && Nil != req_1 && OP_FUTURE == node_get_type(req_1) &&
         PURE_PROPOSITIONAL == game_get_expression_kind(car(req_1)))) {
      *property = new_node(nodemgr,REACHTARGET, NODE_FROM_INT(1), car(req_1));
      success = true;
    }
    /* Check if this is a buchi or gen-reactivity game. */
    if (!success) {
      /* Convert each req into a list. AND are already in the form of a list. */
      node_ptr iter;

      success = true; /* Set to false later if things don't work out. */

      if (req_1 != Nil) {
        if (node_get_type(req_1) != AND) { /* just one element */
          req_1 = new_lined_node(nodemgr,CONS, req_1, Nil, node_get_lineno(req_1));
        }
        else { /* AND-list to CONS-list conversions */
          for (iter = req_1; node_get_type(cdr(iter)) == AND; iter = cdr(iter)) {
            node_set_type(iter, CONS);
          }
          node_set_type(iter, CONS);
          node_node_setcdr(iter, cons(nodemgr,cdr(iter), Nil));
        }
      }

      if (req_2 != Nil) {
        if (node_get_type(req_2) != AND) { /* just one element */
          req_2 = new_lined_node(nodemgr,CONS, req_2, Nil, node_get_lineno(req_2));
        }
        else { /* AND-list to CONS-list conversions */
          for (iter = req_2; node_get_type(cdr(iter)) == AND; iter = cdr(iter)) {
            node_set_type(iter, CONS);
          }
          node_set_type(iter, CONS);
          node_node_setcdr(iter, cons(nodemgr,cdr(iter), Nil));
        }
      }
      /* Here req 2 must be not Nil. Create dummy requirement: "G F true". */
      if (Nil == req_2) {
        req_2 = cons(nodemgr,new_node(nodemgr,OP_GLOBAL,
                              new_node(nodemgr,OP_FUTURE,
                                       new_node(nodemgr,TRUEEXP, Nil, Nil),
                                       Nil),
                              Nil),
                     Nil);
      }

      /* Check that req are list of G F expressions only and then
         remove that G F. */
      for (iter = req_1; iter != Nil; iter = cdr(iter)) {
        node_ptr exp = car(iter);
        if (node_get_type(exp) != OP_GLOBAL ||
            node_get_type(car(exp)) != OP_FUTURE ||
            PURE_PROPOSITIONAL != game_get_expression_kind(car(car(exp)))) {
#ifndef GAME_REQ_TO_GAME_USE_LTLGAME
          ErrorMgr_rpterr(errmgr,"Requirement-to-game translation cannot deal with following "
                 "first player requirement : %s", sprint_node(exp));
          /* not need to free. This is exit point */
#else
          success = false;
#endif
        }
        node_node_setcar(iter, car(car(exp)));
      }

      for (iter = req_2; iter != Nil; iter = cdr(iter)) {
        node_ptr exp = car(iter);
        if (node_get_type(exp) != OP_GLOBAL ||
            node_get_type(car(exp)) != OP_FUTURE ||
            PURE_PROPOSITIONAL != game_get_expression_kind(car(car(exp)))) {
#ifndef GAME_REQ_TO_GAME_USE_LTLGAME
          ErrorMgr_rpterr(errmgr,"Requirement-to-game translation cannot deal with following "
                 "second player requirement : %s", sprint_node(exp));
          /* not need to free. This is exit point */
#else
          success = false;
#endif
        }
        node_node_setcar(iter, car(car(exp)));
      }

      /* Create the property, buchi or gen-reactivity. */
      if (success) {
        if (Nil == req_1) {
          *property = new_node(nodemgr,BUCHIGAME, NODE_FROM_INT(2),
                               new_node(nodemgr,GAME_EXP_LIST, req_2, Nil));
        }
        else {
          *property = new_node(nodemgr,GENREACTIVITY, NODE_FROM_INT(2),
                               new_node(nodemgr,GAME_TWO_EXP_LISTS, req_1, req_2));
        }
      }

    } /* end of buchi or gen-reactivity game */
#ifndef GAME_REQ_TO_GAME_USE_LTLGAME
    nusmv_assert(success);
#else
    /* Resort to LTLGAME. */
    if (!success) {

      *inputVars = inputVars_orig;
      *outputVars = outputVars_orig;
      *init_1 = Nil;
      *trans_1 = Nil;
      *init_2 = Nil;
      *trans_2 = Nil;

      /* Terminate AND chains with TRUEEXP. */
      if (exp_1_orig == Nil) {
        exp_1_orig = find_node(nodemgr,TRUEEXP, Nil, Nil);
      } else {
        node_ptr iter = exp_1_orig;
        if (node_get_type(iter) == AND) {
          while(cdr(iter) != Nil) {
            iter = cdr(iter);
          }
          node_node_setcdr(iter, find_node(nodemgr,TRUEEXP, Nil, Nil));
        }
      }
      if (exp_2_orig == Nil) {
        exp_2_orig = find_node(nodemgr,TRUEEXP, Nil, Nil);
      } else {
        node_ptr iter = exp_2_orig;
        if (node_get_type(iter) == AND) {
          while(cdr(iter) != Nil) {
            iter = cdr(iter);
          }
          node_node_setcdr(iter, find_node(nodemgr,TRUEEXP, Nil, Nil));
        }
      }

      *property = new_node(nodemgr,LTLGAME,
                           NODE_FROM_INT(2),
                           new_node(nodemgr,IMPLIES,
                                    exp_1_orig,
                                    exp_2_orig));
    }
#endif
  } /* end of property construction */

  free_assoc(nameToType);
  free_assoc(expToKind);
  return true;
  /* Here we do not care about freeing memory in the case of abnormal
     termination since NuGaT is expected to exit immediately in this
     case.
  */
}

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Builds the AND of two expressions. ]

  Description [ If any of expressions is Nil the other one is returned. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr game_and_exp(NodeMgr_ptr nodemgr, node_ptr exp1, node_ptr exp2)
{
  if (Nil == exp1) return exp2;
  if (Nil == exp2) return exp1;
  return new_lined_node(nodemgr,AND, exp1, exp2, node_get_lineno(exp2));
}

/**Function********************************************************************

  Synopsis    [ Fills in the hash table of variable names and its types. ]

  Description [ Input are 2 lists of (var, type) pairs. The hash table
                is global nameToType. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_fill_in_var_hash_table(NodeMgr_ptr nodemgr,node_ptr inVarList, node_ptr outVarList)
{
  node_ptr iter;

  for (iter = inVarList; iter != Nil; iter = cdr(iter)) {
    nusmv_assert(CONS == node_get_type(iter)); /* this is a list */
    insert_assoc(nameToType, find_atom(nodemgr,car(car(iter))), cdr(car(iter)));
  }

  for (iter = outVarList; iter != Nil; iter = cdr(iter)) {
    nusmv_assert(CONS == node_get_type(iter)); /* this is a list */
    insert_assoc(nameToType, find_atom(nodemgr,car(car(iter))), cdr(car(iter)));
  }
}

/**Function********************************************************************

  Synopsis    [ Returns a node ATOM with a unique name. ]

  Description [ The returned node is find_atom-ed. Uniqueness is
                w.r.t. the variables stored in 'nameToType'. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr game_create_unique_name(NuSMVEnv_ptr env)
{
  static int i= 0;
  char buffer[100]; /* Should be able to hold longest value of i + 5. */
  node_ptr res;
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  do {
    sprintf(buffer, "_un_%i", ++i);
    res = find_node(nodemgr,ATOM, (node_ptr) UStringMgr_find_string(strings,buffer), Nil);
  } while(Nil != find_assoc(nameToType, res));

  return res;
}

/**Function********************************************************************

  Synopsis    [ Creates a new var with of type 'type' and inserts the
                (name, type) association into the 'nameToType' hash
                table and into the list of vars 'list'. ]

  Description [ Returns the name of new var. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr game_create_new_var(NuSMVEnv_ptr env, node_ptr* list, node_ptr type)
{
  node_ptr name;
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  name = game_create_unique_name(env); /* name is already find_atom-ed */
  insert_assoc(nameToType, name, type);
  *list = cons(nodemgr,new_node(nodemgr,COLON, name, type), *list);

  return name;
}

/**Function********************************************************************

  Synopsis    [ Sets the kind of an expression to the given kind. ]

  Description [ If the expression had some kind it will be rewritten.
                The returned value is equal to parameter 'kind'. ]

  SideEffects [ ]

  SeeAlso     [ game_get_expression_kind ]

******************************************************************************/
static exp_kind game_set_expression_kind(node_ptr exp, exp_kind kind)
{
  insert_assoc(expToKind, exp, (node_ptr) kind);

  return kind;
}

/**Function********************************************************************

  Synopsis    [ Returns the kind of an expression. ]

  Description [ If the kind is unknown yet the kind is inferred,
                remembered and returned.

                Note: if an expression has been processed by
                      game_property_to_game the returned value may be
                      wrong. ]

  SideEffects [ The kind of expression is stored in 'expToKind'. ]

  SeeAlso     [ game_set_expression_kind ]

******************************************************************************/
static exp_kind game_get_expression_kind(node_ptr exp)
{
  node_ptr p = find_assoc(expToKind, exp);

  if (Nil != p) return (exp_kind) p;

  /* Compute kind. */
  {
    exp_kind kind1 = -1; /* wrong value for debugging*/
    exp_kind kind2 = -1; /* wrong value for debugging*/
    int type = node_get_type(exp);

    switch (type) {

    /* --- leaves --- */
    case FAILURE:
    case FALSEEXP:
    case TRUEEXP:
    case NUMBER:
    case NUMBER_UNSIGNED_WORD:
    case NUMBER_SIGNED_WORD:
    case NUMBER_FRAC:
    case NUMBER_REAL:
    case NUMBER_EXP:
    case TWODOTS:
    case DOT:
    case ATOM:
    case SELF:
    case ARRAY:
      kind1 = PURE_PROPOSITIONAL;
      break;

    /* --- unary --- */
    case NOT:
    case CAST_BOOL:
    case CAST_WORD1:
    case CAST_SIGNED:
    case CAST_UNSIGNED:
    case UMINUS:
      kind1 = game_get_expression_kind(car(exp));
      break;

    /* --- binary --- */
    case AND:
    case OR:
    case IMPLIES:
    case XOR:
    case XNOR:
    case IFF:
    case CASE:
    case COLON:
    case EQUAL:
    case NOTEQUAL:
    case BIT_SELECTION:
    case CONCATENATION:
    case EXTEND:
    case TIMES:
    case DIVIDE:
    case PLUS:
    case MINUS:
    case MOD:
    case LSHIFT:
    case RSHIFT:
    case UNION:
    case SETIN:
    case LT:
    case GT:
    case LE:
    case GE:
      kind1 = game_get_expression_kind(car(exp));
      kind2 = game_get_expression_kind(cdr(exp));
      kind1 = kind1 > kind2 ? kind1 : kind2; /* the bigger kind is returned */
      break;

    /* --- LTL --- */

    case NEXT:
      kind1 = game_get_expression_kind(car(exp));
      kind1 = PURE_PROPOSITIONAL == kind1 ? ONCE_NEXT : TEMPORAL;
      break;

    case OP_GLOBAL:
    case OP_FUTURE:
    case UNTIL:
    case RELEASES:
      kind1 = TEMPORAL;
      break;

    default:
      nusmv_assert(false);
    }; /* switch */

    return game_set_expression_kind(exp, kind1);
  }
}

/**Function********************************************************************

  Synopsis    [ Used by game_normalize_syntactically. Takes a tree of AND
                (OR) nodes and converts it to a list. Then it pushes
                NEXT from the operands up. ]

  Description [ Operands of an expression are assumed to be already
                normalized by this function.

                Example of tree to list conversion:
                ((a AND b) AND (c AND d))
                is converted to
                (a AND (b AND (c AND d))).

                Then all of a, b, c and d constituting NEXT
                expressions are grouped together and NEXT is applied
                to all of them. For example,
                (((X a) AND b) AND (X c) AND (X d))
                is converted to
                ((X (a AND c AND d)) AND b)

                If the operator is OR then together with NEXT also
                FUTURE(eventually) is pushed up.

                Note that the NEXT (FUTURE) operator can be only the
                the left operand of AND (OR) and never on the right.

                Currently this is only used for OR. ]

  SideEffects [ The input expression may be modified. ]

  SeeAlso     [ game_normalize_syntactically ]

******************************************************************************/
static void game_convert_to_list_and_push_next_up(node_ptr *exp)
{
  const int type = node_get_type((*exp));
  node_ptr left = car(*exp);
  node_ptr right = cdr(*exp);

  nusmv_yylineno = node_get_lineno((*exp)); /* line info for new nodes */

  /* Currently this is only used for OR by the caller. Check this. */
  nusmv_assert(type == OR);

  if (type == node_get_type(left) && type == node_get_type(right)) {
    /* Lists are on both sides. */

    /* NEXT is in on both lists. Combine and move NEXT to the left. */
    if ((node_get_type(car(left)) == NEXT &&
         node_get_type(car(right)) == NEXT) ||
        (type == OR &&
         node_get_type(car(left)) == OP_FUTURE &&
         node_get_type(car(right)) == OP_FUTURE)) {
      node_node_setcar(left,
                       game_combine_two_next(car(left), car(right), type));
      right = cdr(right);
    }
    /* NEXT is on the right side only. Swap left and right */
    else if (node_get_type(car(right)) == NEXT ||
             (type == OR && node_get_type(car(right)) == OP_FUTURE)) {
      node_ptr tmp = left;
      left = right;
      right = tmp;
    }

    /* Now there is no NEXT on the right. Hence, just combine the
       lists. */
    *exp = game_concatenate_lists(left, right, *exp);
  }
  else if (type == node_get_type(right)) {
    /* A list is on the right only. */

    /* NEXT on both left and right. Combine and move NEXT to the left. */
    if ((NEXT == node_get_type(left) && NEXT == node_get_type(car(right))) ||
        (type == OR &&
         OP_FUTURE == node_get_type(left) &&
         OP_FUTURE == node_get_type(car(right)))) {
      node_node_setcar((*exp), game_combine_two_next(left, car(right), type));
      node_node_setcdr((*exp), cdr(right));
    }
    /* NEXT is only on the right. Swap with the left. */
    else if (NEXT == node_get_type(car(right)) ||
             (type == OR && OP_FUTURE == node_get_type(car(right)))) {
      node_node_setcar((*exp), car(right));
      node_node_setcar(right, left);
    }
    else {
      /* No NEXT on the right. Hence, exp is already normalized. */
    }
  }
  else if (type == node_get_type(left)) {
    /* A list is on the left only. Swap left and right and rerun the
       function. */

    node_node_setcar((*exp), right);
    node_node_setcdr((*exp), left);
    game_convert_to_list_and_push_next_up(exp);
  }
  /* In the remaining cases below there is no list on either side. */
  else if ((NEXT == node_get_type(left) && NEXT == node_get_type(right)) ||
           (type == OR &&
            OP_FUTURE == node_get_type(left) &&
            OP_FUTURE == node_get_type(right))) {
    /* NEXT on both sides. Just combine them. */

    *exp = game_combine_two_next(left, right, type);
    return;
  }
  else if ( NEXT == node_get_type(right)
          ||(type == OR && OP_FUTURE == node_get_type(right))) {
    /* NEXT on right only. Move it to the left. */

    node_node_setcar((*exp), right);
    node_node_setcdr((*exp), left);
  }
  else {
    /* There is no NEXT on the right and there is no list. Hence, exp
       is normalized. */
  }

  return;
}

/**Function********************************************************************

  Synopsis    [ The function takes an AND or OR list and appends 'exp' to
                the end. ]

  Description [ Node 'reuse' can be used instead of creation of a new
                node. The returned value is always the parameter
                'list'. ]

  SideEffects [ The input expressions are modified. ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr game_concatenate_lists(node_ptr list,
                                       node_ptr exp,
                                       node_ptr reuse)
{
  node_ptr iter;
  const int op = node_get_type(list);

  nusmv_assert(AND == op || OR == op);

  /* Find the last element of the list. */
  for (iter = list; node_get_type(cdr(iter)) == op; iter = cdr(iter)) {};

  node_node_setcar(reuse, cdr(iter)); /* last element of the list */
  node_node_setcdr(reuse, exp);
  node_node_setcdr(iter, reuse);

  return list;
}

/**Function********************************************************************

  Synopsis    [ Converts "(NEXT x) op (NEXT y)" to "NEXT (x op y)". ]

  Description [ Given two NEXT expressions 'exp1' and 'exp2', the
                function combines them (with the binary operation
                'op'), pushes NEXT up and normalizes the obtained
                expression. 'op' is expected to be AND or OR only. If
                'op' is OR then FUTURE behaves the same way as NEXT.

                This is an auxiliary function used by
                game_convert_to_list_and_push_next_up only. ]

  SideEffects [ The input expressions are modified. ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr game_combine_two_next(node_ptr exp1, node_ptr exp2, int op)
{
  const int type1 = node_get_type(exp1);
  const int type2 = node_get_type(exp2);

  nusmv_assert((type1 == NEXT && type2 == NEXT && (AND == op || OR == op)) ||
               (type1 == OP_FUTURE && type2 == OP_FUTURE && OR == op));

  node_set_type(exp1, op);
  node_node_setcdr(exp1, car(exp2));
  game_convert_to_list_and_push_next_up(&exp1); /* normalize new AND or OR */
  node_node_setcar(exp2, exp1);

  return exp2;
}

/**Function********************************************************************

  Synopsis    [ Performs various syntactic transformation to simplify the
                conversion from an expression to a game. ]

  Description [ If 'negated' is true, then current expression is
                negated.

                The conversions try to achive the following:

                1. Rewrite operators that are not handled directly.

                2. Push negations towards the bottom of the syntax
                   tree.

                3. Push disjunctions towards the bottom of the syntax
                   tree, but not below negations. Transform trees of
                   disjunctions into lists.

                4. Push conjunctions towards the top of the syntax
                   tree. Transform trees of conjunctions into lists.

                5. Push next operators towards the top of the syntax
                   tree, but not above conjunctions. Finally, convert
                   X to next.

                6. Perform some optimizations.

                The conversions performed are:

                1a. a -> b ==> !a OR b.

                2a. Push NOT below temporal operators (to allow state
                    determinism, see game_property_to_game).

                3a. (F a) | (F b) ==> F (a | b).
                3b. (G F a) | (G F b) ==> G F (a | b).
                3c. Convert OR from trees to lists (to make 3a and b easier).

                4a. G (a & b) ==> (G a) & (G b).
                4b. X (a & b) ==> (X a) & (X b).
                4c. Convert AND from trees to lists.

                5a. F X a ==> X F a.
                5b. G X a ==> X G a.
                5c. (X a) OP (X b) ==> X (a OP b) where OP is OR,
                    XNOR, IFF, XOR, =, !=.
                5d. X a ==> next(a).

                6a. Nil nodes are removed from conjuncts.
                6b. G G a  ==> G a.
                6c. F F a  ==> F a.

                After the transformation AND and OR are represented as
                pure lists (the left operand of an AND (OR) is never
                another AND (OR)). Moreover, NEXT and FUTURE can be
                only on the left side of an OR:
                game_convert_to_list_and_push_next_up guarantees that.

                About 4b: It is necessary to divide X into two
                          expressions and process them separately. For
                          example, if 'a' contains X but 'b' is pure
                          propositional, and first player kill the
                          second one, 'b' must be satisfied in the
                          next state but 'a' may not.

                Note: An input expression may or may not be
                      shared. During normalization a new copy of the
                      whole expression will be created (except leaves)
                      with new_node function.

                Note: The rules above are not applied until a fixed
                      point is reached. Hence, currently, the result
                      is a formula that might leave room for
                      application of more rules. As an example
                      consider F!G p. ]

  SideEffects [ ]

  SeeAlso     [ game_convert_to_list_and_push_next_up, game_property_to_game ]

******************************************************************************/
static node_ptr game_normalize_syntactically(node_ptr exp, boolean negated)
{
  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(exp));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  node_ptr oprd1 = car(exp);
  node_ptr oprd2 = cdr(exp);

  int line = node_get_lineno(exp);
  int type = node_get_type(exp);

  switch(type) {

  /* --- unary propositional --- */
  case NOT: /* just change negation and skip the operation */
    exp = car(exp);
    return game_normalize_syntactically(exp, !negated);

  /* --- binary propositional --- */
  case AND: /* remove Nil from ANDs */
    if (Nil == car(exp)) {
      exp = cdr(exp);
      return game_normalize_syntactically(exp, negated);
    }
    else if (Nil == cdr(exp)) {
      exp = car(exp);
      return game_normalize_syntactically(exp, negated);
    }
    /* skip to OR */

  case OR:
    if (negated) type = (AND == type) ? OR : AND;

    oprd1 = game_normalize_syntactically(oprd1, negated);
    oprd2 = game_normalize_syntactically(oprd2, negated);
    exp = new_lined_node(nodemgr,type, oprd1, oprd2, line);

    /* make a list from the tree (for OR NEXTs have to be pushed up also) */
    if (AND == type && node_get_type(oprd1) == AND) {
      exp = game_concatenate_lists(oprd1, oprd2, exp);
    }
    else if (OR == type) {
      game_convert_to_list_and_push_next_up(&exp);
    }
    return exp;

  case IMPLIES: /* a -> b ==> !a OR b */
    exp = new_lined_node(nodemgr,OR, new_lined_node(nodemgr,NOT, oprd1, Nil, line), oprd2, line);
    return game_normalize_syntactically(exp, negated);

  /* --- ternary propositional --- */
  case CASE: {
    node_ptr cond = car(oprd1);
    node_ptr then = cdr(oprd1);
    /* process CASE */
    cond = game_normalize_syntactically(cond, false); /* condition is
                                                         never
                                                         negated */
    then = game_normalize_syntactically(then, negated);
    oprd1 = new_lined_node(nodemgr,COLON, cond, then, line);
    oprd2 = game_normalize_syntactically(oprd2, negated);
    exp = new_lined_node(nodemgr,CASE, oprd1, oprd2, line);
    return exp;
  }

  /* --- unary LTL --- */
  case OP_NEXT:
    oprd1 = game_normalize_syntactically(oprd1, negated);
    exp = new_lined_node(nodemgr,NEXT, oprd1, Nil, line);

    /* X (a AND b)  ==> (X a) AND (X b)
       Note that AND is a list (after normalization).
    */
    if (AND == node_get_type(oprd1)) {
      node_ptr iter;
      for (iter = oprd1; node_get_type(cdr(iter)) == AND; iter = cdr(iter)) {
        node_node_setcar(iter, new_lined_node(nodemgr,NEXT, car(iter), Nil, line));
      }
      /* last two elements */
      node_node_setcar(iter, new_lined_node(nodemgr,NEXT, car(iter), Nil, line));
      node_node_setcdr(iter, new_lined_node(nodemgr,NEXT, cdr(iter), Nil, line));

      exp = oprd1;
    }
    return exp;

  case OP_GLOBAL:
  case OP_FUTURE: /* G G a ==> G a  and  F F a => F a */
    if (node_get_type(oprd1) == type) {
      exp = oprd1;
      return game_normalize_syntactically(exp, negated);
    }
    /* F X a ==> X F a, G X a ==> X G a */
    else if (node_get_type(oprd1) == OP_NEXT) {
      exp = new_lined_node(nodemgr,OP_NEXT,
                           new_lined_node(nodemgr,type, car(oprd1), Nil, line),
                           Nil,
                           node_get_lineno(oprd1));
      return game_normalize_syntactically(exp, negated);
    }
    /* skip to UNTIL, RELEASES */

  /* --- binary LTL --- */
  case UNTIL:
  case RELEASES:
    /* change the operator to the complementary one */
    if (negated) {
      switch (type) {
      case OP_GLOBAL: type = OP_FUTURE; break;
      case OP_FUTURE: type = OP_GLOBAL; break;
      case UNTIL:     type = RELEASES;  break;
      case RELEASES:  type = UNTIL;     break;
      }
    }
    oprd1 = game_normalize_syntactically(oprd1, negated);
    if (oprd2 != Nil) {
      oprd2 = game_normalize_syntactically(oprd2, negated);
    }
    exp = new_lined_node(nodemgr,type, oprd1, oprd2, line);

    /* G (a AND b) ==> (G a) AND (G b)
       Note that AND is a list (after normalization).
    */
    if (OP_GLOBAL == type && AND == node_get_type(oprd1)) {
      node_ptr iter;
      for (iter = oprd1; node_get_type(cdr(iter)) == AND; iter = cdr(iter)) {
        if (OP_GLOBAL != node_get_type(car(iter))) {
          /* no need to apply G twice */
          node_node_setcar(iter,
                           new_lined_node(nodemgr,OP_GLOBAL, car(iter), Nil, line));
        }
      }
      /* the last two elements */
      if (OP_GLOBAL != node_get_type(car(iter))) {
        /* no need to apply G twice */
        node_node_setcar(iter, new_lined_node(nodemgr,OP_GLOBAL, car(iter), Nil, line));
      }
      if (OP_GLOBAL != node_get_type(cdr(iter))) {
        /* no need to apply G twice */
        node_node_setcdr(iter, new_lined_node(nodemgr,OP_GLOBAL, cdr(iter), Nil, line));
      }

      exp = oprd1;
    }
    return exp;


  /* Below are the expressions which do not participate in the
     transformation but have to be processed to substitute "X" with
     "next".
  */

  /* --- leaves --- */
  case FAILURE: return Nil; /* FAILURE is never processed */

  case FALSEEXP:
  case TRUEEXP:
  case NUMBER:
  case NUMBER_SIGNED_WORD:
  case NUMBER_UNSIGNED_WORD:
  case NUMBER_FRAC:
  case NUMBER_REAL:
  case NUMBER_EXP:
  case TWODOTS:
  case DOT:
  case ATOM:
  case SELF:
  case ARRAY:
    if (negated) exp = new_lined_node(nodemgr,NOT, exp, Nil, line);
    return exp;

  /* --- unary --- */
  case CAST_BOOL:
  case CAST_WORD1:
  case CAST_UNSIGNED:
  case CAST_SIGNED:
  case UMINUS:
    oprd1 = game_normalize_syntactically(oprd1, false);
    exp = new_lined_node(nodemgr,type, oprd1, Nil, line);
    if (negated) exp = new_lined_node(nodemgr,NOT, exp, Nil, line);
    return exp;

  /* --- binary --- */
  /* special care about boolean binary operators and NEXT */
  case XOR:
  case XNOR:
  case IFF:
  case EQUAL:
  case NOTEQUAL:
    if (negated) {
      type = ((type == XOR) ?
              XNOR :
              ((type == XNOR || type == IFF) ?
               XOR :
               ((type == EQUAL) ?
                NOTEQUAL :
                EQUAL)));
      negated = false;
    }
    /* skip to CONCATENATION etc. */

  case CONCATENATION:
  case EXTEND:
  case TIMES:
  case DIVIDE:
  case PLUS:
  case MINUS:
  case MOD:
  case LSHIFT:
  case RSHIFT:
  case UNION:
  case SETIN:
  case LT:
  case GT:
  case LE:
  case GE:
    oprd1 = game_normalize_syntactically(oprd1, false);
    oprd2 = game_normalize_syntactically(oprd2, false);
    exp = new_lined_node(nodemgr,type, oprd1, oprd2, line);
    if (negated) exp = new_lined_node(nodemgr,NOT, exp, Nil, line);

    /* (X a) OP (X b) ==> X (a OP B) where OP is one of above */
    if (node_get_type(oprd1) == NEXT && node_get_type(oprd2) == NEXT) {
      node_node_setcar(exp, car(oprd1));
      node_node_setcdr(exp, car(oprd2));
      exp = new_lined_node(nodemgr,NEXT, exp, Nil, line);
    }
    return exp;

  /* --- bit selections --- */
  case BIT_SELECTION: {
    node_ptr high = car(oprd2);
    node_ptr low = cdr(oprd2);

    nusmv_assert(COLON == node_get_type(oprd2)); /* a range expression */

    oprd1 = game_normalize_syntactically(oprd1, false);
    high = game_normalize_syntactically(high, false);
    low = game_normalize_syntactically(low, false);
    exp = new_lined_node(nodemgr,type,
                         oprd1,
                         new_lined_node(nodemgr,COLON, high, low, line),
                         line);
    if (negated) exp = new_lined_node(nodemgr,NOT, exp, Nil, line);
    return exp;
  }

  /* --- error --- */
  /* --- CTL --- */
  case EX:
  case AX:
  case EF:
  case AF:
  case EG:
  case AG:
  case ABU:
  case EBU:
  case EBF:
  case ABF:
  case EBG:
  case ABG:
  case AU:
  case EU:
    ErrorMgr_rpterr(errmgr,"Found CTL operator in an LTL expression.");

  default:
    nusmv_assert(false);
  }; /* switch */

  return Nil;
}

/**Function********************************************************************

  Synopsis    [ Takes an LTL expression and converts it to a subparts of
                a game. ]

  Description [ The given 'exp' is converted and divided into 3 sets
                which will be an initial condition 'init' (containing
                no temporal operators), transition relation 'trans'
                (containing only the next temporal operator and
                assumed to be under G(lobally)), and remaining
                expressions 'req'.

                'exp' is the expression to be converted, and (after
                the return of the function) the remaining part (not
                converted). 'exp' is expected to be already normalized
                (by game_normalize_syntactically).

                'value' is a kind of context of the position of the
                expression. See EXPECTED_VALUE. If 'value' ==
                TOP_LEVEL *exp will be Nil after the return of the
                function . At the moment there is no meaning to invoke
                this function with 'value' == UNKNOWN_VALUE since no
                conversion will be performed.

                'varList' is a list of (var, type) pairs. Every new
                var must be added to this list.

                'init', 'trans', and 'req' are lists (connected by
                AND) to return initial condition, transition relation
                and remaining requirements.

                The returned value is the kind of returned expression
                (in *exp). Note that game_get_expression_kind(*exp)
                may differ before and after the call to this function
                (since *exp may have been transformed). ]

  SideEffects [ *exp may be modified. ]

  SeeAlso     [ game_normalize_syntactically ]

******************************************************************************/
exp_kind game_property_to_game(NuSMVEnv_ptr env,
                               node_ptr* exp,
                               expected_value value,
                               node_ptr* varList,
                               node_ptr* init,
                               node_ptr* trans,
                               node_ptr* reqs)
{
  node_ptr res;
  exp_kind kind;
  int type;
  int line;
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  /* exp and *exp must not be Nil ever */
  nusmv_assert(((node_ptr*) NULL != exp) && (Nil != *exp));

  type = node_get_type((*exp));
  line = node_get_lineno((*exp));

  /* Below are various pattens we are able to deal with */
  switch (type) {

  /* -------------------- BASIC EXPRESSION -------------- */
  case FAILURE:
  case FALSEEXP:
  case TRUEEXP:
  case NUMBER:
  case NUMBER_SIGNED_WORD:
  case NUMBER_UNSIGNED_WORD:
  case NUMBER_FRAC:
  case NUMBER_REAL:
  case NUMBER_EXP:
  case TWODOTS:
  case DOT:
  case ATOM:
  case SELF:
  case ARRAY:
    kind = PURE_PROPOSITIONAL; /* do not change anything */
    break; /* check if this is a top level expression */

  /* -------------------- NOT, IMPLIES ------------------ */
  case NOT:
  case IMPLIES:
  /* After normalization NOT and IMPLIES can be applied only to
     propositional expressions. */
    nusmv_assert(PURE_PROPOSITIONAL == game_get_expression_kind(*exp));
    kind = PURE_PROPOSITIONAL;
    break; /* check if this is a top level expression */

  /* -------------------- AND --------------------------- */
  case AND:
    {
      /* AND does not change the expected value of the expression. */
      node_ptr exp1 = car(*exp);
      node_ptr exp2 = cdr(*exp);
      exp_kind kind1, kind2;

      kind1 = game_property_to_game(env,&exp1, value, varList, init, trans, reqs);
      kind2 = game_property_to_game(env,&exp2, value, varList, init, trans, reqs);
      node_node_setcar((*exp), exp1);
      node_node_setcdr((*exp), exp2);

      /* get rid of Nil */
      if (Nil == exp1) *exp = exp2;
      else if (Nil == exp2) *exp = exp1;

      kind = kind1 > kind2 ? kind1 : kind2;
      break; /* check if this is a top level expression */
    }

  /* -------------------- OR ---------------------------- */
  case OR:
    {
      node_ptr exp1 = car(*exp);
      node_ptr exp2 = cdr(*exp);
      /* In general, OR makes the expected value UNKNOWN, but if one
         of operands is pure propositional, then the value stays
         DETERMINISTIC_TRUE.
      */
      if ((TOP_LEVEL == value || DETERMINISTIC_TRUE == value)) {
        /* no need to process propositional expressions */
        if (PURE_PROPOSITIONAL == game_get_expression_kind(exp1)) {
          kind = game_property_to_game(env,
                                       &exp2,
                                       DETERMINISTIC_TRUE,
                                       varList,
                                       init,
                                       trans,
                                       reqs);
          node_node_setcdr((*exp), exp2);
          break; /* check if this is a top level expression */
        }
        else if (PURE_PROPOSITIONAL == game_get_expression_kind(exp2)) {
          kind = game_property_to_game(env,
                                       &exp1,
                                       DETERMINISTIC_TRUE,
                                       varList,
                                       init,
                                       trans,
                                       reqs);
          node_node_setcar((*exp), exp1);
          break; /* check if this is a top level expression */
        }
      }

      /* The value is UNKNOWN or no operand is purely propositional.
         No further transformation possible.
      */
      kind = game_get_expression_kind(*exp);
      break; /* check if this is a top level expression */
    }

  /* -------------------- CASE -------------------------- */
  case CASE:
    { /* CASE behaves as OR but only a condition is checked for being
         propositional. */
      node_ptr cond = car(car(*exp));
      node_ptr then = cdr(car(*exp));
      node_ptr tail = cdr(*exp);
      exp_kind kind1, kind2;
      if ((TOP_LEVEL == value || DETERMINISTIC_TRUE == value) &&
          PURE_PROPOSITIONAL == game_get_expression_kind(cond)) {
        kind1 = game_property_to_game(env,
                                      &then,
                                      DETERMINISTIC_TRUE,
                                      varList,
                                      init,
                                      trans,
                                      reqs);
        kind2 = game_property_to_game(env,
                                      &tail,
                                      DETERMINISTIC_TRUE,
                                      varList,
                                      init,
                                      trans,
                                      reqs);
        node_node_setcdr(car(*exp), then);
        node_node_setcdr((*exp), tail);
        kind = kind1 > kind2 ? kind1 : kind2;
      }
      else {
      /* The value is UNKNOWN or the condition is not purely
         propositional. No further conversion possible.
      */
        kind = game_get_expression_kind(*exp);
      }
      break; /* check if this is a top level expression */
    }

  /* -------------------- ALWAYS ------------------------ */
  case OP_GLOBAL:

    /* Special case: "G F res". This case is a kind of optimization:
       At top-level exp should not be processed at all.
       Otherwise, if the value is deterministically-true and res is
       pure-propositional =>
         create new var n and convert the exp to :
         "G F res"   <=>   "n", TRANS += "(n -> next(n))",
         REQS += "G F (res | !n)"
         "n" here means "G F res" must be true (forever).
       Otherwise, no optimizations can be done.
    */
    if (OP_FUTURE == node_get_type(car(*exp))) {
      node_ptr newVar;
      kind = game_get_expression_kind(car(car(*exp)));

      if (TOP_LEVEL == value || PURE_PROPOSITIONAL != kind) {
        kind = TEMPORAL;
        break;
      }
      /* the only values possibles */
      nusmv_assert(DETERMINISTIC_TRUE == value && PURE_PROPOSITIONAL == kind);

      nusmv_yylineno = line; /* All newly created nodes will have this line info. */

      res = car(car(*exp));
      newVar = game_create_new_var(env,varList, new_node(nodemgr,BOOLEAN, Nil, Nil));
      *exp = newVar;
      *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES,
                                     newVar,
                                     new_node(nodemgr,NEXT, newVar, Nil)),
                            *trans);
      *reqs = game_and_exp(nodemgr,new_node(nodemgr,OP_GLOBAL,
                                    new_node(nodemgr,OP_FUTURE,
                                             new_node(nodemgr,OR,
                                                      res,
                                                      new_node(nodemgr,NOT,
                                                               newVar,
                                                               Nil)),
                                             Nil),
                                    Nil),
                           *reqs);
      return PURE_PROPOSITIONAL;
    }

    /* Process the subexpression. ALWAYS does not change the expected
       value (except that subexpression cannot be at top level).
    */
    res = car(*exp);
    kind = game_property_to_game(env,
                                 &res,
                                 TOP_LEVEL == value ? DETERMINISTIC_TRUE : value,
                                 varList,
                                 init,
                                 trans,
                                 reqs);
    node_node_setcar((*exp), res);

    nusmv_yylineno = line; /* All newly created nodes will have this line info. */

    switch (value) {
    /* exp is at top-level. Special care required. */
    case TOP_LEVEL:
      /* subexpression is pure propositional
         => INIT += res, TRANS += next(res) */
      if (PURE_PROPOSITIONAL == kind) {
        *init = game_and_exp(nodemgr,res, *init);
        *trans = game_and_exp(nodemgr,new_node(nodemgr,NEXT, res, Nil), *trans);
      }
      /* subexpression is with next => TRANS += res */
      else if (ONCE_NEXT == kind) {
        *trans = game_and_exp(nodemgr,res, *trans);
      }
      /* a complex temporal subexpression => requirements += ALWAYS res */
      else {
        nusmv_assert(TEMPORAL == kind);
        *reqs = game_and_exp(nodemgr,*exp,*reqs);
      }
      *exp = Nil;
      return PURE_PROPOSITIONAL;/* It does not matter which kind is
                                   returned. */

    /* From a current state it is possible to infer whether the
       expression is necessarily true or not.
    */
    case DETERMINISTIC_TRUE:
      /* subexpression is pure propositional =>
         create new var n and convert the exp to :
         "G res"   <=>   "n ^ res" and TRANS += "(n -> next(res ^ n))"
         Meaning of "n" is that "G res" must be true in the next state.
      */
      if (PURE_PROPOSITIONAL == kind) {
        node_ptr newVar = game_create_new_var(env,varList,
                                              new_node(nodemgr,BOOLEAN, Nil, Nil));
        res = new_node(nodemgr,AND, newVar, res);
        *exp = res;
        res = new_node(nodemgr,NEXT, res, Nil);
        *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES, newVar, res), *trans);
        return PURE_PROPOSITIONAL;
      }
      /* subexpression is with one next =>
         create new var n and convert the exp to :
         "G res"   <=>   "n" and TRANS += "(n -> (next(n) ^ res))"
         Meaning of "n" is that "G res" must be true in the this state.
         Even if this state is the opponent deadlock, "G res" cannot be violated
         because res contains NEXT and can be violated only over a transition.
      */
      else if (ONCE_NEXT == kind) {
        node_ptr newVar = game_create_new_var(env,varList,
                                              new_node(nodemgr,BOOLEAN, Nil, Nil));
        *exp = newVar;
        res = new_node(nodemgr,AND, new_node(nodemgr,NEXT, newVar, Nil), res);
        *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES, newVar, res), *trans);
        return PURE_PROPOSITIONAL;
      }
      /* a complex temporal subexpression => return it as it is */
      else {
        nusmv_assert(TEMPORAL == kind);
        return TEMPORAL;
      }

    case UNKNOWN_VALUE:
      /* At the moment this value is impossible (because it is
         meaningless). */
      nusmv_assert(false);

    default: nusmv_assert(false);
    } /* switch(value) */

    nusmv_assert(false); /* impossible code */
    break;

  /* -------------------- EVENTUALLY -------------------- */
  case OP_FUTURE:
    /* Process the subexpression. FUTURE changes the expected value to
       UNKNOWN.  As a result, there is not reason (no chance) to
       simplify the operand.
    */
    res = car(*exp);
    kind = game_get_expression_kind(res);

    nusmv_yylineno = line; /* All newly created nodes will have this line info. */

    switch (value) {
    /* exp is at top-level. Special care required. */
    case TOP_LEVEL:
      /* subexpression is pure propositional =>
         create new var n and convert the exp to :
         INIT += "res | n", TRANS += "(n -> next(res | n))",
         REQS += "G F !n"
         "n" here means "F res" must be true in next state.
      */
      if (PURE_PROPOSITIONAL == kind) {
        node_ptr newVar = game_create_new_var(env,varList,
                                              new_node(nodemgr,BOOLEAN, Nil, Nil));
        res = new_node(nodemgr,OR, newVar, res);
        *init = game_and_exp(nodemgr,res, *init);
        res = new_node(nodemgr,NEXT, res, Nil);
        *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES, newVar, res), *trans);
        *reqs = game_and_exp(nodemgr,new_node(nodemgr,OP_GLOBAL,
                                      new_node(nodemgr,OP_FUTURE,
                                               new_node(nodemgr,NOT,
                                                        newVar,
                                                        Nil),
                                               Nil),
                                      Nil),
                             *reqs);
        *exp = Nil;
        return PURE_PROPOSITIONAL;
      }
      /* Unfortunately if there is X in the operand of F, F cannot be
         converted to a variable. See case DETERMINISTIC_TRUE. */
      else {
        *reqs = game_and_exp(nodemgr,*exp, *reqs);
        *exp = Nil;
        return TEMPORAL;
      }
      nusmv_assert(false);
      break;

    /* From a current state it is possible to infer whether the
       expression is necessarily true or not.
    */
    case DETERMINISTIC_TRUE:
      /* subexpression is pure propositional =>
         create new var n and convert the exp to :
         "F res"   <=>   "res | n", TRANS += "(n -> next(res | n))",
         REQS += "G F !n"
         "n" here means "F res" must be true in next state.
         res is in returned exp, otherwise "G F !n" may never be true.
      */
      if (PURE_PROPOSITIONAL == kind) {
        node_ptr newVar = game_create_new_var(env,varList,
                                              new_node(nodemgr,BOOLEAN, Nil, Nil));
        res = new_node(nodemgr,OR, newVar, res);
        *exp = res;
        res = new_node(nodemgr,NEXT, res, Nil);
        *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES, newVar, res), *trans);
        *reqs = game_and_exp(nodemgr,new_node(nodemgr,OP_GLOBAL,
                                      new_node(nodemgr,OP_FUTURE,
                                               new_node(nodemgr,NOT,
                                                        newVar,
                                                        Nil),
                                               Nil),
                                      Nil),
                             *reqs);
        return PURE_PROPOSITIONAL;
      }
      /* Unfortunately if there is X in the operand of F, F cannot be
         converted to a variable.

         G (a | F X b) where both a and b are controlled (directly or
         indirectly) by the opponent which has to maintain
         !b -> ((X b) | (X X b)). The exp is true, but after
         transformation becomes false (condition G F !n is violated).
      */
      /* A complex temporal subexpression => return as it is. */
      else {
        nusmv_assert(TEMPORAL == kind || ONCE_NEXT == kind);
        return TEMPORAL;
      }

    case UNKNOWN_VALUE:
      /* The value of expression can not be deterministically inferred
         from current state => return the expression as it is. */
      return TEMPORAL;

    default: nusmv_assert(false);
    } /* switch(value) */

    nusmv_assert(false); /* impossible code */
    break;

  /* -------------------- NEXT -------------------------- */
  case NEXT:
    /* Process the subexpression. NEXT does not change the expected
       value (except that subexpression cannot be at top level).
    */
    res = car(*exp);
    kind = game_property_to_game(env,
                                 &res,
                                 TOP_LEVEL == value ? DETERMINISTIC_TRUE : value,
                                 varList,
                                 init,
                                 trans,
                                 reqs);
    node_node_setcar((*exp), res);

    nusmv_yylineno = line; /* All newly created nodes will have this line info. */

    if (TEMPORAL == kind) {
      break; /* We cannot do anything. Check for being top-level. */
    }

    if (PURE_PROPOSITIONAL == kind) {
      kind = ONCE_NEXT;
      break; /* the exp is good, nothing to do. => check for being top-level */
    }

    nusmv_assert(ONCE_NEXT == kind); /* the only remaining kind */

    if (TOP_LEVEL == value || DETERMINISTIC_TRUE == value) {
      /* Deterministic expression with nested X.
         X b where b contains X, is converted to:
         "X b" ==> X n, TRANS += "n -> b".
      */
      /* only booleans are expected here */
      node_ptr newVar = game_create_new_var(env,varList,
                                            new_node(nodemgr,BOOLEAN, Nil, Nil));
      *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES, newVar, res), *trans);
      node_node_setcar((*exp), newVar);
      break; /* Check for being top-level. The kind remains ONCE_NEXT. */
    }
    else {
      nusmv_assert(UNKNOWN_VALUE == value); /* the only possible value */
      return TEMPORAL;
    }

    nusmv_assert(false); /* impossible code */
    break;

  /* UNTIL and RELEASE are not fully analyzed. At the moment we can
     convert them only if both operands are fully propositional and
     the expected value is top-level or deterministic-true.
  */
  /* -------------------- UNTIL  ------------------------ */
  case UNTIL:
    {
      node_ptr exp1 = car(*exp);
      node_ptr exp2 = cdr(*exp);
      node_ptr newVar;

      /* At the moment we expect that value == top-level or
         deterministic-true. */
      nusmv_assert(TOP_LEVEL == value || DETERMINISTIC_TRUE == value);

      if (PURE_PROPOSITIONAL != game_get_expression_kind(exp1) ||
          PURE_PROPOSITIONAL != game_get_expression_kind(exp2)) {
        kind = TEMPORAL;
        break; /* Check for being top-level */
      }

      nusmv_yylineno = line; /* All newly created nodes will have this line info. */

      /* Operands are pure-propositional. A new var n is introduced:
         "a U b" ==> "b | (a ^ n)", TRANS += "n -> X(b | (a ^ n))",
         REQS += G F !n
         Here n means: exp must be satisfied in the next state.
      */
      newVar = game_create_new_var(env,varList, new_node(nodemgr,BOOLEAN, Nil, Nil));
      res = new_node(nodemgr,OR, exp2, new_node(nodemgr,AND, exp1, newVar));
      *exp = res;
      *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES,
                                     newVar,
                                     new_node(nodemgr,NEXT, res, Nil)),
                            *trans);
      *reqs = game_and_exp(nodemgr,new_node(nodemgr,OP_GLOBAL,
                                    new_node(nodemgr,OP_FUTURE,
                                             new_node(nodemgr,NOT,
                                                      newVar,
                                                      Nil),
                                             Nil),
                                    Nil),
                           *reqs);
      kind = PURE_PROPOSITIONAL;
      break; /* Check for being top-level */
    }

    nusmv_assert(false); /* impossible code */
    break;

  /* See note above UNTIL. */
  /* -------------------- RELEASES  --------------------- */
  case RELEASES:
    {
      node_ptr exp1 = car(*exp);
      node_ptr exp2 = cdr(*exp);
      node_ptr newVar;

      /* At the moment we expect that value == top-level or
         deterministic-true. */
      nusmv_assert(TOP_LEVEL == value || DETERMINISTIC_TRUE == value);

      if (PURE_PROPOSITIONAL != game_get_expression_kind(exp1) ||
          PURE_PROPOSITIONAL != game_get_expression_kind(exp2)) {
        kind = TEMPORAL;
        break; /* Check for being top-level */
      }

      nusmv_yylineno = line; /* All newly created nodes will have this line info. */

      /* Operands are pure-propositional. A new var n is introduced:
         "a R b" ==> "b ^ n", TRANS += "n -> (a | X(b ^ n))"
         Here n means: a occurs in the current state or the whole exp
         must be true in the next state.
      */
      newVar = game_create_new_var(env,varList, new_node(nodemgr,BOOLEAN, Nil, Nil));
      res = new_node(nodemgr,AND, exp2, newVar);
      *exp = res;
      res = new_node(nodemgr,OR, exp1, new_node(nodemgr,NEXT, res, Nil));
      *trans = game_and_exp(nodemgr,new_node(nodemgr,IMPLIES, newVar, res), *trans);
      kind = PURE_PROPOSITIONAL;
      break; /* Check for being top-level */
    }

    nusmv_assert(false); /* impossible code */
    break;

  /* --------------------  ALL OTHERS ------------------------ */
  /* This expression which do not know how to deal with. Potentially
     NEXT operators with not-boolean expressions can be dealt with but
     since obtaining the type info is not implemented we ignore all
     non-boolean expressions.
  */
  case CAST_BOOL:
  case CAST_WORD1:
  case CAST_SIGNED:
  case CAST_UNSIGNED:
  case EXTEND:
  case UMINUS:
  case XOR:
  case XNOR:
  case IFF:
  case EQUAL:
  case NOTEQUAL:
  case BIT_SELECTION:
  case CONCATENATION:
  case TIMES:
  case DIVIDE:
  case PLUS:
  case MINUS:
  case MOD:
  case LSHIFT:
  case RSHIFT:
  case UNION:
  case SETIN:
  case LT:
  case GT:
  case LE:
  case GE:
     kind = game_get_expression_kind(*exp);
     break; /* check if this is a top level expression */

  default: nusmv_assert(false);
  }; /* switch */

  /* Process top level expression (if something remained). */
  if (Nil != *exp && TOP_LEVEL == value) {
    switch (kind) {
    case PURE_PROPOSITIONAL:
      /* INIT += exp */
      *init = game_and_exp(nodemgr,*exp, *init);
      *exp = Nil;
      break;
    case ONCE_NEXT:
      {
        /* create a new var v,  INIT += v, TRANS += v -> exp */
        node_ptr newVar = game_create_new_var(env,varList,
                                              new_node(nodemgr,BOOLEAN, Nil, Nil));
        *init = game_and_exp(nodemgr,newVar, *init);
        *trans = game_and_exp(nodemgr,new_lined_node(nodemgr,IMPLIES,
                                             newVar,
                                             *exp,
                                             line),
                              *trans);
        *exp = Nil;
      }
      break;
    case TEMPORAL:
      /* REQS += exp */
      *reqs = game_and_exp(nodemgr,*exp, *reqs);
      *exp = Nil;
      break;
    default:
      nusmv_assert(false);
    } /* switch */
  }; /* if */

  return kind;
}
