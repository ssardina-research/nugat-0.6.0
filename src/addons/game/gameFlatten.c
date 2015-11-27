/**CFile***********************************************************************

  FileName    [ gameFlatten.c ]

  PackageName [ game ]

  Synopsis    [ Defines functions to flatten a game hierarchy and check
                its well-formedness. ]

  Description [ ]

  SeeAlso     [ compileFlatten.c ]

  Author      [ Andrei Tchaltsev ]

  Copyright   [
  This file is part of the ``game'' package of NuGaT.
  Copyright (C) 2010 FBK-irst.

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

#if HAVE_CONFIG_H
# include "config.h"
#endif

#include "gameInt.h"
#include "GameHierarchy.h"
#include "GamePlayer.h"
#include "PropDbGame.h"
#include "parser/game_symbols.h"

#include "compile/compile.h"
#include "compile/compileInt.h" /* for flattening functions */
#include "enc/enc.h"
#include "node/node.h"
#include "opt/opt.h"
#include "parser/symbols.h"
#include "parser/psl/pslNode.h" /* a the psl convertion functions */
#include "prop/propPkg.h"
#include "utils/utils.h"
#include "utils/NodeList.h"
#include "utils/assoc.h"
#include "utils/error.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: gameFlatten.c,v 1.1.2.11 2010-02-10 14:44:51 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/**Variable********************************************************************

  Synopsis    [ This is a global variable storing the constructs of input
                game modules. This variable is used only if a game
                hierarchy is given and used instead of the
                mainFlatHierarchy variable. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
GameHierarchy_ptr mainGameHierarchy = GAME_HIERARCHY(NULL);

EXTERN FILE* nusmv_stdout;
EXTERN FILE* nusmv_stderr;
EXTERN node_ptr parsed_tree;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
/* flatten hierarchy functions */
static GameHierarchy_ptr
  game_flatten_game_hierarchy ARGS((SymbTable_ptr symbol_table,
                                    SymbLayer_ptr model_layer_1,
                                    node_ptr module_1,
                                    SymbLayer_ptr model_layer_2,
                                    node_ptr module_2,
                                    boolean expand_bounded_arrays));

static void game_check_first_player ARGS((NuSMVEnv_ptr env,
                                          SymbTable_ptr st,
                                          FlatHierarchy_ptr player_1,
                                          NodeList_ptr vars));

static void game_check_first_player_recur ARGS((NuSMVEnv_ptr env,
                                                SymbTable_ptr st,
                                                node_ptr expr,
                                                NodeList_ptr vars,
                                                boolean allowCurrentVar,
                                                boolean isInNext));
;
/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Performs the "flatten_hierarchy" command for games. ]

  Description [ This function is used in CommandFlattenHierarchy to
                adopt the "flatten_hierarchy" command to deal with a
                game declaration. Returns 0 if everything is OK, and 1
                otherwise. ]

  SideEffects [ ]

  SeeAlso     [ CommandGameFlattenHierarchy, CommandFlattenHierarchy,
                compile_flatten_smv ]

******************************************************************************/
int Game_CommandFlattenHierarchy(NuSMVEnv_ptr env,boolean expand_bounded_arrays)
{
  SymbTable_ptr st = SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  int propErr;

  if (opt_verbose_level_gt(opts, 0)) {
    fprintf(nusmv_stderr, "Flattening hierarchy...\n");
  }

  /* Initializes the flattener, that must be initialized *after* the
     parsing phase. */
  CompileFlatten_init_flattener(env);

  /* Processing of the parse tree and constructions of all the
     expressions for the state machine(s). Here the expansions are
     performed so that modules are created. The expansion of modules
     is such that the formal parameters (if any) are replaced by the
     actual ones and the machine is replicated.
  */

  /* create two layers - one for variables of every player */
  SymbLayer_ptr model_layer_1 = SymbTable_create_layer(st,
                                                       MODEL_LAYER_1,
                                                       SYMB_LAYER_POS_BOTTOM);
  SymbLayer_ptr model_layer_2 = SymbTable_create_layer(st,
                                                       MODEL_LAYER_2,
                                                       SYMB_LAYER_POS_BOTTOM);
  SymbTable_layer_add_to_class(st, MODEL_LAYER_1, MODEL_LAYERS_CLASS);
  SymbTable_layer_add_to_class(st, MODEL_LAYER_2, MODEL_LAYERS_CLASS);
  SymbTable_set_default_layers_class_name(st, MODEL_LAYERS_CLASS);

  /* Compilation the input file:

     Processing of the parse tree and constructions of all the
     expressions for the state machine(s).

     Note that two special modules PLAYER_NAME_1 and PLAYER_NAME_2 are
     actually the players\' declarations.
  */
  mainGameHierarchy = game_flatten_game_hierarchy(st,
                                                  model_layer_1,
                                                  sym_intern(env,PLAYER_NAME_1),
                                                  model_layer_2,
                                                  sym_intern(env,PLAYER_NAME_2),
                                                  expand_bounded_arrays);

  /* We store properties in the DB of properties */
  nusmv_assert(GameHierarchy_get_ctlspec(mainGameHierarchy) == Nil &&
               GameHierarchy_get_compute(mainGameHierarchy) == Nil &&
               GameHierarchy_get_ltlspec(mainGameHierarchy) == Nil &&
               GameHierarchy_get_pslspec(mainGameHierarchy) == Nil &&
               GameHierarchy_get_invarspec(mainGameHierarchy) == Nil);

  propErr = PropDbGame_fill(PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)),
                            st,
                            GameHierarchy_get_reachtarget(mainGameHierarchy),
                            GameHierarchy_get_avoidtarget(mainGameHierarchy),
                            GameHierarchy_get_reachdeadlock(mainGameHierarchy),
                            GameHierarchy_get_avoiddeadlock(mainGameHierarchy),
                            GameHierarchy_get_buchigame(mainGameHierarchy),
                            GameHierarchy_get_ltlgame(mainGameHierarchy),
                            GameHierarchy_get_genreactivity(mainGameHierarchy));
  if (0 != propErr) {
    GameHierarchy_destroy(mainGameHierarchy);
    mainGameHierarchy = GAME_HIERARCHY(NULL);
    SymbTable_remove_layer(st, model_layer_1);
    SymbTable_remove_layer(st, model_layer_2);
    PropDb_clean(PROP_DB(NuSMVEnv_get_value(env, ENV_PROP_DB)));
    CompileFlatten_quit_flattener(env);
    cmp_struct_unset_read_model(cmps); /* resets also the command read_model */
    return 1; /* error */
  }

  /* Disable static order heuristics (see warning in
     nusmv/src/enc/enc.c::Enc_init_bdd_encoding). */
  set_bdd_static_order_heuristics(opts,
                                  BDD_STATIC_ORDER_HEURISTICS_NONE);

  if (opt_use_coi_size_sorting(opts)) {
    fprintf(nusmv_stderr,
            "*** WARNING: "
            "Game addon does not support properties COI size sorting.  ***\n");
    fprintf(nusmv_stderr,
            "*** WARNING: "
            "Properties COI size sorting will be disabled.             ***\n");
    unset_use_coi_size_sorting(opts);
  }

  cmp_struct_set_flatten_hrc(cmps);
  if (opt_verbose_level_gt(opts, 0)) {
    fprintf(nusmv_stderr, "...done\n");
  }

  return 0;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Traverses the input file (game and modules declarations)
                and creates a game hierarchy which consists of two
                flat hierarchies (one for every player). ]

  Description [ This function is the same as Compile_FlattenHierarchy
                but adopted for game declarations. Note that:
                1. There are two special modules that are actually
                   player declarations (they are created during
                   parsing).
                2. Players are instantiated with name "Nil".
                3. No input variables or processes are allowed.
                4. The first player is checked for using the variables
                   of the second player correctly.
                5. The game specifications are processed in this
                   function (not during processing of the players).

                If Compile_FlattenHierarchy changes this function also
                has to be changed. ]

  SideEffects [ ]

  SeeAlso     [ Compile_FlattenHierarchy ]

******************************************************************************/
static GameHierarchy_ptr
game_flatten_game_hierarchy(SymbTable_ptr symbol_table,
                            SymbLayer_ptr model_layer_1,
                            node_ptr module_1,
                            SymbLayer_ptr model_layer_2,
                            node_ptr module_2,
                            boolean expand_bounded_arrays)
{
  node_ptr tmp, iter;
  node_ptr ctlspec = Nil;
  node_ptr ltlspec = Nil;
  node_ptr invarspec = Nil;
  node_ptr pslspec = Nil;
  node_ptr compute = Nil;
  node_ptr reachtarget = Nil;
  node_ptr avoidtarget = Nil;
  node_ptr reachdeadlock = Nil;
  node_ptr avoiddeadlock = Nil;
  node_ptr buchigame = Nil;
  node_ptr ltlgame = Nil;
  node_ptr genreactivity = Nil;

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(symbol_table));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  FlatHierarchy_ptr player_1 = FlatHierarchy_create(symbol_table);
  FlatHierarchy_ptr player_2 = FlatHierarchy_create(symbol_table);
  hash_ptr instances = new_assoc();

  /* Collect all the constructs of a hierarchy (instance name is
     Nil). */
  Compile_ConstructHierarchy(env,
                             symbol_table,
                             model_layer_1,
                             module_1,
                             Nil,
                             Nil,
                             player_1,
                             HRC_NODE(NULL),
                             instances,
                             expand_bounded_arrays);

  Compile_ConstructHierarchy(env,
                             symbol_table,
                             model_layer_2,
                             module_2,
                             Nil,
                             Nil,
                             player_2,
                             HRC_NODE(NULL),
                             instances,
                             expand_bounded_arrays);

  free_assoc(instances);

  /* Processes are not allowed in realizability (game declaration). */
  nusmv_assert(Nil != FlatHierarchy_get_assign(player_1) &&
               Nil != FlatHierarchy_get_assign(player_2));
  if (Nil != cdr(FlatHierarchy_get_assign(player_1)) ||
      Nil != cdr(FlatHierarchy_get_assign(player_2))) {
    ErrorMgr_rpterr(errmgr,"A game declaration should not contain process declarations.\n");
  }
  /* input vars are not allowed. */
   if (SymbTable_get_input_vars_num(symbol_table)>0) ErrorMgr_error_game_definition_contains_input_vars(errmgr,car(tmp));
   /*OLD_CODE_START
  tmp = NodeList_to_node_ptr(SymbTable_get_input_vars(symbol_table));
  if (Nil != tmp) ErrorMgr_error_game_definition_contains_input_vars(errmgr,car(tmp));
  OLD_CODE_END*/

  /* Process the created hierarchy. The 5th parameter is true to allow
     some additional checking of expressions (such as for circular
     dependencies of assignments).
  */
  Compile_ProcessHierarchy(env,
                           symbol_table,
                           model_layer_1,
                           player_1,
                           Nil,
                           true,
                           true);
  Compile_ProcessHierarchy(env,
                           symbol_table,
                           model_layer_2,
                           player_2,
                           Nil,
                           true,
                           true);


  /* Check that the first player correctly used the second player
     variables. */
   /*NEW_CODE_START*/
   SymbLayerIter iter2;
   SymbLayer_gen_iter(model_layer_2, &iter2, STT_VAR);
   game_check_first_player(env,
                           symbol_table,
                           player_1,
                           SymbLayer_iter_to_list(model_layer_2, iter2));
   /*NEW_CODE_END*/

   /*OLD_CODE_START
  game_check_first_player(symbol_table,
                          player_1,
                          SymbLayer_get_all_vars(model_layer_2));
  OLD_CODE_END*/

  /* Now process the game specifications, i.e., perform flattening of
     game specification. This code is the very similar to the code in
     function compile_process_hierarchy.
  */
  for (iter = car(parsed_tree); iter != Nil; iter = cdr(iter)) {
    node_ptr spec = car(iter);
    node_ptr* list = (node_ptr*) NULL; /* used to deal with GAME specs */

    switch (node_get_type(spec)) {
    case SPEC:
      ctlspec = cons(nodemgr,find_node(nodemgr,CONTEXT, Nil, car(spec)), ctlspec);
      break;
    case LTLSPEC:
      ltlspec = cons(nodemgr,find_node(nodemgr,CONTEXT, Nil, car(spec)), ltlspec);
      break;
    case INVARSPEC:
      invarspec = cons(nodemgr,find_node(nodemgr,CONTEXT, Nil, car(spec)), invarspec);
      break;
    case PSLSPEC:
      pslspec = cons(nodemgr,PslNode_new_context(nodemgr,PSL_NULL, car(spec)), pslspec);
      break;
    case COMPUTE:
      compute = cons(nodemgr,find_node(nodemgr,CONTEXT, Nil, car(spec)), compute);
      break;

    /* The true game spec is dealt below, outside of switch statement. */
    case REACHTARGET:   list = &reachtarget; break;
    case AVOIDTARGET:   list = &avoidtarget; break;
    case REACHDEADLOCK: list = &reachdeadlock; break;
    case AVOIDDEADLOCK: list = &avoiddeadlock; break;
    case BUCHIGAME:     list = &buchigame; break;
    case LTLGAME:       list = &ltlgame; break;
    case GENREACTIVITY: list = &genreactivity; break;

    default: nusmv_assert(false); /* unknown specification */
    } /* switch */

    /* For true game specifications a special wrapper is created -- a
       node whose type is GAME_SPEC_WRAPPER, its left child is the
       ATOM with name of the player having the spec and its right
       child is the body of spec.
    */
    if (list != (node_ptr*) NULL) {
      spec = find_node(nodemgr,GAME_SPEC_WRAPPER,
                       sym_intern(env,((car(spec)) == (node_ptr)1 ?
                                   PLAYER_NAME_1 :
                                   PLAYER_NAME_2)),
                       cdr(spec));
      *list = cons(nodemgr,spec, *list);
    }
  } /* for */

  if (FlatHierarchy_get_compassion(player_1) != Nil ||
      FlatHierarchy_get_compassion(player_2) != Nil) {
    fprintf(nusmv_stdout,
         "WARNING *** The model contains COMPASSION declarations.        ***\n"
         "WARNING *** Full fairness is not yet fully supported in NuGaT. ***\n"
         "WARNING *** Currently, COMPASSION declarations are only        ***\n"
         "WARNING *** supported for BDD-based LTL Model Checking.        ***\n"
         "WARNING *** Results for game properties may be wrong.          ***\n");
  }

  /* Create the game hierarchy. */
  return GameHierarchy_create(player_1,
                              player_2,
                              ctlspec,
                              ltlspec,
                              invarspec,
                              pslspec,
                              compute,
                              reachtarget,
                              avoidtarget,
                              reachdeadlock,
                              avoiddeadlock,
                              buchigame,
                              ltlgame,
                              genreactivity);
}

/**Function********************************************************************

  Synopsis    [ Checks that constraints of the first player use the
                variables of the second player correctly. ]

  Description [ There are a few constraints on the use of variables of
                the second player in the body of the first player:

                1. INIT, INVAR, init-assign, invar-assign, justice and
                   compassion should not mention the (current state)
                   variables of the second player.

                2. TRANS and next-assign should not mention the next
                   state variables of the second player.

                The parameter var_list is a list of the second
                player\'s variables. All the expressions of a player
                should be already flattened (but may not be
                expanded). ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_check_first_player(NuSMVEnv_ptr env,
                                    SymbTable_ptr st,
                                    FlatHierarchy_ptr player_1,
                                    NodeList_ptr vars)
{
  NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  /* check init */
  game_check_first_player_recur(env,
                                st,
                                FlatHierarchy_get_init(player_1),
                                vars,
                                false,
                                false);
  /* check invar */
  game_check_first_player_recur(env,
                                st,
                                FlatHierarchy_get_invar(player_1),
                                vars,
                                false,
                                false);
  /* check justice */
  game_check_first_player_recur(env,
                                st,
                                FlatHierarchy_get_justice(player_1),
                                vars,
                                false,
                                false);
  /* check compassion */
  game_check_first_player_recur(env,
                                st,
                                FlatHierarchy_get_compassion(player_1),
                                vars,
                                false,
                                false);
  /* check trans */
  game_check_first_player_recur(env,
                                st,
                                FlatHierarchy_get_trans(player_1),
                                vars,
                                true,
                                false);
  /* check assign. "map" is used to get rid of processes names */
  game_check_first_player_recur(env,
                                st,
                                map(nodemgr,cdr, FlatHierarchy_get_assign(player_1)),
                                vars,
                                false,
                                false);
}

/**Function********************************************************************

  Synopsis    [ Checks that constrains of the first players correctly use
                the variables of the second player. ]

  Description [ This is a recursive subroutine of
                game_check_first_player. Parameter allowCurrent makes
                a current variable in the list 'vars' legal in an
                expression, otherwise both current and next variables
                are illegal. Paremeter isInNext is a flag that we are
                inside a next-expression. ]

  SideEffects [ ]

  SeeAlso     [ game_check_first_player ]

******************************************************************************/
static void game_check_first_player_recur(NuSMVEnv_ptr env,
                                          SymbTable_ptr st,
                                          node_ptr expr,
                                          NodeList_ptr vars,
                                          boolean allowCurrent,
                                          boolean isInNext)
{
  if (Nil == expr) return;

  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  switch (node_get_type(expr)) {
  /* usual constant => return success */
  case FAILURE:
  case NUMBER:
  case TRUEEXP:
  case FALSEEXP:
  case NUMBER_UNSIGNED_WORD:
  case NUMBER_SIGNED_WORD:
  case NUMBER_FRAC:
  case NUMBER_REAL:
  case NUMBER_EXP:
    break;

  /* expr is expected to be flattened (but may not be expanded). Only
     constant, defines and vars can be here (parameter cannot be here
     since players do not have parameters). Constants are skipped,
     vars are checked for being in the list 'vars', defines are
     expanded.
  */
  case ATOM:
  case BIT:
  case DOT:
  case ARRAY:
    {
      SymbTable_ptr st = SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE));
      if (SymbTable_is_symbol_constant(st, expr)) {
        /* it is a constant => skip */
        break;
      }
      else if (SymbTable_is_symbol_define(st, expr)) {
        /* it is define => expand */
        expr = SymbTable_get_define_flatten_body(st, expr);
        game_check_first_player_recur(env,st, expr, vars, allowCurrent, isInNext);
      }
      else if (SymbTable_is_symbol_var(st, expr)) {
        /* it is a var => check it */
        if ((!allowCurrent || isInNext) && NodeList_belongs_to(vars, expr)) {
          if (allowCurrent) ErrorMgr_error_second_player_next_var (errmgr,expr);
          else ErrorMgr_error_second_player_var(errmgr,expr);
        }
      }
      else {
        /* expr can be only constant, var or define */
        nusmv_assert(false);
      }
    }
    break;

  /* the expression should have been already flattened */
  case CONTEXT: nusmv_assert(false);

  case NEXT: /* allowCurrent is of no importance any more */
    game_check_first_player_recur(env,st, car(expr), vars, allowCurrent, true);
    break;

  /* assignment */
  case EQDEF:
    nusmv_yylineno = node_get_lineno(expr); /* for further error messages */
    if (NEXT == node_get_type(car(expr))) { /* trans-assign */
      game_check_first_player_recur(env,st, car(expr), vars, true, false);
      game_check_first_player_recur(env,st, cdr(expr), vars, true, false);
    }
    else { /* init-assign or invar-assign */
      game_check_first_player_recur(env,st, car(expr), vars, false, false);
      game_check_first_player_recur(env,st, cdr(expr), vars, false, false);
    }
    break;

  default:
    nusmv_yylineno = node_get_lineno(expr); /* for further error messages */
    game_check_first_player_recur(env,st, car(expr), vars, allowCurrent, isInNext);
    game_check_first_player_recur(env,st, cdr(expr), vars, allowCurrent, isInNext);
    break;
  } /* switch */

  return;
}
