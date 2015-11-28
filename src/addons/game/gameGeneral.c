/**CFile***********************************************************************

  FileName    [ gameGeneral.c ]

  PackageName [ game ]

  Synopsis    [ Auxiliary functions needed by game, but not strongly
                related to any particular part of game. ]

  Description [ ]

  SeeAlso     [ game.h ]

  Author      [ Andrei Tchaltsev, Viktor Schuppan ]

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

#include "game.h"
#include "gameInt.h"
#include "GameStrategy.h"
#include "PropGame.h"
#include "fsm/GameBddFsm.h"

#include "compile/compile.h"
#include "enc/enc.h"
#include "node/node.h"
#include "opt/opt.h"
#include "prop/propPkg.h"
#include "utils/utils.h"
#include "utils/array.h"
#include "utils/error.h"
#include "utils/NodeList.h"
#include <stdio.h>

/*---------------------------------------------------------------------------*/
static char rcsid[] UTIL_UNUSED = "$Id: gameGeneral.c,v 1.1.2.9 2010-02-05 17:19:08 nusmv Exp $";
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stderr;
EXTERN FILE* nusmv_stdout;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static void game_print_prop_exp ARGS((FILE *file, PropGame_ptr prop));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Preparation for checking a game specification. ]

  Description [ Preparation consists of:
                - printing spec if required,
                - performing COI, and
                - creating FSM. ]

  SideEffects [ ]

  SeeAlso     [ Game_AfterCheckingSpec ]

******************************************************************************/
void Game_BeforeCheckingSpec(NuSMVEnv_ptr env,PropGame_ptr prop)
{
  GameBddFsm_ptr fsm;

  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  PROP_GAME_CHECK_INSTANCE(prop);

  if (opt_verbose_level_gt(opts, 0)) {
    fprintf(nusmv_stderr, "computing ");
    game_print_prop_exp(nusmv_stderr, prop);
    fprintf(nusmv_stderr, "\n");
  }

  if (opt_cone_of_influence(opts) == true) {
    /*
       The goal states also include opponent deadlock states =>
       variables from deadlock states should also be considered in the
       dependencies.

       The variables for COI should be taken from deadlock states,
       i.e. states with no successors(in BDD). Then if bdd_support of
       a var intersect with deadlock => create arbitrary expr with
       this var and so on for all var. Then invoke standard
       Prop_apply_coi_for_bdd
    */
    /*Prop_apply_coi_for_bdd(prop, FSM_BUILDER(NuSMVEnv_get_value(env, ENV_FSM_BUILDER)));*/
  }

  fsm = PropGame_get_game_bdd_fsm(prop);
  if (fsm == GAME_BDD_FSM(NULL)) {
    Prop_set_environment_fsms(env, PROP(prop));
    fsm = PropGame_get_game_bdd_fsm(prop);
    GAME_BDD_FSM_CHECK_INSTANCE(fsm);
  }
}

/**Function********************************************************************

  Synopsis    [ Printing and cleaning after checking a game
                specification. ]

  Description [ This consists of:
                - printing a message of success or failure,
                - printing strategy if required,
                - setting prop status, and
                - freeing the strategy.

                Parameters:
                - prop: property to print
                - status: status of a property (realizable,
                  unrealizable, unknown)
                - strategy: strategy to print (can be NULL)
                - varList1: a list of additional variables which will
                  be considered as belonging to player 1 during
                  printing.  For example, these vars could have been
                  created just to construct the strategy. Normal vars
                  of player 1 will be printed in any case. Members
                  will be declared in the strategy module.
                - varList2: the same as varList1 but for player 2. ]

  SideEffects [ ]

  SeeAlso     [ Game_BeforeCheckingSpec ]

******************************************************************************/
void Game_AfterCheckingSpec(NuSMVEnv_ptr env,
                            PropGame_ptr prop,
                            Game_RealizabilityStatus status,
                            GameStrategy_ptr strategy,
                            node_ptr varList1,
                            node_ptr varList2,
                            gameParams_ptr params)

{
  boolean has_params;

  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  PROP_GAME_CHECK_INSTANCE(prop);

  has_params = ((gameParams_ptr) NULL != params);

  /* ----------  Print the result ----------- */
  fprintf(nusmv_stdout, "-- ");
  game_print_prop_exp(nusmv_stdout, prop);

  /* strategy reached */
  switch (status) {
  case GAME_REALIZABLE:
    Prop_set_status(PROP(prop), Prop_True);
    fprintf(nusmv_stdout, " : the strategy has been found\n");
    break;
  case GAME_UNREALIZABLE:
    Prop_set_status(PROP(prop), Prop_False);
    fprintf(nusmv_stdout, " : no strategy exists\n");
    break;
  case GAME_UNKNOWN:
    /* status should remain unknown */
    nusmv_assert(Prop_Unchecked == Prop_get_status(PROP(prop)));
    fprintf(nusmv_stdout, " : existence of a strategy is unknown\n");
    break;
  default: ErrorMgr_internal_error(errmgr,"unknown status of a problem");
  }

  /* print a strategy for a player or an opponent */
  if (((has_params && params->strategy_printout)
       || opt_game_print_strategy(opts)) &&
      ((status == GAME_REALIZABLE) ||
       (status == GAME_UNREALIZABLE))) {

    if (GAME_STRATEGY(NULL) != strategy) {
      array_t* layers;
      BddEnc_ptr enc;
      SymbTable_ptr st;
      NodeList_ptr vars;
      NodeList_ptr vars_to_decl;
      NodeList_ptr vars1;
      NodeList_ptr vars2;

      GAME_STRATEGY_CHECK_INSTANCE(strategy);

      /* Symbol table local reference */
      enc = GameStrategy_get_bdd_enc(strategy);
      st = BaseEnc_get_symb_table(BASE_ENC(enc));

      /* extract variables from game layers */
      layers = array_alloc(char *, 4);
      array_insert_last(char *, layers, MODEL_LAYER_1);
      array_insert_last(char *, layers, MODEL_LAYER_2);
      /* There shouldnt be any variables in the determinization layers. */
      {
        SymbLayer_ptr dl1 = SymbTable_get_layer(st, DETERM_LAYER_1);
        SymbLayer_ptr dl2 = SymbTable_get_layer(st, DETERM_LAYER_2);
        /**OLD_CODE_START
        nusmv_assert((dl1 == SYMB_LAYER(NULL)) ||
                     (NodeList_get_length(SymbLayer_get_all_symbols(dl1)) ==
                      0));
        nusmv_assert((dl2 == SYMB_LAYER(NULL)) ||
                     (NodeList_get_length(SymbLayer_get_all_symbols(dl2)) ==
                      0));
        OLD_CODE_END**/

        /**NEW_CODE_START**/
        SymbLayerIter iter1;
        NodeList_ptr syms1;
        SymbLayer_gen_iter(dl1, &iter1, STT_ALL);
        syms1 = SymbLayer_iter_to_list(dl1, iter1);

        SymbLayerIter iter2;
        NodeList_ptr syms2;
        SymbLayer_gen_iter(dl2, &iter2, STT_ALL);
        syms2 = SymbLayer_iter_to_list(dl2, iter2);
        fprintf(nusmv_stdout,"Hi\n");
        nusmv_assert((dl1 == SYMB_LAYER(NULL)) ||
                     (NodeList_get_length(syms1) ==
                      0));
        nusmv_assert((dl2 == SYMB_LAYER(NULL)) ||
                     (NodeList_get_length(syms2) ==
                      0));
        /**NEW_CODE_END**/
      }

      /* obtain variables */
      vars = SymbTable_get_layers_sf_i_vars(st, layers);
      vars_to_decl = NodeList_create();
      vars1 = NodeList_create_from_list(varList1);
      vars2 = NodeList_create_from_list(varList2);
      NodeList_concat(vars, vars1);
      NodeList_concat(vars, vars2);
      NodeList_concat(vars_to_decl, vars1);
      NodeList_concat(vars_to_decl, vars2);

      GameStrategy_print_module(strategy, vars, vars_to_decl, params);

      /* free local variables */
      NodeList_destroy(vars);
      NodeList_destroy(vars_to_decl);
      NodeList_destroy(vars1);
      NodeList_destroy(vars2);
      array_free(layers);

      /* free strategy */
      GameStrategy_destroy(strategy);
    } else {
      fprintf(nusmv_stderr,
              "\nWarning: strategy printing requested, but strategy = NULL.\n");
    }
  }

  fprintf(nusmv_stdout,"\n");
  return;
}

/**Function********************************************************************

  Synopsis    [ const char* to Game_Who ]

  Description [ Caller retains ownership of passed string. ]

  SideEffects [ None. ]

  SeeAlso     [ ]

******************************************************************************/
Game_Who Game_Who_from_string(const char* s)
{
  if (strcmp(s, GAME_WHO_NONE_STRING) == 0) {
    return GAME_WHO_NONE;
  } else if (strcmp(s, GAME_WHO_BOTH_STRING) == 0) {
    return GAME_WHO_BOTH;
  } else if (strcmp(s, GAME_WHO_PROTAGONIST_STRING) == 0) {
    return GAME_WHO_PROTAGONIST;
  } else if (strcmp(s, GAME_WHO_ANTAGONIST_STRING) == 0) {
    return GAME_WHO_ANTAGONIST;
  } else if (strcmp(s, GAME_WHO_PLAYER_1_STRING) == 0) {
    return GAME_WHO_PLAYER_1;
  } else if (strcmp(s, GAME_WHO_PLAYER_2_STRING) == 0) {
    return GAME_WHO_PLAYER_2;
  } else if (strcmp(s, GAME_WHO_WINNER_STRING) == 0) {
    return GAME_WHO_WINNER;
  } else if (strcmp(s, GAME_WHO_LOSER_STRING) == 0) {
    return GAME_WHO_LOSER;
  } else {
    return GAME_WHO_INVALID;
  }
  nusmv_assert(false);
}

/**Function********************************************************************

  Synopsis    [ Game_Who to const char*. ]

  Description [ Returned string is statically allocated and must not be
                freed. ]

  SideEffects [ None. ]

  SeeAlso     [ ]

******************************************************************************/
const char* Game_Who_to_string(const Game_Who w)
{
  switch (w) {
  case GAME_WHO_INVALID:     return GAME_WHO_INVALID_STRING;
  case GAME_WHO_NONE:        return GAME_WHO_NONE_STRING;
  case GAME_WHO_BOTH:        return GAME_WHO_BOTH_STRING;
  case GAME_WHO_PROTAGONIST: return GAME_WHO_PROTAGONIST_STRING;
  case GAME_WHO_ANTAGONIST:  return GAME_WHO_ANTAGONIST_STRING;
  case GAME_WHO_PLAYER_1:    return GAME_WHO_PLAYER_1_STRING;
  case GAME_WHO_PLAYER_2:    return GAME_WHO_PLAYER_2_STRING;
  case GAME_WHO_WINNER:      return GAME_WHO_WINNER_STRING;
  case GAME_WHO_LOSER:       return GAME_WHO_LOSER_STRING;
  default:                   nusmv_assert(false);
  }
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis           [ Prints the property. ]

  Description        [ Prints the kind of the property and its expression. ]

  SideEffects        []

  SeeAlso            []

******************************************************************************/
static void game_print_prop_exp(FILE *file, PropGame_ptr prop)
{
  fprintf(file, " ");
  Prop_print(PROP(prop), (OStream_ptr)file, PROP_PRINT_FMT_FORMULA);
}
