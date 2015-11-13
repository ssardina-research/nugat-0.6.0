/**CFile***********************************************************************

  FileName    [ gameBuildModel.c ]

  PackageName [ game ]

  Synopsis    [ Defines functions to build scalar (flat), boolean and BDD
                models of a game hierarchy. ]

  Description [ ]

  SeeAlso     [ compleCmd.h ]

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

#include <code/nusmv/core/bmc/bmcInt.h>
#include "gameInt.h"
#include "GameHierarchy.h"
#include "PropDbGame.h"
#include "fsm/GameBddFsm.h"
#include "fsm/GameSexpFsm.h"

#include "compile/compile.h"
#include "dd/dd.h"
#include "enc/enc.h"
#include "fsm/FsmBuilder.h"
#include "fsm/bdd/BddFsm.h"
#include "fsm/sexp/SexpFsm.h"
#include "opt/opt.h"
#include "prop/propPkg.h"
#include "set/set.h"
#include "utils/utils.h"
#include "utils/NodeList.h"
#include "utils/error.h"

static char rcsid[] UTIL_UNUSED = "$Id: gameBuildModel.c,v 1.1.2.8 2010-02-10 14:45:31 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FsmBuilder_ptr global_fsm_builder;
EXTERN int yylineno;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Partly performs the "build_model" command for games. ]

  Description [ This function is used in CommandBuildFlatModel to
                adopt "build_model" command to deal with a game
                declaration. ]

  SideEffects [ ]

  SeeAlso     [ compile_create_flat_model, Game_CommandBuildBddModel ]

******************************************************************************/
void Game_CommandBuildFlatModel(NuSMVEnv_ptr env)
{
  if (GAME_SEXP_FSM(NULL) == PropDbGame_master_get_game_scalar_sexp_fsm( \
                                   PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)))) {
    SymbTable_ptr st;
    SymbLayer_ptr model_layer_1;
    SymbLayer_ptr model_layer_2;
    GameSexpFsm_ptr scalar_fsm;
    Set_t set, set1, set2;
    SymbLayerIter iter1, iter2;
    SymbTableIter titer;

    st = Compile_get_global_symb_table();
    model_layer_1 = SymbTable_get_layer(st, MODEL_LAYER_1);
    model_layer_2 = SymbTable_get_layer(st, MODEL_LAYER_2);




     /*NEW_CODE_START*/
     SymbTable_gen_iter(st,&titer,STT_VAR);
     set = SymbTable_iter_to_set(st, titer);

     SymbLayer_gen_iter(model_layer_1, &iter1, STT_VAR);
     set1 = SymbLayer_iter_to_set(model_layer_1, iter1);

     SymbLayer_gen_iter(model_layer_2, &iter2, STT_VAR);
     set2 = SymbLayer_iter_to_set(model_layer_2, iter2);

     /*NEW_CODE_END*/

     /*OLD_CODE_START
    set = Set_Make(NodeList_to_node_ptr(SymbTable_get_vars(st)));
    set1 =
      Set_Make(NodeList_to_node_ptr(SymbLayer_get_all_vars(model_layer_1)));
    set2 =
      Set_Make(NodeList_to_node_ptr(SymbLayer_get_all_vars(model_layer_2)));
      *OLD_CODE_END*/
    scalar_fsm =
      GameSexpFsm_create(/* we assume that symbol table contains only variables
                            from the game */
                         set,
                         GameHierarchy_get_player_1(mainGameHierarchy),
                         GameHierarchy_get_player_2(mainGameHierarchy),
                         set1,
                         set2);

    PropDbGame_master_set_game_scalar_sexp_fsm( \
                         PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)), scalar_fsm);

    Set_ReleaseSet(set2);
    Set_ReleaseSet(set1);
    Set_ReleaseSet(set);
  }
}

/**Function********************************************************************

  Synopsis    [ Performs the "build_boolean_model" command for games. ]

  Description [ This function is used in CommandBuildBooleanModel to
                adopt "build_boolean_model" command to deal with a
                game declaration.

                New determinization layers are created and committed
                to both the boolean and bdd encoding. Note that these
                layers cannot have any variables and are added only
                for compatability with corresponding functions dealing
                with usual (not-game) models. ]

  SideEffects [ ]

  SeeAlso     [ compile_create_boolean_model, Game_CommandBuildFlatModel ]

******************************************************************************/
void Game_CommandBuildBooleanModel(NuSMVEnv_ptr env)
{
  if (GAME_SEXP_FSM(NULL) == PropDbGame_master_get_game_bool_sexp_fsm( \
                                   PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)))) {
    GameSexpFsm_ptr scalar_fsm;
    GameSexpFsm_ptr bool_fsm;
    SymbTable_ptr st;
    SymbLayer_ptr determ_layer_1;
    SymbLayer_ptr determ_layer_2;

    int reord_status;
    dd_reorderingtype rt;
    BddEnc_ptr enc = BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)));
    DDMgr_ptr dd;

    /* temporary disables reordering */
    dd = BddEnc_get_dd_manager(enc);
    reord_status = dd_reordering_status(dd, &rt);
    if (reord_status == 1) { dd_autodyn_disable(dd); }

    /* create determinization layers */
    st = Compile_get_global_symb_table();

    determ_layer_1 = SymbTable_create_layer(st,
                                            DETERM_LAYER_1,
                                            SYMB_LAYER_POS_BOTTOM);
    determ_layer_2 = SymbTable_create_layer(st,
                                            DETERM_LAYER_2,
                                            SYMB_LAYER_POS_BOTTOM);

    /* convert existing scalar FSM to the boolean FSM */
    scalar_fsm = PropDbGame_master_get_game_scalar_sexp_fsm( \
                                     PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)));

    bool_fsm = GameSexpFsm_scalar_to_boolean(scalar_fsm,
                                             enc,
                                             determ_layer_1,
                                             determ_layer_2);

    PropDbGame_master_set_game_bool_sexp_fsm( \
                           PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)), bool_fsm);

    /* commits layers to the encodings */
    BaseEnc_commit_layer(BASE_ENC(Enc_get_bool_encoding()),
                         DETERM_LAYER_1);
    BaseEnc_commit_layer(BASE_ENC(Enc_get_bool_encoding()),
                         DETERM_LAYER_2);

    BaseEnc_commit_layer(BASE_ENC(EBddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)))),
                         DETERM_LAYER_1);
    BaseEnc_commit_layer(BASE_ENC(BddFsm_get_bdd_encoding(BDD_FSM(GAME_SEXP_FSM(NULL)))),
                         DETERM_LAYER_2);

     /*NEW_CODE_START*/
     SymbLayerIter iter1;
     NodeList_ptr syms1;
     SymbLayer_gen_iter(determ_layer_1, &iter1, STT_ALL);
     syms1 = SymbLayer_iter_to_list(determ_layer_1, iter1);

     SymbLayerIter iter2;
     NodeList_ptr syms2;
     SymbLayer_gen_iter(determ_layer_2, &iter2, STT_ALL);
     syms2 = SymbLayer_iter_to_list(determ_layer_2, iter2);

     /* determinization variables are not supported in Game */
     if (NodeList_get_length(syms1) != 0 ||
         NodeList_get_length(syms2) != 0) {
        yylineno = 0; /* for error messages */
        rpterr("determinization variables are not supported by realizability "
                       "algorithms, \nbut were created during booleanisation\n"
                       "(check ASSIGN with boolean on the left and boolean-set on the "
                       "right)\n");
     }
     /*NEW_CODE_END*/

     /*OLD_CODE_START
    /*
    if (NodeList_get_length(SymbLayer_get_all_symbols(determ_layer_1)) != 0 ||
        NodeList_get_length(SymbLayer_get_all_symbols(determ_layer_2)) != 0) {
      yylineno = 0;
      rpterr("determinization variables are not supported by realizability "
             "algorithms, \nbut were created during booleanisation\n"
             "(check ASSIGN with boolean on the left and boolean-set on the "
             "right)\n");
    }
      OLD_CODE_END*/
  } /* if */
}

/**Function********************************************************************

  Synopsis    [ Partly performs the "build_model" command for games. ]

  Description [ This function is used in CommandBuildModel to adopt
                "build_model" command to deal with a game declaration. ]

  SideEffects [ ]

  SeeAlso     [ CommandBuildModel, Game_CommandBuildFlatModel ]

******************************************************************************/
void Game_CommandBuildBddModel(NuSMVEnv_ptr env)
{
  SymbTable_ptr st = Compile_get_global_symb_table();
  GameSexpFsm_ptr scalar_fsm = PropDbGame_master_get_game_scalar_sexp_fsm( \
                                     PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)));

  GameBddFsm_ptr bdd_fsm =
    Game_CreateGameBddFsm(global_fsm_builder,
                          BddFsm_get_bdd_encoding(BDD_FSM(scalar_fsm)),
                          scalar_fsm,
                          SymbTable_get_layer(st, MODEL_LAYER_1),
                          SymbTable_get_layer(st, MODEL_LAYER_2),
                          get_partition_method(OptsHandler_create()));
  PropDbGame_master_set_game_bdd_fsm(PROP_DB_GAME(NuSMVEnv_get_value(env, ENV_PROP_DB)),
                                     bdd_fsm);
}

/**Function********************************************************************

  Synopsis    [ Creates a GameBddFsm instance from a given GameSexpFsm. ]

  Description [ Very similar to FsmBuilder_create_bdd_fsm, but creates
                a Game BDD FSM instead of usual BDD FSM. The main
                differences of Game BDD FSM from usual BDD FSM are:
                1. A game consist of two BDD FSM (one for each
                   player).
                2. There cannot be input variables.
                3. Variables are divided into two sets (one for every
                   player) and their cubes are also kept separately.

                Parameters layer_1 and layer_2 are model layers, which
                contain all the (state) variables of the first and
                second player, respectively. It is presumed that the
                system does not have any other variables. ]

  SideEffects [ ]

  SeeAlso     [ FsmBuilder_create_bdd_fsm ]

******************************************************************************/
GameBddFsm_ptr Game_CreateGameBddFsm(const FsmBuilder_ptr self,
                                     BddEnc_ptr enc,
                                     const GameSexpFsm_ptr sexp_fsm,
                                     const SymbLayer_ptr layer_1,
                                     const SymbLayer_ptr layer_2,
                                     const TransType trans_type)
{
  DDMgr_ptr dd;
  bdd_ptr one;
  SexpFsm_ptr player_1;
  SexpFsm_ptr player_2;
  GameBddFsm_ptr gameFsm;
  BddFsm_ptr bddfsm_1, bddfsm_2;
  BddVarSet_ptr curVarsCube_1,
    curVarsCube_2,
    nextVarsCube_1,
    nextVarsCube_2,
    curFrozVarsCube_1,
    curFrozVarsCube_2;

  FSM_BUILDER_CHECK_INSTANCE(self);
  BDD_ENC_CHECK_INSTANCE(enc);
  GAME_SEXP_FSM_CHECK_INSTANCE(sexp_fsm);
  SYMB_LAYER_CHECK_INSTANCE(layer_1);
  SYMB_LAYER_CHECK_INSTANCE(layer_2);

  dd = BddEnc_get_dd_manager(enc);
  one = bdd_true(dd);
  player_1 = GameSexpFsm_get_player_1(sexp_fsm);
  player_2 = GameSexpFsm_get_player_2(sexp_fsm);

  /* ---------------------------------------------------------------------- */
  /* Players variables cubes constraction                                   */
  /* ---------------------------------------------------------------------- */

  /* Game cannot have input variables */


   nusmv_assert(0 == SymbLayer_get_input_vars_num(layer_1) &&
                        0 == SymbLayer_get_input_vars_num(layer_2));

   /*OLD_CODE_START
  nusmv_assert(0 == NodeList_get_length(SymbLayer_get_input_vars(layer_1)) &&
               0 == NodeList_get_length(SymbLayer_get_input_vars(layer_2)));
  OLD_CODE_END*/

  /* create a cube of current state, next state and
     both state and frozen variables for player 1 */
  curVarsCube_1 = BddEnc_get_layer_vars_cube(enc, layer_1, VFT_CURRENT);
  curVarsCube_2 = BddEnc_get_layer_vars_cube(enc, layer_2, VFT_CURRENT);

  nextVarsCube_1 = BddEnc_state_var_to_next_state_var(enc, curVarsCube_1);
  nextVarsCube_2 = BddEnc_state_var_to_next_state_var(enc, curVarsCube_2);

  curFrozVarsCube_1 = BddEnc_get_layer_vars_cube(enc, layer_1, VFT_CURR_FROZEN);
  curFrozVarsCube_2 = BddEnc_get_layer_vars_cube(enc, layer_2, VFT_CURR_FROZEN);

  /* ---------------------------------------------------------------------- */
  /* Construct BDD FSM for players and then Game BDD FSM                    */
  /* ---------------------------------------------------------------------- */

  bddfsm_1 = FsmBuilder_create_bdd_fsm_of_vars(self,
                                               player_1,
                                               trans_type,
                                               enc,
                                               curVarsCube_1,
                                               one,
                                               nextVarsCube_1);
  bddfsm_2 = FsmBuilder_create_bdd_fsm_of_vars(self,
                                               player_2,
                                               trans_type,
                                               enc,
                                               curVarsCube_2,
                                               one,
                                               nextVarsCube_2);
  gameFsm = GameBddFsm_create(enc,
                              bddfsm_1, curVarsCube_1, curFrozVarsCube_1,
                              bddfsm_2, curVarsCube_2, curFrozVarsCube_2);

  bdd_free(dd, curVarsCube_1);
  bdd_free(dd, curVarsCube_2);
  bdd_free(dd, nextVarsCube_1);
  bdd_free(dd, nextVarsCube_2);
  bdd_free(dd, curFrozVarsCube_1);
  bdd_free(dd, curFrozVarsCube_2);
  bdd_free(dd, one);

  return gameFsm;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/
