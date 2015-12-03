/**CFile***********************************************************************

  FileName    [ gameCheckLTLSF07.c ]

  PackageName [ game ]

  Synopsis    [ Implements a BDD-based algorithm for realizability and
                synthesis of LTL games largely based on

                S. Schewe, B. Finkbeiner: Bounded Synthesis. ATVA'07.

                and

                E. Filiot, N. Jin, J. Raskin: An Antichain Algorithm
                for LTL Realizability. CAV'09. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Viktor Schuppan ]

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

#include <stdio.h>

#include "gameInt.h"
#include "gameCheckLTLSF07_gba.h"
#include "gameCheckLTLSF07_gba_wring.h"
#include "PropGame.h"
#include "parser/game_symbols.h"

#include "bmc/bmcInt.h"
#include "wff/wff.h"//#include "bmc/bmcWff.h"
#include "wff/w2w/w2w.h"
#include "wff/w2w/w2wInt.h"
#include "compile/compile.h"
#include "enc/enc.h"
#include "node/node.h"
#include "parser/symbols.h"
#include "prop/propPkg.h"
#include "utils/Slist.h"
#include "utils/error.h"
#include "utils/ustring.h"
#include "utils/utils.h"

static char rcsid[] UTIL_UNUSED = "$Id: gameCheckLTLSF07.c,v 1.1.2.9 2010-02-05 17:21:55 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Definition of the public accessor. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct Game_SF07_StructCheckLTLGameSF07_TAG*
  Game_SF07_StructCheckLTLGameSF07_ptr;

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Struct**********************************************************************

  Synopsis    [ Structure storing the input, current state and results of
                the sf07 algorithm. ]

  Description [ The structure has two main parts:

                - The iteration-invariant parts remains unmodified
                  during the iterations of the algorithm.

                - The iteration-variant part is changed in each
                  iteration of the algorithm.

                The iteration-invariant fields are as follows:

                - prop: The property for which realizabilty/synthesis
                  is carried out. Not owned.

                - player: The player in prop.

                - params: Parameters (see game.h). Not owned.

                - kmin: The minimal bound used in the algorithm. Start
                  iterating from here. Must be at least 0.

                - kmax: The maximal bound used in the algorithm. Stop
                  iterating here. Must be at least kmin.

                - w: For whom to play. Admissible values:
                     - GAME_WHO_BOTH,
                     - GAME_WHO_PROTAGONIST,
                     - GAME_WHO_ANTAGONIST,
                     - GAME_WHO_PLAYER_1,
                     - GAME_WHO_PLAYER_2.
                     This implementation is complete only for
                     GAME_WHO_BOTH, as no check is performed whether
                     the reached bound is large enough to conclude
                     unrealizability.

                - player1_ba: The B\"uchi automaton when curr_player
                  == PLAYER_1. Owned.

                - player2_ba: The B\"uchi automaton when curr_player
                  == PLAYER_2. Owned.

                - bdd_enc: The BDD encoder. Not owned.

                - bool_enc: The Boolean encoder. Not owned.

                - dd_manager: The BDD manager. Not owned.

                - symb_table: The symbol table. Not owned.

                The iteration-variant fields are as follows:

                - curr_k: The current bound.

                - curr_player: The current player. Note that this may
                  be different from the player in prop.

                - curr_player1_monitor_layer: The current layer where
                  player1 monitor variables will be added. Owned.

                - curr_player2_monitor_layer: The current layer where
                  player2 monitor variables will be added. Owned.

                - node_ptr curr_goal: The current goal. Not
                  owned/shared node_ptr.

                - curr_unique_number: A unique number to obtain
                  distinct variable names.

                - curr_player1_monitor_sexp: The current player1
                  monitor as a node_ptr module. Not owned/shared
                  node_ptr.

                - curr_player2_monitor_sexp: The current player2
                  monitor as a node_ptr module. Not owned/shared
                  node_ptr.

                - curr_player2_monitor_sexp_copy: A deep (not
                  find_noded) copy of the body of the current player2
                  monitor. For strategy printing. Owned.

                - curr_monitor_game_bdd_fsm: The current monitor as a
                  GameBddFsm. Owned.

                - curr_product_game_bdd_fsm: The current product of
                  model and monitor as a GameBddFsm. Owned.

                - curr_goal_realizability: The realizability status of
                  curr_goal.

                - strategy: The strategy of the winning player. Owned. ]

  SeeAlso    [ ]

******************************************************************************/
typedef struct Game_SF07_StructCheckLTLGameSF07_TAG {


  /* This part is invariant through iterations. */


  /* The property for which realizabilty/synthesis is carried out. */
  PropGame_ptr prop;

  /* The player in prop. */
  GamePlayer player;

  /* Parameters (see game.h) */
  gameParams_ptr params;

  /* The minimal bound. */
  unsigned int kmin;

  /* The maximal bound. */
  unsigned int kmax;

  /* Whom are we playing for. */
  Game_Who w;

  /* The B\"uchi automaton when curr_player == PLAYER_1. */
  Game_SF07_gba_ptr player1_ba;

  /* The B\"uchi automaton when curr_player == PLAYER_2. */
  Game_SF07_gba_ptr player2_ba;

  /* The BDD encoder. */
  BddEnc_ptr bdd_enc;

  /* The Boolean encoder. */
  BoolEnc_ptr bool_enc;

  /* The BDD manager. */
  DDMgr_ptr dd_manager;

  /* The symbol table. */
  SymbTable_ptr symb_table;


  /* This part is variant through iterations. */


  /* The current bound. */
  unsigned int curr_k;

  /* The current player. Note that this may be different from the
     player in prop. */
  GamePlayer curr_player;

  /* The current layer where player1 monitor variables will be added. */
  SymbLayer_ptr curr_player1_monitor_layer;

  /* The current layer where player2 monitor variables will be added. */
  SymbLayer_ptr curr_player2_monitor_layer;

  /* The current goal. */
  node_ptr curr_goal;

  /* A unique number to obtain distinct variable names. */
  int curr_unique_number;

  /* The current player1 monitor as a node_ptr module. */
  node_ptr curr_player1_monitor_sexp;

  /* The current player2 monitor as a node_ptr module. */
  node_ptr curr_player2_monitor_sexp;

  /* A deep (not find_noded) copy of the body of the current player2
     monitor. For strategy printing. */
  node_ptr curr_player2_monitor_sexp_copy;

  /* The current monitor as a GameBddFsm. */
  GameBddFsm_ptr curr_monitor_game_bdd_fsm;

  /* The current product of model and monitor as a GameBddFsm. */
  GameBddFsm_ptr curr_product_game_bdd_fsm;

  /* The realizability status of curr_goal. */
  Game_RealizabilityStatus curr_goal_realizability;

  /* The strategy of the winning player. */
  GameStrategy_ptr strategy;

} Game_SF07_StructCheckLTLGameSF07;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/



/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ To cast and check instances of
                Game_SF07_STructCheckLTLGameSf07. ]

  Description [ These macros must be used respectively to cast and to
                check instances of Game_SF07_STructCheckLTLGameSf07. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07(x) \
  ((Game_SF07_StructCheckLTLGameSF07_ptr) x)
#define GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(x) \
  ( nusmv_assert(GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07(x) != \
                 GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07(NULL)) )

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static Game_SF07_StructCheckLTLGameSF07_ptr
Game_SF07_StructCheckLTLGameSF07_create
ARGS((NuSMVEnv_ptr env,
      PropGame_ptr prop,
      gameParams_ptr params,
      unsigned int kmin,
      unsigned int kmax,
      Game_Who w));

static void Game_SF07_StructCheckLTLGameSF07_destroy
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_create_iteration
ARGS((Game_SF07_StructCheckLTLGameSF07_ptr self,
      unsigned int k,
      GamePlayer player,
      int curr_unique_number));

static void Game_SF07_StructCheckLTLGameSF07_destroy_iteration
ARGS((NodeMgr_ptr nodemgr,Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_run_iteration
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self,
      unsigned int curr_k,
      GamePlayer curr_player));

static void Game_SF07_StructCheckLTLGameSF07_construct_ba
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_construct_goal
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_construct_monitor_sexp
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static node_ptr Game_SF07_StructCheckLTLGameSF07_construct_monitor_var_decls
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static node_ptr
Game_SF07_StructCheckLTLGameSF07_construct_monitor_init_statements
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static node_ptr
Game_SF07_StructCheckLTLGameSF07_construct_monitor_trans_statements
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_construct_monitor_game_bdd_fsm
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_construct_product_game_bdd_fsm
ARGS((Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_check
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self));

static node_ptr Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name
ARGS((NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self,
      Game_SF07_gba_state_ptr state));

static node_ptr find_node_number ARGS((NodeMgr_ptr nodemgr, int n));

static void Game_SF07_StructCheckLTLGameSF07_print_monitor
ARGS((MasterPrinter_ptr wffprint,FILE* ostream, node_ptr module, boolean body_only));

static void Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_sexp
ARGS((Game_SF07_StructCheckLTLGameSF07_ptr self));

static void Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_bdd
ARGS((Game_SF07_StructCheckLTLGameSF07_ptr self));

static node_ptr Game_SF07_StructCheckLTLGameSF07_copy_node ARGS((NodeMgr_ptr nodemgr, node_ptr node));

static void Game_SF07_StructCheckLTLGameSF07_free_node ARGS((NodeMgr_ptr nodemgr,node_ptr node));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ High-level function exporting the sf07 algorithm and
                containing the top-level loop. ]

  Description [ Executes the sf07 algorithm. For an explanation of the
                arguments see the explanation of
                Game_SF07_StructCheckLTLGameSF07. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_CheckLtlGameSpecSF07(PropGame_ptr prop,
                               gameParams_ptr params,
                               unsigned int kmin,
                               unsigned int kmax,
                               Game_Who w)
{
  Game_SF07_StructCheckLTLGameSF07_ptr cls;
  unsigned int curr_k;
  GamePlayer curr_player;
  boolean done;

  NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(prop));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  FILE* outstream = StreamMgr_get_output_stream(streams);
  FILE* errstream = StreamMgr_get_error_stream(streams);
  OStream_ptr outostream = StreamMgr_get_output_ostream(streams);
  OStream_ptr errostream = StreamMgr_get_error_ostream(streams);

  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(Prop_get_status(PROP(prop)) == Prop_Unchecked);
  nusmv_assert(0 <= kmin);
  nusmv_assert(kmin <= kmax);
  nusmv_assert((w == GAME_WHO_BOTH) ||
               (w == GAME_WHO_PROTAGONIST) ||
               (w == GAME_WHO_ANTAGONIST) ||
               (w == GAME_WHO_PLAYER_1) ||
               (w == GAME_WHO_PLAYER_2));
  nusmv_assert(opt_game_game_initial_condition(opts) ==
               'N');

  cls = Game_SF07_StructCheckLTLGameSF07_create(env,prop, params, kmin, kmax, w);

  /* As in gameGeneral.c::Game_BeforeCheckingSpec. */
  if (opt_verbose_level_ge(opts, 1)) {
    fprintf(errstream, "computing ");
    fprintf(errstream, " ");
    Prop_print(PROP(cls->prop), errostream, PROP_PRINT_FMT_FORMULA);
    fprintf(errstream, "\n");
  }

  /* Some additional info. */
  if (opt_verbose_level_ge(opts, 2)) {
    fprintf(errstream,
       "\nwith Game_CheckLtlGameSpecSF07 using kmin = %d, kmax = %d, w = %s.\n",
            cls->kmin,
            cls->kmax,
            Game_Who_to_string(cls->w));
  }

  /* The main loop. */
  curr_k = kmin;
  done = false;
  while ((!done) && (curr_k <= kmax)) {
    if (((w == GAME_WHO_PROTAGONIST) && (cls->player == PLAYER_1)) ||
        ((w == GAME_WHO_ANTAGONIST) && (cls->player == PLAYER_2)) ||
        ((w == GAME_WHO_BOTH) && (cls->player == PLAYER_1)) ||
        (w == GAME_WHO_PLAYER_1)) {
      curr_player = PLAYER_1;
    } else {
      curr_player = PLAYER_2;
    }
    Game_SF07_StructCheckLTLGameSF07_run_iteration(env,cls, curr_k, curr_player);
    if ((Prop_get_status(PROP(cls->prop)) == Prop_True) ||
        (Prop_get_status(PROP(cls->prop)) == Prop_False)) {
      done = true;
    }

    if ((!done) && (w == GAME_WHO_BOTH)) {
      if (curr_player == PLAYER_1) {
        curr_player = PLAYER_2;
      } else {
        curr_player = PLAYER_1;
      }
      Game_SF07_StructCheckLTLGameSF07_run_iteration(env,cls, curr_k, curr_player);
      if ((Prop_get_status(PROP(cls->prop)) == Prop_True) ||
          (Prop_get_status(PROP(cls->prop)) == Prop_False)) {
        done = true;
      }
    }

    if (!done) {
      curr_k++;
    }
  }

  /* Similar to gameGeneral.c::Game_AfterCheckingSpec. */

  /* Announce result. */
  {
    fprintf(outstream, "-- ");
    fprintf(outstream, " ");
    Prop_print(PROP(prop), outostream, PROP_PRINT_FMT_FORMULA);

    switch (Prop_get_status(PROP(cls->prop))) {
    case Prop_True:
      fprintf(outstream, " : the strategy has been found\n");
      break;
    case Prop_False:
      fprintf(outstream, " : no strategy exists\n");
      break;
    case Prop_Unchecked:
      fprintf(outstream, " : existence of a strategy is unknown\n");
      nusmv_assert(cls->strategy == GAME_STRATEGY(NULL));
      break;
    default:
      nusmv_assert(false);
      break;
    }
  }

  /* Print strategy. */
  if ((((cls->params != (gameParams_ptr) NULL) && params->strategy_printout) ||
      opt_game_print_strategy(opts)) &&
      ((Prop_get_status(PROP(cls->prop)) == Prop_True) ||
       (Prop_get_status(PROP(cls->prop)) == Prop_False)))
  {
    if (get_game_sf07_strategy_printing_mode(opts) ==
        GAME_SF07_STRATEGY_PRINTING_MODE_SEXP) {
      Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_sexp(cls);
    } else {
      Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_bdd(cls);
    }
  }

  fprintf(outstream, "\n");

  /* Clean up. */
  if (Prop_get_status(PROP(cls->prop)) == Prop_True ||
      Prop_get_status(PROP(cls->prop)) == Prop_False) {
    Game_SF07_StructCheckLTLGameSF07_destroy_iteration(nodemgr,cls);
  }
  Game_SF07_StructCheckLTLGameSF07_destroy(env,cls);
}

/**Function********************************************************************

  Synopsis    [ Game_SF07_StrategyPrintingMode to const char*. ]

  Description [ Returned string is statically allocated and must not be
                freed. ]

  SideEffects [ None. ]

  SeeAlso     [ ]

******************************************************************************/
const char*
Game_SF07_StrategyPrintingMode_to_string(const Game_SF07_StrategyPrintingMode m)
{
  switch (m) {
  case GAME_SF07_STRATEGY_PRINTING_MODE_SEXP:
    return GAME_SF07_STRATEGY_PRINTING_MODE_SEXP_STRING;
  case GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE:
    return GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE_STRING;
  case GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED:
    return GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED_STRING;
  default:
    nusmv_assert(false);
  }
}

/*---------------------------------------------------------------------------*/
/* Static function definitions                                               */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Constructor for Game_SF07_StructCheckLTLGameSF07. ]

  Description [ Does meaningful initialization only for the
                iteration-invariant parts. The iteration-variant parts
                are set to NULL or similar. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_destroy,
                Game_SF07_StructCheckLTLGameSF07_create_iteration ]

******************************************************************************/
static Game_SF07_StructCheckLTLGameSF07_ptr
Game_SF07_StructCheckLTLGameSF07_create(NuSMVEnv_ptr env,
                                        PropGame_ptr prop,
                                        gameParams_ptr params,
                                        unsigned int kmin,
                                        unsigned int kmax,
                                        Game_Who w)
{
  Game_SF07_StructCheckLTLGameSF07_ptr res;

  PROP_GAME_CHECK_INSTANCE(prop);

  res = ALLOC(Game_SF07_StructCheckLTLGameSF07, 1);
  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(res);

  /* The iteration-invariant parts. */

  res->prop = prop;
  res->player = Game_StrToPlayer(env,PropGame_get_player(prop));
  res->params = params;
  res->kmin = kmin;
  res->kmax = kmax;
  res->w = w;
  res->player1_ba = GAME_SF07_GBA(NULL);
  res->player2_ba = GAME_SF07_GBA(NULL);

  res->bdd_enc = NuSMVEnv_get_value(env, ENV_BDD_ENCODER);
  res->bool_enc =
    BoolEncClient_get_bool_enc(BOOL_ENC_CLIENT(res->bdd_enc));
  res->dd_manager = BddEnc_get_dd_manager(res->bdd_enc);
  res->symb_table = SYMB_TABLE(NuSMVEnv_get_value(env, ENV_SYMB_TABLE));

  if (!cmp_struct_get_bmc_init(cmps)) {
      NuSMVEnv_get_handled_hash_ptr(env, ENV_W2W_WFF2NNF_HASH);
  }

  /* The iteration-variant parts. */

  res->curr_player1_monitor_layer = SYMB_LAYER(NULL);
  res->curr_player2_monitor_layer = SYMB_LAYER(NULL);
  res->curr_goal = Nil;
  res->curr_player1_monitor_sexp = Nil;
  res->curr_player2_monitor_sexp = Nil;
  res->curr_player2_monitor_sexp_copy = Nil;
  res->curr_monitor_game_bdd_fsm = GAME_BDD_FSM(NULL);
  res->curr_product_game_bdd_fsm = GAME_BDD_FSM(NULL);
  res->curr_goal_realizability = GAME_UNKNOWN;
  res->strategy = GAME_STRATEGY(NULL);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Destructor for Game_SF07_StructCheckLTLGameSF07. ]

  Description [ Does meaningful destruction only for the
                iteration-invariant parts. The iteration-variant parts
                are assumed to be NULL or similar. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_create,
                Game_SF07_StructCheckLTLGameSF07_destroy_iteration ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_destroy
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);

  /* The iteration-invariant parts. */

  /* Don't destroy prop: doesn't belong here. */
  if (self->player1_ba) {
    Game_SF07_gba_destroy(self->player1_ba);
  }
  if (self->player2_ba) {
    Game_SF07_gba_destroy(self->player2_ba);
  }
  /* Don't destroy params: doesn't belong here. */
  /* Don't destroy bdd_enc: doesn't belong here. */
  /* Don't destroy bool_enc: doesn't belong here. */
  /* Don't destroy dd_manager: doesn't belong here. */
  /* Don't destroy symb_table: doesn't belong here. */

  if (!cmp_struct_get_bmc_init(cmps)) {
      clear_assoc(NuSMVEnv_get_handled_hash_ptr(env, ENV_W2W_WFF2NNF_HASH));
  }

  /* The iteration-variant parts. */

  nusmv_assert(self->curr_player1_monitor_layer == SYMB_LAYER(NULL));
  nusmv_assert(self->curr_player2_monitor_layer == SYMB_LAYER(NULL));
  /* Don't destroy goal: node_ptr are shared. */
  /* Don't destroy player1_monitor_sexp: node_ptr are shared. */
  /* Don't destroy player2_monitor_sexp: node_ptr are shared. */
  nusmv_assert(self->curr_player2_monitor_sexp_copy == Nil);
  nusmv_assert(self->curr_monitor_game_bdd_fsm == GAME_BDD_FSM(NULL));
  nusmv_assert(self->curr_product_game_bdd_fsm == GAME_BDD_FSM(NULL));
  nusmv_assert(self->strategy == GAME_STRATEGY(NULL));

  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Initializes the iteration-variant parts. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_create,
                Game_SF07_StructCheckLTLGameSF07_destroy_iteration ]

******************************************************************************/
static void
Game_SF07_StructCheckLTLGameSF07_create_iteration
(Game_SF07_StructCheckLTLGameSF07_ptr self,
 unsigned int curr_k,
 GamePlayer curr_player,
 int curr_unique_number)
{
  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  nusmv_assert(self->kmin <= curr_k);
  nusmv_assert(curr_k <= self->kmax);
  nusmv_assert(((self->w == GAME_WHO_PROTAGONIST) &&
                (self->player == curr_player)) ||
               ((self->w == GAME_WHO_ANTAGONIST) &&
                (self->player != curr_player)) ||
               (self->w == GAME_WHO_BOTH) ||
               ((self->w == GAME_WHO_PLAYER_1) && (curr_player == PLAYER_1)) ||
               ((self->w == GAME_WHO_PLAYER_2) && (curr_player == PLAYER_2)));

  self->curr_k = curr_k;
  self->curr_player = curr_player;
  self->curr_player1_monitor_layer =
    SymbTable_create_layer(self->symb_table, NULL, SYMB_LAYER_POS_BOTTOM);
  self->curr_player2_monitor_layer =
    SymbTable_create_layer(self->symb_table, NULL, SYMB_LAYER_POS_BOTTOM);
  self->curr_goal = Nil;
  self->curr_unique_number = curr_unique_number;
  self->curr_player1_monitor_sexp = Nil;
  self->curr_player2_monitor_sexp = Nil;
  self->curr_player2_monitor_sexp_copy = Nil;
  self->curr_monitor_game_bdd_fsm = GAME_BDD_FSM(NULL);
  self->curr_product_game_bdd_fsm = GAME_BDD_FSM(NULL);
  self->curr_goal_realizability = GAME_UNKNOWN;
  self->strategy = GAME_STRATEGY(NULL);
}

/**Function********************************************************************

  Synopsis    [ Destroys the iteration-variant parts. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_destroy,
                Game_SF07_StructCheckLTLGameSF07_create_iteration ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_destroy_iteration
(NodeMgr_ptr nodemgr,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);

  /* Remove player1_monitor_layer. */
  if (BaseEnc_layer_occurs(BASE_ENC(self->bdd_enc),
                        SymbLayer_get_name(self->curr_player1_monitor_layer))) {
    BaseEnc_remove_layer(BASE_ENC(self->bdd_enc),
                         SymbLayer_get_name(self->curr_player1_monitor_layer));
  }
  if (BaseEnc_layer_occurs(BASE_ENC(self->bool_enc),
                        SymbLayer_get_name(self->curr_player1_monitor_layer))) {
    BaseEnc_remove_layer(BASE_ENC(self->bool_enc),
                         SymbLayer_get_name(self->curr_player1_monitor_layer));
  }
  SymbTable_remove_layer(self->symb_table, self->curr_player1_monitor_layer);
  self->curr_player1_monitor_layer = SYMB_LAYER(NULL);
  /* Remove player2_monitor_layer. */
  if (BaseEnc_layer_occurs(BASE_ENC(self->bdd_enc),
                        SymbLayer_get_name(self->curr_player2_monitor_layer))) {
    BaseEnc_remove_layer(BASE_ENC(self->bdd_enc),
                         SymbLayer_get_name(self->curr_player2_monitor_layer));
  }
  if (BaseEnc_layer_occurs(BASE_ENC(self->bool_enc),
                        SymbLayer_get_name(self->curr_player2_monitor_layer))) {
    BaseEnc_remove_layer(BASE_ENC(self->bool_enc),
                         SymbLayer_get_name(self->curr_player2_monitor_layer));
  }
  SymbTable_remove_layer(self->symb_table, self->curr_player2_monitor_layer);
  self->curr_player2_monitor_layer = SYMB_LAYER(NULL);
  /* Don't destroy goal: node_ptr are shared. */
  self->curr_goal = Nil;
  self->curr_unique_number = -1;
  /* Don't destroy player1_monitor_sexp: node_ptr are shared. */
  self->curr_player1_monitor_sexp = Nil;
  /* Don't destroy player2_monitor_sexp: node_ptr are shared. */
  self->curr_player2_monitor_sexp = Nil;
  {
    node_ptr n = self->curr_player2_monitor_sexp_copy;
    Game_SF07_StructCheckLTLGameSF07_free_node(nodemgr,n);
    self->curr_player2_monitor_sexp_copy = Nil;
  }
  GameBddFsm_destroy(self->curr_monitor_game_bdd_fsm);
  self->curr_monitor_game_bdd_fsm = GAME_BDD_FSM(NULL);
  GameBddFsm_destroy(self->curr_product_game_bdd_fsm);
  self->curr_product_game_bdd_fsm = GAME_BDD_FSM(NULL);
  self->curr_goal_realizability = GAME_UNKNOWN;
  if (self->strategy) {
    GameStrategy_destroy(self->strategy);
    self->strategy = GAME_STRATEGY(NULL);
  }
}

/**Function********************************************************************

  Synopsis    [ Executes one iteration of the sf07 algorithm. ]

  Description [ One iteration is defined by one bound (curr_k) and one
                player (curr_player).

                It consists of the following steps:

                - Construct the B\"uchi automaton for the property or
                  its negation (if not yet performed).

                - Construct the current goal.

                - Construct the current monitor.

                - Form the product of the model and the current
                  monitor.

                - Check whether the current goal is realizable in the
                  product. ]

  SideEffects [ ]

  SeeAlso     [ Game_CheckLtlGameSpecSF07 ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_run_iteration
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self,
 unsigned int curr_k,
 GamePlayer curr_player)
{
  static int ltlgame_sf07_unique_number = -1;

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);

  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  FILE* errstream = StreamMgr_get_error_stream(streams);

  /* Increase counter. */
  nusmv_assert(ltlgame_sf07_unique_number < 999999999);
  ltlgame_sf07_unique_number++;

  Game_SF07_StructCheckLTLGameSF07_create_iteration(self,
                                                    curr_k,
                                                    curr_player,
                                                    ltlgame_sf07_unique_number);

  if (opt_verbose_level_ge(opts, 2)) {
    fprintf(errstream,
            "\nGame_CheckLtlGameSpecSF07: performing iteration with curr_k = "
            "%d, curr_player = %d.\n\n",
            curr_k,
            (curr_player == PLAYER_1) ? 1 : 2);
  }

  CATCH(errmgr) {
    Game_SF07_StructCheckLTLGameSF07_construct_ba(env,self);
    Game_SF07_StructCheckLTLGameSF07_construct_goal(env,self);
    Game_SF07_StructCheckLTLGameSF07_construct_monitor_sexp(env,self);
    Game_SF07_StructCheckLTLGameSF07_construct_monitor_game_bdd_fsm(env,self);
    Game_SF07_StructCheckLTLGameSF07_construct_product_game_bdd_fsm(self);
    Game_SF07_StructCheckLTLGameSF07_check(env,self);
    if (self->curr_goal_realizability == GAME_REALIZABLE) {
      if (self->player == self->curr_player) {
        Prop_set_status(PROP(self->prop), Prop_True);
      } else {
        Prop_set_status(PROP(self->prop), Prop_False);
      }
    }
  }
  FAIL(errmgr) {
    fprintf(errstream,
            "Error executing an iteration of the sf07 algorithm.\n");
    ErrorMgr_nusmv_exit(errmgr,1);
  }

  if (opt_verbose_level_ge(opts, 2)) {
    fprintf(errstream,
            "\nGame_CheckLtlGameSpecSF07: finished iteration. Sub game is %s.\n",
            ((self->curr_goal_realizability == GAME_REALIZABLE) ?
             "realizable" :
             "unrealizable"));
  }

  /* The top-level algorithm terminates once a sub game is
     realizable. In that case some iteration-variant fields are kept
     for strategy printing. Destruction of the iteration-variant parts
     is done in Game_CheckLtlGameSpecSF07. */
  if (self->curr_goal_realizability != GAME_REALIZABLE) {
    Game_SF07_StructCheckLTLGameSF07_destroy_iteration(nodemgr,self);
  }
}

/**Function********************************************************************

  Synopsis    [ Constructs the B\"uchi automaton for the property or its
                negation if it has not been constructed yet. ]

  Description [ The (possibly negated) property is Booleanized and
                nnfed before handing it to the LTL to B\"uchi translator.

                The resulting B\"uchi automaton should not be
                generalized, i.e., only have a single fairness
                constraint. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_construct_ba
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  node_ptr formula;
  node_ptr booleanized;
  node_ptr nnfed;
  Game_SF07_gba_ptr ba;

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  PROP_GAME_CHECK_INSTANCE(self->prop);

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const ErrorMgr_ptr  errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
  const MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  FILE* errstream = StreamMgr_get_error_stream(streams);

  /* Has the ba already been constructed? */
  if (((self->curr_player == PLAYER_1) &&
       (self->player1_ba != GAME_SF07_GBA(NULL))) ||
      ((self->curr_player == PLAYER_2) &&
       (self->player2_ba != GAME_SF07_GBA(NULL)))) {
    return;
  }

  /* If the current play is for the protagonist, then negate the
     formula. */
  formula = Prop_get_expr_core(PROP(self->prop));
  if (self->player == self->curr_player) {
    formula = find_node(nodemgr,NOT, formula, Nil);
  }

  /* Booleanize and nnfize. */
  {
    SymbLayer_ptr det_layer;

    /* Booleanize. */
    nusmv_assert(Compile_check_if_bool_model_was_built(env,(FILE*) NULL, true) == 0);
    det_layer = SymbTable_create_layer(self->symb_table,
                                       (char*) NULL, /* temp name */
                                       SYMB_LAYER_POS_DEFAULT);
    booleanized = NODE_PTR(Compile_expr2bexpr(self->bdd_enc,
                                              det_layer,
                                              formula));
    /**NEW_CODE_START**/
    SymbLayerIter iter;
    NodeList_ptr syms;
    SymbLayer_gen_iter(det_layer, &iter, STT_ALL);
    syms = SymbLayer_iter_to_list(det_layer, iter);
    /**NEW_CODE_END**/
    if (NodeList_get_length(/*SymbLayer_get_all_symbols(det_layer)*/syms) != 0) {
      char* tmp;
      tmp = sprint_node(wffprint,formula);
      fprintf(errstream,
              "Error generating B\"uchi automaton for formula %s: "
              "booleanization introduced determinization variables.\n",
              tmp);
      FREE(tmp);
      ErrorMgr_nusmv_exit(errmgr,1);
    }
    SymbTable_remove_layer(self->symb_table, det_layer);

    /* Nnfize. */
    nnfed = Wff2Nnf(env,booleanized);

    /* Log result. */
    if (opt_verbose_level_ge(opts, 4)) {
      fprintf(errstream,
              "\nGame_SF07_StructCheckLTLGameSF07_construct_ba: booleanized, "
              "nnfed formula is:\n");
      print_node(wffprint,errstream, nnfed);
      fprintf(errstream,
              "\nGame_SF07_StructCheckLTLGameSF07_construct_ba: end "
              "booleanized, nnfed formula\n");
    }
  }

  /* Construct ba. */
  ba = Game_SF07_gba_wring_ltl2gba(env,nnfed);
  if (ba == GAME_SF07_GBA(NULL)) {
    char* tmp;
    tmp = sprint_node(wffprint,formula);
    fprintf(errstream,
            "Error generating B\"uchi automaton for formula %s.\n",
            tmp);
    FREE(tmp);
    ErrorMgr_nusmv_exit(errmgr,1);
  }
  if (Game_SF07_gba_get_fairness_constraints_count(ba) > 1) {
    char* tmp;
    tmp = sprint_node(wffprint,formula);
    fprintf(errstream,
            "Error generating B\"uchi automaton for formula %s: result has "
            "more than 1 fairness constraints.\n",
            tmp);
    FREE(tmp);
    ErrorMgr_nusmv_exit(errmgr,1);
  }

  /* Fix the ba if it has no sets of fairness constraints: add the set
     of states as a fairness constraint. That also deals with the case
     of a completely empty automaton (no states, no nothing), which is
     the result of translating FALSE. */
  {
    if (Game_SF07_gba_get_fairness_constraints_count(ba) == 0) {
      hash_ptr fairness_constraint;
      Slist_ptr states;
      Siter s_iter;

      fairness_constraint = new_assoc();
      Game_SF07_gba_add_fairness_constraint(ba, fairness_constraint);
      states = Game_SF07_gba_get_states(ba);
      SLIST_FOREACH(states, s_iter) {
        Game_SF07_gba_state_ptr state;
        state = GAME_SF07_GBA_STATE(Siter_element(s_iter));
        Game_SF07_gba_add_state_to_fairness_constraint(ba,
                                                       fairness_constraint,
                                                       state);
      }
    }
  }

  /* Store ba. */
  if (self->curr_player == PLAYER_1) {
    self->player1_ba = ba;
  } else {
    self->player2_ba = ba;
  }
}

/**Function********************************************************************

  Synopsis    [ Constructs the goal for the current iteration. ]

  Description [ The goal is that the current player can avoid that any
                of the monitor state variables reaches the value
                self->curr_k. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_construct_monitor_sexp ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_construct_goal
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  Game_SF07_gba_ptr ba;
  Slist_ptr states;
  Siter s_iter;
  node_ptr avoidtarget_statement;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  if (self->curr_player == PLAYER_1) {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player1_ba);
  } else {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player2_ba);
  }
  nusmv_assert(self->curr_goal == Nil);

  if (self->curr_player == PLAYER_1) {
    ba = self->player1_ba;
  } else {
    ba = self->player2_ba;
  }
  states = Game_SF07_gba_get_states(ba);
  avoidtarget_statement = find_node(nodemgr,FALSEEXP, Nil, Nil);

  /* Form the disjunction of all fair states having reached the
     current bound. */
  SLIST_FOREACH(states, s_iter) {
    Game_SF07_gba_state_ptr state;
    node_ptr state_var_name;

    state = GAME_SF07_GBA_STATE(Siter_element(s_iter));
    state_var_name =
      Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name(env,self, state);

    if (Game_SF07_gba_is_state_in_first_fairness_constraint(ba, state)) {
      avoidtarget_statement = find_node(nodemgr,OR,
                                        find_node(nodemgr,EQUAL,
                                                  state_var_name,
                                                find_node_number(nodemgr, self->curr_k)),
                                        avoidtarget_statement);
    }
  }

  self->curr_goal = find_node(nodemgr,AVOIDTARGET,
                              NODE_FROM_INT((self->curr_player == PLAYER_1) ?
                                            1 :
                                            2),
                              avoidtarget_statement);
}

/**Function********************************************************************

  Synopsis    [ Constructs the monitor for the current iteration as a sexp. ]

  Description [ Only the monitor for player 2 is meaningful. The
                monitor for player 1 is universal, i.e., it places no
                restrictions on the game.

                The monitor is a mix of scalar and Boolean
                sexps. While the major parts directly constructed here
                or in subroutines are scalar, the cubes characterizing
                states in the B\"uchi automaton may be Boolean. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_construct_goal ]

******************************************************************************/
#define GAME_SF07_PLAYER1_MONITOR_MODULE_BASE_NAME "game_sf07_player1_monitor_"
#define GAME_SF07_PLAYER2_MONITOR_MODULE_BASE_NAME "game_sf07_player2_monitor_"
static void Game_SF07_StructCheckLTLGameSF07_construct_monitor_sexp
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  node_ptr var_decls;
  node_ptr init_statements;
  node_ptr trans_statements;
  char* module_name;
  node_ptr monitor;

    const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
    MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));
    const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));
    OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
    StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
    FILE* errstream = StreamMgr_get_error_stream(streams);

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  if (self->curr_player == PLAYER_1) {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player1_ba);
    nusmv_assert(Game_SF07_gba_is_simple(self->player1_ba));
  } else {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player2_ba);
    nusmv_assert(Game_SF07_gba_is_simple(self->player2_ba));
  }
  nusmv_assert(self->curr_player1_monitor_sexp == Nil);
  nusmv_assert(self->curr_player2_monitor_sexp == Nil);

  /* player 2 */
  {
    /* Construct module name. */
    module_name = ALLOC(char,
                        strlen(GAME_SF07_PLAYER2_MONITOR_MODULE_BASE_NAME)+10);
    nusmv_assert(module_name != (char*) NULL);
    sprintf(module_name,
            "%s%u",
            GAME_SF07_PLAYER2_MONITOR_MODULE_BASE_NAME,
            self->curr_unique_number);

    /* Construct parts. */
    var_decls =
      Game_SF07_StructCheckLTLGameSF07_construct_monitor_var_decls(env,self);
    init_statements =
      Game_SF07_StructCheckLTLGameSF07_construct_monitor_init_statements(env,self);
    trans_statements =
      Game_SF07_StructCheckLTLGameSF07_construct_monitor_trans_statements(env,self);

    /* Link parts. */
    monitor = Nil;
    monitor = append(monitor, trans_statements);
    monitor = append(monitor, init_statements);
    if (var_decls != Nil) {
      monitor = new_node(nodemgr,CONS, var_decls, monitor);
    }
    monitor = new_node(nodemgr,MODULE,
                       new_node(nodemgr,MODTYPE,
                                new_node(nodemgr,ATOM,
                                         (node_ptr) UStringMgr_find_string(strings,module_name),
                                         Nil),
                                Nil),
                       monitor);

    if (opt_verbose_level_ge(opts, 4)) {
      fprintf(errstream,
              "\nGame_SF07_StructCheckLTLGameSF07_construct_monitor_sexp: "
              "player 2 monitor is:\n");
      Game_SF07_StructCheckLTLGameSF07_print_monitor(wffprint,
                                                     errstream,
                                                     monitor,
                                                     false);
      fprintf(errstream,
              "\nGame_SF07_StructCheckLTLGameSF07_construct_monitor_sexp: end "
              "player 2 monitor\n");
    }

    /* Clean up. */
    FREE(module_name);

    /* Store and copy (for later use in strategy printing). */
    self->curr_player2_monitor_sexp = monitor;
    self->curr_player2_monitor_sexp_copy =
      Game_SF07_StructCheckLTLGameSF07_copy_node(nodemgr,monitor);
  }

  /* player 1 */
  {
    /* Construct module name. */
    module_name = ALLOC(char,
                        strlen(GAME_SF07_PLAYER1_MONITOR_MODULE_BASE_NAME)+10);
    nusmv_assert(module_name != (char*) NULL);
    sprintf(module_name,
            "%s%u",
            GAME_SF07_PLAYER1_MONITOR_MODULE_BASE_NAME,
            self->curr_unique_number);

    /* Construct empty module. */
    monitor = new_node(nodemgr,MODULE,
                       new_node(nodemgr,MODTYPE,
                                new_node(nodemgr,ATOM,
                                         (node_ptr) UStringMgr_find_string(strings,module_name),
                                         Nil),
                                Nil),
                       Nil);

    if (opt_verbose_level_ge(opts, 4)) {
      fprintf(errstream,
              "\nGame_SF07_StructCheckLTLGameSF07_construct_monitor_sexp: "
              "player 1 monitor is:\n");
      Game_SF07_StructCheckLTLGameSF07_print_monitor(wffprint,
                                                     errstream,
                                                     monitor,
                                                     false);
      fprintf(errstream,
              "\nGame_SF07_StructCheckLTLGameSF07_construct_monitor_sexp: end "
              "player 1 monitor\n");
    }

    /* Clean up. */
    FREE(module_name);

    self->curr_player1_monitor_sexp = monitor;
  }
}

/**Function********************************************************************

  Synopsis    [ Constructs the variable declarations for the monitor in
                the current iteration as a sexp. ]

  Description [ For each state in the B\"uchi automaton in the current
                iteration there is one state variable with range -1 to
                self->curr_k. ]

  SideEffects [ ]

  SeeAlso     [
             Game_SF07_StructCheckLTLGameSF07_construct_monitor_init_statements,
             Game_SF07_StructCheckLTLGameSF07_construct_monitor_trans_statements
              ]

******************************************************************************/
static node_ptr Game_SF07_StructCheckLTLGameSF07_construct_monitor_var_decls
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  Game_SF07_gba_ptr ba;
  Slist_ptr states;
  node_ptr var_type;
  Siter s_iter;
  node_ptr var_decls;
  node_ptr res;

    const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  if (self->curr_player == PLAYER_1) {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player1_ba);
  } else {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player2_ba);
  }

  if (self->curr_player == PLAYER_1) {
    ba = self->player1_ba;
  } else {
    ba = self->player2_ba;
  }
  states = Game_SF07_gba_get_states(ba);
  var_decls = Nil;

  var_type = find_node(nodemgr,TWODOTS,
                       find_node_number(nodemgr, -1),
                       find_node_number(nodemgr, self->curr_k));

  /* For each state in the current ba there is one variable with range
     -1 .. curr_k. */
  SLIST_FOREACH(states, s_iter) {
    Game_SF07_gba_state_ptr state;
    node_ptr state_var_name;
    node_ptr var_decl;

    state = GAME_SF07_GBA_STATE(Siter_element(s_iter));
    state_var_name =
      Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name(env,self, state);
    var_decl = new_node(nodemgr,COLON, state_var_name, var_type);
    var_decls = new_node(nodemgr,CONS, var_decl, var_decls);
  }

  if (var_decls != Nil) {
    res = new_node(nodemgr,VAR, reverse(var_decls), Nil);
  } else {
    res = Nil;
  }

  return res;
}

/**Function********************************************************************

  Synopsis    [ Constructs the INIT statements for the monitor in the
                current iteration as a sexp. ]

  Description [ The initial value of a state variable in the monitor
                depends on whether the corresponding state in the
                B\"uchi automaton ba for the property of the current
                player is an initial state in ba, whether it is a fair
                state in ba, and on the current bound self->curr_k:

                - State variables for ba initial states whose label is
                  not fulfilled are initialized with -1.

                - State variables for ba initial, non-fair states
                  whose label is fulfilled are initialized with 0. So
                  are state variables for ba initial, fair states
                  whose label is fulfilled if self->curr_k is 0.

                - State variables for ba initial, fair states whose
                  label is fulfilled are initialized with 1 if
                  self->curr_k is > 0.

                The statements are a mix of scalar and Boolean
                sexps. While the major parts directly constructed here
                or in subroutines are scalar, the cubes characterizing
                states in the B\"uchi automaton may be Boolean. ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_construct_monitor_var_decls,
           Game_SF07_StructCheckLTLGameSF07_construct_monitor_trans_statements ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr
Game_SF07_StructCheckLTLGameSF07_construct_monitor_init_statements
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  Game_SF07_gba_ptr ba;
  Slist_ptr states;
  Siter s_iter;
  node_ptr init_statements;
  node_ptr res;

    const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  if (self->curr_player == PLAYER_1) {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player1_ba);
    nusmv_assert(Game_SF07_gba_is_simple(self->player1_ba));
  } else {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player2_ba);
    nusmv_assert(Game_SF07_gba_is_simple(self->player2_ba));
  }

  if (self->curr_player == PLAYER_1) {
    ba = self->player1_ba;
  } else {
    ba = self->player2_ba;
  }
  states = Game_SF07_gba_get_states(ba);
  init_statements = Nil;

  SLIST_FOREACH(states, s_iter) {
    Game_SF07_gba_state_ptr state;
    node_ptr state_var_name;
    node_ptr init_statement;

    state = GAME_SF07_GBA_STATE(Siter_element(s_iter));
    state_var_name =
      Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name(env,self, state);

    if (!Game_SF07_gba_is_state_initial(ba, state)) {
      init_statement = new_node(nodemgr,INIT,
                                find_node(nodemgr,EQUAL,
                                          state_var_name,
                                          find_node_number(nodemgr, -1)),
                                Nil);
    } else {
      node_ptr label;
      node_ptr inv_false;
      node_ptr inv_true;
      int inv_true_init_value;

      label = Game_SF07_gba_state_get_label(state);

      if ((!Game_SF07_gba_is_state_in_first_fairness_constraint(ba, state)) ||
          (self->curr_k == 0)) {
        inv_true_init_value = 0;
      } else {
        inv_true_init_value = 1;
      }

      inv_false = find_node(nodemgr,IFF,
                            find_node(nodemgr,NOT,
                                      label,
                                      Nil),
                            find_node(nodemgr,EQUAL,
                                      state_var_name,
                                      find_node_number(nodemgr, -1)));
      inv_true = find_node(nodemgr,IFF,
                           label,
                           find_node(nodemgr,EQUAL,
                                     state_var_name,
                                     find_node_number(nodemgr, inv_true_init_value)));
      init_statement = new_node(nodemgr,INIT,
                                find_node(nodemgr,AND,
                                          inv_false,
                                          inv_true),
                                Nil);
    }

    init_statements = new_node(nodemgr,CONS, init_statement, init_statements);
  }

  res = reverse(init_statements);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Constructs the TRANS statements for the monitor in the
                current iteration as a sexp. ]

  Description [ Let v_s be a state variable in the monitor for state s
                in the B\"uchi automaton ba of the current
                player. Constraints are as follows.

                For each outgoing transition (s,t):

                - for i = 0 ... self->curr_k - 1

                  - if t is not fair

                    (v_s = i) -> ((next(label(t))) -> (next(v_t) >= i))

                  - if t is fair

                    (v_s = i) -> ((next(label(t))) -> (next(v_t) > i))

                - i = self->curr_k

                  (v_s = i) -> ((next(label(t))) -> (next(v_t) = i))

                Incoming transitions to ba state s:

                - if s has no incoming transitions

                  (next(vs_s) = i) -> FALSE

                - if s has incoming transitions

                  - if s is not fair

                    - for i = 0 ... self->curr_k

                      (next(v_s) = i) -> (next(label(s))
                                          &
                                          (forall (r,s) . v_r <= i)
                                          &
                                          (exists (r,s) . v_r = i))

                  - if s is fair:

                    - if self->curr_k = 0 (= i):

                      (next(v_s) = i) -> (next(label(s))
                                          &
                                          (forall (r,s) . v_r <= i)
                                          &
                                          (exists (r,s) . v_r = i))

                    - if self->curr_k > 0:

                      - i = 0:

                        (next(v_s) = i) -> FALSE

                      - i = 1 ... self->curr_k - 1:

                        (next(v_s) = i) -> (next(label(s))
                                            &
                                            (forall (r,s) . v_r < i)
                                            &
                                            (exists (r,s) . v_r = i - 1))

                      - i = self->curr_k:

                        (next(v_s) = i) -> (next(label(s))
                                            &
                                            (forall (r,s) . v_r <= i)
                                            &
                                            (exists (r,s) . v_r >= i - 1))

                The statements are a mix of scalar and Boolean
                sexps. While the major parts directly constructed here
                or in subroutines are scalar, the cubes characterizing
                states in the B\"uchi automaton may be Boolean. ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_construct_monitor_var_decls,
            Game_SF07_StructCheckLTLGameSF07_construct_monitor_init_statements ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr
Game_SF07_StructCheckLTLGameSF07_construct_monitor_trans_statements
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  Game_SF07_gba_ptr ba;
  Slist_ptr states;
  Siter s_iter;
  node_ptr trans_statements;
  node_ptr res;

    const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  if (self->curr_player == PLAYER_1) {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player1_ba);
    nusmv_assert(Game_SF07_gba_is_simple(self->player1_ba));
  } else {
    GAME_SF07_GBA_CHECK_INSTANCE(self->player2_ba);
    nusmv_assert(Game_SF07_gba_is_simple(self->player2_ba));
  }

  if (self->curr_player == PLAYER_1) {
    ba = self->player1_ba;
  } else {
    ba = self->player2_ba;
  }
  states = Game_SF07_gba_get_states(ba);
  trans_statements = Nil;

  SLIST_FOREACH(states, s_iter) {
    Game_SF07_gba_state_ptr state;
    node_ptr state_var_name;
    node_ptr state_label;
    node_ptr next_of_state_label;
    Slist_ptr transitions;
    int i;

    state = GAME_SF07_GBA_STATE(Siter_element(s_iter));
    state_var_name =
      Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name(env,self, state);

    /* handle outgoing transitions */
    transitions = Game_SF07_gba_state_get_outgoing(state);
    for (i = 0; i <= self->curr_k; i++) {
      Siter t_iter;
      node_ptr i_lhs;
      node_ptr i_conjuncts;
      node_ptr i_trans;

      i_lhs = find_node(nodemgr,EQUAL,
                        state_var_name,
                        find_node_number(nodemgr, i));

      i_conjuncts = find_node(nodemgr,TRUEEXP, Nil, Nil);
      SLIST_FOREACH(transitions, t_iter) {
        Game_SF07_gba_transition_ptr transition;
        Game_SF07_gba_state_ptr target_state;
        node_ptr target_state_var_name;
        node_ptr next_of_target_state_var_name;
        node_ptr target_state_label;
        node_ptr next_of_target_state_label;
        short int rhs_type;
        node_ptr rhs;

        transition = GAME_SF07_GBA_TRANSITION(Siter_element(t_iter));
        target_state = Game_SF07_gba_transition_get_target(transition);
        target_state_var_name =
          Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name(env,self,
                                                                 target_state);
        next_of_target_state_var_name = find_node(nodemgr,NEXT,
                                                  target_state_var_name,
                                                  Nil);
        target_state_label = Game_SF07_gba_state_get_label(target_state);
        next_of_target_state_label = find_node(nodemgr,NEXT,
                                               target_state_label,
                                               Nil);

        if (i < self->curr_k) {
          if (!Game_SF07_gba_is_state_in_first_fairness_constraint(ba,
                                                                target_state)) {
            rhs_type = GE;
          } else {
            rhs_type = GT;
          }
        } else {
          rhs_type = EQUAL;
        }
        rhs = find_node(nodemgr,rhs_type,
                        next_of_target_state_var_name,
                        find_node_number(nodemgr, i));
        i_conjuncts = find_node(nodemgr,AND,
                                i_conjuncts,
                                find_node(nodemgr,IMPLIES,
                                          next_of_target_state_label,
                                          rhs));
      }

      i_trans = new_node(nodemgr,TRANS,
                         find_node(nodemgr,IMPLIES,
                                   i_lhs,
                                   i_conjuncts),
                         Nil);

      trans_statements = new_node(nodemgr,CONS, i_trans, trans_statements);
    }

    /* handle incoming transitions */
    state_label = Game_SF07_gba_state_get_label(state);
    next_of_state_label = find_node(nodemgr,NEXT, state_label, Nil);
    transitions = Game_SF07_gba_state_get_incoming(state);
    for (i = 0; i <= self->curr_k; i++) {
      Siter t_iter;
      node_ptr i_lhs;
      node_ptr i_rhs;
      node_ptr i_trans;

      i_lhs = find_node(nodemgr,EQUAL,
                        find_node(nodemgr,NEXT,
                                  state_var_name,
                                  Nil),
                        find_node_number(nodemgr, i));

      if ((!Slist_is_empty(transitions)) &&
          ((!Game_SF07_gba_is_state_in_first_fairness_constraint(ba, state)) ||
           (self->curr_k == 0) ||
           (i > 0))) {
        node_ptr i_conjuncts;
        node_ptr i_disjuncts;

        i_conjuncts = find_node(nodemgr,TRUEEXP, Nil, Nil);
        i_disjuncts = find_node(nodemgr,FALSEEXP, Nil, Nil);
        SLIST_FOREACH(transitions, t_iter) {
          Game_SF07_gba_transition_ptr transition;
          Game_SF07_gba_state_ptr source_state;
          node_ptr source_state_var_name;
          short int i_conj_type;
          short int i_disj_type;
          unsigned int i_disj_value;
          node_ptr i_conjunct;
          node_ptr i_disjunct;

          transition = GAME_SF07_GBA_TRANSITION(Siter_element(t_iter));
          source_state = Game_SF07_gba_transition_get_source(transition);
          source_state_var_name =
            Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name(env,self,
                                                                source_state);

          if (!Game_SF07_gba_is_state_in_first_fairness_constraint(ba,
                                                                   state)) {
            i_conj_type = LE;
            i_disj_type = EQUAL;
            i_disj_value = i;
          } else if (self->curr_k == 0) {
            i_conj_type = LE;
            i_disj_type = EQUAL;
            i_disj_value = i;
          } else if ((0 < i) && (i < self->curr_k)) {
            i_conj_type = LT;
            i_disj_type = EQUAL;
            i_disj_value = i - 1;
          } else {
            nusmv_assert(i == self->curr_k);
            i_conj_type = LE;
            i_disj_type = GE;
            i_disj_value = i - 1;
          }

          i_conjunct = find_node(nodemgr,i_conj_type,
                                 source_state_var_name,
                                 find_node_number(nodemgr, i));
          i_conjuncts = find_node(nodemgr,AND,
                                  i_conjuncts,
                                  i_conjunct);

          i_disjunct = find_node(nodemgr,i_disj_type,
                                 source_state_var_name,
                                 find_node_number(nodemgr, i_disj_value));
          i_disjuncts = find_node(nodemgr,OR,
                                  i_disjuncts,
                                  i_disjunct);

          i_rhs = find_node(nodemgr,AND,
                            next_of_state_label,
                            find_node(nodemgr,AND,
                                      i_conjuncts,
                                      i_disjuncts));
        }
      } else {
        i_rhs = find_node(nodemgr,FALSEEXP, Nil, Nil);
      }

      i_trans = new_node(nodemgr,TRANS,
                         find_node(nodemgr,IMPLIES,
                                   i_lhs,
                                   i_rhs),
                         Nil);

      trans_statements = new_node(nodemgr,CONS, i_trans, trans_statements);
    }
  }

  res = reverse(trans_statements);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Constructs the game BDD FSM for the monitor in the
                current iteration. ]

  Description [ The game BDD FSM is constructed by separately
                constructing the flat hierarchies, sexp FSMs and BDD
                FSMs for both players and then invoking the
                constructor on the two resulting BDD FSMs.

                The sexps for the monitors of the current iteration
                should be considered not usable after invocation of
                this function.

                The code is following the example of nusmv/ltl/ltl.c. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_construct_monitor_game_bdd_fsm
(NuSMVEnv_ptr env, Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  FlatHierarchy_ptr player1_monitor_flat_hierarchy;
  FlatHierarchy_ptr player2_monitor_flat_hierarchy;
  GameBddFsm_ptr prop_game_bdd_fsm;
  GameSexpFsm_ptr prop_game_sexp_fsm;
  SexpFsm_ptr player1_monitor_sexp_fsm;
  SexpFsm_ptr player2_monitor_sexp_fsm;
  bdd_ptr player1_monitor_cur_vars_cube;
  bdd_ptr player1_monitor_next_vars_cube;
  bdd_ptr player1_monitor_cur_froz_vars_cube;
  bdd_ptr player2_monitor_cur_vars_cube;
  bdd_ptr player2_monitor_next_vars_cube;
  bdd_ptr player2_monitor_cur_froz_vars_cube;
  TransType trans_type;
  bdd_ptr one;
  Set_t vars;
  BddFsm_ptr player1_monitor_bdd_fsm;
  BddFsm_ptr player2_monitor_bdd_fsm;

  FsmBuilder_ptr builder = FSM_BUILDER(NuSMVEnv_get_value(env, ENV_FSM_BUILDER));

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  nusmv_assert(self->curr_player2_monitor_sexp != Nil);
  nusmv_assert(self->curr_player1_monitor_sexp != Nil);
  nusmv_assert(self->curr_monitor_game_bdd_fsm == GAME_BDD_FSM(NULL));

  /* Construct hierarchies. */
  CompileFlatten_hash_module(env,self->curr_player2_monitor_sexp);
  player2_monitor_flat_hierarchy =
    Compile_FlattenHierarchy(env,
                             self->symb_table,
                             self->curr_player2_monitor_layer,
                             car(car(self->curr_player2_monitor_sexp)),
                             Nil,
                             Nil,
                             false,
                             true,
                             false,
                             HRC_NODE(NULL));
  CompileFlatten_hash_module(env,self->curr_player1_monitor_sexp);
  player1_monitor_flat_hierarchy =
    Compile_FlattenHierarchy(env,
                             self->symb_table,
                             self->curr_player1_monitor_layer,
                             car(car(self->curr_player1_monitor_sexp)),
                             Nil,
                             Nil,
                             false,
                             true,
                             false,
                             HRC_NODE(NULL));

  /* Commit layers. */
  BaseEnc_commit_layer(BASE_ENC(self->bool_enc),
                       SymbLayer_get_name(self->curr_player2_monitor_layer));
  BaseEnc_commit_layer(BASE_ENC(self->bdd_enc),
                       SymbLayer_get_name(self->curr_player2_monitor_layer));
  BaseEnc_commit_layer(BASE_ENC(self->bool_enc),
                       SymbLayer_get_name(self->curr_player1_monitor_layer));
  BaseEnc_commit_layer(BASE_ENC(self->bdd_enc),
                       SymbLayer_get_name(self->curr_player1_monitor_layer));

  /* Retrieve self->prop's fsms. */
  prop_game_bdd_fsm = PropGame_get_game_bdd_fsm(self->prop);
  if (prop_game_bdd_fsm == GAME_BDD_FSM(NULL)) {
    Prop_set_environment_fsms(env, PROP(self->prop));
    prop_game_bdd_fsm = PropGame_get_game_bdd_fsm(self->prop);
  }
  GAME_BDD_FSM_CHECK_INSTANCE(prop_game_bdd_fsm);
  prop_game_sexp_fsm = PropGame_get_game_scalar_sexp_fsm(self->prop);
  GAME_SEXP_FSM_CHECK_INSTANCE(prop_game_sexp_fsm);

  /* Some more preparations. */
  {
    BddTrans_ptr trans;
    SymbTableIter titer;

    trans = GameBddFsm_get_trans_1(prop_game_bdd_fsm);
    trans_type = GenericTrans_get_type(GENERIC_TRANS(trans));
    one = bdd_true(self->dd_manager);
    //vars = Set_Make(NodeList_to_node_ptr(SymbTable_get_vars(self->symb_table)));
     SymbTable_gen_iter(self->symb_table,&titer,STT_VAR);
     vars = SymbTable_iter_to_set(self->symb_table, titer);
  }

  /* Add player 2 model variables to player2_monitor_flat_hierarchy. */
  {
    SexpFsm_ptr player2_model_sexp_fsm;
    FlatHierarchy_ptr player2_model_flat_hierarchy;
    Set_t player2_model_vars;
    Set_Iterator_t iter;

    player2_model_sexp_fsm =
      GameSexpFsm_get_player_2(prop_game_sexp_fsm);
    player2_model_flat_hierarchy =
      SexpFsm_get_hierarchy(player2_model_sexp_fsm);
    player2_model_vars =
      FlatHierarchy_get_vars(player2_model_flat_hierarchy);
    SET_FOREACH(player2_model_vars, iter) {
      FlatHierarchy_add_var(player2_monitor_flat_hierarchy,
                            Set_GetMember(player2_model_vars, iter));
    }
  }

  /* Construct (non-game) SexpFsm for player 2 monitor. */
  player2_monitor_sexp_fsm =
    SexpFsm_create(player2_monitor_flat_hierarchy, vars);

  /* Construct (non-game) BddFsm for player 2 monitor. */
  {
    SymbLayer_ptr player2_model_layer;
    bdd_ptr player2_model_tmp;
    bdd_ptr player2_monitor_tmp;

    /* Get layer. */
    player2_model_layer =
      SymbTable_get_layer(self->symb_table, MODEL_LAYER_2);

    /* Get current state vars cube. */
    player2_model_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           player2_model_layer,
                                           VFT_CURRENT);
    player2_monitor_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           self->curr_player2_monitor_layer,
                                           VFT_CURRENT);
    player2_monitor_cur_vars_cube = bdd_cube_union(self->dd_manager,
                                                   player2_model_tmp,
                                                   player2_monitor_tmp);
    bdd_free(self->dd_manager, player2_model_tmp);
    bdd_free(self->dd_manager, player2_monitor_tmp);

    /* Get next state vars cube. */
    player2_monitor_next_vars_cube =
      BddEnc_state_var_to_next_state_var(self->bdd_enc,
                                         player2_monitor_cur_vars_cube);

    /* Get current state and frozen vars cube. */
    player2_model_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           player2_model_layer,
                                           VFT_CURR_FROZEN);
    player2_monitor_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           self->curr_player2_monitor_layer,
                                           VFT_CURR_FROZEN);
    player2_monitor_cur_froz_vars_cube = bdd_cube_union(self->dd_manager,
                                                        player2_model_tmp,
                                                        player2_monitor_tmp);
    bdd_free(self->dd_manager, player2_model_tmp);
    bdd_free(self->dd_manager, player2_monitor_tmp);

    /* Construct fsm. */
    player2_monitor_bdd_fsm =
      FsmBuilder_create_bdd_fsm_of_vars(builder,
                                        player2_monitor_sexp_fsm,
                                        trans_type,
                                        self->bdd_enc,
                                        player2_monitor_cur_vars_cube,
                                        one,
                                        player2_monitor_next_vars_cube);
  }

  /* Add player 1 model variables to player1_monitor_flat_hierarchy. */
  {
    SexpFsm_ptr player1_model_sexp_fsm;
    FlatHierarchy_ptr player1_model_flat_hierarchy;
    Set_t player1_model_vars;
    Set_Iterator_t iter;

    player1_model_sexp_fsm =
      GameSexpFsm_get_player_1(prop_game_sexp_fsm);
    player1_model_flat_hierarchy =
      SexpFsm_get_hierarchy(player1_model_sexp_fsm);
    player1_model_vars =
      FlatHierarchy_get_vars(player1_model_flat_hierarchy);
    SET_FOREACH(player1_model_vars, iter) {
      FlatHierarchy_add_var(player1_monitor_flat_hierarchy,
                            Set_GetMember(player1_model_vars, iter));
    }
  }

  /* Construct (non-game) SexpFsm for player 1. */
  player1_monitor_sexp_fsm =
    SexpFsm_create(player1_monitor_flat_hierarchy, vars);

  /* Construct (non-game) BddFsm for player 1 monitor. */
  {
    SymbLayer_ptr player1_model_layer;
    bdd_ptr player1_model_tmp;
    bdd_ptr player1_monitor_tmp;

    /* Get layer. */
    player1_model_layer =
      SymbTable_get_layer(self->symb_table, MODEL_LAYER_1);

    /* Get current state vars cube. */
    player1_model_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           player1_model_layer,
                                           VFT_CURRENT);
    player1_monitor_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           self->curr_player1_monitor_layer,
                                           VFT_CURRENT);
    player1_monitor_cur_vars_cube = bdd_cube_union(self->dd_manager,
                                                   player1_model_tmp,
                                                   player1_monitor_tmp);
    bdd_free(self->dd_manager, player1_model_tmp);
    bdd_free(self->dd_manager, player1_monitor_tmp);

    /* Get next state vars cube. */
    player1_monitor_next_vars_cube =
      BddEnc_state_var_to_next_state_var(self->bdd_enc,
                                         player1_monitor_cur_vars_cube);

    /* Get current state and frozen vars cube. */
    player1_model_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           player1_model_layer,
                                           VFT_CURR_FROZEN);
    player1_monitor_tmp =
      (bdd_ptr) BddEnc_get_layer_vars_cube(self->bdd_enc,
                                           self->curr_player1_monitor_layer,
                                           VFT_CURR_FROZEN);
    player1_monitor_cur_froz_vars_cube = bdd_cube_union(self->dd_manager,
                                                        player1_model_tmp,
                                                        player1_monitor_tmp);
    bdd_free(self->dd_manager, player1_model_tmp);
    bdd_free(self->dd_manager, player1_monitor_tmp);

    /* Construct fsm. */
    player1_monitor_bdd_fsm =
      FsmBuilder_create_bdd_fsm_of_vars(builder,
                                        player1_monitor_sexp_fsm,
                                        trans_type,
                                        self->bdd_enc,
                                        player1_monitor_cur_vars_cube,
                                        one,
                                        player1_monitor_next_vars_cube);
  }

  /* Construct GameBddFsm for monitor. */
  self->curr_monitor_game_bdd_fsm =
    GameBddFsm_create(self->bdd_enc,
                      player1_monitor_bdd_fsm,
                      player1_monitor_cur_vars_cube,
                      player1_monitor_cur_froz_vars_cube,
                      player2_monitor_bdd_fsm,
                      player2_monitor_cur_vars_cube,
                      player2_monitor_cur_froz_vars_cube);

  /* Clean up. */
  bdd_free(self->dd_manager, player1_monitor_cur_vars_cube);
  bdd_free(self->dd_manager, player1_monitor_next_vars_cube);
  bdd_free(self->dd_manager, player1_monitor_cur_froz_vars_cube);
  bdd_free(self->dd_manager, player2_monitor_cur_vars_cube);
  bdd_free(self->dd_manager, player2_monitor_next_vars_cube);
  bdd_free(self->dd_manager, player2_monitor_cur_froz_vars_cube);
  SexpFsm_destroy(player1_monitor_sexp_fsm);
  SexpFsm_destroy(player2_monitor_sexp_fsm);
  bdd_free(self->dd_manager, one);
  Set_ReleaseSet(vars);
  FlatHierarchy_destroy(player1_monitor_flat_hierarchy);
  FlatHierarchy_destroy(player2_monitor_flat_hierarchy);
}

/**Function********************************************************************

  Synopsis    [ Constructs the synchronous product of the game BDD FSM of
                the original game and the game BDD FSM of the monitor
                of the current iteration. ]

  Description [ The game BDD FSM of the original game is copied and
                then "multiplied" with the game BDD FSM of the
                monitor.

                The code is following the example of nusmv/ltl/ltl.c. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_construct_product_game_bdd_fsm
(Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  GameBddFsm_ptr prop_game_bdd_fsm;

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  GAME_BDD_FSM_CHECK_INSTANCE(self->curr_monitor_game_bdd_fsm);
  nusmv_assert(self->curr_product_game_bdd_fsm == GAME_BDD_FSM(NULL));

  /* prop_game_bdd_fsm should be non-NULL b/c of previous call to
     construct monitor GameBddFsm. */
  prop_game_bdd_fsm = PropGame_get_game_bdd_fsm(self->prop);
  GAME_BDD_FSM_CHECK_INSTANCE(prop_game_bdd_fsm);

  self->curr_product_game_bdd_fsm = GameBddFsm_copy(prop_game_bdd_fsm);

  GameBddFsm_apply_synchronous_product(self->curr_product_game_bdd_fsm,
                                       self->curr_monitor_game_bdd_fsm);
}

/**Function********************************************************************

  Synopsis    [ Checks whether the subgame of the current iteration is
                realizable for the current player. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_check
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  boolean construct_strategy;
  node_ptr expr;
  PropGame_ptr prop;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  FILE* errstream = StreamMgr_get_error_stream(streams);
  OStream_ptr errostream = StreamMgr_get_error_ostream(streams);

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  GAME_BDD_FSM_CHECK_INSTANCE(self->curr_product_game_bdd_fsm);
  nusmv_assert(self->curr_goal_realizability == GAME_UNKNOWN);
  nusmv_assert(node_get_type(self->curr_goal) == AVOIDTARGET);

  /* Should a strategy be constructed? */
  construct_strategy = (((self->params != (gameParams_ptr) NULL) &&
                         (self->params)->strategy_printout) ||
                        opt_game_print_strategy(opts));

  /* Construct property. */
  expr = find_node(nodemgr,GAME_SPEC_WRAPPER,
                   sym_intern(env,PTR_TO_INT(car(self->curr_goal)) == 1 ?
                              PLAYER_NAME_1 :
                              PLAYER_NAME_2),
                   cdr(self->curr_goal));
  prop = PropGame_create_partial(env,expr, PropGame_AvoidTarget);
  PropGame_set_game_bdd_fsm(prop, self->curr_product_game_bdd_fsm);

  /* Log property. */
  if (opt_verbose_level_ge(opts, 4)) {
    fprintf(errstream,
            "\nGame_SF07_StructCheckLTLGameSF07_check: sub game goal is:\n");
    Prop_print(PROP(prop), errostream, PROP_PRINT_FMT_FORMULA);
    fprintf(errstream,
            "\nGame_SF07_StructCheckLTLGameSF07_check: end sub game goal\n");
  }

  /* Check */
  self->curr_goal_realizability =
    Game_UseStrongReachabilityAlgorithm(prop,
                                        (construct_strategy ?
                                         (&self->strategy) :
                                         (GameStrategy_ptr*) NULL));

  /* Clean up. */
  PropGame_destroy(prop);
}

/**Function********************************************************************

  Synopsis    [ Given a state of the B\"uchi automaton for the current
                player returns a variable name for that state. ]

  Description [ The variable names is constructed as follows:

                  The string GAME_SF07_MONITOR_STATE_BASE_NAME
                + "_"
                + a unique number for the current iteration
                + "_"
                + the state id of the state in the B\"uchi automaton.

                Hence, the names are supposed to be unique not just
                for this execution of the sf07 algorithm but across
                executions. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_MONITOR_STATE_BASE_NAME "ltlgame"
static node_ptr Game_SF07_StructCheckLTLGameSF07_gba_state_to_var_name
(NuSMVEnv_ptr env,Game_SF07_StructCheckLTLGameSF07_ptr self, Game_SF07_gba_state_ptr state)
{
  char* res_s;
  char* state_id_s;
  node_ptr res;

  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  const UStringMgr_ptr strings = USTRING_MGR(NuSMVEnv_get_value(env, ENV_STRING_MGR));

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  nusmv_assert(self->curr_unique_number < 1000000000);

  state_id_s = (char*)UStringMgr_get_string_text(Game_SF07_gba_state_get_id(state));
  /* 10 digits + 2 underscores + 1 '\0' */
  res_s = ALLOC(char,
                (strlen(GAME_SF07_MONITOR_STATE_BASE_NAME) +
                 strlen(state_id_s) +
                 13));
  sprintf(res_s,
          "%s_%d_%s",
          GAME_SF07_MONITOR_STATE_BASE_NAME,
          self->curr_unique_number,
          state_id_s);

  res = find_node(nodemgr,ATOM,
                  (node_ptr) UStringMgr_find_string(strings,res_s),
                  Nil);

  FREE(res_s);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Given an integer n returns NUMBER n for n >= 0 and UMINUS
                NUMBER -n otherwise. ]

  Description [ Results is find_noded. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static node_ptr find_node_number(NodeMgr_ptr nodemgr, int n)
{
  if (n < 0) {
    return find_node(nodemgr,UMINUS, find_node(nodemgr,NUMBER, NODE_FROM_INT(-n), Nil), Nil);
  } else {
    return find_node(nodemgr,NUMBER, NODE_FROM_INT(n), Nil);
  }

  nusmv_assert(false);
  return Nil;
}

/**Function********************************************************************

  Synopsis    [ Prints a module given as an sexp. ]

  Description [ body_only is a flag to disable printing of the MODULE
                and VAR parts. That enables re-(ab-?)use of this
                routine in the strategy printing.

                This is not a general-purpose routine but tailored to
                what is expected in monitors and strategies in this
                file.

                Adapted from ltl/ltl2smv/ltl2smv.c::ltl2smv_print_module. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_print_monitor
(MasterPrinter_ptr wffprint,FILE* ostream, node_ptr module, boolean body_only)
{
  node_ptr iter;

  if (!body_only) {
    nusmv_assert(Nil != module);
    nusmv_assert(MODULE == node_get_type(module));
    nusmv_assert(MODTYPE == node_get_type(car(module)));
    nusmv_assert(ATOM == node_get_type(car(car(module))));
    nusmv_assert(Nil == cdr(car(module)));
    fprintf(ostream,
            "MODULE %s\n",
            (char*)UStringMgr_get_string_text((string_ptr)car(car(car(module)))));
    iter = cdr(module);
  } else {
    iter = module;
  }

  while (Nil != iter) {
    nusmv_assert(CONS == node_get_type(iter));
    switch (node_get_type(car(iter))) {

    case VAR: { /* variable declarations */
      if (!body_only) {
        node_ptr var;
        var = car(car(iter));
        if ( Nil != var) {
          fprintf(ostream, "VAR\n");
          while (Nil != var) { /* iterate over variable declarations */

            nusmv_assert(CONS == node_get_type(var));
            nusmv_assert(COLON == node_get_type(car(var)));
            nusmv_assert(ATOM == node_get_type(car(car(var))));
            nusmv_assert(TWODOTS == node_get_type(cdr(car(var))));

            fprintf(ostream,
                    "  %s : ",
                    (char*)UStringMgr_get_string_text((string_ptr)car(car(car(var)))));
            print_node(wffprint,ostream, car(cdr(car(var))));
            fprintf(ostream, "..");
            print_node(wffprint,ostream, cdr(cdr(car(var))));
            fprintf(ostream, ";\n");

            var = cdr(var);
          }
        }
      }
      break;
    }

    case INIT: /* INIT declarations */
      fprintf(ostream, "INIT\n  ");
      print_node(wffprint,ostream, car(car(iter)));
      fprintf(ostream, "\n");
      break;

    case TRANS: /* TRANS declarations */
      fprintf(ostream, "TRANS\n  ");
      print_node(wffprint,ostream, car(car(iter)));
      fprintf(ostream, "\n");
      break;

    default: nusmv_assert(false); /* unexpected node */
    } /*switch */

    iter = cdr(iter);
  } /* while */

  return;
}

/**Function********************************************************************

  Synopsis    [ Prints a strategy for the winner of the original game by
                printing the strategy in the current subgame and
                printing the current monitor as given by its sexp. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_bdd ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_sexp
(Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  array_t* layers = array_alloc(char*, 2);
  array_t* layers_to_decl = array_alloc(char*, 2);
  NodeList_ptr vars;
  NodeList_ptr vars_to_decl;
  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  const StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  FILE* outstream = StreamMgr_get_output_stream(streams);

  GAME_STRATEGY_CHECK_INSTANCE(self->strategy);
  {
    Game_SF07_StrategyPrintingMode m;
    m = get_game_sf07_strategy_printing_mode(opts);
    nusmv_assert(m == GAME_SF07_STRATEGY_PRINTING_MODE_SEXP);
  }

  /* Extract variables from game layers. */
  array_insert_last(char*, layers, MODEL_LAYER_1);
  array_insert_last(char*, layers, MODEL_LAYER_2);
  /* There shouldnt be any variables in the determinization layers. */
  {
    SymbLayer_ptr dl1 = SymbTable_get_layer(self->symb_table, DETERM_LAYER_1);
    SymbLayer_ptr dl2 = SymbTable_get_layer(self->symb_table, DETERM_LAYER_2);

    /**NEW_CODE_START**/
    SymbLayerIter iter1;
    NodeList_ptr syms1;
    SymbLayer_gen_iter(dl1, &iter1, STT_ALL);
    syms1 = SymbLayer_iter_to_list(dl1, iter1);

    SymbLayerIter iter2;
    NodeList_ptr syms2;
    SymbLayer_gen_iter(dl2, &iter2, STT_ALL);
    syms2 = SymbLayer_iter_to_list(dl2, iter2);

      nusmv_assert((dl1 != SYMB_LAYER(NULL)) &&
                   (NodeList_get_length(syms1) == 0));
      nusmv_assert((dl2 != SYMB_LAYER(NULL)) &&
                   (NodeList_get_length(syms2) == 0));
    /**NEW_CODE_END**/
    /**OLD_CODE_START
    nusmv_assert((dl1 != SYMB_LAYER(NULL)) &&
                 (NodeList_get_length(SymbLayer_get_all_symbols(dl1)) == 0));
    nusmv_assert((dl2 != SYMB_LAYER(NULL)) &&
                 (NodeList_get_length(SymbLayer_get_all_symbols(dl2)) == 0));
    OLD_CODE_END**/
  }
  array_insert_last(char*,
                    layers_to_decl,
                  (char*) SymbLayer_get_name(self->curr_player1_monitor_layer));
  array_insert_last(char*,
                    layers_to_decl,
                  (char*) SymbLayer_get_name(self->curr_player2_monitor_layer));
  /* There is no determinization layer for the monitors. */
  vars = SymbTable_get_layers_sf_i_vars(self->symb_table, layers);
  vars_to_decl = SymbTable_get_layers_sf_i_vars(self->symb_table,
                                                layers_to_decl);
  NodeList_concat(vars, vars_to_decl);

  /* Actually print. */
  {
    FILE* out;
    node_ptr monitor_body;


    GameStrategy_print_module(self->strategy,
                              vars,
                              vars_to_decl,
                              self->params);
    out = (((self->params != (gameParams_ptr) NULL) &&
            (self->params)->strategy_stream != (FILE *) NULL)
           ? (self->params)->strategy_stream
           : outstream);
    monitor_body =
      cdr(self->curr_player2_monitor_sexp_copy);
    Game_SF07_StructCheckLTLGameSF07_print_monitor(wffprint, out,  monitor_body, true);
  }

  /* Clean up. */
  NodeList_destroy(vars);
  NodeList_destroy(vars_to_decl);
  array_free(layers);
  array_free(layers_to_decl);
}

/**Function********************************************************************

  Synopsis    [ Prints a strategy for the winner of the original game by

                - either printing the strategy in the current subgame
                  and separately printing the current monitor as given
                  by its BDD FSM,

                - or conjoining the BDDs for the strategy in the
                  current subgame and of the current monitor given by
                  its BDD FSM and printing the resulting BDDs.

                Which variant applies is determined by the option
                game_sf07_strategy_printing_mode. ]

  Description [ This is a custom adaptation of
                gameGeneral::print_strategy_module. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_sexp ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_print_strategy_monitor_bdd
(Game_SF07_StructCheckLTLGameSF07_ptr self)
{
  static int module_incr_number = 0; /* an internal static
                                        autoincrement variable */
  FILE* out;
  boolean do_sharing;
  boolean do_indentation;
  array_t* layers;
  array_t* layers_to_decl;
  NodeList_ptr vars;
  NodeList_ptr vars_to_decl;
  NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self->symb_table));

  MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  FILE* outstream = StreamMgr_get_output_stream(streams);

  GAME_SF07_STRUCT_CHECK_LTL_GAME_SF07_CHECK_INSTANCE(self);
  GAME_STRATEGY_CHECK_INSTANCE(self->strategy);
  {
    Game_SF07_StrategyPrintingMode m;
    m = get_game_sf07_strategy_printing_mode(opts);
    nusmv_assert((m == GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE) ||
                 (m == GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED));
  }



  module_incr_number++;
  out = ((self->params != (gameParams_ptr) NULL) &&
         (self->params)->strategy_stream != (FILE *) NULL)
    ? (self->params)->strategy_stream
    : outstream;
  do_sharing = (self->params != (gameParams_ptr) NULL) &&
    self->params->printout_as_dag;
  do_indentation = (self->params != (gameParams_ptr) NULL) &&
    self->params->indented_printout;
  layers = array_alloc(char*, 2);
  layers_to_decl = array_alloc(char*, 2);

  /* Extract variables from game layers. */
  array_insert_last(char*, layers, MODEL_LAYER_1);
  array_insert_last(char*, layers, MODEL_LAYER_2);
  /* There shouldnt be any variables in the determinization layers. */
  {
    SymbLayer_ptr dl1 = SymbTable_get_layer(self->symb_table, DETERM_LAYER_1);
    SymbLayer_ptr dl2 = SymbTable_get_layer(self->symb_table, DETERM_LAYER_2);
     /**NEW_CODE_START**/
     SymbLayerIter iter1;
     NodeList_ptr syms1;
     SymbLayer_gen_iter(dl1, &iter1, STT_ALL);
     syms1 = SymbLayer_iter_to_list(dl1, iter1);

     SymbLayerIter iter2;
     NodeList_ptr syms2;
     SymbLayer_gen_iter(dl2, &iter2, STT_ALL);
     syms2 = SymbLayer_iter_to_list(dl2, iter2);

     nusmv_assert((dl1 != SYMB_LAYER(NULL)) &&
                  (NodeList_get_length(syms1) == 0));
     nusmv_assert((dl2 != SYMB_LAYER(NULL)) &&
                  (NodeList_get_length(syms2) == 0));
     /**NEW_CODE_END**/
    /**OLD_CODE_START
    nusmv_assert((dl1 != SYMB_LAYER(NULL)) &&
                 (NodeList_get_length(SymbLayer_get_all_symbols(dl1)) == 0));
    nusmv_assert((dl2 != SYMB_LAYER(NULL)) &&
                 (NodeList_get_length(SymbLayer_get_all_symbols(dl2)) == 0));
    OLD_CODE_END**/
  }
  array_insert_last(char*,
                    layers_to_decl,
                  (char*) SymbLayer_get_name(self->curr_player1_monitor_layer));
  array_insert_last(char*,
                    layers_to_decl,
                  (char*) SymbLayer_get_name(self->curr_player2_monitor_layer));
  /* There is no determinization layer for the monitors. */
  vars = SymbTable_get_layers_sf_i_vars(self->symb_table, layers);
  vars_to_decl = SymbTable_get_layers_sf_i_vars(self->symb_table,
                                                layers_to_decl);
  NodeList_concat(vars, vars_to_decl);

  /* Actually print. */
  {
    bdd_ptr init_bdd;
    bdd_ptr trans_bdd;
    bdd_ptr player2_monitor_init_bdd;
    bdd_ptr player2_monitor_trans_bdd;

    player2_monitor_init_bdd =
      GameBddFsm_get_init_2(self->curr_monitor_game_bdd_fsm);
    player2_monitor_trans_bdd =
      GameBddFsm_get_monolitic_trans_2(self->curr_monitor_game_bdd_fsm);

    fprintf(out, "MODULE STRATEGY_MODULE%d\n\n", module_incr_number);

    /* declare variables */
    if (NodeList_get_length(vars_to_decl) != 0) {
      ListIter_ptr iter;

      fprintf(out, "VAR\n");
      NODE_LIST_FOREACH(vars_to_decl, iter) {
        node_ptr var_name;
        SymbType_ptr var_type;

        var_name = NodeList_get_elem_at(vars_to_decl, iter);
        var_type = SymbTable_get_var_type(self->symb_table, var_name);
        fprintf(out, "  ");
        print_node(wffprint,out, var_name);
        fprintf(out, ": ");
        SymbType_print(var_type,wffprint, out);
        fprintf(out, ";\n");
      }
      fprintf(out, "\n");
    }

    /* Build the BDDs for the INIT section */
    {
      bdd_ptr tmp;

      init_bdd = GameStrategy_get_init_goal(self->strategy);

      tmp = GameStrategy_get_init_opponent_deadlock(self->strategy);
      bdd_or_accumulate(self->dd_manager, &init_bdd, tmp);
      bdd_free(self->dd_manager, tmp);

      tmp = GameStrategy_get_init_moves(self->strategy);
      bdd_or_accumulate(self->dd_manager, &init_bdd, tmp);
      bdd_free(self->dd_manager, tmp);

      if (get_game_sf07_strategy_printing_mode(opts) ==
          GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED) {
        bdd_and_accumulate(self->dd_manager,
                           &init_bdd,
                           player2_monitor_init_bdd);
      }
    }

    /* print'em out */
    {
      const char* init_str = "INIT ";
      fprintf(out, "%s", init_str);
      BddEnc_print_bdd_wff(self->bdd_enc,
                           init_bdd,
                           vars,
                           do_sharing,
                           do_indentation,
                           strlen(init_str),
                           OSTREAM(out));
      if (get_game_sf07_strategy_printing_mode(opts) ==
          GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE) {
        fprintf(out, "%s", init_str);
        BddEnc_print_bdd_wff(self->bdd_enc,
                             player2_monitor_init_bdd,
                             vars,
                             do_sharing,
                             do_indentation,
                             strlen(init_str),
                             OSTREAM(out));
      }
      fprintf(out, "\n");
    }

    /* Build the BDDs for the TRANS section */
    {
      bdd_ptr tmp;

      trans_bdd = GameStrategy_get_goal(self->strategy);

      tmp = GameStrategy_get_opponent_deadlock(self->strategy);
      bdd_or_accumulate(self->dd_manager, &trans_bdd, tmp);
      bdd_free(self->dd_manager, tmp);

      tmp = GameStrategy_get_moves(self->strategy);
      bdd_or_accumulate(self->dd_manager, &trans_bdd, tmp);
      bdd_free(self->dd_manager, tmp);

      if (get_game_sf07_strategy_printing_mode(opts) ==
          GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED) {
        bdd_and_accumulate(self->dd_manager,
                           &trans_bdd,
                           player2_monitor_trans_bdd);
      }
    }

    /* print'em out */
    {
      const char* trans_str = "TRANS ";
      fprintf(out, "%s", trans_str);
      BddEnc_print_bdd_wff(self->bdd_enc,
                           trans_bdd,
                           vars,
                           do_sharing,
                           do_indentation,
                           strlen(trans_str),
                           OSTREAM(out));
      if (get_game_sf07_strategy_printing_mode(opts) ==
          GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE) {
        fprintf(out, "%s", trans_str);
        BddEnc_print_bdd_wff(self->bdd_enc,
                             player2_monitor_trans_bdd,
                             vars,
                             do_sharing,
                             do_indentation,
                             strlen(trans_str),
                             OSTREAM(out));
      }
      fprintf(out, "\n");
    }

    /* cleanup */
    bdd_free(self->dd_manager, init_bdd);
    bdd_free(self->dd_manager, trans_bdd);
    bdd_free(self->dd_manager, player2_monitor_init_bdd);
    bdd_free(self->dd_manager, player2_monitor_trans_bdd);
  }

  /* Clean up. */
  NodeList_destroy(vars);
  NodeList_destroy(vars_to_decl);
  array_free(layers);
  array_free(layers_to_decl);
}

/**Function********************************************************************

  Synopsis    [ Deep copy of a node_ptr. Restricted to few node types! ]

  Description [ Restricted to node types occurring in the monitor for
                player 2. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_free_node ]

******************************************************************************/
static node_ptr Game_SF07_StructCheckLTLGameSF07_copy_node(NodeMgr_ptr nodemgr, node_ptr node) {
  if (node == Nil) {
    return Nil;
  } else {
    short int type;
    node_ptr lhs;
    node_ptr rhs;
    int lineno;

    type = node_get_type(node);
    lhs = car(node);
    rhs = cdr(node);
    lineno = node_get_lineno(node);

    switch (type) {
      /* Treated somewhat special. */
    case ATOM:
    case NUMBER:
      nusmv_assert(rhs == Nil);
      return new_lined_node(nodemgr,type, lhs, rhs, lineno);
    case BIT:
      return new_lined_node(nodemgr,type,
                            Game_SF07_StructCheckLTLGameSF07_copy_node(nodemgr,lhs),
                            rhs,
                            lineno);
      /* Just copied. */
    case AND:
    case ARRAY:
    case COLON:
    case CONS:
    case DOT:
    case EQUAL:
    case FALSEEXP:
    case GE:
    case GT:
    case IFF:
    case IMPLIES:
    case INIT:
    case LE:
    case LT:
    case MODTYPE:
    case MODULE:
    case NEXT:
    case NOT:
    case OR:
    case TRANS:
    case TRUEEXP:
    case TWODOTS:
    case UMINUS:
    case VAR:
      return new_lined_node(nodemgr,type,
                            Game_SF07_StructCheckLTLGameSF07_copy_node(nodemgr,lhs),
                            Game_SF07_StructCheckLTLGameSF07_copy_node(nodemgr,rhs),
                            lineno);
      /* Catch errors. */
    default:
      nusmv_assert(false);
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Recursively frees a node_ptr. Restricted to few node types! ]

  Description [ Restricted to node types occurring in the monitor for
                player 2. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_StructCheckLTLGameSF07_copy_node ]

******************************************************************************/
static void Game_SF07_StructCheckLTLGameSF07_free_node(NodeMgr_ptr nodemgr,node_ptr node) {
  if (node != Nil) {
    short int type;
    node_ptr lhs;
    node_ptr rhs;

    type = node_get_type(node);
    lhs = car(node);
    rhs = cdr(node);

    switch (type) {
      /* Dont free lhs, check rhs == Nil. */
    case ATOM:
    case NUMBER:
      nusmv_assert(rhs == Nil);
      break;
      /* Free lhs. */
    case BIT:
      Game_SF07_StructCheckLTLGameSF07_free_node(nodemgr,lhs);
      break;
      /* Free lhs, rhs. */
    case AND:
    case ARRAY:
    case COLON:
    case CONS:
    case DOT:
    case EQUAL:
    case FALSEEXP:
    case GE:
    case GT:
    case IFF:
    case IMPLIES:
    case INIT:
    case LE:
    case LT:
    case MODTYPE:
    case MODULE:
    case NEXT:
    case NOT:
    case OR:
    case TRANS:
    case TRUEEXP:
    case TWODOTS:
    case UMINUS:
    case VAR:
      Game_SF07_StructCheckLTLGameSF07_free_node(nodemgr,lhs);
      Game_SF07_StructCheckLTLGameSF07_free_node(nodemgr,rhs);
      break;
      /* Catch errors. */
    default:
      nusmv_assert(false);
    }

    free_node(nodemgr,node);
  }
}
