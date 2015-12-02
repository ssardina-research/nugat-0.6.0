/**CHeaderFile*****************************************************************

  FileName    [ gameInt.h ]

  PackageName [ game ]

  Synopsis    [ Internal header file of the game package. ]

  Description [ Internal header file of the game package. ]

  SeeAlso     [ game.h ]

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

  Revision    [$Id: gameInt.h,v 1.1.2.9 2010-02-05 17:19:08 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_INT_H__
#define __GAME_INT_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "game.h"
#include "GameHierarchy.h"
#include "GamePlayer.h"
#include "GameStrategy.h"
#include "PropGame.h"
#include "fsm/GameBddFsm.h"
#include "fsm/GameSexpFsm.h"

#include "opt/opt.h"
#include "compile/compile.h"

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ These are the name of layers used in games (realizability
                problems). ]

  Description [ Note that these strings can not be met as identifiers
                in an input file because they are keywords. ]

******************************************************************************/
#define MODEL_LAYER_1 "layer_of_" PLAYER_NAME_1
#define MODEL_LAYER_2 "layer_of_" PLAYER_NAME_2
#define DETERM_LAYER_1 "determ_layer_of_" PLAYER_NAME_1
#define DETERM_LAYER_2 "determ_layer_of_" PLAYER_NAME_2

/**Macro************************************************************************

  Synopsis    [ The default algorithm
                gameCmd.c::CommandExtractUnrealizableCore. ]

  Description [ When changing this one, also change
                gameCmd.c::UsageExtractUnrealizableCore. ]

******************************************************************************/
#define DEFAULT_GAME_UNREALIZABLE_CORE_ALGORITHM \
  GAME_UNREALIZABLE_CORE_ALGORITHM_EXPLICIT

/**Macro************************************************************************

  Synopsis    [ The default value for N in
                gameCmd.c::CommandExtractUnrealizableCore. ]

  Description [ When changing this one, also change
                gameCmd.c::UsageExtractUnrealizableCore. ]

******************************************************************************/
#define DEFAULT_GAME_UNREALIZABLE_CORE_N 1

/**Macro************************************************************************

  Synopsis    [ The default values for kmin and kmax in
                gameCmd.c::CommandCheckLtlGameSpecSF07. ]

  Description [ - Ensure that 0 <= _KMIN <= _KMAX.
                - When changing this one, also change
                  gameCmd.c::UsageCheckLtlGameSpecSF07. ]

******************************************************************************/
#define DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_KMIN 0
#define DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_KMAX 20

/**Macro************************************************************************

  Synopsis    [ The default value for w in
                gameCmd.c::CommandCheckLtlGameSpecSF07. ]

  Description [ When changing this one, also change
                gameCmd.c::UsageCheckLtlGameSpecSF07. ]

******************************************************************************/
#define DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_W GAME_WHO_BOTH

/* Default GAME options values */
#define DEFAULT_GAME_SF07_GBA_WRING_BINARY \
  "lily.pl"
#define DEFAULT_GAME_SF07_GBA_WRING_HAS_CC true
#define DEFAULT_GAME_SF07_GBA_WRING_INPUT_DIR (char *) NULL
#define DEFAULT_GAME_SF07_GBA_WRING_INPUT_TEMPL "iXXXXXX"
#define DEFAULT_GAME_SF07_GBA_WRING_INPUT_KEEP false
#define DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_DIR (char *) NULL
#define DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_TEMPL "oXXXXXX"
#define DEFAULT_GAME_SF07_GBA_WRING_OUTPUT_KEEP false

/* Internal options */
#define GAME_OPT_INITIALIZED "__game_options_initialized__"

/**Macro***********************************************************************

  Synopsis    [ String values for Game_Who. ]

  Description [ See Game_Who. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_WHO_INVALID_STRING "i"
#define GAME_WHO_NONE_STRING "n"
#define GAME_WHO_BOTH_STRING "b"
#define GAME_WHO_PROTAGONIST_STRING "p"
#define GAME_WHO_ANTAGONIST_STRING "a"
#define GAME_WHO_PLAYER_1_STRING "1"
#define GAME_WHO_PLAYER_2_STRING "2"
#define GAME_WHO_WINNER_STRING "w"
#define GAME_WHO_LOSER_STRING "l"

/**Macro***********************************************************************

  Synopsis    [ String values for Game_UnrealizableCore_Algorithm. ]

  Description [ See Game_UnrealizableCore_Algorithm. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_UNREALIZABLE_CORE_ALGORITHM_INVALID_STRING "invalid"
#define GAME_UNREALIZABLE_CORE_ALGORITHM_ACTIVATION_VARIABLES_STRING "actvars"
#define GAME_UNREALIZABLE_CORE_ALGORITHM_EXPLICIT_STRING "explicit"

/**Macro***********************************************************************

  Synopsis    [ String values for Game_UnrealizableCore_CoreType. ]

  Description [ See Game_UnrealizableCore_CoreType. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_UNREALIZABLE_CORE_CORE_TYPE_INVALID_STRING "invalid"
#define GAME_UNREALIZABLE_CORE_CORE_TYPE_CORE_STRING "core"
#define GAME_UNREALIZABLE_CORE_CORE_TYPE_FIX_STRING "fix"

/**Macro***********************************************************************

  Synopsis    [ String values for Game_SF07_StrategyPrintingMode. ]

  Description [ See Game_SF07_StrategyPrintingMode. ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_STRATEGY_PRINTING_MODE_SEXP_STRING "sexp"
#define GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE_STRING "bdd_separate"
#define GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED_STRING "bdd_conjoined"

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Struct**********************************************************************

  Synopsis    [ Parameters for functions to check game properties,
                related to strategy printing. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
struct GameParams_TAG {
  boolean strategy_printout;
  boolean printout_as_dag;
  boolean indented_printout;
  FILE* strategy_stream;
};
typedef struct GameParams_TAG GameParams;

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ A list of possible status an realizability game can have. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
enum Game_RealizabilityStatus_TAG {
  GAME_REALIZABLE,
  GAME_UNREALIZABLE,
  GAME_UNKNOWN
};
typedef enum Game_RealizabilityStatus_TAG Game_RealizabilityStatus;

/**Type************************************************************************

  Synopsis    [ A list of possible ways to check earlier termination with
                help of initial conditions in realizability checking
                algorithms. ]

  Description [ GAME_INIT_TERM_NONE -- no earlier termination is
                  checked. A complete set of winning states is
                  computed in this case.

                GAME_INIT_TERM_NORMAL -- at the end of every iteration
                  if (overapproximation of) winning states cannot be
                  reached with given initial conditions then algorithm
                  terminates. In this case the game is unrealizable
                  and winning states remains to be overapproximation.

                GAME_INIT_TERM_CONJUNCT -- this mode is only
                  meaningful if (overapproximation of) winning states
                  contains variables outside of a given FSM (i.e. not
                  belonging to any player). Then at the end of every
                  iteration winning states are conjuncted with the
                  result of checking initial conditions (e.g. A p1.(I1
                  -> E p2.(I2 ^Win)), which can consist only of
                  external variables).  In this case winning state may
                  become underapproximation on the value of external
                  variables (but remains to be overapproximation on
                  the value of players' vars).  ]

  SeeAlso     [ ]

******************************************************************************/
enum Game_InitTermination_TAG {
  GAME_INIT_TERM_NONE,
  GAME_INIT_TERM_NORMAL,
  GAME_INIT_TERM_CONJUNCT
};
typedef enum Game_InitTermination_TAG Game_InitTermination;

/**Type************************************************************************

  Synopsis    [ Identifies player(s). ]

  Description [ Convenience data type to store the identification of
                player(s) in different ways. Values:

                GAME_WHO_INVALID: invalid.

                GAME_WHO_NONE: none.

                GAME_WHO_BOTH: both.

                GAME_WHO_PROTAGONIST: the protagonist.

                GAME_WHO_ANTAGONIST: the antagonist.

                GAME_WHO_PLAYER_1: player 1.

                GAME_WHO_PLAYER_2: player 2.

                GAME_WHO_WINNER: winner.

                GAME_WHO_LOSER: loser. ]

  SeeAlso     [ ]

******************************************************************************/
enum Game_Who_TAG {
  GAME_WHO_INVALID = -1,
  GAME_WHO_NONE = 0,
  GAME_WHO_BOTH,
  GAME_WHO_PROTAGONIST,
  GAME_WHO_ANTAGONIST,
  GAME_WHO_PLAYER_1,
  GAME_WHO_PLAYER_2,
  GAME_WHO_WINNER,
  GAME_WHO_LOSER,
};

/**Type************************************************************************

  Synopsis    [ Identifies an algorithm used to extract (un)realizable
                cores. ]

  Description [ Values:

                GAME_UNREALIZABLE_CORE_ALGORITHM_ACTIVATION_VARIABLES:
                  invalid.

                GAME_UNREALIZABLE_CORE_ALGORITHM_ACTIVATION_VARIABLES:
                  an activation variable is introduced for each part
                  of the game that is to be considered for
                  minimization. Then the parameterized realizability
                  problem is solved by a single call to the
                  realizability algorithm. The resulting set of
                  (parameterized) winning states is then used to
                  extract the core.

                GAME_UNREALIZABLE_CORE_ALGORITHM_EXPLICIT: the parts
                  of the game that are to be considered for
                  minimization are removed tentatively to see whether
                  their removal changes the outcome. If no, the removal
                  is made permanent; if yes, the removal is
                  undone. I.o.w., trial and error. ]

  SeeAlso     [ ]

******************************************************************************/
enum Game_UnrealizableCore_Algorithm_TAG {
  GAME_UNREALIZABLE_CORE_ALGORITHM_INVALID = -1,
  GAME_UNREALIZABLE_CORE_ALGORITHM_ACTIVATION_VARIABLES = 0,
  GAME_UNREALIZABLE_CORE_ALGORITHM_EXPLICIT
};

/**Type************************************************************************

  Synopsis    [ Identifies the type of core reported by an unrealizable
                core algorithm. ]

  Description [ Values:

                GAME_UNREALIZABLE_CORE_CORE_TYPE_CORE: This indicates
                  which guarantees need to be kept to preserve
                  unrealizability (resp. which assumptions need to be
                  kept to preserve realizability).

                GAME_UNREALIZABLE_CORE_CORE_TYPE_FIX: This indicates
                  which guarantees need to be removed to obtain a
                  realizable property (resp. which assumptions need to
                  be removed to obtain unrealizability).

  SeeAlso     [ ]

******************************************************************************/
enum Game_UnrealizableCore_CoreType_TAG {
  GAME_UNREALIZABLE_CORE_CORE_TYPE_INVALID = -1,
  GAME_UNREALIZABLE_CORE_CORE_TYPE_CORE = 0,
  GAME_UNREALIZABLE_CORE_CORE_TYPE_FIX
};

/**Type************************************************************************

  Synopsis    [ Determines the way a strategy is printed. ]

  Description [ Contrary to most other game algorithms the sf07
                algorithm builds the final strategy as the product of
                the strategy obtained from the subgame (i.e., in the
                product of the original game and the monitor for the
                property) and the monitor for the subgame. That leaves
                3 possibilities how to deal with the monitor part: (1)
                print the monitor separately directly as it has been
                constructed as an sexp, (2) print the monitor
                separately from its BddFsm, and (3) conjoin the BDDs
                for the strategy and for monitor from its BddFsm and
                print the conjunction.

                GAME_SF07_STRATEGY_PRINTING_MODE_SEXP: Print the
                  monitor separately from its sexp.

                GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE: Print
                  the monitor separately from its BddFsm.

                GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED: Print
                  the conjoined BDDs for the strategy and for the
                  monitor from its BddFsm. ]

  SeeAlso     [ ]

******************************************************************************/
enum Game_SF07_StrategyPrintingMode_TAG {
  GAME_SF07_STRATEGY_PRINTING_MODE_SEXP = 0,
  GAME_SF07_STRATEGY_PRINTING_MODE_BDD_SEPARATE,
  GAME_SF07_STRATEGY_PRINTING_MODE_BDD_CONJOINED
};

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/* keeps the flattened game hierarchy */
EXTERN GameHierarchy_ptr mainGameHierarchy;

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/
EXTERN GameBddFsm_ptr Game_CreateGameBddFsm ARGS((const FsmBuilder_ptr self,
                                                  BddEnc_ptr enc,
                                                  const GameSexpFsm_ptr sexp_fsm,
                                                  const SymbLayer_ptr layer_1,
                                                  const SymbLayer_ptr layer_2,
                                                  const TransType trans_type));

EXTERN void
Game_BeforeCheckingSpec ARGS((PropGame_ptr prop));

EXTERN void Game_AfterCheckingSpec ARGS((PropGame_ptr prop,
                                         Game_RealizabilityStatus status,
                                         GameStrategy_ptr strategy,
                                         node_ptr varList1,
                                         node_ptr varList2,
                                         gameParams_ptr params));

EXTERN boolean Game_ComputeGenReactivity ARGS((NuSMVEnv_ptr env,node_ptr specExp,
                                 GamePlayer player,
                                 GameBddFsm_ptr fsm,
                                 Game_InitTermination earlierTermination,
                                 bdd_ptr overapproxWinStates,
                                 bdd_ptr underapproxWinStates,
                                 bdd_ptr* winningStates));

EXTERN Game_RealizabilityStatus
Game_UseStrongReachabilityAlgorithm ARGS((PropGame_ptr prop,
                                          GameStrategy_ptr* strategy));

EXTERN boolean Game_PropertyToGame
 ARGS((NuSMVEnv_ptr env,node_ptr* inputVars, node_ptr* outputVars,
       node_ptr exp_1, node_ptr* init_1, node_ptr* trans_1,
       node_ptr exp_2, node_ptr* init_2, node_ptr* trans_2,
       node_ptr* property));

EXTERN void Game_init_opt ARGS((NuSMVEnv_ptr env));

#endif /* __GAME_INT_H__ */
