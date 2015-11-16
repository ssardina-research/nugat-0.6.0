/**CHeaderFile***** ************************************************************

  FileName    [ game.h ]

  PackageName [ game ]

  Synopsis    [ The public interface for the <tt>game</tt> package. ]

  Description [ This package contains the generic interface to access
                the game package. ]

  SeeAlso     [ ]

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

  Revision    [$Id: game.h,v 1.1.2.6 2010-02-05 17:19:08 nusmv Exp $]

******************************************************************************/

#ifndef _GAME_H_
#define _GAME_H_

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "PropGame.h"
#include "fsm/GameBddFsm.h"

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Constants declarations                                                    */
/*---------------------------------------------------------------------------*/

/* Options names */
#define GAME_GAME "game_game"
#define GAME_PRINT_PLAN "game_print_strategy"
#define GAME_GAME_INITIAL_CONDITION  "game_game_initial_condition"
#define GAME_SF07_STRATEGY_PRINTING_MODE "game_sf07_strategy_printing_mode"
#define GAME_SF07_GBA_WRING_BINARY "game_sf07_gba_wring_binary"
#define GAME_SF07_GBA_WRING_HAS_CC "game_sf07_gba_wring_has_cc"
#define GAME_SF07_GBA_WRING_INPUT_DIR "game_sf07_gba_wring_input_dir"
#define GAME_SF07_GBA_WRING_INPUT_TEMPL "game_sf07_gba_wring_input_templ"
#define GAME_SF07_GBA_WRING_INPUT_KEEP "game_sf07_gba_wring_input_keep"
#define GAME_SF07_GBA_WRING_OUTPUT_DIR "game_sf07_gba_wring_output_dir"
#define GAME_SF07_GBA_WRING_OUTPUT_TEMPL "game_sf07_gba_wring_output_templ"
#define GAME_SF07_GBA_WRING_OUTPUT_KEEP "game_sf07_gba_wring_output_keep"

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Parameters for functions to check game properties,
                related to strategy printing. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameParams_TAG* gameParams_ptr;

/**Type************************************************************************

  Synopsis    [ Identifies player(s). ]

  Description [ See gameInt.h ]

  SeeAlso     [ ]

******************************************************************************/
typedef enum Game_Who_TAG Game_Who;

/**Type************************************************************************

  Synopsis    [ Determines the algorithm used to extract (un)realizable
                cores. ]

  Description [ See gameInt.h ]

  SeeAlso     [ ]

******************************************************************************/
typedef enum Game_UnrealizableCore_Algorithm_TAG
  Game_UnrealizableCore_Algorithm;

/**Type************************************************************************

  Synopsis    [ Determines the type of core reported by an unrealizable
                core algorithm. ]

  Description [ See gameInt.h ]

  SeeAlso     [ ]

******************************************************************************/
typedef enum Game_UnrealizableCore_CoreType_TAG
  Game_UnrealizableCore_CoreType;

/**Type************************************************************************

  Synopsis    [ Determines the way a strategy is printed. ]

  Description [ See gameInt.h ]

  SeeAlso     [ ]

******************************************************************************/
typedef enum Game_SF07_StrategyPrintingMode_TAG Game_SF07_StrategyPrintingMode;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/
EXTERN void Game_Init ARGS((void));
EXTERN void Game_Quit ARGS((NuSMVEnv_ptr env));
EXTERN void Game_Mode_Enter ARGS((NuSMVEnv_ptr env));
EXTERN void Game_Mode_Exit ARGS((NuSMVEnv_ptr env));

/* various commands used to create the Game FSMs */
EXTERN int Game_CommandFlattenHierarchy ARGS((NuSMVEnv_ptr env));
EXTERN int Game_CommandEncodeVariables ARGS((NuSMVEnv_ptr env,char* input_order_file_name));
EXTERN void Game_CommandBuildFlatModel ARGS((NuSMVEnv_ptr env));
EXTERN void Game_CommandBuildBooleanModel ARGS((NuSMVEnv_ptr env));
EXTERN void Game_CommandBuildBddModel ARGS((NuSMVEnv_ptr env));

EXTERN void Game_CommandWriteFlatModel ARGS((NuSMVEnv_ptr env,FILE* ofileid));
EXTERN void Game_CommandWriteBooleanModel ARGS((NuSMVEnv_ptr env,FILE* ofileid));

/* checking specification */
EXTERN void
Game_CheckReachTargetSpec ARGS((NuSMVEnv_ptr env,PropGame_ptr prop, gameParams_ptr params));

EXTERN void Game_CheckAvoidTargetSpec ARGS((NuSMVEnv_ptr env,PropGame_ptr prop, gameParams_ptr params));

EXTERN void
Game_CheckReachDeadlockSpec ARGS((NuSMVEnv_ptr env,PropGame_ptr prop, gameParams_ptr params));

EXTERN void
Game_CheckAvoidDeadlockSpec ARGS((NuSMVEnv_ptr env,PropGame_ptr prop, gameParams_ptr params));

EXTERN void
Game_CheckBuchiGameSpec ARGS((NuSMVEnv_ptr env,PropGame_ptr prop, gameParams_ptr params));

EXTERN void Game_CheckLtlGameSpecSF07 ARGS((NuSMVEnv_ptr env,PropGame_ptr prop,
                                            gameParams_ptr params,
                                            unsigned int kmin,
                                            unsigned int kmax,
                                            Game_Who w));

EXTERN void
Game_CheckGenReactivitySpec ARGS((NuSMVEnv_ptr env, PropGame_ptr prop, gameParams_ptr params));

EXTERN int Game_CheckGameSpecAndComputeCores ARGS((NuSMVEnv_ptr env,NodeMgr_ptr nodemgr,
                                                   PropGame_ptr prop,
                                           Game_UnrealizableCore_Algorithm algo,
                                              Game_UnrealizableCore_CoreType ct,
                                                   boolean doInit,
                                                   boolean doInvar,
                                                   boolean doTrans,
                                                   boolean doProperty,
                                                   Game_Who w,
                                                   int N));

#if HAVE_LIBEXPAT
EXTERN int Game_RatFileToGame ARGS((const char* filename));
#endif /* HAVE_LIBEXPAT */

/* Game Options */

EXTERN boolean opt_game_game ARGS((OptsHandler_ptr));
EXTERN void    set_game_game ARGS((OptsHandler_ptr));
EXTERN void    unset_game_game ARGS((OptsHandler_ptr));
EXTERN void    set_game_print_strategy ARGS((OptsHandler_ptr opt));
EXTERN void    unset_game_print_strategy ARGS((OptsHandler_ptr opt));
EXTERN boolean opt_game_print_strategy ARGS((OptsHandler_ptr opt));
EXTERN void    set_game_game_initial_condition ARGS((OptsHandler_ptr, char));
EXTERN void    unset_game_game_initial_condition ARGS((OptsHandler_ptr));
EXTERN char    opt_game_game_initial_condition ARGS((OptsHandler_ptr));

EXTERN void set_game_sf07_strategy_printing_mode ARGS((OptsHandler_ptr opt,
                                             Game_SF07_StrategyPrintingMode m));
EXTERN Game_SF07_StrategyPrintingMode
get_game_sf07_strategy_printing_mode ARGS((OptsHandler_ptr opt));
EXTERN void reset_game_sf07_strategy_printing_mode ARGS((OptsHandler_ptr opt));

EXTERN void    set_game_sf07_gba_wring_binary ARGS((OptsHandler_ptr, char*));
EXTERN char *  get_game_sf07_gba_wring_binary ARGS((OptsHandler_ptr));
EXTERN void    reset_game_sf07_gba_wring_binary ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_has_cc ARGS((OptsHandler_ptr));
EXTERN void    unset_game_sf07_gba_wring_has_cc ARGS((OptsHandler_ptr));
EXTERN boolean opt_game_sf07_gba_wring_has_cc ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_input_dir ARGS((OptsHandler_ptr, char*));
EXTERN char *  get_game_sf07_gba_wring_input_dir ARGS((OptsHandler_ptr));
EXTERN void    reset_game_sf07_gba_wring_input_dir ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_input_templ ARGS((OptsHandler_ptr,
                                                         char*));
EXTERN char *  get_game_sf07_gba_wring_input_templ ARGS((OptsHandler_ptr));
EXTERN void    reset_game_sf07_gba_wring_input_templ ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_input_keep ARGS((OptsHandler_ptr));
EXTERN void    unset_game_sf07_gba_wring_input_keep ARGS((OptsHandler_ptr));
EXTERN boolean opt_game_sf07_gba_wring_input_keep ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_output_dir ARGS((OptsHandler_ptr, char*));
EXTERN char *  get_game_sf07_gba_wring_output_dir ARGS((OptsHandler_ptr));
EXTERN void    reset_game_sf07_gba_wring_output_dir ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_output_templ ARGS((OptsHandler_ptr,
                                                          char*));
EXTERN char *  get_game_sf07_gba_wring_output_templ ARGS((OptsHandler_ptr));
EXTERN void    reset_game_sf07_gba_wring_output_templ ARGS((OptsHandler_ptr));

EXTERN void    set_game_sf07_gba_wring_output_keep ARGS((OptsHandler_ptr));
EXTERN void    unset_game_sf07_gba_wring_output_keep ARGS((OptsHandler_ptr));
EXTERN boolean opt_game_sf07_gba_wring_output_keep ARGS((OptsHandler_ptr));

/* Miscellaneous */
EXTERN Game_Who Game_Who_from_string ARGS((const char* s));
EXTERN const char* Game_Who_to_string ARGS((const Game_Who w));

EXTERN Game_UnrealizableCore_Algorithm
Game_UnrealizableCore_Algorithm_from_string ARGS((const char* s));

EXTERN const char* Game_UnrealizableCore_Algorithm_to_string
ARGS((const Game_UnrealizableCore_Algorithm a));

EXTERN Game_UnrealizableCore_CoreType
Game_UnrealizableCore_CoreType_from_string ARGS((const char* s));

EXTERN const char* Game_UnrealizableCore_CoreType_to_string
ARGS((const Game_UnrealizableCore_CoreType a));

EXTERN const char* Game_SF07_StrategyPrintingMode_to_string
ARGS((const Game_SF07_StrategyPrintingMode m));

/* ====================================================================== */

#endif /* _GAME_H_ */
