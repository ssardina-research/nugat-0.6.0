/**CHeaderFile*****************************************************************

  FileName    [ GameBddFsm.h ]

  PackageName [ game.fsm ]

  Synopsis    [ Declares the interface of the class GameBddFsm. ]

  Description [ A GameBddFsm is a Game Finite State Machine (Game FSM)
                which consists of two usual BddFsm (see BddFsm.h), one
                for each player. ]

  SeeAlso     [ GameBddFsm.c ]

  Author      [ Andrei Tchaltsev ]

  Copyright   [
  This file is part of the ``game.fsm'' package of NuGaT.
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

  Revision    [$Id: GameBddFsm.h,v 1.1.2.5 2010-02-05 22:45:41 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_BDD_FSM__H__
#define __GAME_BDD_FSM__H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "addons/game/GamePlayer.h"

#include "dd/dd.h"
#include "enc/bdd/BddEnc.h"
#include "fsm/bdd/bdd.h"
#include "fsm/bdd/BddFsm.h"
#include "trans/bdd/BddTrans.h"
#include "utils/utils.h"

#include <stdio.h>

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Definition of the public accessor for class GameBddFsm. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameBddFsm_TAG*  GameBddFsm_ptr;

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ To cast and check instances of class GameBddFsm. ]

  Description [ These macros must be used respectively to cast and to
                check instances of class GameBddFsm. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_BDD_FSM(x) ((GameBddFsm_ptr) x)
#define GAME_BDD_FSM_CHECK_INSTANCE(x) \
  (nusmv_assert(GAME_BDD_FSM(x) != GAME_BDD_FSM(NULL)))

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

/* Constructors */

EXTERN GameBddFsm_ptr GameBddFsm_create ARGS((BddEnc_ptr enc,
                                              BddFsm_ptr player_1,
                                              bdd_ptr stateVarCube_1,
                                              bdd_ptr stateFrozenVarCube_1,
                                              BddFsm_ptr player_2,
                                              bdd_ptr stateVarCube_2,
                                              bdd_ptr stateFrozenVarCube_2));

EXTERN GameBddFsm_ptr GameBddFsm_copy ARGS((const GameBddFsm_ptr self));

/* Destructors */

EXTERN void GameBddFsm_destroy ARGS((GameBddFsm_ptr self));

/* Accessors */

EXTERN BddFsm_ptr GameBddFsm_get_player_1 ARGS((const GameBddFsm_ptr self));

EXTERN BddFsm_ptr GameBddFsm_get_player_2 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr GameBddFsm_get_state_var_cube_1 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr GameBddFsm_get_state_var_cube_2 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr
GameBddFsm_get_next_state_var_cube_1 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr
GameBddFsm_get_next_state_var_cube_2 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr
GameBddFsm_get_state_frozen_var_cube_1 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr
GameBddFsm_get_state_frozen_var_cube_2 ARGS((const GameBddFsm_ptr self));

EXTERN BddStates GameBddFsm_get_init_1 ARGS((const GameBddFsm_ptr self));

EXTERN BddStates GameBddFsm_get_init_2 ARGS((const GameBddFsm_ptr self));

EXTERN BddInvarStates GameBddFsm_get_invars_1 ARGS((const GameBddFsm_ptr self));

EXTERN BddInvarStates GameBddFsm_get_invars_2 ARGS((const GameBddFsm_ptr self));

EXTERN BddTrans_ptr GameBddFsm_get_trans_1 ARGS((const GameBddFsm_ptr self));

EXTERN BddTrans_ptr GameBddFsm_get_trans_2 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr
GameBddFsm_get_monolitic_trans_1 ARGS((const GameBddFsm_ptr self));

EXTERN bdd_ptr
GameBddFsm_get_monolitic_trans_2 ARGS((const GameBddFsm_ptr self));

EXTERN BddStates GameBddFsm_with_successor_states ARGS((GameBddFsm_ptr self,
                                                        GamePlayer player));

EXTERN BddStates GameBddFsm_without_successor_states ARGS((GameBddFsm_ptr self,
                                                           GamePlayer player));

EXTERN BddStates
GameBddFsm_get_strong_backward_image ARGS((const GameBddFsm_ptr self,
                                           BddStates states,
                                           GamePlayer player));

EXTERN BddStates
GameBddFsm_get_weak_forward_image ARGS((const GameBddFsm_ptr self,
                                        BddStates states));

EXTERN BddStates GameBddFsm_get_move ARGS((const GameBddFsm_ptr self,
                                           BddStates states,
                                           GamePlayer player));

EXTERN boolean GameBddFsm_can_player_satisfy ARGS((const GameBddFsm_ptr self,
                                                   BddStates constr_1,
                                                   BddStates constr_2,
                                                   BddStates goalStates,
                                                   GamePlayer player,
                                                   char quantifiers));

EXTERN BddStates
GameBddFsm_player_satisfies_from ARGS((const GameBddFsm_ptr self,
                                       BddStates constr_1,
                                       BddStates constr_2,
                                       BddStates goalStates,
                                       GamePlayer player,
                                       char quantifiers));

EXTERN void GameBddFsm_print_info ARGS((const GameBddFsm_ptr self, OStream_ptr file));

EXTERN void GameBddFsm_apply_synchronous_product ARGS((GameBddFsm_ptr self,
                                                  const GameBddFsm_ptr other));

/**AutomaticEnd***************************************************************/

#endif /* __GAME_BDD_FSM__H__ */
