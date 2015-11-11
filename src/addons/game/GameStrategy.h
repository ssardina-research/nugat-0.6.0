/**CHeaderFile*****************************************************************

  FileName    [ GameStrategy.h ]

  PackageName [ game ]

  Synopsis    [ Public interface of class 'GameStrategy' ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Andrei Tchaltsev, Viktor Schuppan ]

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

  Revision    [$Id: GameStrategy.h,v 1.1.2.3 2010-02-04 15:42:36 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_STRATEGY__H__
#define __GAME_STRATEGY__H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "game.h"

#include "dd/dd.h"
#include "enc/enc.h"
#include "utils/utils.h"

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Definition of the public accessor for class GameStrategy. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameStrategy_TAG* GameStrategy_ptr;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ To cast and check instances of class GameStrategy. ]

  Description [ These macros must be used respectively to cast and to
                check instances of class. ]

  SideEffects [ None ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_STRATEGY(x) ((GameStrategy_ptr) x)
#define GAME_STRATEGY_CHECK_INSTANCE(x) \
  ( nusmv_assert(GAME_STRATEGY(x) != GAME_STRATEGY(NULL)) )

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

EXTERN GameStrategy_ptr GameStrategy_create ARGS((BddEnc_ptr bdd_enc,
                                             GamePlayer player,
                                             boolean reverseInitialQuantifiers,
                                             bdd_ptr init_goal,
                                             bdd_ptr init_opponent_deadlock,
                                             bdd_ptr init_moves,
                                             bdd_ptr goal,
                                             bdd_ptr opponent_deadlock,
                                             bdd_ptr moves));

EXTERN void GameStrategy_destroy ARGS((GameStrategy_ptr self));

EXTERN GameStrategy_ptr GameStrategy_construct ARGS((GameBddFsm_ptr fsm,
                                             GamePlayer player,
                                             boolean reverseInitialQuantifiers,
                                             bdd_ptr goal,
                                             bdd_ptr winningStates,
                                             bdd_ptr trans));

EXTERN BddEnc_ptr GameStrategy_get_bdd_enc ARGS((GameStrategy_ptr self));

EXTERN GamePlayer GameStrategy_get_player ARGS((GameStrategy_ptr self));

EXTERN bdd_ptr GameStrategy_get_init_goal ARGS((GameStrategy_ptr self));

EXTERN bdd_ptr
GameStrategy_get_init_opponent_deadlock ARGS((GameStrategy_ptr self));

EXTERN bdd_ptr GameStrategy_get_init_moves ARGS((GameStrategy_ptr self));

EXTERN bdd_ptr GameStrategy_get_goal ARGS((GameStrategy_ptr self));

EXTERN bdd_ptr
GameStrategy_get_opponent_deadlock ARGS((GameStrategy_ptr self));

EXTERN bdd_ptr GameStrategy_get_moves ARGS((GameStrategy_ptr self));

EXTERN void GameStrategy_print_module ARGS((const NuSMVEnv_ptr env,
                                            GameStrategy_ptr self,
                                            NodeList_ptr vars,
                                            NodeList_ptr vars_to_decl,
                                            gameParams_ptr params));

/**AutomaticEnd***************************************************************/

#endif /* __GAME_STRATEGY__H__ */
