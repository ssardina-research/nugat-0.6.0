/**CHeaderFile*****************************************************************

  FileName    [ GameBeFsm.h ]

  PackageName [ game.fsm ]

  Synopsis    [ This is a public interface of the Game Finite State
                Machine class in BE format. An instance of this class
                essentially consists of two usual BE FSMs, one for
                each player. ]

  Description [ ]

  SeeAlso     [ GameBeFsm.c ]

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

  Revision    [$Id: GameBeFsm.h,v 1.1.2.3 2010-02-05 22:44:23 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_BE_FSM__H
#define __GAME_BE_FSM__H

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "GameSexpFsm.h"

#include "enc/be/BeEnc.h"
#include "fsm/be/BeFsm.h"
#include "utils/utils.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Struct*********************************************************************

  Synopsis    [ Definition of the public accessor for class GameBeFsm. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameBeFsm_TAG* GameBeFsm_ptr;

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

  Synopsis    [ To cast and check instances of class GameBeFsm. ]

  Description [ These macros must be used respectively to cast and to
                check instances of class GameBeFsm. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_BE_FSM(self) ((GameBeFsm_ptr) self)
#define GAME_BE_FSM_CHECK_INSTANCE(self) \
  (nusmv_assert(GAME_BE_FSM(self) != GAME_BE_FSM(NULL)))

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

EXTERN GameBeFsm_ptr GameBeFsm_create ARGS((BeFsm_ptr player_1,
                                            BeFsm_ptr player_2));

EXTERN GameBeFsm_ptr GameBeFsm_copy ARGS((GameBeFsm_ptr self));

EXTERN GameBeFsm_ptr GameBeFsm_create_from_sexp_fsm ARGS((BeEnc_ptr be_enc,
                                                   const GameSexpFsm_ptr fsm));

EXTERN void GameBeFsm_destroy ARGS((GameBeFsm_ptr self));

EXTERN BeFsm_ptr GameBeFsm_get_player_1 ARGS((const GameBeFsm_ptr self));

EXTERN BeFsm_ptr GameBeFsm_get_player_2 ARGS((const GameBeFsm_ptr self));

/**AutomaticEnd***************************************************************/

#endif /* __GAME_BE_FSM__H */
