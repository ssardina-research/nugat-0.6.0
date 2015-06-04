/**CHeaderFile*****************************************************************

  FileName    [ GameSexpFsm.h ]

  PackageName [ game.fsm ]

  Synopsis    [ Public interface of class 'GameSexpFsm' (Game Scalar
                FSM) ]

  Description [ ]

  SeeAlso     [ GameSexpFsm.c ]

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

  Revision    [$Id: GameSexpFsm.h,v 1.1.2.6 2010-02-05 22:43:06 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_SEXP_FSM_H__
#define __GAME_SEXP_FSM_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "compile/FlatHierarchy.h"
#include "compile/symb_table/SymbLayer.h"
#include "enc/bdd/BddEnc.h"
#include "fsm/sexp/SexpFsm.h"
#include "set/set.h"
#include "utils/utils.h"
#include "utils/NodeList.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type***********************************************************************

  Synopsis    [ Definition of the public accessor for class
                GameSexpFsm. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameSexpFsm_TAG* GameSexpFsm_ptr;

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

  Synopsis    [ To cast and check instances of class GameSexpFsm. ]

  Description [ These macros must be used respectively to cast and to
                check instances of class GameSexpFsm. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SEXP_FSM(x) ((GameSexpFsm_ptr) x)
#define GAME_SEXP_FSM_CHECK_INSTANCE(x) \
  (nusmv_assert(GAME_SEXP_FSM(x) != GAME_SEXP_FSM(NULL)))

/*---------------------------------------------------------------------------*/
/* Public Function Interface                                                 */
/*---------------------------------------------------------------------------*/

/* constructors */

EXTERN GameSexpFsm_ptr GameSexpFsm_create ARGS((Set_t all_vars_set,
                                                FlatHierarchy_ptr hierarchy_1,
                                                FlatHierarchy_ptr hierarchy_2,
                                                Set_t vars_set_1,
                                                Set_t vars_set_2));

EXTERN GameSexpFsm_ptr GameSexpFsm_copy ARGS((const GameSexpFsm_ptr self));

/* destructor */

EXTERN void GameSexpFsm_destroy ARGS((GameSexpFsm_ptr self));

/* conversion to boolean FSM */

EXTERN GameSexpFsm_ptr
GameSexpFsm_scalar_to_boolean ARGS((const GameSexpFsm_ptr self,
                                    BddEnc_ptr enc,
                                    SymbLayer_ptr det_layer_1,
                                    SymbLayer_ptr det_layer_2));

/* access functions */

EXTERN boolean GameSexpFsm_is_boolean ARGS((const GameSexpFsm_ptr self));

EXTERN NodeList_ptr GameSexpFsm_get_all_vars ARGS((const GameSexpFsm_ptr self));

EXTERN NodeList_ptr
GameSexpFsm_get_vars_list_1 ARGS((const GameSexpFsm_ptr self));

EXTERN NodeList_ptr
GameSexpFsm_get_vars_list_2 ARGS((const GameSexpFsm_ptr self));

EXTERN SexpFsm_ptr GameSexpFsm_get_player_1 ARGS((const GameSexpFsm_ptr self));

EXTERN SexpFsm_ptr GameSexpFsm_get_player_2 ARGS((const GameSexpFsm_ptr self));

#endif /* __GAME_SEXP_FSM_H__ */
