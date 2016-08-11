/**CHeaderFile*****************************************************************

  FileName    [ PropDbGame.h ]

  PackageName [ game ]

  Synopsis    [ Public interface of class 'PropDbGame' ]

  Description [ ]

  SeeAlso     [ PropDbGame.c ]

  Author      [ Roberto Cavada, Viktor Schuppan ]

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

  Revision    [$Id$]

******************************************************************************/

#ifndef __PROP_DB_GAME_H__
#define __PROP_DB_GAME_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "PropGame.h"
#include "addons/game/fsm/GameSexpFsm.h"
#include "addons/game/fsm/GameBddFsm.h"
#include "addons/game/fsm/GameBeFsm.h"

#include "prop/PropDb.h"
#include "compile/compile.h"
#include "node/node.h"
#include "utils/utils.h"
#include "utils/ustring.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type***********************************************************************

  Synopsis    [ Definition of the public accessor for class PropDbGame. ]

  Description [ ]

  SeeAlso     [ PropDb ]

******************************************************************************/
typedef struct PropDbGame_TAG* PropDbGame_ptr;

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

  Synopsis    [ To cast and check instances of class PropDbGame. ]

  Description [ These macros must be used respectively to cast and to check
                instances of class PropDbGame. ]

  SeeAlso     [ ]

******************************************************************************/
#define PROP_DB_GAME(self) \
         ((PropDbGame_ptr) self)

#define PROP_DB_GAME_CHECK_INSTANCE(self) \
         (nusmv_assert(PROP_DB_GAME(self) != PROP_DB_GAME(NULL)))

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

EXTERN PropDbGame_ptr PropDbGame_create ARGS((const NuSMVEnv_ptr env));
EXTERN void PropDbGame_destroy ARGS((PropDbGame_ptr self));
EXTERN void PropDbGame_clean ARGS((const NuSMVEnv_ptr env,PropDbGame_ptr self));

EXTERN int PropDbGame_fill ARGS((PropDbGame_ptr self,
                                 SymbTable_ptr symb_table,
                                 node_ptr reachtarget,
                                 node_ptr avoidtarget,
                                 node_ptr reachdeadlock,
                                 node_ptr avoiddeadlock,
                                 node_ptr buchigame,
                                 node_ptr ltlgame,
                                 node_ptr genreactivity));
EXTERN void PropDbGame_verify_all_type_player ARGS((PropDbGame_ptr self,
                                                    PropGame_Type type,
                                                    string_ptr player));
EXTERN void PropDbGame_print_all_type_player_status ARGS((PropDbGame_ptr self,
                                                          OStream_ptr file,
                                                          PropGame_Type type,
                                                          string_ptr player,
                                                          Prop_Status status));

/* Master's FSMs getters: */
EXTERN GameSexpFsm_ptr
PropDbGame_master_get_game_scalar_sexp_fsm ARGS((const PropDbGame_ptr self));
EXTERN GameSexpFsm_ptr
PropDbGame_master_get_game_bool_sexp_fsm ARGS((const PropDbGame_ptr self));
EXTERN GameBddFsm_ptr
PropDbGame_master_get_game_bdd_fsm ARGS((const PropDbGame_ptr self));
EXTERN GameBeFsm_ptr
PropDbGame_master_get_game_be_fsm ARGS((const PropDbGame_ptr self));

/* Master's FSMs setters: */
EXTERN void
PropDbGame_master_set_game_scalar_sexp_fsm ARGS((PropDbGame_ptr self,
                                                 GameSexpFsm_ptr fsm));
EXTERN void
PropDbGame_master_set_game_bool_sexp_fsm ARGS((PropDbGame_ptr self,
                                               GameSexpFsm_ptr fsm));
EXTERN void
PropDbGame_master_set_game_bdd_fsm ARGS((PropDbGame_ptr self,
                                         GameBddFsm_ptr fsm));
EXTERN void
PropDbGame_master_set_game_be_fsm ARGS((PropDbGame_ptr self,
                                        GameBeFsm_ptr fsm));

/**AutomaticEnd***************************************************************/

#endif /* __PROP_DB_GAME_H__ */
