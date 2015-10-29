/**CHeaderFile*****************************************************************

  FileName    [ PropGame.h ]

  PackageName [ game ]

  Synopsis    [ Public interface of class 'PropGame' ]

  Description [ This is the extension of prop/Prop.h for the game
                package. ]

  SeeAlso     [ PropGame.c, Prop.h ]

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

#ifndef __PROP_GAME_H__
#define __PROP_GAME_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "fsm/GameSexpFsm.h"
#include "fsm/GameBddFsm.h"
#include "fsm/GameBeFsm.h"

//#include "fsm/sexp/Expr.h" // not exist in NuSMV 2.6.0
#include "prop/Prop.h"
#include "utils/utils.h"
#include "utils/ustring.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/**Constant********************************************************************

  Synopsis    [ String representations of PropGame_Type values. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
#define PROP_GAME_REACH_TARGET_STRING   "ReachTarget"
#define PROP_GAME_AVOID_TARGET_STRING   "AvoidTarget"
#define PROP_GAME_REACH_DEADLOCK_STRING "ReachDeadlock"
#define PROP_GAME_AVOID_DEADLOCK_STRING "AvoidDeadlock"
#define PROP_GAME_BUCHI_GAME_STRING     "BuchiGame"
#define PROP_GAME_LTL_GAME_STRING       "LtlGame"
#define PROP_GAME_GEN_REACTIVITY_STRING "GenReactivity"

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Enumerates the different types of a game specification. ]

  Description [ This extends Prop_Type in prop/Prop.h. It effectively
                abuses lack of propery type checking for enums in C. ]

  SeeAlso     [ Prop_Type in prop/Prop.h ]

******************************************************************************/
enum PropGame_Type_TAG {
  PropGame_PropGame_Type_First = 200, /* Do not touch this */
  /* ---------------------------------------------------------------------- */
  /* Game specifications: ReachTarget should be the first and
     GenReactivity should be the last in game specs. */
  PropGame_ReachTarget,
  PropGame_AvoidTarget,
  PropGame_ReachDeadlock,
  PropGame_AvoidDeadlock,
  PropGame_BuchiGame,
  PropGame_LtlGame,
  PropGame_GenReactivity,
  /* ---------------------------------------------------------------------- */
  PropGame_PropGame_Type_Last /* Do not touch this */
};
typedef enum PropGame_Type_TAG PropGame_Type;

/**Type***********************************************************************

  Synopsis    [ Definition of the public accessor for class PropGame. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct PropGame_TAG* PropGame_ptr;

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

  Synopsis    [ To cast and check instances of class PropGame. ]

  Description [ These macros must be used respectively to cast and to
                check instances of class PropGame. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define PROP_GAME(self) \
         ((PropGame_ptr) self)

#define PROP_GAME_CHECK_INSTANCE(self) \
         (nusmv_assert(PROP_GAME(self) != PROP_GAME(NULL)))

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

EXTERN PropGame_ptr PropGame_create ARGS((void));
EXTERN PropGame_ptr PropGame_create_partial ARGS((Expr_ptr expr,
                                                  PropGame_Type type));
EXTERN void PropGame_destroy ARGS((PropGame_ptr self));

EXTERN GameSexpFsm_ptr
PropGame_get_game_scalar_sexp_fsm ARGS((const PropGame_ptr self));
EXTERN GameSexpFsm_ptr
PropGame_get_game_bool_sexp_fsm ARGS((const PropGame_ptr self));
EXTERN GameBddFsm_ptr
PropGame_get_game_bdd_fsm ARGS((const PropGame_ptr self));
EXTERN GameBeFsm_ptr
PropGame_get_game_be_fsm ARGS((const PropGame_ptr self));

EXTERN void PropGame_set_game_scalar_sexp_fsm ARGS((PropGame_ptr self,
                                                    GameSexpFsm_ptr fsm));
EXTERN void PropGame_set_game_bool_sexp_fsm ARGS((PropGame_ptr self,
                                                  GameSexpFsm_ptr fsm));
EXTERN void PropGame_set_game_bdd_fsm ARGS((PropGame_ptr self,
                                            GameBddFsm_ptr fsm));
EXTERN void PropGame_set_game_be_fsm ARGS((PropGame_ptr self,
                                           GameBeFsm_ptr fsm));

EXTERN string_ptr PropGame_get_player ARGS((const PropGame_ptr self));

EXTERN const char* PropGame_Type_to_string ARGS((const PropGame_Type type));

EXTERN boolean PropGame_type_is_game ARGS((const PropGame_Type type));
EXTERN boolean PropGame_type_is_game_or_notype ARGS((const PropGame_Type type));

/**AutomaticEnd***************************************************************/

#endif /* __PROP_GAME_H__ */
