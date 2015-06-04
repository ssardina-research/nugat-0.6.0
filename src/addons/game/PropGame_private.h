/**CHeaderFile*****************************************************************

  FileName    [ PropGame_private.h ]

  PackageName [ game ]

  Synopsis    [ Private and protected interface of class 'PropGame' ]

  Description [ This file can be included only by derived and friend
                classes. ]

  SeeAlso     [ PropGame.h, Prop_private.h ]

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

#ifndef __PROP_GAME_PRIVATE_H__
#define __PROP_GAME_PRIVATE_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "prop/Prop.h"
#include "prop/Prop_private.h"

#include "utils/object.h"
#include "utils/utils.h"

/**Struct**********************************************************************

  Synopsis    [ PropGame class definition derived from class Prop. ]

  Description [ This structure contains informations about a given
  property:<br>
  <dl>
  <dt><code>game_scalar_fsm</code>
      <dd>The FSM associated to the property in scalar format.
  <dt><code>game_bool_fsm</code>
      <dd>The FSM associated to the property in boolean format.
  <dt><code>game_bdd_fsm</code>
      <dd>The FSM associated to the property in BDD format.
  <dt><code>game_be_fsm</code>
      <dd>The FSM associated to the property in BE format.
  </dl>]

  SeeAlso     [ Base class Prop ]

******************************************************************************/
typedef struct PropGame_TAG
{
  /* this MUST stay on the top */
  INHERITS_FROM(Prop);

  /* -------------------------------------------------- */
  /*                  Private members                   */
  /* -------------------------------------------------- */
  GameSexpFsm_ptr game_scalar_fsm; /* the game scalar FSM */
  GameSexpFsm_ptr game_bool_fsm;   /* the game scalar FSM converted to
                                      Boolean */
  GameBddFsm_ptr  game_bdd_fsm;    /* the game BDD FSM */
  GameBeFsm_ptr   game_be_fsm;     /* the game BE FSM */

} PropGame;

/* ---------------------------------------------------------------------- */
/* Private methods to be used by derivated and friend classes only        */
/* ---------------------------------------------------------------------- */
EXTERN void prop_game_init ARGS((PropGame_ptr self));
EXTERN void prop_game_deinit ARGS((PropGame_ptr self));

Expr_ptr prop_game_get_expr(const PropGame_ptr self);
const char* prop_game_get_type_as_string(const PropGame_ptr self);
void prop_game_print(const PropGame_ptr self, FILE* file);
void prop_game_print_db(const PropGame_ptr self, FILE* file);
void prop_game_verify(PropGame_ptr self);

void prop_game_set_game_scalar_sexp_fsm ARGS((PropGame_ptr self,
                                              GameSexpFsm_ptr fsm,
                                              const boolean duplicate));
void prop_game_set_game_bool_sexp_fsm ARGS((PropGame_ptr self,
                                            GameSexpFsm_ptr fsm,
                                            const boolean duplicate));
void prop_game_set_game_bdd_fsm ARGS((PropGame_ptr self,
                                      GameBddFsm_ptr fsm,
                                      const boolean duplicate));
void prop_game_set_game_be_fsm ARGS((PropGame_ptr self,
                                     GameBeFsm_ptr fsm,
                                     const boolean duplicate));

#endif /* __PROP_GAME_PRIVATE_H__ */
