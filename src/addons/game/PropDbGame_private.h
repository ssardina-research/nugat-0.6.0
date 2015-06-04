/**CHeaderFile*****************************************************************

  FileName    [ PropDbGame_private.h ]

  PackageName [ game ]

  Synopsis    [ Private and protected interface of class 'PropDbGame' ]

  Description [ This file can be included only by derived and friend
                classes. ]

  SeeAlso     [ PropDbGame.h, PropDb_private.h ]

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

#ifndef __PROP_DB_GAME_PRIVATE_H__
#define __PROP_DB_GAME_PRIVATE_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "PropDbGame.h"
#include "PropGame.h"

#include "prop/PropDb.h"
#include "prop/PropDb_private.h"

#include "utils/object.h"
#include "utils/object_private.h"

#include "utils/utils.h"

/**Struct**********************************************************************

  Synopsis    [ PropDbGame class definition derived from class PropDb. ]

  Description [ ]

  SeeAlso     [ Base class PropDb ]

******************************************************************************/
typedef struct PropDbGame_TAG
{
  /* this MUST stay on the top */
  INHERITS_FROM(PropDb);

  /* -------------------------------------------------- */
  /*                  Private members                   */
  /* -------------------------------------------------- */

  /* -------------------------------------------------- */
  /*                  Virtual methods                   */
  /* -------------------------------------------------- */

} PropDbGame;

/* ---------------------------------------------------------------------- */
/* Private methods to be used by derivated and friend classes only         */
/* ---------------------------------------------------------------------- */
EXTERN void prop_db_game_init ARGS((PropDbGame_ptr self));
EXTERN void prop_db_game_deinit ARGS((PropDbGame_ptr self));

int prop_db_game_prop_create_and_add(PropDbGame_ptr self,
                                     SymbTable_ptr symb_table,
                                     node_ptr spec,
                                     PropGame_Type type);
void prop_db_game_set_fsm_to_master(PropDbGame_ptr self, PropGame_ptr prop);
void prop_db_game_verify_all(const PropDbGame_ptr self);

#endif /* __PROP_DB_GAME_PRIVATE_H__ */
