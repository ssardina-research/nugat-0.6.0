/**CHeaderFile*****************************************************************

  FileName    [ GameHierarchy.h ]

  PackageName [ game ]

  Synopsis    [ The class is used to store the result of compilation of a
                game definition. ]

  Description [ This class is very similar to FlatHierarchy (from
                compile package) except that this class is used to
                store results of flattening a game hierarchy.

                This class consists of two flattened hierarchies
                (FlatHierarchy class), one for each player, and also
                constains a set of fields to store game problems
                (i.e. AVOIDTARGET, READDEADLOCK, etc). All these
                structures are obtained after flattening parsed tree
                (i.e. modules and game definition ).

                See FlatHierarchy_create for more info on this
                class. ]

  SeeAlso     [ GameHierarchy.c, FlatHierarchy.h ]

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

  Revision    [$Id]

******************************************************************************/

#ifndef __GAME_HIERARCHY_H__
#define __GAME_HIERARCHY_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "compile/FlatHierarchy.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Definition of the public accessor for class GameHierarchy. ]

  Description [ The struct store info of the flattened modules. ]

  SeeAlso     [ FlatHierarchy_ptr ]

******************************************************************************/
typedef struct GameHierarchy_TAG* GameHierarchy_ptr;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ To cast and check instances of class GameHierarchy. ]

  Description [ These macros must be used respectively to cast and to
                check instances of this class. ]

  SideEffects [ None ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_HIERARCHY(x) ((GameHierarchy_ptr) x)
#define GAME_HIERARCHY_CHECK_INSTANCE(x) \
         ( nusmv_assert(GAME_HIERARCHY(x) != GAME_HIERARCHY(NULL)) )

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

EXTERN GameHierarchy_ptr GameHierarchy_create ARGS((FlatHierarchy_ptr player1,
                                                    FlatHierarchy_ptr player2,
                                                    node_ptr spec,
                                                    node_ptr ltlspec,
                                                    node_ptr invarspec,
                                                    node_ptr pslspec,
                                                    node_ptr compute,
                                                    node_ptr reachtarget,
                                                    node_ptr avoidtarget,
                                                    node_ptr reachdeadlock,
                                                    node_ptr avoiddeadlock,
                                                    node_ptr buchigame,
                                                    node_ptr ltlgame,
                                                    node_ptr genreactivity));

EXTERN void  GameHierarchy_destroy ARGS((GameHierarchy_ptr self));

/* -- Access function to the class's fields : constrains and specifications --*/

EXTERN FlatHierarchy_ptr
GameHierarchy_get_player_1 ARGS((GameHierarchy_ptr self));

EXTERN FlatHierarchy_ptr
GameHierarchy_get_player_2 ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_ctlspec ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_ltlspec ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_invarspec ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_pslspec ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_compute ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_reachtarget ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_avoidtarget ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_reachdeadlock ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_avoiddeadlock ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_buchigame ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_ltlgame ARGS((GameHierarchy_ptr self));

EXTERN node_ptr GameHierarchy_get_genreactivity ARGS((GameHierarchy_ptr self));

#endif /* __GAME_HIERARCHY_H__ */
