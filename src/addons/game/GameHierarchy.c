/**CFile***********************************************************************

  FileName    [ GameHierarchy.c ]

  PackageName [ game ]

  Synopsis    [ The class is used to store results of flattening a game
                hierarchy. ]

  Description [ See the description in GameHierarchy.h. ]

  SeeAlso     [ GameHierarchy.h, FlatHierarchy.c ]

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

******************************************************************************/

#include "GameHierarchy.h"

#include "parser/symbols.h"
#include "utils/utils.h"

static char rcsid[] UTIL_UNUSED = "$Id: GameHierarchy.c,v 1.1.2.3 2010-02-08 16:05:50 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Struct**********************************************************************

  Synopsis    [ Data structure used to store the results of compilation. ]

  Description [ ]

  SeeAlso     [ FlatHierarchy ]

******************************************************************************/
struct GameHierarchy_TAG {
  FlatHierarchy_ptr player_1;
  FlatHierarchy_ptr player_2;
  node_ptr spec_expr;
  node_ptr ltlspec_expr;
  node_ptr invarspec_expr;
  node_ptr pslspec_expr;
  node_ptr compute_expr;
  node_ptr reachtarget_expr;
  node_ptr avoidtarget_expr;
  node_ptr reachdeadlock_expr;
  node_ptr avoiddeadlock_expr;
  node_ptr buchigame_expr;
  node_ptr ltlgame_expr;
  node_ptr genreactivity_expr;
};
typedef struct GameHierarchy_TAG GameHierarchy;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void game_hierarchy_init ARGS((GameHierarchy_ptr self,
                                      FlatHierarchy_ptr player1,
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

static void game_hierarchy_deinit ARGS((GameHierarchy_ptr self));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Constructor for class GameHierarchy. ]

  Description [ The class is used to store information obtained after
                flattening a game hierarchy (module list and a game
                definition). This class stores: two FlatHierarchies
                (one for every player) and a list of specifications:
                SPEC, LTLSPEC, PSLSPEC, INVARSPEC, COMPUTE
                REACHTARGET, AVOIDTARGET, REACHDEADLOCK,
                AVOIDDEADLOCK, BUCHIGAME, LTLGAME, GENREACTIVITY.

                NOTE: This structure is filled in by
                      game_flatten_game_hierarchy. There are a few
                      assumptions about the content stored in this
                      class:

                      1. Players\' hierarchies are usual hierarchies
                         and obey corresponding rules (see
                         FlatHierarchy_create), except that players do
                         not have any specifications.

                      2. All expressions are stored in the same order
                         as in the input file (in module body or
                         module instantiation order).

                NOTE: The desctructor will not free memory from the
                      node_ptr, but will destroy the given
                      FlatHierarchy objects. ]

  SideEffects [ ]

  SeeAlso     [ GameHierarchy_destroy, FlatHierarchy_create ]

******************************************************************************/
GameHierarchy_ptr GameHierarchy_create(FlatHierarchy_ptr player1,
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
                                       node_ptr genreactivity)
{
  GameHierarchy_ptr self = ALLOC(GameHierarchy, 1);
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  game_hierarchy_init(self,
                      player1,
                      player2,
                      spec,
                      ltlspec,
                      invarspec,
                      pslspec,
                      compute,
                      reachtarget,
                      avoidtarget,
                      reachdeadlock,
                      avoiddeadlock,
                      buchigame,
                      ltlgame,
                      genreactivity);

  return self;
}

/**Function********************************************************************

  Synopsis    [ Destructor of class GameHierarchy. ]

  Description [ The destructor does not destroy the nodes given to it
                with access functions, but does destroy the
                FlatHierarchy objects. ]

  SideEffects [ ]

  SeeAlso     [ GameHierarchy_create, FlatHierarchy_destroy ]

******************************************************************************/
void GameHierarchy_destroy(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  game_hierarchy_deinit(self);
  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Getter for player_1. ]

  Description [ self keeps ownership of result. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
FlatHierarchy_ptr GameHierarchy_get_player_1(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->player_1);
}

/**Function********************************************************************

  Synopsis    [ Getter for player_2. ]

  Description [ self keeps ownership of result. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
FlatHierarchy_ptr GameHierarchy_get_player_2(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->player_2);
}

/**Function********************************************************************

  Synopsis    [ Getter for ctlspec. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_ctlspec(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->spec_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for ltlspec. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_ltlspec(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->ltlspec_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for invarspec. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_invarspec(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->invarspec_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for pslspec. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_pslspec(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->pslspec_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for compute. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_compute(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->compute_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for reachtarget. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_reachtarget(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->reachtarget_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for avoidtarget. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_avoidtarget(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->avoidtarget_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for reachdeadlock. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_reachdeadlock(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->reachdeadlock_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for avoiddeadlock. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_avoiddeadlock(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->avoiddeadlock_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for buchigame. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_buchigame(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->buchigame_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for ltlgame. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_ltlgame(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->ltlgame_expr);
}

/**Function********************************************************************

  Synopsis    [ Getter for genreactivity. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
node_ptr GameHierarchy_get_genreactivity(GameHierarchy_ptr self)
{
  GAME_HIERARCHY_CHECK_INSTANCE(self);

  return(self->genreactivity_expr);
}

/*---------------------------------------------------------------------------*/
/* Static function definitions                                               */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Private initializer for class GameHierarchy. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ game_hierarchy_deinit ]

******************************************************************************/
void game_hierarchy_init(GameHierarchy_ptr self,
                         FlatHierarchy_ptr player1,
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
                         node_ptr genreactivity)
{
  self->player_1       = player1;
  self->player_2       = player2;
  self->spec_expr      = spec;
  self->ltlspec_expr   = ltlspec;
  self->pslspec_expr   = pslspec;
  self->invarspec_expr = invarspec;
  self->compute_expr   = compute;
  self->reachtarget_expr   = reachtarget;
  self->avoidtarget_expr   = avoidtarget;
  self->reachdeadlock_expr = reachdeadlock;
  self->avoiddeadlock_expr = avoiddeadlock;
  self->buchigame_expr     = buchigame;
  self->ltlgame_expr       = ltlgame;
  self->genreactivity_expr = genreactivity;
}

/**Function********************************************************************

  Synopsis    [ Private deinitalizer for class GameHierarchy. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void game_hierarchy_deinit(GameHierarchy_ptr self)
{
  FlatHierarchy_destroy(self->player_1);
  FlatHierarchy_destroy(self->player_2);

  self->player_1 = FLAT_HIERARCHY(NULL);
  self->player_2 = FLAT_HIERARCHY(NULL);
}
