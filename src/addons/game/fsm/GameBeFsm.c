/**CFile***********************************************************************

  FileName    [ GameBeFsm.c ]

  PackageName [ game.fsm ]

  Synopsis    [ Implementation of class GameBeFsm ]

  Description [ ]

  SeeAlso     [ ]

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

******************************************************************************/

#include "GameBeFsm.h"
#include "GameSexpFsm.h"

#include "enc/be/BeEnc.h"
#include "fsm/be/BeFsm.h"
#include "fsm/sexp/SexpFsm.h"
#include "utils/utils.h"

static char rcsid[] UTIL_UNUSED = "$Id: GameBeFsm.c,v 1.1.2.6 2010-02-10 14:57:17 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Struct*********************************************************************

  Synopsis    [ Game boolean expression FSM, the type exported by this
                package. ]

  Description [ A game boolean expression FSM consists of two usual
                FSMs of the same kind. ]

                See BeFsm_TAG for more info on BeFsm_ptr.

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameBeFsm_TAG {
  BeFsm_ptr player_1;
  BeFsm_ptr player_2;
} GameBeFsm;

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static void game_be_fsm_init ARGS((GameBeFsm_ptr self,
                                   BeFsm_ptr player_1,
                                   BeFsm_ptr player_2));

static void game_be_fsm_deinit ARGS((GameBeFsm_ptr self));

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Class GameBeFsm constructor ]

  Description [ Creates a Game BE FSM from two BE FSMs of players.

                If the mask for enumeratives has not been taken into
                account while building the BeFsms player_1 and
                player_2, then this FSM will not have these
                constraints. ]

  SideEffects [ ]

  SeeAlso     [ GameBeFsm_destroy ]

******************************************************************************/
GameBeFsm_ptr GameBeFsm_create(BeFsm_ptr player_1, BeFsm_ptr player_2)
{
  GameBeFsm_ptr self;

  BE_FSM_CHECK_INSTANCE(player_1);
  BE_FSM_CHECK_INSTANCE(player_2);

  self = ALLOC(GameBeFsm, 1);
  GAME_BE_FSM_CHECK_INSTANCE(self);

  game_be_fsm_init(self, player_1, player_2);

  return self;
}

/**Function********************************************************************

  Synopsis    [ Copy constructor for class GameBeFsm ]

  Description [ Creates a new independent copy of the given FSM
                instance.  The returned instance must be destroyed by
                invoking the class destructor when it is no longer
                needed. ]

  SideEffects [ ]

  SeeAlso     [ GameBeFsm_destroy ]

******************************************************************************/
GameBeFsm_ptr GameBeFsm_copy(GameBeFsm_ptr self)
{
  GameBeFsm_ptr copy;

  GAME_BE_FSM_CHECK_INSTANCE(self);

  game_be_fsm_init(copy,
                   BeFsm_copy(self->player_1),
                   BeFsm_copy(self->player_2));

  return copy;
}

/**Function********************************************************************

  Synopsis    [ Class GameBeFsm constructor ]

  Description [ Creates a new instance of GameBeFsm, getting
                information from an instance of GameSexpFsm.

                If the mask for enumeratives has not been taken into
                account while building the BeFsms player_1 and
                player_2, then this FSM will not have these
                constraints. ]

  SideEffects [ ]

  SeeAlso     [ GameBeFsm_create, GameBeFsm_destroy ]

******************************************************************************/
GameBeFsm_ptr GameBeFsm_create_from_sexp_fsm(BeEnc_ptr be_enc,
                                             const GameSexpFsm_ptr bfsm)
{
  GameBeFsm_ptr self;
  BoolSexpFsm_ptr bsexpfsm1;
  BoolSexpFsm_ptr bsexpfsm2;
  BeFsm_ptr befsm1;
  BeFsm_ptr befsm2;

  BE_ENC_CHECK_INSTANCE(be_enc);
  GAME_SEXP_FSM_CHECK_INSTANCE(bfsm);

  bsexpfsm1 = BOOL_SEXP_FSM(GameSexpFsm_get_player_1(bfsm));
  bsexpfsm2 = BOOL_SEXP_FSM(GameSexpFsm_get_player_2(bfsm));

  befsm1 = BeFsm_create_from_sexp_fsm(be_enc, bsexpfsm1);
  befsm2 = BeFsm_create_from_sexp_fsm(be_enc, bsexpfsm2);

  self = GameBeFsm_create(befsm1, befsm2);

  return self;
}

/**Function********************************************************************

  Synopsis    [ Class GameBeFsm destructor ]

  Description [ ]

  SideEffects [ self will be invalidated ]

  SeeAlso     [ GameBeFsm_create, GameBeFsm_create_from_sexp_fsm ]

******************************************************************************/
void GameBeFsm_destroy(GameBeFsm_ptr self)
{
  GAME_BE_FSM_CHECK_INSTANCE(self);

  game_be_fsm_deinit(self);
  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Returns the BE FSM of the first player ]

  Description [ self keeps ownership of the returned FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
BeFsm_ptr GameBeFsm_get_player_1(const GameBeFsm_ptr self)
{
  GAME_BE_FSM_CHECK_INSTANCE(self);

  return self->player_1;
}


/**Function********************************************************************

  Synopsis    [ Returns the BE FSM of the second player. ]

  Description [ self keeps ownership of the returned FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
BeFsm_ptr GameBeFsm_get_player_2(const GameBeFsm_ptr self)
{
  GAME_BE_FSM_CHECK_INSTANCE(self);

  return self->player_2;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Private service to initialize the internal members. ]

  Description [ ]

  SideEffects [ self will change internally. ]

  SeeAlso     [ ]

******************************************************************************/
static void game_be_fsm_init(GameBeFsm_ptr self,
                             BeFsm_ptr player_1,
                             BeFsm_ptr player_2)
{
  self->player_1 = player_1;
  self->player_2 = player_2;
}

/**Function********************************************************************

  Synopsis    [ Private service to deinitialize the internal members. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_be_fsm_deinit(GameBeFsm_ptr self)
{
  BeFsm_destroy(self->player_1);
  BeFsm_destroy(self->player_2);
}
