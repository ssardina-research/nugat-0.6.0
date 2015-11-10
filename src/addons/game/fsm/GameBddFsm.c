/**CFile***********************************************************************

  FileName    [ GameBddFsm.c ]

  PackageName [ game.fsm ]

  Synopsis    [ Defines the public interface for the class GameBddFsm. ]

  Description [ A GameBddFsm is a BDD representation of the game
                Finite State Machine (FSM). Essentially, a game FSM
                consists of two FSMs of the same kind, one for each
                player. See BddFsm.c for more details. ]

  SeeAlso     [ GameSexpFsm.h ]

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

#include "GameBddFsm.h"

#include "compile/compile.h"
#include "dd/dd.h"
#include "enc/enc.h"
#include "fsm/bdd/BddFsm.h"
#include "trans/bdd/BddTrans.h"
#include "utils/error.h"
#include "utils/utils.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: GameBddFsm.c,v 1.1.2.4 2010-02-08 14:07:32 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Game BDD FSM, the type exported by this package ]

  Description [ A game BDD FSM consists of two usual FSMs of the same
                kind. ]

                See BddFsm_TAG for more info on BddFsm_ptr. ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct GameBddFsm_TAG
{
  BddEnc_ptr enc;
  DDMgr_ptr dd;

  BddFsm_ptr player_1;
  BddFsm_ptr player_2;

  bdd_ptr stateVarCube_1;
  bdd_ptr stateVarCube_2;
  bdd_ptr nextStateVarCube_1;   /* created for efficiency only */
  bdd_ptr nextStateVarCube_2;   /* created for efficiency only */
  bdd_ptr stateFrozenVarCube_1;
  bdd_ptr stateFrozenVarCube_2;

  BddStates withSuccessors_1;   /* states with successor for player 1 */
  BddStates withSuccessors_2;   /* states with successor for player 2 */
  BddStates woSuccessors_1;     /* states without successor for player 1 */
  BddStates woSuccessors_2;     /* states without successor for player 2 */
} GameBddFsm;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
long gameBddFsm_notGoalTotalTime;
long gameBddFsm_andInvar2TotalTime;
long gameBddFsm_moveGoalAndInvar2TotalTime;
long gameBddFsm_trans2TotalTime;
long gameBddFsm_notTrans2TotalTime;
long gameBddFsm_moveInvar1TotalTime;
long gameBddFsm_andInvar1TotalTime;
long gameBddFsm_trans1TotalTime;
long gameBddFsm_andInvar1AndInvar2TotalTime;
long gameBddFsm_totalMoveTotalTime;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static void game_bdd_fsm_init ARGS((GameBddFsm_ptr self,
                                    BddEnc_ptr enc,
                                    BddFsm_ptr player_1,
                                    bdd_ptr stateVarCube_1,
                                    bdd_ptr stateFrozenVarCube_1,
                                    BddFsm_ptr player_2,
                                    bdd_ptr stateVarCube_2,
                                    bdd_ptr stateFrozenVarCube_2));

static void game_bdd_fsm_copy ARGS((const GameBddFsm_ptr self,
                                    GameBddFsm_ptr copy));

static void game_bdd_fsm_deinit ARGS((GameBddFsm_ptr self));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Constructor for GameBddFsm ]

  Description [ Takes two BddFsm, one for every player, and four BDDs
                representing cubes of players' variables. Self becomes
                the owner of these FSMs. The given BDDs are referenced
                by the constructor (the invoker remains their owner).

                Note: stateVarCube_... and stateFrozenVarCube_... are
                cubes of state variables excluding frozen variables,
                and both state and frozen variables, respectively. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_destroy ]

******************************************************************************/
GameBddFsm_ptr GameBddFsm_create(BddEnc_ptr enc,
                                 BddFsm_ptr player_1,
                                 bdd_ptr stateVarCube_1,
                                 bdd_ptr stateFrozenVarCube_1,
                                 BddFsm_ptr player_2,
                                 bdd_ptr stateVarCube_2,
                                 bdd_ptr stateFrozenVarCube_2)
{
  GameBddFsm_ptr self;

  BDD_ENC_CHECK_INSTANCE(enc);
  BDD_FSM_CHECK_INSTANCE(player_1);
  BDD_FSM_CHECK_INSTANCE(player_2);

  self = ALLOC(GameBddFsm, 1);
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  game_bdd_fsm_init(self, enc,
                    player_1, stateVarCube_1, stateFrozenVarCube_1,
                    player_2, stateVarCube_2, stateFrozenVarCube_2);

  nusmv_assert(bdd_is_true(self->dd, BddFsm_get_input_constraints(player_1)) &&
               bdd_is_true(self->dd, BddFsm_get_input_constraints(player_2)));

  return self;
}

/**Function********************************************************************

  Synopsis    [ Destructor of class GameBddFsm. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void GameBddFsm_destroy(GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  game_bdd_fsm_deinit(self);
  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Copy constructor for GameBddFsm. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameBddFsm_ptr GameBddFsm_copy(const GameBddFsm_ptr self)
{
  GameBddFsm_ptr copy;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  copy = ALLOC(GameBddFsm, 1);
  GAME_BDD_FSM_CHECK_INSTANCE(copy);

  game_bdd_fsm_copy(self, copy);

  return copy;
}

/**Function********************************************************************

  Synopsis    [ Returns the BDD FSM of player_1. ]

  Description [ Self keeps the ownership of the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_player_2 ]

******************************************************************************/
BddFsm_ptr GameBddFsm_get_player_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->player_1;
}

/**Function********************************************************************

  Synopsis    [ Returns the BDD FSM of player_2 ]

  Description [ Self keeps the ownership of the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_player_1 ]

******************************************************************************/
BddFsm_ptr GameBddFsm_get_player_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->player_2;
}

/**Function********************************************************************

  Synopsis    [ Returns the cube of state variables of the first
                player. ]

  Description [ This cube is a big AND of all boolean variables of the
                player excluding frozen variables. Self keeps the
                ownership of the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_state_var_cube_2 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_state_var_cube_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->stateVarCube_1;
}

/**Function********************************************************************

  Synopsis    [ Returns the cube of state variables of the second
                player. ]

  Description [ This cube is a big AND of all boolean variables of the
                player excluding frozen variables. Self keeps the
                ownership of the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_state_var_cube_1 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_state_var_cube_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->stateVarCube_2;
}

/**Function********************************************************************

  Synopsis    [ Returns the cube of state variables of the first player
                in the next state. ]

  Description [ This cube is a big AND of all boolean variables of the
                player excluding frozen variables. Self keeps the
                ownership of the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_next_state_var_cube_2 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_next_state_var_cube_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->nextStateVarCube_1;
}

/**Function********************************************************************

  Synopsis    [ Returns the cube of state variables of the second player
                in the next state. ]

  Description [ This cube is a big AND of all boolean variables of the
                player excluding frozen variables. Self keeps the
                ownership of the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_next_state_var_cube_1 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_next_state_var_cube_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->nextStateVarCube_2;
}

/**Function********************************************************************

  Synopsis    [ Returns the cube of state and frozen variables of the
                first player. ]

  Description [ This cube is a big AND of all boolean state and frozen
                variables of the player. Self keeps the ownership of
                the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_state_frozen_var_cube_2 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_state_frozen_var_cube_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->stateFrozenVarCube_1;
}

/**Function********************************************************************

  Synopsis    [ Returns the cube of state and frozen variables of the
                second player. ]

  Description [ This cube is a big AND of all boolean state and frozen
                variables of the player. Self keeps the ownership of
                the returned object. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_state_frozen_var_cube_1 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_state_frozen_var_cube_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return self->stateFrozenVarCube_2;
}

/**Function********************************************************************

  Synopsis    [ Returns init (initial) condition of the first player. ]

  Description [ Returned BDD is referenced. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_init_2 ]

******************************************************************************/
BddStates GameBddFsm_get_init_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_init(self->player_1);
}

/**Function********************************************************************

  Synopsis    [ Returns init (initial) condition of the second player. ]

  Description [ Returned BDD is referenced. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_init_1 ]

******************************************************************************/
BddStates GameBddFsm_get_init_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_init(self->player_2);
}

/**Function********************************************************************

  Synopsis    [ Returns the invars of the first player. ]

  Description [ Returned BDD is referenced. Free it after use. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_invars_2 ]

******************************************************************************/
BddInvarStates GameBddFsm_get_invars_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_state_constraints(self->player_1);
}

/**Function********************************************************************

  Synopsis    [ Returns the invars of the second player. ]

  Description [ Returned BDD is referenced. Free it after use. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_invars_1 ]

******************************************************************************/
BddInvarStates GameBddFsm_get_invars_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_state_constraints(self->player_2);
}

/**Function********************************************************************

  Synopsis    [ Returns the trans of the first player. ]

  Description [ Returned Trans belongs to self, i.e. do not modify or
                delete it.]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_trans_2 ]

******************************************************************************/
BddTrans_ptr GameBddFsm_get_trans_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_trans(self->player_1);
}

/**Function********************************************************************

  Synopsis    [ Returns the trans of the second player. ]

  Description [ Returned Trans belongs to self, i.e. do not modify or
                delete it. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_trans_1 ]

******************************************************************************/
BddTrans_ptr GameBddFsm_get_trans_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_trans(self->player_2);
}

/**Function********************************************************************

  Synopsis    [ Returns the trans of the first player as a monolitic BDD. ]

  Description [ NOTE: invariants are not added to the returned
                transition.

                ADVICE: Probably, GameBddFsm_get_move is required, not
                this function.

                Returned BDD is referenced. Free it after using. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_monolitic_trans_2 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_monolitic_trans_1(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_monolithic_trans_bdd(self->player_1);
}

/**Function********************************************************************

  Synopsis    [ Returns the trans of the second player as a monolitic BDD. ]

  Description [ NOTE: invariants are not added to the returned
                transition.

                ADVICE: Probably, GameBddFsm_get_move is required, not
                this function.

                Returned BDD is referenced. Free it after using. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_get_monolitic_trans_1 ]

******************************************************************************/
bdd_ptr GameBddFsm_get_monolitic_trans_2(const GameBddFsm_ptr self)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);

  return BddFsm_get_monolithic_trans_bdd(self->player_2);
}

/**Function********************************************************************

  Synopsis    [ Returns the set of states that have at least one legal
                successor. ]

  Description [ Paramater player defines for which player the states
                are computed. A state "s" is the result of the
                function if all the following conditions hold: 1) s is
                a state satisfying Invars for both players. 2) there
                is at least one transition from s which is leads to a
                state satisfying Invars for a given player.

                More formally, if p1 are the vars of first player and
                p2 are the vars of the second player then the returned
                states for the first and second player are,
                respectively:

                NS_1 = {<p1,p2> | Invar_1(p1) & Invar_2(p1,p2)
                                  & Exist p1'.Trans_1(p1,p2,p1') & Invar_1(p1')}

                NS_2 =  {<p1,p2,p1'> | Invar_1(p1) & Invar_2(p1,p2)
                                       & Trans_1(p1,p2,p1') & Invar_1(p1')
                                       & Exist p2'.Trans_2(p1,p2,p1',p2')
                                                   & Invar_2(p1',p2')}'

                The returned BDD belongs to this function. ]

  SideEffects [ Internal cache could change. ]

  SeeAlso     [ GameBddFsm_without_successor_states ]

******************************************************************************/
BddStates GameBddFsm_with_successor_states(GameBddFsm_ptr self,
                                           GamePlayer player)
{
  BddStates* withSuccessors;
  BddStates* withoutSuccessors;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  withSuccessors = PLAYER_1 == player
    ? &self->withSuccessors_1 : &self->withSuccessors_2;
  withoutSuccessors = PLAYER_1 == player
    ? &self->woSuccessors_1 : &self->woSuccessors_2;

  /* check the cache. Compute if result has not been computed before */
  if (BDD_STATES(NULL) == *withSuccessors) {
    bdd_ptr constr_1, constr_2, with, without;

    /* with and without successor states are computed here only */
    nusmv_assert((bdd_ptr) NULL == *withoutSuccessors);

    constr_1 = GameBddFsm_get_invars_1(self);
    constr_2 = GameBddFsm_get_invars_2(self);

    if (PLAYER_1 == player) { /* FIRST PLAYER */
      bdd_ptr tmp;
      tmp = BddEnc_state_var_to_next_state_var(self->enc, constr_1);
      with = BddTrans_get_backward_image_state(GameBddFsm_get_trans_1(self),
                                               tmp);
      without = bdd_not(self->dd, with);
      bdd_free(self->dd, tmp);
    }
    else { /* SECOND PLAYER */
      bdd_ptr tmp;
      bdd_ptr trans;
      tmp = BddEnc_state_var_to_next_state_var(self->enc, constr_2);
      with = BddTrans_get_backward_image_state(GameBddFsm_get_trans_2(self),
                                               tmp);
      without = bdd_not(self->dd, with);
      bdd_free(self->dd, tmp);

      tmp = BddEnc_state_var_to_next_state_var(self->enc, constr_1);
      bdd_and_accumulate(self->dd, &with, tmp);
      bdd_and_accumulate(self->dd, &without, tmp);
      bdd_free(self->dd, tmp);

      trans = BddFsm_get_monolithic_trans_bdd(self->player_1);
      bdd_and_accumulate(self->dd, &with, trans);
      bdd_and_accumulate(self->dd, &without, trans);
      bdd_free(self->dd, trans);
    }

    bdd_and_accumulate(self->dd, &with, constr_1);
    bdd_and_accumulate(self->dd, &with, constr_2);
    bdd_and_accumulate(self->dd, &without, constr_1);
    bdd_and_accumulate(self->dd, &without, constr_2);
    *withSuccessors = with;
    *withoutSuccessors = without;

    bdd_free(self->dd, constr_2);
    bdd_free(self->dd, constr_1);
  }

  return *withSuccessors;
}

/**Function********************************************************************

  Synopsis    [ Returns the set of states without successors. ]

  Description [ This method returns the set of states with no
                successor. Paramater 'player' defines for which player
                the no-successor states are computed. A state "ns" has
                no successor if all the following conditions hold: 1)
                ns is a state satisfying Invars for players. 2) no
                transition from ns exists which is leads to a state
                satisfying Invars for players.

                Formally, if p1 are the vars of first player and p2
                are the vars of the second player then the
                no-successor states for the first and second player
                are, respectively:

                NS_1 = {<p1,p2> | Invar_1(p1) & Invar_2(p1,p2)
                                  & not Exist p1'.Trans_1(p1,p2,p1')
                                                  & Invar_1(p1')}

                NS_2 =  {<p1,p2,p1'> | Invar_1(p1) & Invar_2(p1,p2)
                                       & Trans_1(p1,p2,p1') & Invar_1(p1')
                                       & not Exist p2'.Trans_2(p1,p2,p1',p2')
                                                       & Invar_2(p1',p2')}'

                The returned BDD belongs to this function. ]

  SideEffects [ Internal cache could change. ]

  SeeAlso     [ GameBddFsm_with_successor_states ]

******************************************************************************/
BddStates GameBddFsm_without_successor_states(GameBddFsm_ptr self,
                                              GamePlayer player)
{
  BddStates* withoutSuccessors;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  withoutSuccessors = PLAYER_1 == player
    ? &self->woSuccessors_1 : &self->woSuccessors_2;

  /* Check the cache. Compute if result has not been computed before. */
  if (BDD_STATES(NULL) == *withoutSuccessors) {
    GameBddFsm_with_successor_states(self, player);
  }
  nusmv_assert( (bdd_ptr)NULL != *withoutSuccessors);

  return *withoutSuccessors;
}

/**Function********************************************************************

  Synopsis    [ Returns the strong backward image of a set of states. ]

  Description [ This method computes the set of states that have at
                least one legal (satisfying INVAR) successor and such
                that player can force the whole system to take
                transition to the given (input) set of states.

                'player' is a player which forces the whole system to
                take transition to the input set of states.

                The strong backward image of S(P1, P2) is computed as
                follows (P1 and P2 are state vars of player 1 and 2,
                respectively):

                For player 1:
                S_1 (P1, P2) = {<p1, p2> |
                                Invar_1(p1) & Invar_2(p1,p2) &
                                Exist p1'.Tr_1(p1,p2,p1') & Invar_1(p1') &
                                Any p2'.(Tr_2(p1,p2,p1',p2') & Invar_2(p1',p2'))
                                        -> goal(p1',p2')}

                For player 2:
                S_2 (P1, P2) = {<p1, p2> |
                                Invar_1(p1) & Invar_2(p1,p2) &
                                Any p1'.(Tr_1(p1,p2,p1') & Invar_1(p1')) ->
                                Exist p2'.Tr_2(p1,p2,p1',p2')
                                          & Invar_2(p1',p2') & goal(p1',p2')}

                Note: frozen variables do not participate in quantifications.

                The returned BDD is referenced. ]

  SideEffects [ ]

******************************************************************************/
BddStates GameBddFsm_get_strong_backward_image(const GameBddFsm_ptr self,
                                               BddStates goal,
                                               GamePlayer player)
{
  /* Rewriting of the above formulas:

     S_1 = Inv1 & Inv2 & E p1'.Tr1 & Inv1' & not E p2'.Tr2 & Inv2' & not goal

     S_2 = Inv1 & Inv2 & not E p1'.Tr1 & Inv1' & not E p2'.Tr2 & Inv2' & goal
  */

  bdd_ptr tmp, constr_1, constr_2, result;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  long time;

       gameBddFsm_totalMoveTotalTime -= util_cpu_time();
       time = util_cpu_time();


  constr_1 = GameBddFsm_get_invars_1(self);
  constr_2 = GameBddFsm_get_invars_2(self);

  /* depending on the player 'goal' or 'not goal' is used */
  result = PLAYER_1 == player ? bdd_not(self->dd, goal) : bdd_dup(goal);

      gameBddFsm_notGoalTotalTime += util_cpu_time() - time;
      time = util_cpu_time();

  /* Invariants of the next states MUST be added to the constraints,
     i.e.  it is not enough to have invars in the input 'goal'.
     Otherwise, for example, some states would be erroneously removed
     from the result.
  */

  /* add the second player constraints and move to the next state */
  bdd_and_accumulate(self->dd, &result, constr_2);
        gameBddFsm_andInvar2TotalTime += util_cpu_time() - time;
        time = util_cpu_time();
  tmp = BddEnc_state_var_to_next_state_var(self->enc, result);
  bdd_free(self->dd, result);
  result = tmp;
        gameBddFsm_moveGoalAndInvar2TotalTime += util_cpu_time() - time;
        time = util_cpu_time();

  /* apply Exist p2'.Tr_2 and negate. NOTE: there should be no input vars. */
  tmp = BddTrans_get_backward_image_state_input(GameBddFsm_get_trans_2(self),
                                                result);
  bdd_free(self->dd, result);
        gameBddFsm_trans2TotalTime += util_cpu_time() - time;
        time = util_cpu_time();
  result = bdd_not(self->dd, tmp);
  bdd_free(self->dd, tmp);
        gameBddFsm_notTrans2TotalTime += util_cpu_time() - time;
        time = util_cpu_time();

  /* add the first player constraints moved to the next state */
  tmp = BddEnc_state_var_to_next_state_var(self->enc, constr_1);
        gameBddFsm_moveInvar1TotalTime += util_cpu_time() - time;
        time = util_cpu_time();
  bdd_and_accumulate(self->dd, &result, tmp);
  bdd_free(self->dd, tmp);
        gameBddFsm_andInvar1TotalTime += util_cpu_time() - time;
        time = util_cpu_time();

  /* apply Exist p1'.Tr_1. NOTE: there should be no input vars. */
  tmp = BddTrans_get_backward_image_state_input(GameBddFsm_get_trans_1(self),
                                                result);
  bdd_free(self->dd, result);
  /* negate if the game is for player 2 */
  result = PLAYER_2 == player ? bdd_not(self->dd, tmp) : bdd_dup(tmp);
  bdd_free(self->dd, tmp);
        gameBddFsm_trans1TotalTime += util_cpu_time() - time;
        time = util_cpu_time();

  /* apply both constraints on the current state */
  bdd_and_accumulate(self->dd, &result, constr_1);
  bdd_and_accumulate(self->dd, &result, constr_2);
        gameBddFsm_andInvar1AndInvar2TotalTime += util_cpu_time() - time;
        time = util_cpu_time();

  bdd_free(self->dd, constr_1);
  bdd_free(self->dd, constr_2);

  /* this would make the player win only if opponent survive.
     Probably, this is not good because if this is a goal state it may not
     have a transition (i.e. it may be a deadlock and this is OK).
   */
       gameBddFsm_totalMoveTotalTime += util_cpu_time();
  return BDD_STATES(result);
}

/**Function********************************************************************

  Synopsis    [ Returns the weak forward image of a set of states. ]

  Description [ This method computes the set of states that CAN be a
                successor of the given states. Note that parameter
                'states' can potentially have constraints on the
                current as well as on the next states.

                The computed formula (p1,p2 - current variables of
                players 1 and 2, respectively) is:

                next_to_current(Exist p1 p2, states(p1,p2,p1',p2')
                                             & inv1 & trans1 & inv1'
                                             & inv2 & trans2 & inv2')

                Note: frozen variables do not participate in
                quantifications.

                The returned BDD is referenced. ]

  SideEffects [ ]

******************************************************************************/
BddStates GameBddFsm_get_weak_forward_image(const GameBddFsm_ptr self,
                                            BddStates states)
{
  /* The function BddTrans_get_forward_image_state cannot be used
     TWICE (one for every player) because during the second
     application it will introduce the opponent state vars (in
     transtion) which just have been abstracted.
  */

  bdd_ptr constr_1, constr_2, trans_1, trans_2, tmp, result;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  constr_1 = GameBddFsm_get_invars_1(self);
  constr_2 = GameBddFsm_get_invars_2(self);
  trans_1 = BddFsm_get_monolithic_trans_bdd(self->player_1);
  trans_2 = BddFsm_get_monolithic_trans_bdd(self->player_2);

  /* compute the formula
     Exist p1 (Exist p2, tr2 & (tr1 & constr_1 & constr_2 & states))
  */
  tmp = bdd_dup(states);
  bdd_and_accumulate(self->dd, &tmp, constr_1);
  bdd_and_accumulate(self->dd, &tmp, constr_2);
  bdd_and_accumulate(self->dd, &tmp, trans_1);

  result = BddTrans_get_forward_image_state(GameBddFsm_get_trans_2(self), tmp);
  bdd_free(self->dd, tmp);

  tmp = bdd_forsome(self->dd, result, GameBddFsm_get_state_var_cube_1(self));
  bdd_free(self->dd, result);

  /* move to the current state and add the remaining invariants */
  result = BddEnc_next_state_var_to_state_var(self->enc, tmp);
  bdd_free(self->dd, tmp);

  bdd_and_accumulate(self->dd, &result, constr_1);
  bdd_and_accumulate(self->dd, &result, constr_2);

  bdd_free(self->dd, constr_1);
  bdd_free(self->dd, constr_2);
  bdd_free(self->dd, trans_1);
  bdd_free(self->dd, trans_2);

  return BDD_STATES(result);
}

/**Function********************************************************************

  Synopsis    [ Returns a move of a player, which leads to a set of states. ]

  Description [ This method computes the set of current-next states
                which are legal (obey invars), there is (at least one)
                transition from current state to the next one, and the
                next state satisfy the given condition 'toState'.
                More accurately:

                For player 1 the returned formula is

                {<p1,p2,p1'> | Invar_1(p1) & Trans_1(p1,p2,p1')
                               & Invar_1(p1') & Invar_2(p1,p2)
                               & Exist p2',Trans_2(p1,p2,p1',p2')
                                           & Invar_2(p1',p2')
                               & Any p2',(Trans_2(p1,p2,p1',p2')
                                          & Invar_2(p1',p2'))
                                         -> toState(p1',p2') }

                This means that there must be at least one legal
                successor, and ALL possible moves of p2 go to
                'states'.

                For player 2:

                {<p1,p2,p1',p2'> | Invar_1(p1) & Trans_1(p1,p2,p1')
                                   & Invar_1(p1') & Invar_2(p1,p2)
                                   & Trans_2(p1,p2,p1',p2') & Invar_2(p1',p2')
                                   & toState(p1',p2') }

                Note: frozen variables do not participate in
                quantifications.

                The returned BDD is referenced. ]

  SideEffects [ ]

******************************************************************************/
BddStates GameBddFsm_get_move(const GameBddFsm_ptr self,
                              BddStates toState,
                              GamePlayer player)
{
  bdd_ptr tmp, constr_1, constr_2, result;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  constr_1 = GameBddFsm_get_invars_1(self);
  constr_2 = GameBddFsm_get_invars_2(self);

  if (PLAYER_1 == player) {
    /* Any p2', Trans_2(p1,p2,p1',p2') & Invar_2(p1',p2') -> States(p1',p2')
         is the same as
       not Exist p2', trans & invar' & not toState'
    */
    tmp = bdd_not(self->dd, toState);
    bdd_and_accumulate(self->dd, &tmp, constr_2);

    result = BddEnc_state_var_to_next_state_var(self->enc, tmp);
    bdd_free(self->dd, tmp);

    tmp = BddTrans_get_backward_image_state(GameBddFsm_get_trans_2(self),
                                            result);
    bdd_free(self->dd, result);
    result = bdd_not(self->dd, tmp);
    bdd_free(self->dd, tmp);

    bdd_and_accumulate(self->dd,
                       &result,
                       GameBddFsm_with_successor_states(self, PLAYER_2));
   }
  else {
    tmp = bdd_and(self->dd, toState, constr_1);
    bdd_and_accumulate(self->dd, &tmp, constr_2);
    result = BddEnc_state_var_to_next_state_var(self->enc, tmp);
    bdd_free(self->dd, tmp);

    tmp = BddFsm_get_monolithic_trans_bdd(self->player_1);
    bdd_and_accumulate(self->dd, &result, tmp);
    bdd_free(self->dd, tmp);

    tmp = BddFsm_get_monolithic_trans_bdd(self->player_2);
    bdd_and_accumulate(self->dd, &result, tmp);
    bdd_free(self->dd, tmp);

    bdd_and_accumulate(self->dd, &result, constr_1);
    bdd_and_accumulate(self->dd, &result, constr_2);
  }

  bdd_free(self->dd, constr_1);
  bdd_free(self->dd, constr_2);

  return result;
}


/**Function********************************************************************

  Synopsis    [ The function returns true if a given player can satisfy
                (stay in, choose) goal-states taking into account
                interpretation (quantification) of player roles and
                players' constraints. ]

  Description [ The interpretation of players' roles is given by
                parameter "quantifiers" (stored typically in
                opt_game_game_initial_condition).

                The formal description of the result is the following.

                If "quantifiers" is "N" (normal)
                for player 1:
                  Exist p1, constr_1(p1)
                            & Any p2, constr_2(p1,p2) -> GoalStates(p1,p2)
                for player 2:
                  Any p1, constr_1(p1)
                          -> Exist p2, constr_2(p1,p2) & GoalStates(p1,p2)

                If "quantifiers" is "A" (universal)
                for both players
                  Any p1, constr_1(p1)
                          -> (Any p2, constr_2(p1,p2) -> GoalStates(p1,p2))

                If "quantifiers" is "E" (existential)
                for both players
                  Exist p1, constr_1(p1)
                            & Exist p2, constr_2(p1,p2) & GoalStates(p1,p2)

                Note: there is no transition here.

                Note: p1 and p2 are both state and frozen variables.

                Note: all provided constraints must be already
                      conjoined with invariants, i.e.

                      constr_1 <= GameBddFsm_get_invars_1(),
                      constr_2 <= GameBddFsm_get_invars_2(),
                      goalStates <= GameBddFsm_get_invars_1()
                                    & GameBddFsm_get_invars_2().

                Note: all provided bdd_ptr are expected to have
                      current-state and frozen vars only, and contain
                      only the given Game FSM vars. Thus, the result
                      is always a constant. If there are other
                      variables see function
                      GameBddFsm_player_satisfies_from. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_player_satisfies_from ]

******************************************************************************/
EXTERN boolean GameBddFsm_can_player_satisfy(const GameBddFsm_ptr self,
                                             BddStates constr_1,
                                             BddStates constr_2,
                                             BddStates goalStates,
                                             GamePlayer player,
                                             char quantifiers)
{
  /* For developers: if the code of this function changes then
     implementation of GameBddFsm_player_satisfies_from has to be
     changed as well !!!
  */

  DDMgr_ptr dd_manager;
  bdd_ptr tmp, result;
  boolean isOne;
  boolean goalNegation, p2Negation, p1Negation;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  dd_manager = BddEnc_get_dd_manager(self->enc);

  /* The above formulas can be rewritten as
     Interpretation is "N":
       for player 1 : E p1, Cnstr1 & not E p2, Cnstr2 & not Goal
       for player 2 : not E p1, Cnstr1 & not E p2, Cnstr2 & Goal
     Interpretation is "A":
       for both players : not E p1, Cnstr1 & E p2, Cnstr2 & not Goal
     Interpretation is "E":
       for both players : E p1, Cnstr1 & E p2, Cnstr2 & Goal

     The difference is only in negations. Lets identify them.
  */

  switch (quantifiers) {
  case 'N': /* Normal interpretation of initial conditions */
    if (PLAYER_1 == player) {
      p1Negation = false;
      p2Negation = true;
      goalNegation = true;
    }
    else {
      p1Negation = true;
      p2Negation = true;
      goalNegation = false;
    }
    break;

  case 'A': /* Universal interpration of initial conditions */
    p1Negation = true;
    p2Negation = false;
    goalNegation = true;
    break;

  case 'E': /* Existential interpration of initial conditions */
    p1Negation = false;
    p2Negation = false;
    goalNegation = false;
    break;

  default:
    internal_error("unknown intial condition interpretation");
  } /* switch */

  /* negate the goal states */
  result = goalNegation ? bdd_not(dd_manager, goalStates) : bdd_dup(goalStates);

  bdd_and_accumulate(dd_manager, &result, constr_2);
  tmp = bdd_forsome(dd_manager,
                    result,
                    GameBddFsm_get_state_frozen_var_cube_2(self));
  bdd_free(dd_manager, result);

  result = p2Negation ? bdd_not(dd_manager, tmp) : bdd_dup(tmp);
  bdd_free(dd_manager, tmp);

  bdd_and_accumulate(dd_manager, &result, constr_1);

  /* NEW_CODE */
  /* Here is an optimisation:  (E p.G) != 0 <=> G != 0 and
     (not E p.G) != 0 <=> G == 0. I.e. quantification of p1 is not required.
     Benchmarking showed that this code is more efficient.
  */
  isOne = bdd_isnot_false(dd_manager, result);
  if (p1Negation) isOne = !isOne;
  bdd_free(dd_manager, result);

  return isOne;
}

/**Function********************************************************************

  Synopsis    [ The function returns a set of states such that a given
                player can satisfy (stay in, choose) goal-states
                taking into account interpretation (quantification) of
                player roles and players' constraints. ]

  Description [ This function is the same as
                GameBddFsm_can_player_satisfy but instead of returning
                true or false returns a set of states.

                The function has meaning only if there are variables
                not belonging to current-state and frozen variable of
                the given FSM. The players' variables are quantified
                out and the returned BDD can consist only of that
                external or next-state variables.

                See the description of GameBddFsm_can_player_satisfy
                for the exact definition of the result.

                Invoker is responsible to de-reference the returned
                BDD. ]

  SideEffects [ ]

  SeeAlso     [ GameBddFsm_can_player_satisfy ]

******************************************************************************/
EXTERN BddStates GameBddFsm_player_satisfies_from(const GameBddFsm_ptr self,
                                                  BddStates constr_1,
                                                  BddStates constr_2,
                                                  BddStates goalStates,
                                                  GamePlayer player,
                                                  char quantifiers)
{
  /* For developers: this is exactly the same as in
     GameBddFsm_can_player_satisfy except that quantification is
     performed completely and the remaining BDD is returned.

     If the code of this function changes then implementation of
     GameBddFsm_can_player_satisfies has likely to be changed as well
     !!!
  */

  DDMgr_ptr dd_manager;
  bdd_ptr tmp, result;
  boolean goalNegation, p2Negation, p1Negation;

  GAME_BDD_FSM_CHECK_INSTANCE(self);

  dd_manager = BddEnc_get_dd_manager(self->enc);

  /* The above formulas can be rewritten as
     Interpretation is "N":
       for player 1 : E p1, Cnstr1 & not E p2, Cnstr2 & not Goal
       for player 2 : not E p1, Cnstr1 & not E p2, Cnstr2 & Goal
     Interpretation is "A":
       for both players : not E p1, Cnstr1 & E p2, Cnstr2 & not Goal
     Interpretation is "E":
       for both players : E p1, Cnstr1 & E p2, Cnstr2 & Goal

     The difference is only in negations. Lets identify them.
  */

  switch (quantifiers) {
  case 'N': /* Normal interpretation of initial conditions */
    if (PLAYER_1 == player) {
      p1Negation = false;
      p2Negation = true;
      goalNegation = true;
    }
    else {
      p1Negation = true;
      p2Negation = true;
      goalNegation = false;
    }
    break;

  case 'A': /* Universal interpration of initial conditions */
    p1Negation = true;
    p2Negation = false;
    goalNegation = true;
    break;

  case 'E': /* Existential interpration of initial conditions */
    p1Negation = false;
    p2Negation = false;
    goalNegation = false;
    break;

  default:
    internal_error("unknown intial condition interpretation");
  } /* switch */

  /* negate the goal states */
  result = goalNegation ? bdd_not(dd_manager, goalStates) : bdd_dup(goalStates);

  bdd_and_accumulate(dd_manager, &result, constr_2);
  tmp = bdd_forsome(dd_manager,
                    result,
                    GameBddFsm_get_state_frozen_var_cube_2(self));
  bdd_free(dd_manager, result);

  result = p2Negation ? bdd_not(dd_manager, tmp) : bdd_dup(tmp);
  bdd_free(dd_manager, tmp);

  bdd_and_accumulate(dd_manager, &result, constr_1);

  /* --- THIS PART IS DIFFERENT FROM GameBddFsm_can_player_satisfy --- */
  tmp = bdd_forsome(dd_manager,
                    result,
                    GameBddFsm_get_state_frozen_var_cube_1(self));
  bdd_free(dd_manager, result);

  result = p1Negation ? bdd_not(dd_manager, tmp) : bdd_dup(tmp);
  bdd_free(dd_manager, tmp);

  /* Here the result should may be not only a constant TRUE or FALSE,
     because original BDD may contain not only currect-state and
     frozen vars of given FSM.
  */

  return result;
}

/**Function********************************************************************

  Synopsis    [ Prints some information about this GameBddFsm. ]

  Description [ ]

  SideEffects [ None ]

  SeeAlso     [ ]

******************************************************************************/
void GameBddFsm_print_info(const GameBddFsm_ptr self, FILE* file)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);
  nusmv_assert((FILE *) NULL != file);

  fprintf(file, "Statistics on Game BDD FSM.\n");
  fprintf(file, "Statistics on player 1 :\n");
  BddFsm_print_info(self->player_1, file);
  fprintf(file, "Statistics on player 2 :\n");
  BddFsm_print_info(self->player_2, file);
}

/**Function********************************************************************

  Synopsis    [ Performs the synchronous product of two GameBddFsms. ]

  Description [ The product is mostly formed by constructing the
                product of the component BddFsms.

                Note that the component products are formed only on
                the two components respective variable sets.

                The cached fields for states w/, w/o successors are
                reset. ]

  SideEffects [ self will change ]

  SeeAlso     [ BddFsm_apply_synchronous_product_custom_varsets ]

******************************************************************************/
void GameBddFsm_apply_synchronous_product(GameBddFsm_ptr self,
                                          const GameBddFsm_ptr other)
{
  GAME_BDD_FSM_CHECK_INSTANCE(self);
  GAME_BDD_FSM_CHECK_INSTANCE(other);

  /* check for the same encoding and dd manager */
  nusmv_assert(self->enc == other->enc);
  nusmv_assert(self->dd == other->dd);

  /* var cubes: union of players' cubes */
  {
    bdd_ptr tmp;

    tmp = self->stateVarCube_1;
    self->stateVarCube_1 = bdd_cube_union(self->dd,
                                          self->stateVarCube_1,
                                          other->stateVarCube_1);
    bdd_free(self->dd, tmp);
    tmp = self->stateVarCube_2;
    self->stateVarCube_2 = bdd_cube_union(self->dd,
                                          self->stateVarCube_2,
                                          other->stateVarCube_2);
    bdd_free(self->dd, tmp);
    tmp = self->nextStateVarCube_1;
    self->nextStateVarCube_1 = bdd_cube_union(self->dd,
                                              self->nextStateVarCube_1,
                                              other->nextStateVarCube_1);
    bdd_free(self->dd, tmp);
    tmp = self->nextStateVarCube_2;
    self->nextStateVarCube_2 = bdd_cube_union(self->dd,
                                              self->nextStateVarCube_2,
                                              other->nextStateVarCube_2);
    bdd_free(self->dd, tmp);
    tmp = self->stateFrozenVarCube_1;
    self->stateFrozenVarCube_1 = bdd_cube_union(self->dd,
                                                self->stateFrozenVarCube_1,
                                                other->stateFrozenVarCube_1);
    bdd_free(self->dd, tmp);
    tmp = self->stateFrozenVarCube_2;
    self->stateFrozenVarCube_2 = bdd_cube_union(self->dd,
                                                self->stateFrozenVarCube_2,
                                                other->stateFrozenVarCube_2);
    bdd_free(self->dd, tmp);
  }

  /* w, w/o successors cache: reset */
  if (self->withSuccessors_1) {
    bdd_free(self->dd, self->withSuccessors_1);
    self->withSuccessors_1 = BDD_STATES(NULL);
  }
  if (self->withSuccessors_2) {
    bdd_free(self->dd, self->withSuccessors_2);
    self->withSuccessors_2 = BDD_STATES(NULL);
  }
  if (self->woSuccessors_1) {
    bdd_free(self->dd, self->woSuccessors_1);
    self->woSuccessors_1 = BDD_STATES(NULL);
  }
  if (self->woSuccessors_2) {
    bdd_free(self->dd, self->woSuccessors_2);
    self->woSuccessors_2 = BDD_STATES(NULL);
  }

  /* player_1, 2: synchronous product of players */
  {
    bdd_ptr one;

    one = bdd_true(self->dd);
    BddFsm_apply_synchronous_product_custom_varsets(self->player_1,
                                                    other->player_1,
                                                    self->stateVarCube_1,
                                                    one,
                                                    self->nextStateVarCube_1);
    BddFsm_apply_synchronous_product_custom_varsets(self->player_2,
                                                    other->player_2,
                                                    self->stateVarCube_2,
                                                    one,
                                                    self->nextStateVarCube_2);
    bdd_free(self->dd, one);
  }
}

/* ---------------------------------------------------------------------- */
/*                         Static functions                               */
/* ---------------------------------------------------------------------- */

/**Function********************************************************************

  Synopsis    [ Private initializer ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_bdd_fsm_init(GameBddFsm_ptr self,
                              BddEnc_ptr enc,
                              BddFsm_ptr player_1,
                              bdd_ptr stateVarCube_1,
                              bdd_ptr stateFrozenVarCube_1,
                              BddFsm_ptr player_2,
                              bdd_ptr stateVarCube_2,
                              bdd_ptr stateFrozenVarCube_2)
{
  self->enc = enc;
  self->dd = BddEnc_get_dd_manager(enc);
  self->player_1 = player_1;
  self->player_2 = player_2;
  self->stateVarCube_1 = bdd_dup(stateVarCube_1);
  self->stateVarCube_2 = bdd_dup(stateVarCube_2);
  self->nextStateVarCube_1 = BddEnc_state_var_to_next_state_var(enc,
                                                                stateVarCube_1);
  self->nextStateVarCube_2 = BddEnc_state_var_to_next_state_var(enc,
                                                                stateVarCube_2);
  self->stateFrozenVarCube_1 = bdd_dup(stateFrozenVarCube_1);
  self->stateFrozenVarCube_2 = bdd_dup(stateFrozenVarCube_2);

  self->withSuccessors_1 = BDD_STATES(NULL);
  self->withSuccessors_2 = BDD_STATES(NULL);
  self->woSuccessors_1 = BDD_STATES(NULL);
  self->woSuccessors_2 = BDD_STATES(NULL);
}

/**Function********************************************************************

  Synopsis    [ Private copy constructor ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_bdd_fsm_copy(const GameBddFsm_ptr self, GameBddFsm_ptr copy)
{
  copy->enc = self->enc;
  copy->dd = self->dd;
  copy->player_1 = BddFsm_copy(self->player_1);
  copy->player_2 = BddFsm_copy(self->player_2);
  copy->stateVarCube_1 = bdd_dup(self->stateVarCube_1);
  copy->stateVarCube_2 = bdd_dup(self->stateVarCube_2);
  copy->nextStateVarCube_1 = bdd_dup(self->nextStateVarCube_1);
  copy->nextStateVarCube_2 = bdd_dup(self->nextStateVarCube_2);
  copy->stateFrozenVarCube_1 = bdd_dup(self->stateFrozenVarCube_1);
  copy->stateFrozenVarCube_2 = bdd_dup(self->stateFrozenVarCube_2);

  copy->withSuccessors_1 = self->withSuccessors_1 != BDD_STATES(NULL)
    ? bdd_dup(self->withSuccessors_1) : BDD_STATES(NULL);
  copy->withSuccessors_2 = self->withSuccessors_2 != BDD_STATES(NULL)
    ? bdd_dup(self->withSuccessors_2) : BDD_STATES(NULL);
  copy->woSuccessors_1 = self->woSuccessors_1 != BDD_STATES(NULL)
    ? bdd_dup(self->woSuccessors_1) : BDD_STATES(NULL);
  copy->woSuccessors_2 = self->woSuccessors_2 != BDD_STATES(NULL)
    ? bdd_dup(self->woSuccessors_2) : BDD_STATES(NULL);
}


/**Function********************************************************************

  Synopsis    [ Private member called by the destructor ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_bdd_fsm_deinit(GameBddFsm_ptr self)
{
  BddFsm_destroy(self->player_1);
  BddFsm_destroy(self->player_2);
  bdd_free(self->dd, self->stateVarCube_1);
  bdd_free(self->dd, self->stateVarCube_2);
  bdd_free(self->dd, self->nextStateVarCube_1);
  bdd_free(self->dd, self->nextStateVarCube_2);
  bdd_free(self->dd, self->stateFrozenVarCube_1);
  bdd_free(self->dd, self->stateFrozenVarCube_2);

  if (self->withSuccessors_1) bdd_free(self->dd, self->withSuccessors_1);
  if (self->withSuccessors_2) bdd_free(self->dd, self->withSuccessors_2);
  if (self->woSuccessors_1) bdd_free(self->dd, self->woSuccessors_1);
  if (self->woSuccessors_2) bdd_free(self->dd, self->woSuccessors_2);
}
