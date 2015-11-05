/**CFile***********************************************************************

  FileName    [GameStrategy.c]

  PackageName [game]

  Synopsis    [Implementaion of class 'GameStrategy']

  Description [Hold a strategy for some player.]

  SeeAlso     []

  Author      [Andrei Tchaltsev, Viktor Schuppan]

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

#include "game.h"
#include "gameInt.h"
#include "GameStrategy.h"

#include "dd/dd.h"
#include "enc/enc.h"
#include "opt/opt.h"
#include "utils/utils.h"

static char rcsid[] UTIL_UNUSED = "$Id: GameStrategy.c,v 1.1.2.6 2010-02-05 14:08:39 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Struct**********************************************************************

  Synopsis    [ A structure which can store a strategy for a player. ]

  Description [ A strategy defines how the player to whom the strategy
                applies should behave (usually, but not necessarily,
                to win a game).

                The main elements of a strategy are the following 6
                BDDs: init_goal, init_opponent_deadlock, init_moves,
                goal, opponent_deadlock, moves.

                Three BDDs describe how to move in the player\'s very
                first move of the game (init_goal,
                init_opponent_deadlock, and init_moves}) and the three
                others how to continue the game from the player\'s
                second move onwards (goal, opponent_deadlock, and
                moves}).

                Two BDDs state whether a goal state has just been
                reached or how it can be reached (init_goal, goal).
                Two BDDs state how a deadlock of the opponent can be
                enforced (init_opponent_deadlock,
                opponent_deadlock). In both previous cases the game
                either has been won or will be won after performing
                one of the moves contained. The remaining two BDDs
                (init_moves, moves) list moves that (in case of a
                winning strategy) ensure ultimately winning the game,
                but possibly not immediately.

                Depending on the

                - initial condition (N(+1), A(+1), E(+1)),

                - the player (PLAYER_1, PLAYER_2), and

                - the kind of move ((init_)goal,
                  (init_)opponent_deadlock, (init_)moves)

                the variables over which the BDDs are defined can be
                partitioned into two sets, called "condition
                variables" C (renamed from the historical, but
                possibly confusing, "state variables") and "action
                variables" A.

                Given this partition of variables, an assignment x
                making one of the BDDs true is understood as follows
                (where |_ denotes existential projection): if x|_C is
                true, then carry out the assignment x|_A.

                Two special cases are C={} ({} denotes the empty set)
                and A={}. The case C={} is straightforward in that the
                corresponding move may be carried out
                unconditionally. An example is init_moves when player
                = PLAYER_1 and the initial condition is N(+1): there
                is no previous/partial state over which a condition
                could be formulated. The case A={} merely recognizes
                truth of some condition (such as being a goal state)
                but does not necessitate an action. An example here is
                goal when player = PLAYER_1 and the initial condition
                is N(+1): The previous move of PLAYER_2 took the game
                into a goal state and PLAYER_1 has won without any
                further action.

                Below the partition into C and A is explained. p1 and
                p2 stand for current state variables of PLAYER_1 and
                PLAYER_2, next(p1) and next(p2) for next state
                variables of PLAYER_1 and PLAYER_2. + denotes set
                union.

                ======================================================
                init_goal
                ======================================================
                N,N+1

                PLAYER_1: C = {}, A = p1
                          Player 1 only recognizes having won once a
                          goal state has been reached. Hence,
                          init_goal is always false here.

                PLAYER_2: C = p1, A = p2
                          Depending on the choices of player 1, the
                          moves of player 2 that directly reach a goal
                          state.
                ------------------------------------------------------
                A,E+1:    C = p1 + p2, A = {}
                          Here a strategy needs to cover each initial
                          state (the opponent can pick (legal) values
                          for both player 1 and player 2 variables in
                          the initial state). Hence, the player cannot
                          decide which move to make and the variables
                          are only partitioned in order to allow
                          recognition of whether the game already ends
                          after the initial moves or not (here: is in
                          a goal state).
                ------------------------------------------------------
                E,A+1:    C = {}, A = p1 + p2
                          Here a strategy needs to cover only a single
                          initial state (the player can pick (legal)
                          values for both player 1 and player 2
                          variables in the initial state). Hence, both
                          player 1 and player 2 variables are action
                          variables. The partitioning allows
                          recognition of which moves end the game
                          already after the initial moves (here: is in
                          a goal state).
                ======================================================

                ======================================================
                init_opponent_deadlock
                ======================================================
                N,N+1

                PLAYER_1: C = {}, A = p1
                          The moves of player 1 that s.t. subsequently
                          player 2 has no legal move.

                PLAYER_2: C = p1, A = p2
                          Depending on the choices of player 1, the
                          moves of player 2 s.t. player 1 subsequently
                          has no legal move.
                ------------------------------------------------------
                A,E+1

                PLAYER_1: C = p1 + p2, A = {}
                          The strategy needs to be valid only for
                          combinations of legal player 1 and player 2
                          initial states. Hence, a player 1 initial
                          state that is a deadlock for player 2 does
                          not need to be covered and, therefore,
                          init_opponent_deadlock is always false here.

                PLAYER_2: C = p1 + p2, A = {}
                          Analogous to init_goal.
                ------------------------------------------------------
                E,A+1

                PLAYER_1: C = {}, A = p1 + p2
                          The strategy needs to be valid for some
                          combination of legal player 1 and player 2
                          initial states. Hence, a player 1 initial
                          state that is a deadlock for player 2 makes
                          no sense and, therefore,
                          init_opponent_deadlock is always false here.

                PLAYER_2: C = {}, A = p1 + p2
                          Analogous to init_goal.
                ======================================================

                ======================================================
                init_moves
                ======================================================
                N,N+1

                PLAYER_1: C = {}, A = p1
                          The moves of player 1 that, when following
                          the strategy, let him win (but not
                          necessarily right after this move).

                PLAYER_2: C = p1, A = p2
                          Depending on the choices of player 1, the
                          moves of player 2 that, when following the
                          strategy, let him win (but not necessarily
                          right after this move).
                ------------------------------------------------------
                A,E+1:    C = p1 + p2, A = {}
                          Analogous to init_goal.
                ------------------------------------------------------
                E,A+1:    C = {}, A = p1 + p2
                          Analogous to init_goal.
                ======================================================

                ======================================================
                goal
                ======================================================
                PLAYER_1: C = p1 + p2, A = {}
                          The states that are goal states. I.e.,
                          player 1 has just won the game without
                          making any further move.

                PLAYER_2: C = p1 + p2 + next(p1), A = next(p2)
                          Depending on the current state and the
                          choices of player 1, the moves of player 2
                          that directly reach a goal state.
                ======================================================

                ======================================================
                opponent_deadlock
                ======================================================
                PLAYER_1: C = p1 + p2, A = next(p1)
                          Depending on the current state, the moves of
                          player 1 s.t. player 2 subsequently has no
                          legal move.

                PLAYER_2: C = p1 + p2 + next(p1), A = next(p2)
                          Depending on the current state and the
                          choices of player 1, the moves of player 2
                          s.t. player 1 subsequently has no legal
                          move.
                ======================================================

                ======================================================
                moves
                ======================================================
                PLAYER_1: C = p1 + p2, A = next(p1)
                          Depending on the current state, the moves of
                          player 1 that, when following the strategy,
                          let him win (but not necessarily right after
                          this move).

                PLAYER_2: C = p1 + p2 + next(p1), A = next(p2)
                          Depending on the current state and the
                          choices of player 1, the moves of player 2
                          that, when following the strategy, let him
                          win (but not necessarily right after this
                          move).
                ======================================================

              ]

  SeeAlso     [ ]

******************************************************************************/
struct GameStrategy_TAG {

  BddEnc_ptr bdd_enc;

  DdManager* dd_manager;

  /* Which player this strategy belongs to (1 or 2). */
  GamePlayer player;

  /* A flag that initial quantifiers must be reversed during
     printing. This is used when a strategy is created for an
     opponent */
  boolean reverseInitialQuantifiers;

  /* See above. */
  bdd_ptr init_goal;
  bdd_ptr init_opponent_deadlock;
  bdd_ptr init_moves;
  bdd_ptr goal;
  bdd_ptr opponent_deadlock;
  bdd_ptr moves;
};
typedef struct GameStrategy_TAG GameStrategy;

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

EXTERN FILE* nusmv_stdout;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void game_strategy_init ARGS((GameStrategy_ptr self,
                                     BddEnc_ptr bdd_enc,
                                     GamePlayer player,
                                     boolean reverseInitialQuantifiers,
                                     bdd_ptr init_goal,
                                     bdd_ptr init_opponent_deadlock,
                                     bdd_ptr init_moves,
                                     bdd_ptr goal,
                                     bdd_ptr opponent_deadlock,
                                     bdd_ptr moves));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Constructor for class GameStrategy ]

  Description [ All BDDs are referenced locally, i.e., caller retains
                ownership. The constructor is "dumb" in that it only
                assigns the constructor arguments to the fields of the
                struct. ]

  SideEffects [ ]

  SeeAlso     [ GameStrategy_destroy, GameStrategy_construct ]

******************************************************************************/
GameStrategy_ptr GameStrategy_create(BddEnc_ptr bdd_enc,
                                     GamePlayer player,
                                     boolean reverseInitialQuantifiers,
                                     bdd_ptr init_goal,
                                     bdd_ptr init_opponent_deadlock,
                                     bdd_ptr init_moves,
                                     bdd_ptr goal,
                                     bdd_ptr opponent_deadlock,
                                     bdd_ptr moves)
{
  GameStrategy_ptr self = ALLOC(GameStrategy, 1);
  GAME_STRATEGY_CHECK_INSTANCE(self);

  game_strategy_init(self,
                     bdd_enc,
                     player,
                     reverseInitialQuantifiers,
                     init_goal,
                     init_opponent_deadlock,
                     init_moves,
                     goal,
                     opponent_deadlock,
                     moves);

  return self;
}

/**Function********************************************************************

  Synopsis    [ Destructor of class GameStrategy ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ GameStrategy_create ]

******************************************************************************/
void GameStrategy_destroy(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  bdd_free(self->dd_manager, self->init_goal);
  bdd_free(self->dd_manager, self->init_opponent_deadlock);
  bdd_free(self->dd_manager, self->init_moves);
  bdd_free(self->dd_manager, self->goal);
  bdd_free(self->dd_manager, self->opponent_deadlock);
  bdd_free(self->dd_manager, self->moves);

  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Constructor for class GameStrategy ]

  Description [ This constructor is designed to be used after having
                checked a game property.

                player - is the player the game was played for.

                reverseInitialQuantifiers - is a flag that the
                  strategy is computed for the opponent and it is
                  necessary to change quantifiers to the opposite
                  values.

                goal - a set of goal states (if they are reached a
                  game is considered winning).

                winningStates - is the set of all the states the game
                  can be won from (including opponent deadlocks).

                trans - is the set of transitions which allow the
                  player to win the game.

                Note: both winningStates and trans can be zero Bdd if
                game is won with the help of initial conditions only
                (i.e. the opponent initial condition is zero).

                Caller retains ownership of all arguments. ]

  SideEffects [ ]

  SeeAlso     [ GameStrategy_destroy, GameStrategy_construct,
                Game_UseStrongReachabilityAlgorithm,
                game_use_reachability_approximation,
                game_compute_gen_reactivity, game_compute_buchi_game ]

******************************************************************************/
GameStrategy_ptr GameStrategy_construct(GameBddFsm_ptr fsm,
                                        GamePlayer player,
                                        boolean reverseInitialQuantifiers,
                                        bdd_ptr goal,
                                        bdd_ptr winningStates,
                                        bdd_ptr trans)
{
    /* Note for future implementation: the strategy can potentially be
       liminited to reachable states only. This is not required but
       decreases the outputted strategy.

       Since player's moves can be limited to one value (for
       particular state) only the reachable states can be recomputed
       in a better way. Now a simpler version of reachable states is computed.
    */

  GameStrategy_ptr self;
  bdd_ptr init_1;
  bdd_ptr init_2;
  bdd_ptr opponentDeadlock;
  bdd_ptr reachable;

  GAME_BDD_FSM_CHECK_INSTANCE(fsm);

  self = ALLOC(GameStrategy, 1);
  GAME_STRATEGY_CHECK_INSTANCE(self);

  self->bdd_enc = Enc_get_bdd_encoding();
  self->dd_manager = BddEnc_get_dd_manager(self->bdd_enc);
  self->player = player;
  self->reverseInitialQuantifiers = reverseInitialQuantifiers;

  /* prepare the initial states (obtain them and add the invariants) */
  {
    bdd_ptr invar_1;
    bdd_ptr invar_2;

    init_1 = GameBddFsm_get_init_1(fsm);
    init_2 = GameBddFsm_get_init_2(fsm);
    invar_1 = GameBddFsm_get_invars_1(fsm);
    invar_2 = GameBddFsm_get_invars_2(fsm);

    bdd_and_accumulate(self->dd_manager, &init_1, invar_1);
    bdd_and_accumulate(self->dd_manager, &init_2, invar_2);

    bdd_free(self->dd_manager, invar_1);
    bdd_free(self->dd_manager, invar_2);
  }

  opponentDeadlock = GameBddFsm_without_successor_states(fsm,
                                                         (player == PLAYER_1 ?
                                                          PLAYER_2 :
                                                          PLAYER_1));

  /* reachable states. Currectly, the computation of reachable states
     is not perfect because it does not take into account that the
     action value can be limited to one value for a particular state
  */
  reachable = bdd_and(self->dd_manager, init_1, init_2);

  /* INIT-GOAL, INIT-MOVE, INIT-OPPONENT-DEADLOCK */
  /* Here a hack is used: reverseInitialQuantifiers is added
     to opt_game_game_initial_condition. So there can be 6 values,
     N, N+1, E, E+1, A, A+1, and they are all distinguishable.
  */
  switch (opt_game_game_initial_condition(OptsHandler_create()) +
          reverseInitialQuantifiers) {
  case 'N':    /* normal initial condition. */
  case 'N' + 1:
    {
      /* Note that parameter reverseInitialQuantifiers does not
         influence quantifers here since changing a player
         automatically changes quantifiers as required, i.e. Normal
         for player 1 is Exist-Any, and for player 2 is Any-Exist.
      */
      if (PLAYER_1 == player) {
        bdd_ptr tmp, state;

        /* INIT-GOAL */
        self->init_goal = bdd_false(self->dd_manager);

        /* INIT-OPPONENT-DEADLOCK:
           Init1 & Invar1 & not Exist p2, Init2 & Invar2.

           p2 consists of state and frozen variables */
        tmp = bdd_forsome(self->dd_manager,
                          init_2,
                          GameBddFsm_get_state_frozen_var_cube_2(fsm));
        state = bdd_not(self->dd_manager, tmp);
        bdd_free(self->dd_manager, tmp);
        bdd_and_accumulate(self->dd_manager, &state, init_1);
        self->init_opponent_deadlock = state;

        /* INIT-MOVES:
           Init1 & Invar1 & (Any p2, Init2 & Invar2 -> WinStates) &
           Exist p2 Init2 & Invar2.

           p2 consists of state and frozen variables.
        */
        tmp = bdd_imply(self->dd_manager, init_2, winningStates);
        state = bdd_forall(self->dd_manager,
                           tmp,
                           GameBddFsm_get_state_frozen_var_cube_2(fsm));
        bdd_free(self->dd_manager, tmp);
        tmp = bdd_not(self->dd_manager, self->init_opponent_deadlock);
        bdd_and_accumulate(self->dd_manager, &state, tmp);
        bdd_free(self->dd_manager, tmp);
        bdd_and_accumulate(self->dd_manager, &state, init_1);
        /* constrain init-move to 1 arbitrary value, since one
           path only is required for stratergy
        */
        tmp = bdd_get_one_sparse_sat(self->dd_manager, state);
        bdd_free(self->dd_manager, state);
        self->init_moves = tmp;

        /* compute reachable states */
        bdd_and_accumulate(self->dd_manager, &reachable, self->init_moves);
      }
      else { /* PLAYER_2 */
        bdd_ptr tmp, state;

        /* INIT-GOAL: Init1 & Invar1 & Init2 & Invar2 & goal */
        self->init_goal = bdd_and(self->dd_manager, reachable, goal);

        /* INIT-OPPONENT-DEADLOCK:
           Init1 & Invar1 & Init2 & Invar2 & opponent-deadlock &
           WinStates & not Goal

           WinStates is required because not all the deadlock states
           may be good (for example, for avoid-target spec).
        */
        state = bdd_and(self->dd_manager, reachable, opponentDeadlock);
        bdd_and_accumulate(self->dd_manager, &state, winningStates);
        tmp = bdd_not(self->dd_manager, goal);
        bdd_and_accumulate(self->dd_manager, &state, tmp);
        bdd_free(self->dd_manager, tmp);
        self->init_opponent_deadlock = state;

        /* INIT-MOVES:
           Init1 & Invar1 & Init2 & Invar2 & winning & not Goal & not
           opponent-deadlock
        */
        state = bdd_and(self->dd_manager, reachable, winningStates);
        tmp = bdd_not(self->dd_manager, goal);
        bdd_and_accumulate(self->dd_manager, &state, tmp);
        bdd_free(self->dd_manager, tmp);
        tmp = bdd_not(self->dd_manager, opponentDeadlock);
        bdd_and_accumulate(self->dd_manager, &state, tmp);
        bdd_free(self->dd_manager, tmp);
        self->init_moves = state;

        /* reachable are those reached at initial states */
        bdd_free(self->dd_manager, reachable);
        reachable = bdd_dup(self->init_moves);
      }
      break;
    }

  case 'A': /* universal initial condition */
  case 'E' + 1:
    {
      bdd_ptr tmp;

      /* INIT-GOAL: Init1 & Invar1 & Init2 & Invar2 & goal */
      self->init_goal = bdd_and(self->dd_manager, reachable, goal);

      /* INIT-OPPONENT-DEADLOCK:
         Init1 & Invar1 & Init2 & Invar2 & opponent-deadlock &
         WinStates

         WinStates is required because not all the deadlock states may
         be good (for example, for avoid-target spec).
      */
      if (PLAYER_1 == player) {
        /* deadlock of player 2 are dealt by usual state-actions */
        self->init_opponent_deadlock = bdd_false(self->dd_manager);
      }
      else {
        self->init_opponent_deadlock = bdd_and(self->dd_manager,
                                               reachable,
                                               opponentDeadlock);
        bdd_and_accumulate(self->dd_manager,
                           &self->init_opponent_deadlock,
                           winningStates);
      }

      /* INIT-MOVES: zero. there is no action before initial state */
      self->init_moves = bdd_false(self->dd_manager);

      /* restrict reachable to "not deadlock" and "not goal" */
      tmp = bdd_not(self->dd_manager, goal);
      bdd_and_accumulate(self->dd_manager, &reachable, tmp);
      bdd_free(self->dd_manager, tmp);
      tmp = bdd_not(self->dd_manager, self->init_opponent_deadlock);
      bdd_and_accumulate(self->dd_manager, &reachable, tmp);
      bdd_free(self->dd_manager, tmp);
    }
    break;

  case 'E': /* existential initial condition */
  case 'A' + 1:
    {
      bdd_ptr state, tmp;

      /* INIT-GOAL: Init1 & Invar1 & Init2 & Invar2 & goal */
      self->init_goal = bdd_and(self->dd_manager, reachable, goal);

      /* INIT-OPPONENT-DEADLOCK:
         Init1 & Invar1 & Init2 & Invar2 & opponent-deadlock &
         WinStates

         WinStates is required because not all the deadlock states may
         be good (for example, for avoid-target spec).
      */
      if (PLAYER_1 == player) {
        /* deadlock of player 2 are dealt by usual state-actions */
        self->init_opponent_deadlock = bdd_false(self->dd_manager);
      }
      else {
        self->init_opponent_deadlock = bdd_and(self->dd_manager,
                                               reachable,
                                               opponentDeadlock);
        bdd_and_accumulate(self->dd_manager,
                           &self->init_opponent_deadlock,
                           winningStates);
        /* since quantifiers are existential only one value is required */
        if (bdd_isnot_false(self->dd_manager, self->init_opponent_deadlock)) {
          bdd_free(self->dd_manager, reachable);
          reachable = bdd_false(self->dd_manager);
        }
      }

      /* INIT-MOVES:
         Init1 & Invar1 & Init2 & Invar2 & winning & not Goal & not
         opponent-deadlock
      */
      state = bdd_and(self->dd_manager, reachable, winningStates);
      tmp = bdd_not(self->dd_manager, goal);
      bdd_and_accumulate(self->dd_manager, &state, tmp);
      bdd_free(self->dd_manager, tmp);
      tmp = bdd_not(self->dd_manager, self->init_opponent_deadlock);
      bdd_and_accumulate(self->dd_manager, &state, tmp);
      bdd_free(self->dd_manager, tmp);
      /* constrain init-move to 1 arbitrary value, since one
         path only is required for stratergy
      */
      tmp = bdd_get_one_sparse_sat(self->dd_manager, state);
      bdd_free(self->dd_manager, state);
      self->init_moves = tmp;

      /* reachable are those reached at initial states */
      bdd_free(self->dd_manager, reachable);
      reachable = bdd_dup(self->init_moves);
    }
    break;

  /* unknown interpretation of initial conditions */
  default: nusmv_assert(false);
  } /* switch */

  /* recompute reachable states.
     Here the actions are not contrained to one value (but could be for
     better results, smaller strategy).
     If this will be implemented check that it with the introduction
     of additional variables in trans does not corrupt the strategy.
  */
  {
    bdd_ptr prevReachable = bdd_false(self->dd_manager);

    while (prevReachable != reachable) {
      bdd_free(self->dd_manager, prevReachable);
      prevReachable = reachable;
      /* Note: trans cannot be used here because it may contains
         additional vars not from the Game FSM */
      reachable = GameBddFsm_get_weak_forward_image(fsm, reachable);
      bdd_and_accumulate(self->dd_manager, &reachable, winningStates);
      bdd_or_accumulate(self->dd_manager, &reachable, prevReachable);
    }

    bdd_free(self->dd_manager, prevReachable);
  }

  /* GOAL, MOVES, OPPONENT-DEADLOCK */
  if (PLAYER_1 == player) {
    /* ------------      FIRST PLAYER     --------------------*/
    bdd_ptr state;

    /* GOAL: goal & reachable */
    self->goal = bdd_and(self->dd_manager, goal, reachable);

    /* OPPONENT-DEADLOCK: deadlock & reachable & not goal*/
    state = bdd_not(self->dd_manager, goal);
    bdd_and_accumulate(self->dd_manager, &state, reachable);
    bdd_and_accumulate(self->dd_manager, &state, opponentDeadlock);
    self->opponent_deadlock = state;

    /* MOVES: all the legal moves from reachable states and NOT to goal
       or opponent-deadlock */
    state = bdd_not(self->dd_manager, opponentDeadlock);
    self->moves = bdd_and(self->dd_manager, trans, state);
    bdd_free(self->dd_manager, state);
    state = bdd_not(self->dd_manager, goal);
    bdd_and_accumulate(self->dd_manager, &self->moves, state);
    bdd_free(self->dd_manager, state);
    bdd_and_accumulate(self->dd_manager, &self->moves, reachable);
  } /* end of FIRST PLAYER */
  else {
    /* ----------------  SECOND PLAYER --------------------*/
    bdd_ptr tmp, moves, nextGoal, nextDeadlock;

    /* constrain trans to reachable states only */
    nextGoal = BddEnc_state_var_to_next_state_var(self->bdd_enc, goal);
    nextDeadlock = BddEnc_state_var_to_next_state_var(self->bdd_enc,
                                                      opponentDeadlock);

    /* limit trans to reachable states only */
    moves = bdd_and(self->dd_manager, trans, reachable);

    /* GOAL: moves to goal */
    self->goal = bdd_and(self->dd_manager, moves, nextGoal);

    /* OPPONENT-DEADLOCK: moves to opponent deadlocks */
    tmp = bdd_not(self->dd_manager, nextGoal);
    bdd_and_accumulate(self->dd_manager, &nextDeadlock, tmp);
    bdd_free(self->dd_manager, tmp);
    self->opponent_deadlock = bdd_and(self->dd_manager, moves, nextDeadlock);

    /* MOVES: clean from moves to deadlocks and goals */
    tmp = bdd_not(self->dd_manager, nextGoal);
    bdd_and_accumulate(self->dd_manager, &moves, tmp);
    bdd_free(self->dd_manager, tmp);
    tmp = bdd_not(self->dd_manager, nextDeadlock);
    bdd_and_accumulate(self->dd_manager, &moves, tmp);
    bdd_free(self->dd_manager, tmp);
    self->moves = moves;

    bdd_free(self->dd_manager, nextDeadlock);
    bdd_free(self->dd_manager, nextGoal);
  }/* end of SECOND PLAYER */

  bdd_free(self->dd_manager, init_1);
  bdd_free(self->dd_manager, init_2);

  return self;
}

/**Function********************************************************************

  Synopsis    [ Getter for bdd_enc ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
BddEnc_ptr GameStrategy_get_bdd_enc(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return self->bdd_enc;
}

/**Function********************************************************************

  Synopsis    [ Getter for player ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GamePlayer GameStrategy_get_player(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return self->player;
}

/**Function********************************************************************

  Synopsis    [ Getter for init_goal ]

  Description [ Result is referenced, i.e., caller obtains ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
bdd_ptr GameStrategy_get_init_goal(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return bdd_dup(self->init_goal);
}

/**Function********************************************************************

  Synopsis    [ Getter for init_opponent_deadlock ]

  Description [ Result is referenced, i.e., caller obtains ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
bdd_ptr GameStrategy_get_init_opponent_deadlock(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return bdd_dup(self->init_opponent_deadlock);
}

/**Function********************************************************************

  Synopsis    [ Getter for init_moves ]

  Description [ Result is referenced, i.e., caller obtains ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
bdd_ptr GameStrategy_get_init_moves(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return bdd_dup(self->init_moves);
}

/**Function********************************************************************

  Synopsis    [ Getter for goal ]

  Description [ Result is referenced, i.e., caller obtains ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
bdd_ptr GameStrategy_get_goal(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return bdd_dup(self->goal);
}

/**Function********************************************************************

  Synopsis    [ Getter for opponent_deadlock ]

  Description [ Result is referenced, i.e., caller obtains ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
bdd_ptr GameStrategy_get_opponent_deadlock(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return bdd_dup(self->opponent_deadlock);
}

/**Function********************************************************************

  Synopsis    [ Getter for moves ]

  Description [ Result is referenced, i.e., caller obtains ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
bdd_ptr GameStrategy_get_moves(GameStrategy_ptr self)
{
  GAME_STRATEGY_CHECK_INSTANCE(self);

  return bdd_dup(self->moves);
}

/**Function********************************************************************

  Synopsis    [ Prints the strategy generated by game specification
                checking functions (such as
                game_compute_strong_reach_strategy) as a NuSMV
                module. ]

  Description [ Builds and prints a strategy module for a game
                problem. The newly created strategy module will be
                called "STRATEGY_MODULE n", being n a unique
                auto-incremented natural number.

                'vars' contains the variables for printing. Its subset
                vars_to_decls contains variables for the strategy that
                need to be declared. Caller retains ownership of both
                lists.

                If the initial condition of the game is N(+1), then
                the resulting strategy module can be simply put in
                parallel with the corresponding player. However, if
                the initial condition is A(+1) or E(+1) and the player
                is PLAYER_1, then the initial condition might also
                contain player 2 variables. In that case (and also in
                the case N(+1)) the strategy module can be used as
                follows:
                - Turn the game into a standard NuSMV module by
                  merging both players.
                - Form the synchronous product of that module and the
                  strategy module.
                Now one can, e.g., perform simulation or verification. ]

  SideEffects [ Prints the strategy module. ]

  SeeAlso     [ ]

******************************************************************************/
void GameStrategy_print_module(GameStrategy_ptr self,
                               NodeList_ptr vars,
                               NodeList_ptr vars_to_decl,
                               gameParams_ptr params)
{
  /* an internal static autoincrement variable */
  static int module_incr_number = 0;

  SymbTable_ptr st;
  FILE* out;
  boolean do_sharing;
  boolean do_indentation;

  GAME_STRATEGY_CHECK_INSTANCE(self);
  NODE_LIST_CHECK_INSTANCE(vars);
  NODE_LIST_CHECK_INSTANCE(vars_to_decl);

  st = BaseEnc_get_symb_table(BASE_ENC(self->bdd_enc));
  out = ((params != (gameParams_ptr) NULL) &&
         (params->strategy_stream != (FILE*) NULL)) ?
    params->strategy_stream :
    nusmv_stdout;
  do_sharing = ((params != (gameParams_ptr) NULL) &&
                params->printout_as_dag);
  do_indentation = ((params != (gameParams_ptr) NULL) &&
                    params->indented_printout);

  fprintf(out, "MODULE STRATEGY_MODULE%d\n\n", ++module_incr_number);

  /* declare variables */
  if (NodeList_get_length(vars_to_decl) != 0) {
    ListIter_ptr iter;

    fprintf(out, "VAR\n");
    NODE_LIST_FOREACH(vars_to_decl, iter) {
      node_ptr var_name;
      SymbType_ptr var_type;

      var_name = NodeList_get_elem_at(vars_to_decl, iter);
      var_type = SymbTable_get_var_type(st, var_name);
      fprintf(out, "  ");
      print_node(out, var_name);
      fprintf(out, ": ");
      SymbType_print(var_type, out);
      fprintf(out, ";\n");
    }
    fprintf(out, "\n");
  }

  /* Print initial moves. */
  {
    /* OR the BDDs for the INIT section */
    bdd_ptr init_bdd = bdd_dup(self->init_goal);
    bdd_or_accumulate(self->dd_manager,
                      &init_bdd,
                      self->init_opponent_deadlock);
    bdd_or_accumulate(self->dd_manager, &init_bdd, self->init_moves);

    /* print'em out */
    const char *init_str = "INIT ";
    fprintf(out, "%s", init_str);
    BddEnc_print_bdd_wff(self->bdd_enc,
                         init_bdd,
                         vars,
                         do_sharing,
                         do_indentation,
                         strlen(init_str),
                         out);
    fprintf(out, "\n");

    bdd_free(self->dd_manager, init_bdd);
  }

  /* Print non-initial moves. */
  {
    /* OR the BDDs for the TRANS section */
    bdd_ptr trans_bdd = bdd_dup(self->goal);
    bdd_or_accumulate(self->dd_manager, &trans_bdd, self->opponent_deadlock);
    bdd_or_accumulate(self->dd_manager, &trans_bdd, self->moves);

    /* print'em out */
    const char *trans_str = "TRANS ";
    fprintf(out, "%s", trans_str);
    BddEnc_print_bdd_wff(self->bdd_enc,
                         trans_bdd,
                         vars,
                         do_sharing,
                         do_indentation,
                         strlen(trans_str),
                         out);
    fprintf(out, "\n");

    bdd_free(self->dd_manager, trans_bdd);
  }
}

/*---------------------------------------------------------------------------*/
/* Static function definitions                                               */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Private initializer for class GameStrategy ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void game_strategy_init(GameStrategy_ptr self,
                               BddEnc_ptr bdd_enc,
                               GamePlayer player,
                               boolean reverseInitialQuantifiers,
                               bdd_ptr init_goal,
                               bdd_ptr init_opponent_deadlock,
                               bdd_ptr init_moves,
                               bdd_ptr goal,
                               bdd_ptr opponent_deadlock,
                               bdd_ptr moves)
{
  self->bdd_enc = bdd_enc;
  self->dd_manager = BddEnc_get_dd_manager(self->bdd_enc);
  self->player = player;
  self->reverseInitialQuantifiers = reverseInitialQuantifiers;
  self->init_goal = bdd_dup(init_goal);
  self->init_opponent_deadlock = bdd_dup(init_opponent_deadlock);
  self->init_moves = bdd_dup(init_moves);
  self->goal = bdd_dup(goal);
  self->opponent_deadlock = bdd_dup(opponent_deadlock);
  self->moves = bdd_dup(moves);
}

/**AutomaticEnd***************************************************************/
