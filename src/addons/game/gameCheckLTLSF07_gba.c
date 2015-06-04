/**CFile***********************************************************************

  FileName    [ gameCheckLTLSF07_gba.c ]

  PackageName [ game ]

  Synopsis    [ Implements an explicit, state-labeled generalized B\"uchi
                automaton. ]

  Description [ States and transitions are given explicitly as
                lists. The set of initial states is a
                hash_map. Fairness constraints is a list of hash
                maps.

                Note: this is not some fancy general-purpose
                implementation designed to support all kinds of things
                efficiently but basically just a data structure to
                hold the elements of a GBA as needed in the SF07
                algorithm. That's also why sets of states and
                transitions are just lists w/o efficient membership
                checks. ]

  SeeAlso     [ ]

  Author      [ Viktor Schuppan ]

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

#include "gameCheckLTLSF07_gba.h"

#include "node/node.h"
#include "utils/utils.h"
#include "utils/Slist.h"
#include "utils/assoc.h"
#include "utils/ustring.h"

static char rcsid[] UTIL_UNUSED = "$Id: gameCheckLTLSF07_gba.c,v 1.1.2.3 2010-02-08 12:06:25 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/**Struct**********************************************************************

  Synopsis    [ State of a GBA. ]

  Description [ Fields:

                id - identifier of this state as a string. Considered
                  to be unique, i.e., states are compared based on
                  this; owned but shared;

                label - label as conjunction of literals; owned but
                  shared;

                incoming - list of incoming transitions; list owned
                  but not its members;

                outgoing - list of outgoing transitions; list owned
                  but not its members. ]

  SeeAlso     [ Game_SF07_gba_transition, Game_SF07_gba ]

******************************************************************************/
typedef struct Game_SF07_gba_state_TAG {
  /* identifier; owned but shared */
  string_ptr id;

  /* label as conjunction of literals; owned but shared */
  node_ptr label;

  /* list of incoming transitions; list owned; list members not owned */
  Slist_ptr incoming;

  /* list of outgoing transitions; list owned; list members not owned */
  Slist_ptr outgoing;
} Game_SF07_gba_state;

/**Struct**********************************************************************

  Synopsis    [ Transition of a GBA. ]

  Description [ Fields:

                source - source state; not owned;

                target - target state; not owned. ]

  SeeAlso     [ Game_SF07_gba_state, Game_SF07_gba ]

******************************************************************************/
typedef struct Game_SF07_gba_transition_TAG {
  /* source state; not owned */
  Game_SF07_gba_state_ptr source;

  /* target state; not owned */
  Game_SF07_gba_state_ptr target;
} Game_SF07_gba_transition;

/**Struct**********************************************************************

  Synopsis    [ GBA. ]

  Description [ Fields:

                states - list of states; list and members onwed;

                transitions - list of transitions; list and members owned;

                initial_states - set of initial states; hash map
                  onwed, members not owned;

                fairness_constraints - list of sets of fair states;
                  list, hash maps owned, members not owned. ]

  SeeAlso     [ Game_SF07_gba_state, Game_SF07_gba_transition ]

******************************************************************************/
typedef struct Game_SF07_gba_TAG {
  /* list of states; list and list members owned */
  Slist_ptr states;

  /* list of transitions; list and list members owned */
  Slist_ptr transitions;

  /* hash map (set) of initial states; hashmap owned; list members not owned */
  hash_ptr initial_states;

  /* list of hashmaps (sets) of fair states;
     list, hashmaps owned; states now owned */
  Slist_ptr fairness_constraints;
} Game_SF07_gba;

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Constructor for states. ]

  Description [ self takes ownership of incoming and outgoing. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_state_destroy ]

******************************************************************************/
Game_SF07_gba_state_ptr Game_SF07_gba_state_create(string_ptr id,
                                                   node_ptr label,
                                                   Slist_ptr incoming,
                                                   Slist_ptr outgoing)
{
  Game_SF07_gba_state_ptr state;

  nusmv_assert(id);
  nusmv_assert(label);
  SLIST_CHECK_INSTANCE(incoming);
  SLIST_CHECK_INSTANCE(outgoing);
  /* No sanity check of label. */
  /* No sanity check of incoming and outgoing. */

  state = ALLOC(Game_SF07_gba_state, 1);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);

  state->id = id;
  state->label = label;
  state->incoming = incoming;
  state->outgoing = outgoing;

  return state;
}

/**Function********************************************************************

  Synopsis    [ Destructor for states. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_state_create ]

******************************************************************************/
void Game_SF07_gba_state_destroy(Game_SF07_gba_state_ptr self)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);

  /* Don't destroy id: string_ptr are shared. */

  /* Don't destroy label: node_ptr are shared. */

  /* Destroy incoming but not members (done in automaton). */
  Slist_destroy(self->incoming);

  /* Destroy outgoing but not members (done in automaton). */
  Slist_destroy(self->outgoing);

  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Getter for state id. ]

  Description [ self keeps ownership (but shared). ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
string_ptr Game_SF07_gba_state_get_id(Game_SF07_gba_state_ptr self)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);

  return self->id;
}

/**Function********************************************************************

  Synopsis    [ Getter for state label. ]

  Description [ self keeps ownership (but shared). ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
node_ptr Game_SF07_gba_state_get_label(Game_SF07_gba_state_ptr self)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);

  return self->label;
}

/**Function********************************************************************

  Synopsis    [ Getter for state incoming transitions. ]

  Description [ self keeps ownership. ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
Slist_ptr Game_SF07_gba_state_get_incoming(Game_SF07_gba_state_ptr self)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);

  return self->incoming;
}

/**Function********************************************************************

  Synopsis    [ Getter for state outgoing transitions. ]

  Description [ self keeps ownership. ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
Slist_ptr Game_SF07_gba_state_get_outgoing(Game_SF07_gba_state_ptr self)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);

  return self->outgoing;
}

/**Function********************************************************************

  Synopsis    [ Add transition to list of state incoming transitions. ]

  Description [ Caller keeps ownership of in. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_state_add_incoming(Game_SF07_gba_state_ptr self,
                                      Game_SF07_gba_transition_ptr in)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(in);

  Slist_push(self->incoming, (void *) in);
}

/**Function********************************************************************

  Synopsis    [ Add transition to list of state outgoing transitions. ]

  Description [ Caller keeps ownership of out. ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Game_SF07_gba_state_add_outgoing(Game_SF07_gba_state_ptr self,
                                      Game_SF07_gba_transition_ptr out)
{
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(self);
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(out);

  Slist_push(self->outgoing, (void *) out);
}

/**Function********************************************************************

  Synopsis    [ Constructor for transitions. ]

  Description [ Caller keeps ownership of source, target. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_transition_destroy ]

******************************************************************************/
Game_SF07_gba_transition_ptr Game_SF07_gba_transition_create(
  Game_SF07_gba_state_ptr source,
  Game_SF07_gba_state_ptr target)
{
  Game_SF07_gba_transition_ptr transition;

  GAME_SF07_GBA_STATE_CHECK_INSTANCE(source);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(target);

  transition = ALLOC(Game_SF07_gba_transition, 1);
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(transition);

  transition->source = source;
  transition->target = target;

  return transition;
}

/**Function********************************************************************

  Synopsis    [ Destructor for transitions. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_transition_create ]

******************************************************************************/
void Game_SF07_gba_transition_destroy(Game_SF07_gba_transition_ptr self)
{
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(self);

  /* Don't destroy either source or target. */

  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Getter for transition source. ]

  Description [ No transfer of ownership (not even owned by self). ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
Game_SF07_gba_state_ptr Game_SF07_gba_transition_get_source(
  Game_SF07_gba_transition_ptr self)
{
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(self);

  return self->source;
}

/**Function********************************************************************

  Synopsis    [ Getter for transition target. ]

  Description [ No transfer of ownership (not even owned by self). ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
Game_SF07_gba_state_ptr Game_SF07_gba_transition_get_target(
  Game_SF07_gba_transition_ptr self)
{
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(self);

  return self->target;
}

/**Function********************************************************************

  Synopsis    [ Constructor for GBA. ]

  Description [ self takes ownership of states, transitions,
                initial_states, fairness_constraints including their
                members. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_destroy ]

******************************************************************************/
Game_SF07_gba_ptr Game_SF07_gba_create(Slist_ptr states,
                                       Slist_ptr transitions,
                                       hash_ptr initial_states,
                                       Slist_ptr fairness_constraints)
{
  Game_SF07_gba_ptr gba;

  SLIST_CHECK_INSTANCE(states);
  SLIST_CHECK_INSTANCE(transitions);
  nusmv_assert(initial_states);
  SLIST_CHECK_INSTANCE(fairness_constraints);
  /* No more sanity checks as sets of states and transitions are lists. */

  gba = ALLOC(Game_SF07_gba, 1);
  GAME_SF07_GBA_CHECK_INSTANCE(gba);

  gba->states = states;
  gba->transitions = transitions;
  gba->initial_states = initial_states;
  gba->fairness_constraints = fairness_constraints;

  return gba;
}

/**Function********************************************************************

  Synopsis    [ Destructor for GBA. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_create ]

******************************************************************************/
void Game_SF07_gba_destroy(Game_SF07_gba_ptr self)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);

  {
    Siter s_iter;
    SLIST_FOREACH(self->states, s_iter) {
      Game_SF07_gba_state_ptr state = GAME_SF07_GBA_STATE(Siter_element(s_iter));
      Game_SF07_gba_state_destroy(state);
    }
    Slist_destroy(self->states);
  }

  {
    Siter t_iter;
    SLIST_FOREACH(self->transitions, t_iter) {
      Game_SF07_gba_transition_ptr transition =
        GAME_SF07_GBA_TRANSITION(Siter_element(t_iter));
      Game_SF07_gba_transition_destroy(transition);
    }
    Slist_destroy(self->transitions);
  }

  free_assoc(self->initial_states);

  {
    Siter fc_iter;
    SLIST_FOREACH(self->fairness_constraints, fc_iter) {
      hash_ptr fairness_constraint = (hash_ptr) Siter_element(fc_iter);
      free_assoc(fairness_constraint);
    }
    Slist_destroy(self->fairness_constraints);
  }

  FREE(self);
}

/**Function********************************************************************

  Synopsis    [ Adds a state. ]

  Description [ self takes ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_add_state(Game_SF07_gba_ptr self,
                             Game_SF07_gba_state_ptr state)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  /* No check for state not yet being a state of self as set of states
     is a list. */

  Slist_push(self->states, state);
}

/**Function********************************************************************

  Synopsis    [ Adds a transition. ]

  Description [ self takes ownership of transition but not its source
                and target. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_add_transition(Game_SF07_gba_ptr self,
                                  Game_SF07_gba_transition_ptr transition)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);
  GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(transition);
  /* No check for transition not yet being a transition of self as set
     of transitions is a list. */
  /* No check for source/target states being states of self as set of
     states is a list. */

  Slist_push(self->transitions, transition);
}

/**Function********************************************************************

  Synopsis    [ Adds a state to the set of initial states. ]

  Description [ Caller keeps ownership. State must not be inital yet. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_add_state_to_initial_states(Game_SF07_gba_ptr self,
                                               Game_SF07_gba_state_ptr state)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  nusmv_assert(!Game_SF07_gba_is_state_initial(self, state));
  /* No check for state being a state of self as set of states is a list. */

  /* We use an arbitrary non-Nil node_ptr to signal presence in hashmap. */
  insert_assoc(self->initial_states, (node_ptr) state, FAILURE_NODE);
}

/**Function********************************************************************

  Synopsis    [ Adds a fairness constraint. ]

  Description [ self takes ownership of fairness constraint (but not
                its members). ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_add_fairness_constraint(Game_SF07_gba_ptr self,
                                           hash_ptr fairness_constraint)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);
  nusmv_assert(fairness_constraint);
  /* No check of states in fairness_constraint being states of self. */
  /* No check/comparison of fairnes_constraint with other fairness
     constraints of self. */

  Slist_push(self->fairness_constraints, (void *)fairness_constraint);
}

/**Function********************************************************************

  Synopsis    [ Adds state to fairness constraint. ]

  Description [ Caller keeps ownership of state. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Game_SF07_gba_add_state_to_fairness_constraint(Game_SF07_gba_ptr self,
                                                    hash_ptr fairness_constraint,
                                                  Game_SF07_gba_state_ptr state)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);
  nusmv_assert(fairness_constraint);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  /* No check for fairness_constraint being a fairness constraint of
     self as set of fairness constraints is a list. */
  /* No check for state being a state of self as set of states is a list. */

  /* We use an arbitrary non-Nil node_ptr to signal presence in hashmap. */
  insert_assoc(fairness_constraint, (node_ptr) state, FAILURE_NODE);
}

/**Function********************************************************************

  Synopsis    [ Getter for states. ]

  Description [ self keeps ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
Slist_ptr Game_SF07_gba_get_states(Game_SF07_gba_ptr self)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);

  return self->states;
}

/**Function********************************************************************

  Synopsis    [ Getter for transitions. ]

  Description [ self keeps ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
Slist_ptr Game_SF07_gba_get_transitions(Game_SF07_gba_ptr self)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);

  return self->transitions;
}

/**Function********************************************************************

  Synopsis    [ Returns true if state is an initial state. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
boolean Game_SF07_gba_is_state_initial(Game_SF07_gba_ptr self,
                                       Game_SF07_gba_state_ptr state)
{
  boolean res;

  GAME_SF07_GBA_CHECK_INSTANCE(self);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  /* No check for state being a state of self as set of states is a list. */

  /* We use an arbitrary non-Nil node_ptr to signal presence in hashmap. */
  res = (find_assoc(self->initial_states, (node_ptr) state) != Nil);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Getter for fairness constraints. ]

  Description [ self keeps ownership. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
Slist_ptr Game_SF07_gba_get_fairness_constraints(Game_SF07_gba_ptr self)
{
  GAME_SF07_GBA_CHECK_INSTANCE(self);

  return self->fairness_constraints;
}

/**Function********************************************************************

  Synopsis    [ Returns the first fairness constraint. ]

  Description [ self keeps ownership. The number of fairness
                constraints must be at least 1. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
hash_ptr Game_SF07_gba_get_first_fairness_constraint(Game_SF07_gba_ptr self)
{
  Siter fc_iter;
  hash_ptr res;

  GAME_SF07_GBA_CHECK_INSTANCE(self);
  nusmv_assert(Game_SF07_gba_get_fairness_constraints_count(self) >= 1);

  fc_iter = Slist_first(self->fairness_constraints);
  res = (hash_ptr) Siter_element(fc_iter);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Returns true if a state is in the given fairness
                constraint. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_is_state_in_first_fairness_constraint ]

******************************************************************************/
boolean Game_SF07_gba_is_state_in_fairness_constraint(
  Game_SF07_gba_ptr self,
  hash_ptr fairness_constraint,
  Game_SF07_gba_state_ptr state)
{
  boolean res;

  GAME_SF07_GBA_CHECK_INSTANCE(self);
  nusmv_assert(fairness_constraint);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  /* No check for fairness_constraint being a fairness constraint of
     self as set of fairness constraints is a list. */
  /* No check for state being a state of self as set of states is a list. */

  /* We use an arbitrary non-Nil node_ptr to signal presence in hashmap. */
  res = (find_assoc(fairness_constraint, (node_ptr) state) != Nil);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Returns true if state is in the first fairness constraint
                of self. ]

  Description [ The number of fairness constraints must be at least 1. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_is_state_in_fairness_constraint ]

******************************************************************************/
boolean Game_SF07_gba_is_state_in_first_fairness_constraint(
  Game_SF07_gba_ptr self,
  Game_SF07_gba_state_ptr state)
{
  hash_ptr fc;
  boolean res;

  GAME_SF07_GBA_CHECK_INSTANCE(self);
  nusmv_assert(Game_SF07_gba_get_fairness_constraints_count(self) >= 1);
  GAME_SF07_GBA_STATE_CHECK_INSTANCE(state);
  /* No check for state being a state of self as set of states is a list. */

  fc = Game_SF07_gba_get_first_fairness_constraint(self);
  res = Game_SF07_gba_is_state_in_fairness_constraint(self, fc, state);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Returns the number of fairness constraints. ]

  Description [ Just the length of the list, w/o looking into its elements. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_is_simple ]

******************************************************************************/
unsigned int Game_SF07_gba_get_fairness_constraints_count(
  Game_SF07_gba_ptr self)
{
  unsigned int res;

  GAME_SF07_GBA_CHECK_INSTANCE(self);

  res = Slist_get_size(self->fairness_constraints);

  return res;
}

/**Function********************************************************************

  Synopsis    [ Returns true if a GBA is simple. ]

  Description [ A GBA is simple if it has a single fairness
                constraint. It checks just the number of fairness
                constraints without looking into them/comparing them
                etc. ]

  SideEffects [ ]

  SeeAlso     [ Game_SF07_gba_get_fairness_constraints_count ]

******************************************************************************/
boolean Game_SF07_gba_is_simple(Game_SF07_gba_ptr self)
{
  boolean res;

  GAME_SF07_GBA_CHECK_INSTANCE(self);

  res = (Game_SF07_gba_get_fairness_constraints_count(self) == 1);

  return res;
}

/*---------------------------------------------------------------------------*/
/* Static function definitions                                               */
/*---------------------------------------------------------------------------*/
