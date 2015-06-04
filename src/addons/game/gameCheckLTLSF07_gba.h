/**CHeaderFile*****************************************************************

  FileName    [ gameCheckLTLSF07_gba.h ]

  PackageName [ game ]

  Synopsis    [ Implements an explicit, state-labeled generalized B\"uchi
                automaton. ]

  Description [ See gameCheckLTLSF07_gba.c. ]

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

  Revision    [$Id: gameCheckLTLSF07_gba.h,v 1.1.2.1 2010-01-11 15:23:12 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_CHECKLTLSF07_GBA__H__
#define __GAME_CHECKLTLSF07_GBA__H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "node/node.h"
#include "utils/utils.h"
#include "utils/Slist.h"
#include "utils/assoc.h"
#include "utils/ustring.h"

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ State of a GBA. ]

  Description [ ]

  SeeAlso     [ Game_SF07_gba_transition, Game_SF07_gba ]

******************************************************************************/
typedef struct Game_SF07_gba_state_TAG* Game_SF07_gba_state_ptr;
#define GAME_SF07_GBA_STATE(x) ((Game_SF07_gba_state_ptr) x)
#define GAME_SF07_GBA_STATE_CHECK_INSTANCE(x) \
  ( nusmv_assert(GAME_SF07_GBA_STATE(x) != GAME_SF07_GBA_STATE(NULL)) )

/**Type************************************************************************

  Synopsis    [ Transition of a GBA. ]

  Description [ ]

  SeeAlso     [ Game_SF07_gba_state, Game_SF07_gba ]

******************************************************************************/
typedef struct Game_SF07_gba_transition_TAG* Game_SF07_gba_transition_ptr;
#define GAME_SF07_GBA_TRANSITION(x) ((Game_SF07_gba_transition_ptr) x)
#define GAME_SF07_GBA_TRANSITION_CHECK_INSTANCE(x) \
  ( nusmv_assert(GAME_SF07_GBA_TRANSITION(x) != GAME_SF07_GBA_TRANSITION(NULL)) )

/**Type************************************************************************

  Synopsis    [ GBA. ]

  Description [ ]

  SeeAlso     [ Game_SF07_gba_state, Game_SF07_gba_transition ]

******************************************************************************/
typedef struct Game_SF07_gba_TAG* Game_SF07_gba_ptr;
#define GAME_SF07_GBA(x) ((Game_SF07_gba_ptr) x)
#define GAME_SF07_GBA_CHECK_INSTANCE(x) \
  ( nusmv_assert(GAME_SF07_GBA(x) != GAME_SF07_GBA(NULL)) )

/* ---------------------------------------------------------------------- */
/* Public Interface                                                       */
/* ---------------------------------------------------------------------- */

/* States */

EXTERN Game_SF07_gba_state_ptr
Game_SF07_gba_state_create ARGS((string_ptr id,
                                 node_ptr label,
                                 Slist_ptr incoming,
                                 Slist_ptr outgoing));
EXTERN void
Game_SF07_gba_state_destroy ARGS((Game_SF07_gba_state_ptr self));
EXTERN string_ptr
Game_SF07_gba_state_get_id ARGS((Game_SF07_gba_state_ptr self));
EXTERN node_ptr
Game_SF07_gba_state_get_label ARGS((Game_SF07_gba_state_ptr self));
EXTERN Slist_ptr
Game_SF07_gba_state_get_incoming ARGS((Game_SF07_gba_state_ptr self));
EXTERN Slist_ptr
Game_SF07_gba_state_get_outgoing ARGS((Game_SF07_gba_state_ptr self));
EXTERN void
Game_SF07_gba_state_add_incoming ARGS((Game_SF07_gba_state_ptr self,
                                       Game_SF07_gba_transition_ptr in));
EXTERN void
Game_SF07_gba_state_add_outgoing ARGS((Game_SF07_gba_state_ptr self,
                                       Game_SF07_gba_transition_ptr out));
/* Transitions */

EXTERN Game_SF07_gba_transition_ptr
Game_SF07_gba_transition_create ARGS((Game_SF07_gba_state_ptr source,
                                      Game_SF07_gba_state_ptr target));
EXTERN void
Game_SF07_gba_transition_destroy ARGS((Game_SF07_gba_transition_ptr self));
EXTERN Game_SF07_gba_state_ptr
Game_SF07_gba_transition_get_source ARGS((Game_SF07_gba_transition_ptr self));
EXTERN Game_SF07_gba_state_ptr
Game_SF07_gba_transition_get_target ARGS((Game_SF07_gba_transition_ptr self));

/* GBA */

EXTERN Game_SF07_gba_ptr
Game_SF07_gba_create ARGS((Slist_ptr states,
                           Slist_ptr transitions,
                           hash_ptr initial_states,
                           Slist_ptr fairness_constraints));
EXTERN void Game_SF07_gba_destroy ARGS((Game_SF07_gba_ptr self));
EXTERN void Game_SF07_gba_add_state ARGS((Game_SF07_gba_ptr self,
                                          Game_SF07_gba_state_ptr state));
EXTERN void
Game_SF07_gba_add_transition ARGS((Game_SF07_gba_ptr self,
                                   Game_SF07_gba_transition_ptr transition));
EXTERN void
Game_SF07_gba_add_state_to_initial_states ARGS((Game_SF07_gba_ptr self,
                                                Game_SF07_gba_state_ptr state));
EXTERN void
Game_SF07_gba_add_fairness_constraint ARGS((Game_SF07_gba_ptr self,
                                            hash_ptr fairness_constraint));
EXTERN void
Game_SF07_gba_add_state_to_fairness_constraint ARGS((Game_SF07_gba_ptr self,
                                                   hash_ptr fairness_constraint,
                                                Game_SF07_gba_state_ptr state));
EXTERN Slist_ptr Game_SF07_gba_get_states ARGS((Game_SF07_gba_ptr self));
EXTERN Slist_ptr Game_SF07_gba_get_transitions ARGS((Game_SF07_gba_ptr self));
EXTERN boolean
Game_SF07_gba_is_state_initial ARGS((Game_SF07_gba_ptr self,
                                     Game_SF07_gba_state_ptr state));
EXTERN Slist_ptr
Game_SF07_gba_get_fairness_constraints ARGS((Game_SF07_gba_ptr self));
EXTERN hash_ptr
Game_SF07_gba_get_first_fairness_constraint ARGS((Game_SF07_gba_ptr self));
EXTERN boolean
Game_SF07_gba_is_state_in_fairness_constraint ARGS((Game_SF07_gba_ptr self,
                                                    hash_ptr fairness_constraint,
                                                Game_SF07_gba_state_ptr state));
EXTERN boolean
Game_SF07_gba_is_state_in_first_fairness_constraint ARGS((Game_SF07_gba_ptr self,
                                                Game_SF07_gba_state_ptr state));
EXTERN unsigned int
Game_SF07_gba_get_fairness_constraints_count ARGS((Game_SF07_gba_ptr self));
EXTERN boolean
Game_SF07_gba_is_simple ARGS((Game_SF07_gba_ptr self));

#endif /* __GAME_CHECKLTLSF07_GBA__H__ */
