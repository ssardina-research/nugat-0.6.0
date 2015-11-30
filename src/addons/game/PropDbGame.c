/**CFile***********************************************************************

  FileName    [ PropDbGame.c ]

  PackageName [ game ]

  Synopsis    [ Implementation of class 'PropDbGame' ]

  Description [ ]

  SeeAlso     [ PropDbGame.h PropDb.c ]

  Author      [ Marco Roveri, Roberto Cavada, Viktor Schuppan ]

  Copyright   [
  This file is part of the ``prop'' package of NuGaT.
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

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "PropDbGame.h"
#include "PropDbGame_private.h"

#include "GamePlayer.h"
#include "PropGame.h"
#include "PropGame_private.h"
#include "TypeCheckerGame.h"

#include "prop/PropDb.h"
#include "prop/PropDb_private.h"
#include "prop/Prop.h"

#include "compile/compile.h"
#include "compile/symb_table/SymbTable.h"
#include "opt/opt.h"
#include "parser/symbols.h"
#include "utils/utils.h"
#include "utils/ustring.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id$";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/
/* See 'PropDbGame_private.h' for class 'PropDbGame' definition. */

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stdout;
EXTERN FILE* nusmv_stderr;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void prop_db_game_finalize ARGS((Object_ptr object, void* dummy));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PropDbGame class constructor. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PropDbGame_destroy, PropDb_create ]

******************************************************************************/
PropDbGame_ptr PropDbGame_create(const NuSMVEnv_ptr env)
{
  PropDbGame_ptr self = ALLOC(PropDbGame, 1);
  PROP_DB_GAME_CHECK_INSTANCE(self);

  prop_db_game_init(self,env);
  return self;
}

/**Function********************************************************************

  Synopsis     [ The PropDbGame class destructor. ]

  Description  [ ]

  SideEffects  [ ]

  SeeAlso      [ PropDbGame_create, PropDb_destroy ]

******************************************************************************/
void PropDbGame_destroy(PropDbGame_ptr self)
{
  PROP_DB_GAME_CHECK_INSTANCE(self);

  Object_destroy(OBJECT(self), NULL);
}

/**Function********************************************************************

  Synopsis    [ Disposes the DB of properties. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PropDb_clean ]

******************************************************************************/
void PropDbGame_clean(const NuSMVEnv_ptr env,PropDbGame_ptr self)
{
  PROP_DB_CHECK_INSTANCE(self);

  prop_db_game_deinit(self);
  prop_db_game_init(self,env);
}

/**Function********************************************************************

  Synopsis    [ Fills the DB with game properties. ]

  Description [ Given for each kind of game property a list of
                respective formulae, this function is responsible to
                fill the DB with them. Returns 1 if an error occurred,
                0 otherwise. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int PropDbGame_fill(PropDbGame_ptr self,
                    SymbTable_ptr symb_table,
                    node_ptr reachtarget,
                    node_ptr avoidtarget,
                    node_ptr reachdeadlock,
                    node_ptr avoiddeadlock,
                    node_ptr buchigame,
                    node_ptr ltlgame,
                    node_ptr genreactivity)
{
  node_ptr l;
  int res;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  SYMB_TABLE_CHECK_INSTANCE(symb_table);

  for (l = reachtarget; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_ReachTarget);
    if (res == -1) return 1;
  }
  for (l = avoidtarget; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_AvoidTarget);
    if (res == -1) return 1;
  }
  for (l = reachdeadlock; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_ReachDeadlock);
    if (res == -1) return 1;
  }
  for (l = avoiddeadlock; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_AvoidDeadlock);
    if (res == -1) return 1;
  }
  for (l = buchigame; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_BuchiGame);
    if (res == -1) return 1;
  }
  for (l = ltlgame; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_LtlGame);
    if (res == -1) return 1;
  }
  for (l = genreactivity; l != Nil; l = cdr(l)) {
    res = PropDb_prop_create_and_add(PROP_DB(self),
                                     symb_table,
                                     car(l),
                                     PropGame_GenReactivity);
    if (res == -1) return 1;
  }

  return 0;
}

/**Function********************************************************************

  Synopsis    [ Verifies all properties of a given type and player. ]

  Description [ The DB of properties is searched for a property of the
                given type and player. Prop_NoType and (string_ptr)
                NULL serve as wildcards. All the found properties are
                then verified calling the appropriate model checking
                algorithm. Properties already checked will be
                ignored. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropDbGame_verify_all_type_player(const PropDbGame_ptr self,
                                       PropGame_Type type,
                                       string_ptr player)
{
  int i;

  PROP_DB_GAME_CHECK_INSTANCE(self);

  for (i = 0; i < PropDb_get_size(PROP_DB(self)); ++i) {
    PropGame_ptr p = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self), i));
    if (((type == Prop_NoType) || (Prop_get_type(PROP(p)) == type)) &&
        ((player == (string_ptr) NULL) || (PropGame_get_player(p) == player))) {
      Prop_verify(PROP(p));
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Prints all properties of a given type, player, and
                status. ]

  Description [ Prints on the given file stream all properties stored
                in the DB whose type, player, and status match the
                requested ones. Prop_NoStatus, (string_ptr) NULL, and
                Prop_NoType serve as wildcards. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropDbGame_print_all_type_player_status(const PropDbGame_ptr self,
                                             FILE* file,
                                             PropGame_Type type,
                                             string_ptr player,
                                             Prop_Status status)
{
  int i;

  PROP_DB_GAME_CHECK_INSTANCE(self);

  for (i = 0; i < PropDb_get_size(PROP_DB(self)); ++i) {
    PropGame_ptr p = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self), i));
    if (((type == Prop_NoType) || (Prop_get_type(PROP(p)) == type)) &&
        ((player == (string_ptr) NULL) || (PropGame_get_player(p) == player)) &&
        ((status == Prop_NoStatus) || (Prop_get_status(PROP(p)) == status))) {
      Prop_print_db(PROP(p), OSTREAM(file), PROP_PRINT_FMT_FORMULA);
    }
  }
}

/**Function********************************************************************

  Synopsis    [ Returns the game scalar sexp FSM of the master property. ]

  Description [ The caller is NOT the owner of the returned FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameSexpFsm_ptr
PropDbGame_master_get_game_scalar_sexp_fsm(const PropDbGame_ptr self)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  return PropGame_get_game_scalar_sexp_fsm(prop);
}

/**Function********************************************************************

  Synopsis    [ Sets the game scalar sexp FSM of the master property. ]

  Description [ Destroys the previously set FSM if any. The passed FSM
                no longer belongs to the ccaller. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropDbGame_master_set_game_scalar_sexp_fsm(PropDbGame_ptr self,GameSexpFsm_ptr fsm)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  prop_game_set_game_scalar_sexp_fsm(prop, fsm, false /*do not duplicate*/);
}

/**Function********************************************************************

  Synopsis    [ Returns the game boolean sexp FSM of the master property. ]

  Description [ The caller is NOT the owner of the returned FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameSexpFsm_ptr
PropDbGame_master_get_game_bool_sexp_fsm(const PropDbGame_ptr self)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  return PropGame_get_game_bool_sexp_fsm(prop);
}


/**Function********************************************************************

  Synopsis    [ Sets the game boolean sexp FSM of the master property. ]

  Description [ Destroys the previously set FSM if any. The passed FSM
                no longer belongs to the ccaller. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropDbGame_master_set_game_bool_sexp_fsm(PropDbGame_ptr self,GameSexpFsm_ptr fsm)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  prop_game_set_game_bool_sexp_fsm(prop, fsm, false /*do not duplicate*/);
}

/**Function********************************************************************

  Synopsis    [ Returns the game BDD FSM of the master property. ]

  Description [ The caller is NOT the owner of the returned FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameBddFsm_ptr PropDbGame_master_get_game_bdd_fsm(const PropDbGame_ptr self)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  return PropGame_get_game_bdd_fsm(prop);
}

/**Function********************************************************************

  Synopsis    [ Sets the game BDD FSM of the master property. ]

  Description [ Destroys the previously set FSM if any. The passed FSM
                no longer belongs to the ccaller. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropDbGame_master_set_game_bdd_fsm(PropDbGame_ptr self,GameBddFsm_ptr fsm)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  prop_game_set_game_bdd_fsm(prop, fsm, false /*do not duplicate*/);
}

/**Function********************************************************************

  Synopsis    [ Returns the game BE FSM of the master property. ]

  Description [ The caller is NOT the owner of the returned FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameBeFsm_ptr PropDbGame_master_get_game_be_fsm(const PropDbGame_ptr self)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  return PropGame_get_game_be_fsm(prop);
}

/**Function********************************************************************

  Synopsis    [ Sets the game BE FSM of the master property. ]

  Description [ Destroys the previously set FSM if any. The passed FSM
                no longer belongs to the ccaller. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropDbGame_master_set_game_be_fsm(PropDbGame_ptr self, GameBeFsm_ptr fsm)
{
  PropGame_ptr prop;

  PROP_DB_GAME_CHECK_INSTANCE(self);
  prop = PROP_GAME(PropDb_get_prop_at_index(PROP_DB(self),0)); // PropDb_get_last(PROP_DB(self))
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(prop))));

  prop_game_set_game_be_fsm(prop, fsm, false /*do not duplicate*/);
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PropDbGame class private initializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PropDbGame_create, PropDbGame_clean, prop_db_init ]

******************************************************************************/
void prop_db_game_init(PropDbGame_ptr self,const NuSMVEnv_ptr env)
{
  PROP_DB_GAME_CHECK_INSTANCE(self);

  /* base class initialization */
  prop_db_init(PROP_DB(self),env);

    /* Members initialization. Here: just replace master with a game
     property. */
    //Prop_destroy(PropDb_get_prop_at_index(PROP_DB(self),0),0));
//    PropDb_add(PROP_DB(self),PROP(Prop_create(env)));

  /* virtual methods settings */
  OVERRIDE(Object, finalize) = prop_db_game_finalize;
  OVERRIDE(PropDb, prop_create_and_add) =
    (PropDb_prop_create_and_add_method) prop_db_game_prop_create_and_add;

  /*OVERRIDE(PropDb, set_fsm_to_master) =
        (PropDb_set_fsm_to_master_method) prop_db_game_set_fsm_to_master;*///  //prop_db_game_set_fsm_to_master(PROP_GAME(B(selfs)elf//)); TODO

  OVERRIDE(Prop, set_environment_fsms) = PROP(self)->set_environment_fsms;


  OVERRIDE(PropDb, verify_all) =
    (PropDb_verify_all_method) prop_db_game_verify_all;
}

/**Function********************************************************************

  Synopsis    [ The PropDbGame class private deinitializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PropDbGame_destroy, PropDbGame_clean, prop_db_deinit ]

******************************************************************************/
void prop_db_game_deinit(PropDbGame_ptr self)
{
  PROP_DB_GAME_CHECK_INSTANCE(self);

  /* members deinitialization */

  /* base class deinitialization */
  prop_db_deinit(PROP_DB(self));
}

/**Function********************************************************************

  Synopsis    [ Inserts a property in the DB of properties. ]

  Description [ Given a formula and its type, a property is created
                and stored in the DB of properties. It returns either
                -1 in case of failure, or the index of the inserted
                property. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int prop_db_game_prop_create_and_add(PropDbGame_ptr self,
                                     SymbTable_ptr symb_table,
                                     node_ptr spec,
                                     PropGame_Type type)
{
  int retval, index;
  PropGame_ptr prop;

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  PROP_DB_GAME_CHECK_INSTANCE(self);
  SYMB_TABLE_CHECK_INSTANCE(symb_table);
  nusmv_assert(PropGame_type_is_game(type));

  retval = 0;
  index = PropDb_get_size(PROP_DB(self));

  prop = PropGame_create_partial(env,spec, type);
  Prop_set_index(PROP(prop), index);

  if (!TypeCheckerGame_check_property(SymbTable_get_type_checker(symb_table),
                                      PROP(prop))) {
    fprintf(stderr, "ERROR: Property \"");
    Prop_print(PROP(prop), (OStream_ptr)nusmv_stderr, PROP_PRINT_FMT_FORMULA);
    fprintf(stderr, "\b\" is not correct or not well typed.\n");
    return -1; /* type violation */
  }

  /* Add property to database */
  if (opt_verbose_level_gt(opts, 3)) {
    fprintf(stdout,
            "Attempting to add %s property (index %d) to property list.\n",
            Prop_get_type_as_string(PROP(prop)), index);
  }
  retval = PropDb_add(PROP_DB(self), PROP(prop));
  if (opt_verbose_level_gt(opts, 3)) {
    if (retval == 1) {
      fprintf(stdout, \
              "Failing to add %s property (index %d) to property list.\n", \
              Prop_get_type_as_string(PROP(prop)), index);
    }
    else {
      fprintf(stdout, \
              "%s property (index %d) successfully added to property list.\n",\
              Prop_get_type_as_string(PROP(prop)), index);
    }
  }

  retval = (retval == 1) ? -1 : index;
  return retval;
}

/**Function********************************************************************

  Synopsis    [ Copies the FSMs of the master property into prop. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ prop_db_set_fsm_to_master ]

******************************************************************************/
void prop_db_game_set_fsm_to_master(PropDbGame_ptr self, PropGame_ptr prop)
{
  PROP_DB_GAME_CHECK_INSTANCE(self);
  PROP_GAME_CHECK_INSTANCE(prop);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(prop))));

    PropGame_set_game_scalar_sexp_fsm(prop,PropDbGame_master_get_game_scalar_sexp_fsm(self));
    PropGame_set_game_bool_sexp_fsm(prop,PropDbGame_master_get_game_bool_sexp_fsm(self));
    PropGame_set_game_bdd_fsm(prop, PropDbGame_master_get_game_bdd_fsm(self));
    PropGame_set_game_be_fsm(prop, PropDbGame_master_get_game_be_fsm(self));
}

/**Function********************************************************************

  Synopsis    [ Verifies all the properties in the DB. ]

  Description [ All the properties stored in the database not yet
                verified will be verified. The properties are verified
                following the order ReachTarget, AvoidTarget,
                ReachDeadlock, AvoidDeadlock, BuchiGame, LtlGame,
                GenReactivity. ]

  SideEffects [ ]

  SeeAlso     [ prop_db_verify_all ]

******************************************************************************/
void prop_db_game_verify_all(const PropDbGame_ptr self)
{
  PROP_DB_GAME_CHECK_INSTANCE(self);

  PropDb_verify_all_type(PROP_DB(self), PropGame_ReachTarget);
  PropDb_verify_all_type(PROP_DB(self), PropGame_AvoidTarget);
  PropDb_verify_all_type(PROP_DB(self), PropGame_ReachDeadlock);
  PropDb_verify_all_type(PROP_DB(self), PropGame_AvoidDeadlock);
  PropDb_verify_all_type(PROP_DB(self), PropGame_BuchiGame);
  PropDb_verify_all_type(PROP_DB(self), PropGame_LtlGame);
  PropDb_verify_all_type(PROP_DB(self), PropGame_GenReactivity);
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PropDbGame class virtual finalizer. ]

  Description [ Called by the class destructor. ]

  SideEffects []

  SeeAlso     []

******************************************************************************/
static void prop_db_game_finalize(Object_ptr object, void* dummy)
{
  PropDbGame_ptr self = PROP_DB_GAME(object);
  PROP_DB_GAME_CHECK_INSTANCE(self);

  prop_db_game_deinit(self);
  FREE(self);
}

/**AutomaticEnd***************************************************************/
