/**CFile***********************************************************************

  FileName    [ PropGame.c ]

  PackageName [ game ]

  Synopsis    [ Implementation of class 'PropGame'. ]

  Description [ ]

  SeeAlso     [ PropGame.h ]

  Author      [ Marco Roveri, Roberto Cavada, Viktor Schuppan ]

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

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "game.h"
#include "gameInt.h"
#include "PropGame.h"
#include "PropGame_private.h"
#include "parser/game_symbols.h"

#include "node/node.h"
#include "parser/symbols.h"
#include "prop/Prop.h"
#include "prop/Prop_private.h"
#include "utils/utils.h"
#include "utils/utils_io.h"
#include "utils/object.h"
#include "../../smgame/printStrategy.h"
#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id$";

EXTERN GameParams gameParams;
/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/
/* See 'PropGame_private.h' for class 'PropGame' definition. */

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
static void prop_game_finalize ARGS((Object_ptr object, void* dummy));

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PropGame class constructor. ]

  Description [ Allocate a property. If no more room is available then
                a call to <tt>numsv_exit</tt> is performed. All the
                fields of the PropGame structure are initialized to
                either NULL or the corresponding default type. ]

  SideEffects [ ]

  SeeAlso     [ PropGame_destroy ]

******************************************************************************/
PropGame_ptr PropGame_create(const NuSMVEnv_ptr env)
{
  PropGame_ptr self = ALLOC(PropGame, 1);
  PROP_GAME_CHECK_INSTANCE(self);

  prop_game_init(self,env);
  return self;
}

/**Function********************************************************************

  Synopsis    [ Creates a property, but does not insert it into the
                database, so the property can be used on the fly. ]

  Description [ Creates a property structure filling only the property
                and property type fields. The property index in the
                database is not set. ]

  SideEffects [ ]

  SeeAlso     [ PropGame_create, PropGame_destroy ]

******************************************************************************/
PropGame_ptr PropGame_create_partial(const NuSMVEnv_ptr env,Expr_ptr expr, PropGame_Type type)
{
  PropGame_ptr self;

  nusmv_assert(PropGame_type_is_game(type));

  self = PropGame_create(env);
  PROP_GAME_CHECK_INSTANCE(self);

  /* DEBUGGING: game properties must be wrapped into
     GAME_SPEC_WRAPPER. */
  if (Nil != expr) {
    nusmv_assert(GAME_SPEC_WRAPPER == node_get_type(expr));
  }

  (PROP(self))->index = -1;
  (PROP(self))->status = Prop_Unchecked;
  (PROP(self))->prop = expr;
  (PROP(self))->type = type;

  return self;
}

/**Function********************************************************************

  Synopsis    [ The PropGame class destructor. ]

  Description [ Free a property. Notice that before freeing the
                property all the elements of the property that need
                to be freed will be automatically freed. ]

  SideEffects [ ]

  SeeAlso     [ PropGame_create, PropGame_create_partial, Prop_destroy ]

******************************************************************************/
void PropGame_destroy(PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  Object_destroy(OBJECT(self), NULL);
}

/**Function********************************************************************

  Synopsis    [ Returns the game scalar FSM of a property. ]

  Description [ Returns the game scalar FSM associated to the
                property. Self keeps the ownership of the given fsm. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameSexpFsm_ptr PropGame_get_game_scalar_sexp_fsm(const PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  return self->game_scalar_fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game scalar FSM of a property. ]

  Description [ The given FSM will be duplicated, so the caller keeps
                the ownership of FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropGame_set_game_scalar_sexp_fsm(PropGame_ptr self, GameSexpFsm_ptr fsm)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  prop_game_set_game_scalar_sexp_fsm(self, fsm, true);
}

/**Function********************************************************************

  Synopsis    [ Returns the game boolean FSM of a property. ]

  Description [ Returns the game boolean FSM in sexp associated to the
                property. Self keeps the ownership of the given FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameSexpFsm_ptr PropGame_get_game_bool_sexp_fsm(const PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  return self->game_bool_fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game boolean FSM of a property. ]

  Description [ The given game boolean FSM will be duplicated, so the
                caller keeps the ownership of the given FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropGame_set_game_bool_sexp_fsm(PropGame_ptr self, GameSexpFsm_ptr fsm)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  prop_game_set_game_bool_sexp_fsm(self, fsm, true);
}

/**Function********************************************************************

  Synopsis    [ Returns the game BDD FSM of a property. ]

  Description [ Returns the game BDD FSM associated to the
                property. Self keeps the ownership of the given FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameBddFsm_ptr PropGame_get_game_bdd_fsm(PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  return self->game_bdd_fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game BDD FSM of a property. ]

  Description [ The given game BDD fsm will be duplicated, so the
                caller keeps the ownership of the given FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropGame_set_game_bdd_fsm(PropGame_ptr self, GameBddFsm_ptr fsm)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  prop_game_set_game_bdd_fsm(self, fsm, true);
}

/**Function********************************************************************

  Synopsis    [ Returns the game BE FSM of a property. ]

  Description [ Returns the game boolean BE FSM associated to the
                property. Self keeps the ownership of the given FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
GameBeFsm_ptr PropGame_get_game_be_fsm(const PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  return self->game_be_fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game boolean BE FSM of a property. ]

  Description [ The given game boolean BE FSM will be duplicated, so
                the caller keeps the ownership of the given FSM. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void PropGame_set_game_be_fsm(PropGame_ptr self, GameBeFsm_ptr fsm)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game_or_notype(Prop_get_type(PROP(self))));

  prop_game_set_game_be_fsm(self, fsm, true);
}

/**Function********************************************************************

  Synopsis    [ Returns the player this property is for. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
string_ptr PropGame_get_player(const PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(self))));
  nusmv_assert(Nil != (PROP(self))->prop &&
               GAME_SPEC_WRAPPER == node_get_type((PROP(self))->prop) &&
               Nil != car((PROP(self))->prop) &&
               ATOM == node_get_type(car((PROP(self))->prop)) &&
               NULL != (string_ptr) car(car((PROP(self))->prop)));

  return (string_ptr) car(car((PROP(self))->prop));
}

/**Function********************************************************************

  Synopsis    [ Returns the a string associated to a property type. ]

  Description [ Returns the string corresponding to a property type
                for printing it. Returned string must NOT be
                deleted. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
const char* PropGame_Type_to_string(const PropGame_Type type)
{
  char* res = (char*) NULL;

  nusmv_assert(PropGame_type_is_game(type));

  switch (type) {
  case PropGame_ReachTarget:   res = PROP_GAME_REACH_TARGET_STRING; break;
  case PropGame_AvoidTarget:   res = PROP_GAME_AVOID_TARGET_STRING; break;
  case PropGame_ReachDeadlock: res = PROP_GAME_REACH_DEADLOCK_STRING; break;
  case PropGame_AvoidDeadlock: res = PROP_GAME_AVOID_DEADLOCK_STRING; break;
  case PropGame_BuchiGame:     res = PROP_GAME_BUCHI_GAME_STRING; break;
  case PropGame_LtlGame:       res = PROP_GAME_LTL_GAME_STRING; break;
  case PropGame_GenReactivity: res = PROP_GAME_GEN_REACTIVITY_STRING; break;
  default: nusmv_assert(false); /* unknown type! */
  }

  return res;
}

/**Function********************************************************************

  Synopsis    [ Returns true iff type is a PropGame_Type. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
boolean PropGame_type_is_game(const PropGame_Type type)
{
  return (PropGame_PropGame_Type_First < type &&
          PropGame_PropGame_Type_Last > type);
}

/**Function********************************************************************

  Synopsis    [ Returns true iff type is a PropGame_Type or Prop_NoType. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
boolean PropGame_type_is_game_or_notype(const PropGame_Type type)
{
  return PropGame_type_is_game(type) || (type == Prop_NoType);
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PropGame class private initializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PropGame_create, prop_init ]

******************************************************************************/
void prop_game_init(PropGame_ptr self,const NuSMVEnv_ptr env)
{
  PROP_GAME_CHECK_INSTANCE(self);

  /* base class initialization */
  prop_init(PROP(self),env);

  /* members initialization */
  self->game_scalar_fsm = GAME_SEXP_FSM(NULL);
  self->game_bool_fsm = GAME_SEXP_FSM(NULL);
  self->game_bdd_fsm = GAME_BDD_FSM(NULL);
  self->game_be_fsm = GAME_BE_FSM(NULL);

  /* virtual methods settings */
  OVERRIDE(Object, finalize) = prop_game_finalize;
  OVERRIDE(Prop, get_expr) = (Prop_get_expr_method) prop_game_get_expr;
  OVERRIDE(Prop, get_type_as_string) =
    (Prop_get_type_as_string_method) prop_game_get_type_as_string;
  OVERRIDE(Prop, print) = (Prop_print_method) prop_game_print;
  OVERRIDE(Prop, print_db_tabular) = (Prop_print_db_method) prop_game_print_db;
  OVERRIDE(Prop, verify) = (Prop_verify_method) prop_game_verify;
  OVERRIDE(Prop, set_environment_fsms) = (Prop_set_environment_fsms_method) prop_game_set_environment_fsms;
}

/**Function********************************************************************

  Synopsis    [ The PropGame class private deinitializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PropGame_destroy, prop_deinit ]

******************************************************************************/
void prop_game_deinit(PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);

  /* members deinitialization */
  if (self->game_be_fsm != GAME_BE_FSM(NULL)) {
    GameBeFsm_destroy(self->game_be_fsm);
  }
  if (self->game_bdd_fsm != GAME_BDD_FSM(NULL)) {
    GameBddFsm_destroy(self->game_bdd_fsm);
  }
  if (self->game_bool_fsm != GAME_SEXP_FSM(NULL)) {
    GameSexpFsm_destroy(self->game_bool_fsm);
  }
  if (self->game_scalar_fsm != GAME_SEXP_FSM(NULL)) {
    GameSexpFsm_destroy(self->game_scalar_fsm);
  }

  /* base class deinitialization */
  prop_deinit(PROP(self));
}

/**Function********************************************************************

  Synopsis    [ Returns the property as it has been parsed and created. ]

  Description [ Returns the cdr of the property stored. car is player. ]

  SideEffects [ ]

  SeeAlso     [ Prop_get_expr_core, prop_get_expr ]

******************************************************************************/
Expr_ptr prop_game_get_expr(const PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(self))));

  /* Game properties are wrapped into a GAME_SPEC_WRAPPER node with
     the players name on the left and the expression on the
     right. Return only the pure expression. */
  return cdr((PROP(self))->prop);
}

/**Function********************************************************************

  Synopsis    [ Returns the a string associated to the propertys type. ]

  Description [ Returns the string corresponding to the propertys type
                for printing it. Returned string must NOT be
                deleted. ]

  SideEffects [ ]

  SeeAlso     [ prop_get_type_as_string ]

******************************************************************************/
const char* prop_game_get_type_as_string(const PropGame_ptr self)
{
  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(self))));

  return PropGame_Type_to_string(Prop_get_type(PROP(self)));
}

/**Function********************************************************************

  Synopsis    [ Prints a property. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ prop_print ]

******************************************************************************/
void prop_game_print(const PropGame_ptr self, OStream_ptr file)
{
  node_ptr p;
  node_ptr context;

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));

  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(self))));

  p = Prop_get_expr(PROP(self));
  context = Nil;

  if (p != Nil && node_get_type(p) == CONTEXT) {
    context = car(p);
    p = cdr(p);
  }

    /* Print the specification type and the player responsible for the
       specification. */
    OStream_printf(file,
            " %s %s ",
            Prop_get_type_as_string(PROP(self)),
            UStringMgr_get_string_text(PropGame_get_player(self)));

    OStream_nprintf(file, wffprint, "%N ", p);

    if (context != Nil) {
        OStream_nprintf(file, wffprint, "IN %N", context);
    }

}

/**Function********************************************************************

  Synopsis    [ Prints a property with info on its position and status in
                the database. ]

  Description [ Prints a property on the specified FILE stream. Some
                of the information stored in the property is printed
                out (e.g. property, property kind, property status,
                ...). ]

  SideEffects [ ]

  SeeAlso     [ prop_print_db ]

******************************************************************************/
void prop_game_print_db(const PropGame_ptr self, OStream_ptr file)
{

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  MasterPrinter_ptr wffprint = MASTER_PRINTER(NuSMVEnv_get_value(env, ENV_WFF_PRINTER));

  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(self))));

  OStream_printf(file, "%.3d : ", (PROP(self))->index);
  prop_game_print(self, file);
  OStream_printf(file, "\n");

  OStream_printf(file, "  [%-15s", Prop_get_type_as_string(PROP(self)));
  OStream_printf(file, "%-15s", Prop_get_status_as_string(PROP(self)));

  if ((PROP(self))->trace == 0) OStream_printf(file, "N/A    ");
  else OStream_printf(file, "%-7d", (PROP(self))->trace);

  if ((PROP(self))->name != Nil) print_node(wffprint,(FILE*)file, (PROP(self))->name);
  else OStream_printf(file, "N/A");
  OStream_printf(file, "]\n");
}

/**Function********************************************************************

  Synopsis    [ Verifies a given property. ]

  Description [ Depending the property, different algorithms are
                called. The status of the property is updated
                accordingly to the result of the verification
                process. ]

  SideEffects [ ]

  SeeAlso     [ prop_verify ]

******************************************************************************/
void prop_game_verify(PropGame_ptr self)
{
  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));

  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  PROP_GAME_CHECK_INSTANCE(self);
  nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(self))));
  /* the input file contains game */
  nusmv_assert(opt_game_game(opts));

  if (Prop_get_status(PROP(self)) == Prop_Unchecked)  {
    switch (Prop_get_type(PROP(self))) {
    case PropGame_ReachTarget:
      Game_CheckReachTargetSpec(self, &gameParams);
      break;
    case PropGame_AvoidTarget:
      Game_CheckAvoidTargetSpec(self, &gameParams);
      break;
    case PropGame_ReachDeadlock:
      Game_CheckReachDeadlockSpec(self, &gameParams);
      break;
    case PropGame_AvoidDeadlock:
      Game_CheckAvoidDeadlockSpec(self, &gameParams);
      break;
    case PropGame_BuchiGame:
      Game_CheckBuchiGameSpec(self, &gameParams);
      break;
    case PropGame_LtlGame:
      Game_CheckLtlGameSpecSF07(self,
                                &gameParams,
                                DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_KMIN,
                                DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_KMAX,
                                DEFAULT_GAME_CHECK_LTL_GAME_SPEC_SF07_W);
      break;
    case PropGame_GenReactivity:
      Game_CheckGenReactivitySpec(self, &gameParams);
      break;
    default: nusmv_assert(false); /* invalid type */
    }
  }
}


/**Function********************************************************************

  Synopsis    [ Copies the FSMs of the master property into prop. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ prop_set_environment_fsms ]

******************************************************************************/
void prop_game_set_environment_fsms(const NuSMVEnv_ptr env, PropGame_ptr prop)
{
    PROP_GAME_CHECK_INSTANCE(prop);
    nusmv_assert(PropGame_type_is_game(Prop_get_type(PROP(prop))));

    if (NuSMVEnv_has_value(env, ENV_SEXP_FSM)) {
        PropGame_set_game_scalar_sexp_fsm(prop, GAME_SEXP_FSM(NuSMVEnv_get_value(env, ENV_SEXP_FSM)));
    }
    if (NuSMVEnv_has_value(env, ENV_BOOL_FSM)) {
        PropGame_set_game_bool_sexp_fsm(prop, GAME_SEXP_FSM(NuSMVEnv_get_value(env, ENV_BOOL_FSM)));
    }
    if (NuSMVEnv_has_value(env, ENV_BDD_FSM)) {
        PropGame_set_game_bdd_fsm(prop, GAME_BDD_FSM(NuSMVEnv_get_value(env, ENV_BDD_FSM)));
    }
    if (NuSMVEnv_has_value(env, ENV_BE_FSM)) {
        PropGame_set_game_be_fsm(prop, GAME_BE_FSM(NuSMVEnv_get_value(env, ENV_BE_FSM)));
    }

}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Sets the game scalar FSM of a property. ]

  Description [ If duplicate is true, then the given FSM will be
                duplicated. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void prop_game_set_game_scalar_sexp_fsm(PropGame_ptr self,
                                        GameSexpFsm_ptr fsm,
                                        const boolean duplicate)
{
  PROP_GAME_CHECK_INSTANCE(self);

  if (self->game_scalar_fsm != GAME_SEXP_FSM(NULL)) {
    GameSexpFsm_destroy(self->game_scalar_fsm);
  }
  if (duplicate && (fsm != GAME_SEXP_FSM(NULL))) {
    self->game_scalar_fsm = GameSexpFsm_copy(fsm);
  }
  else self->game_scalar_fsm = fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game boolean FSM of a property. ]

  Description [ If duplicate is true, then the given FSM will be
                duplicated. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void prop_game_set_game_bool_sexp_fsm(PropGame_ptr self,
                                      GameSexpFsm_ptr fsm,
                                      const boolean duplicate)
{
  PROP_GAME_CHECK_INSTANCE(self);

  if (self->game_bool_fsm != GAME_SEXP_FSM(NULL)) {
    GameSexpFsm_destroy(self->game_bool_fsm);
  }
  if (duplicate && (fsm != GAME_SEXP_FSM(NULL))) {
    self->game_bool_fsm = GameSexpFsm_copy(fsm);
  }
  else self->game_bool_fsm = fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game BDD FSM of a property. ]

  Description [ If duplicate is true, then the given FSM will be
                duplicated. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void prop_game_set_game_bdd_fsm(PropGame_ptr self,
                                GameBddFsm_ptr fsm,
                                const boolean duplicate)
{
  PROP_GAME_CHECK_INSTANCE(self);

  if (self->game_bdd_fsm != GAME_BDD_FSM(NULL)) {
    GameBddFsm_destroy(self->game_bdd_fsm);
  }
  if (duplicate && (fsm != GAME_BDD_FSM(NULL))) {
    self->game_bdd_fsm = GameBddFsm_copy(fsm);
  }
  else self->game_bdd_fsm = fsm;
}

/**Function********************************************************************

  Synopsis    [ Sets the game BE FSM of a property. ]

  Description [ If duplicate is true, then the given FSM will be
                duplicated. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void prop_game_set_game_be_fsm(PropGame_ptr self,
                               GameBeFsm_ptr fsm,
                               const boolean duplicate)
{
  PROP_GAME_CHECK_INSTANCE(self);

  if (self->game_be_fsm != (GameBeFsm_ptr) NULL) {
    GameBeFsm_destroy(self->game_be_fsm);
  }
  if (duplicate && (fsm != (GameBeFsm_ptr) NULL)) {
    self->game_be_fsm = GameBeFsm_copy(fsm);
  }
  else self->game_be_fsm = fsm;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PropGame class virtual finalizer. ]

  Description [ Called by the class destructor. ]

  SideEffects [ ]

  SeeAlso     [ prop_finalize ]

******************************************************************************/
static void prop_game_finalize(Object_ptr object, void* dummy)
{
  PropGame_ptr self = PROP_GAME(object);
  PROP_GAME_CHECK_INSTANCE(self);

  prop_game_deinit(self);
  FREE(self);
}

/**AutomaticEnd***************************************************************/
