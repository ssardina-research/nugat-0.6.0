/**CFile***********************************************************************

  FileName    [ PrinterSexpGame.c ]

  PackageName [ game.walkers ]

  Synopsis    [ Implementation of class 'PrinterSexpGame' ]

  Description [ This class is used to print expressions and constructs
                related to the Game package. ]

  SeeAlso     [ PrinterSexpGame.h ]

  Author      [ Viktor Schuppan ]

  Copyright   [
  This file is part of the ``game.walkers'' package of NuGaT.
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

  Revision    [$Id: PrinterSexpGame.c,v 1.1.2.3 2010-02-08 14:39:01 nusmv Exp $]

******************************************************************************/

#include "PrinterSexpGame.h"
#include "PrinterSexpGame_private.h"
#include "addons/game/parser/game_symbols.h"

#include "parser/symbols.h"
#include "utils/utils.h"
#include "utils/ErrorMgr.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: PrinterSexpGame.c,v 1.1.2.3 2010-02-08 14:39:01 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/
/* See 'PrinterSexpGame_private.h' for class 'PrinterSexpGame' definition. */

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ Short way of calling printer_base_throw_print_node. ]

  Description [ Use this macro to recursively call print_node. ]

  SeeAlso     [ ]

******************************************************************************/
#define _THROW(n, p) printer_base_throw_print_node(PRINTER_BASE(self), n, p)

/**Macro***********************************************************************

  Synopsis    [ Short way of calling printer_base_print_string. ]

  Description [ Use to print a string (that will be redirected to the
                currently used stream). ]

  SeeAlso     [ ]

******************************************************************************/
#define _PRINT(str) printer_base_print_string(PRINTER_BASE(self), str)

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static void printer_sexp_game_finalize(Object_ptr object, void* dummy);

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PrinterSexpGame class constructor. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PrinterSexpGame_destroy ]

******************************************************************************/
PrinterSexpGame_ptr PrinterSexpGame_create(NuSMVEnv_ptr env,const char* name)
{
  PrinterSexpGame_ptr self = ALLOC(PrinterSexpGame, 1);
  PRINTER_SEXP_GAME_CHECK_INSTANCE(self);

  printer_sexp_game_init(env,
                         self,
                         name,
                         NUSMV_GAME_SYMBOL_FIRST,
                         NUSMV_GAME_SYMBOL_LAST - NUSMV_GAME_SYMBOL_FIRST);

  return self;
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PrinterSexpGame class private initializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PrinterSexpGame_create ]

******************************************************************************/
void printer_sexp_game_init(NuSMVEnv_ptr env,
                            PrinterSexpGame_ptr self,
                            const char* name,
                            int low,
                            size_t num)
{
  /* base class initialization */
  printer_base_init(PRINTER_BASE(self),env, name, low, num, false);

  /* members initialization */

  /* virtual methods settings */
  OVERRIDE(Object, finalize) = printer_sexp_game_finalize;
  OVERRIDE(PrinterBase, print_node) = printer_sexp_game_print_node;
}

/**Function********************************************************************

  Synopsis    [ The PrinterSexpGame class private deinitializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PrinterSexpGame_destroy ]

******************************************************************************/
void printer_sexp_game_deinit(PrinterSexpGame_ptr self)
{
  /* members deinitialization */

  /* base class initialization */
  printer_base_deinit(PRINTER_BASE(self));
}

/**Function********************************************************************

  Synopsis    [ Virtual method that prints the given node (Game specific
                nodes are handled here). ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int printer_sexp_game_print_node(const NuSMVEnv_ptr env,PrinterBase_ptr self, node_ptr n, int priority)
{
  int result;
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));

  nusmv_assert(n != Nil); /* Here only game tokens. */
  switch (node_get_type(n)) {
  case GAME:
    result = _PRINT("\n(GAME ") &&
      _THROW(car(n), 0) &&
      _THROW(cdr(n), 0) &&
      _PRINT(") ");
    break;
  case REACHTARGET:
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(REACHTARGET of ") &&
        _PRINT(buf) &&
        _THROW(cdr(n), 0) &&
        _PRINT(")");
      break;
    }
  case AVOIDTARGET:
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(AVOIDTARGET of ") &&
        _PRINT(buf) &&
        _THROW(cdr(n), 0) &&
        _PRINT(")");
      break;
    }
  case REACHDEADLOCK :
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(REACHDEADLOCK of ") &&
        _PRINT(buf) &&
        _PRINT(")");
      break;
    }
  case AVOIDDEADLOCK:
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(AVOIDDEADLOCK of ") &&
        _PRINT(buf) &&
        _PRINT(")");
      break;
    }
  case BUCHIGAME:
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(BUCHIGAME of ") &&
        _PRINT(buf) &&
        _THROW(cdr(n), 0) &&
        _PRINT(")");
      break;
    }
  case LTLGAME:
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(LTLGAME of ") &&
        _PRINT(buf) &&
        _THROW(cdr(n), 0) &&
        _PRINT(")");
      break;
    }
  case GENREACTIVITY:
    {
      char buf[20];
      sprintf(buf, "%d ", NODE_TO_INT(car(n)));
      result = _PRINT("\n(GENREACTIVITY of ") &&
        _PRINT(buf) &&
        _THROW(cdr(n), 0) &&
        _PRINT(")");
      break;
    }
  case GAME_SPEC_WRAPPER:
    result = _PRINT("\n(GAME_SPEC_WRAPPER ") &&
      _THROW(car(n), 0) &&
      _THROW(cdr(n), 0) &&
      _PRINT(") ");
    break;
  case GAME_EXP_LIST:
    result = _PRINT("(") &&
      _THROW(car(n), 0) &&
      _PRINT(")");
    break;
  case GAME_TWO_EXP_LISTS:
    result = _PRINT("(") &&
      _THROW(car(n), 0) &&
      _PRINT(") -> (") &&
      _THROW(cdr(n), 0) &&
      _PRINT(")");
    break;
  default:
    ErrorMgr_internal_error(errmgr,"No match for node of type %d", node_get_type(n));
    result = 0;
  }
  return result;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PrinterSexpGame class virtual finalizer. ]

  Description [ Called by the class destructor. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void printer_sexp_game_finalize(Object_ptr object, void* dummy)
{
  PrinterSexpGame_ptr self = PRINTER_SEXP_GAME(object);

  printer_sexp_game_deinit(self);
  FREE(self);
}

/**AutomaticEnd***************************************************************/
