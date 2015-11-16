/**CFile***********************************************************************

  FileName    [ PrinterGame.c ]

  PackageName [ game.walkers ]

  Synopsis    [ Implementaion of class 'PrinterGame' ]

  Description [ This class is used to print expressions and constructs
                related to the Game package. ]

  SeeAlso     [ PrinterGame.h ]

  Author      [ Andrei Tchaltsev ]

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

  Revision    [$Id: PrinterGame.c,v 1.1.2.3 2010-02-08 14:39:01 nusmv Exp $]

******************************************************************************/

#include "PrinterGame.h"
#include "PrinterGame_private.h"
#include "addons/game/parser/game_symbols.h"

#include "parser/symbols.h"

#include "utils/error.h"
#include "utils/ErrorMgr.h"

static char rcsid[] UTIL_UNUSED = "$Id: PrinterGame.c,v 1.1.2.3 2010-02-08 14:39:01 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/
/* See 'PrinterGame_private.h' for class 'PrinterGame' definition. */

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
static void printer_game_finalize(Object_ptr object, void* dummy);

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PrinterGame class constructor. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PrinterGame_destroy ]

******************************************************************************/
PrinterGame_ptr PrinterGame_create(const NuSMVEnv_ptr env,const char* name)
{
  PrinterGame_ptr self = ALLOC(PrinterGame, 1);
  PRINTER_GAME_CHECK_INSTANCE(self);

  printer_game_init(env,
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

  Synopsis    [ The PrinterGame class private initializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PrinterGame_create ]

******************************************************************************/
void printer_game_init(const NuSMVEnv_ptr env,
                       PrinterGame_ptr self,
                       const char* name,
                       int low,
                       size_t num)
{
  /* base class initialization */
  printer_base_init(PRINTER_BASE(self),env, name, low, num,
                    false /*NULL not handled*/);

  /* members initialization */

  /* virtual methods settings */
  OVERRIDE(Object, finalize) = printer_game_finalize;
  OVERRIDE(PrinterBase, print_node) = printer_game_print_node;
}

/**Function********************************************************************

  Synopsis    [ The PrinterGame class private deinitializer. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ PrinterGame_destroy ]

******************************************************************************/
void printer_game_deinit(PrinterGame_ptr self)
{
  /* members deinitialization */

  /* base class initialization */
  printer_base_deinit(PRINTER_BASE(self));
}

/**Function********************************************************************

  Synopsis    [ Virtual menthod that prints the given node (Game specific
                nodes are handled here). ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
int printer_game_print_node(PrinterBase_ptr self, node_ptr n, int priority)
{

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  const ErrorMgr_ptr errmgr = ERROR_MGR(NuSMVEnv_get_value(env, ENV_ERROR_MANAGER));
    
  switch (node_get_type(n)) {
  case GAME:
    /* this node is not expected to be printted as usual expression */
    ErrorMgr_rpterr(errmgr,"Unexpected printing of high-level GAME constructs");

  case REACHTARGET:
  case AVOIDTARGET:
  case REACHDEADLOCK:
  case AVOIDDEADLOCK:
  case BUCHIGAME:
  case LTLGAME:
  case GENREACTIVITY:
    /* these specifications are not expected to be printted as usual exp */
    ErrorMgr_rpterr(errmgr,"Unexpected printing of high-level GAME specifications");

    /* this is GAME specifications wrapper. Player name is on the left
       and the expression on the right */
  case GAME_SPEC_WRAPPER:
    if (cdr(n) == Nil) {
      /* Here we should be in REACH or AVOIDDEADLOCK. No way to check
         though. */
      return _THROW(car(n), 0) /* print the player name */;
    } else {
      return _THROW(car(n), 0) /* print the player name */ &&
        _PRINT(" ") &&
        _THROW(cdr(n), 0) /* print the expression */;
    }
    break;

  case GAME_EXP_LIST: /* print parentheses around the expressions in the list */
    nusmv_assert(Nil == cdr(n) &&
                 Nil != car(n) && CONS == node_get_type(car(n)));
    return _PRINT("(") && _THROW(car(n), 0) &&  _PRINT(")");
    break;

    /* print parentheses around the the lists and put "->" between them */
  case GAME_TWO_EXP_LISTS:
    nusmv_assert(Nil != car(n) && Nil != cdr(n) &&
                 CONS == node_get_type(car(n)) &&
                 CONS == node_get_type(cdr(n)));
    return _PRINT("(") &&
      _THROW(car(n), 0) &&
      _PRINT(") -> (") &&
      _THROW(cdr(n), 0) &&
      _PRINT(")");

  default:
    ErrorMgr_internal_error(errmgr,"printer_game_print_node: unsupported type = %d",
                   node_get_type(n));
  }

  ErrorMgr_rpterr(errmgr,"PrinterGame.c : Impossible code");
  return 1;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ The PrinterGame class virtual finalizer. ]

  Description [ Called by the class destructor. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
static void printer_game_finalize(Object_ptr object, void* dummy)
{
  PrinterGame_ptr self = PRINTER_GAME(object);

  printer_game_deinit(self);
  FREE(self);
}

/**AutomaticEnd***************************************************************/
