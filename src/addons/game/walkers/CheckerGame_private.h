/**CHeaderFile*****************************************************************

  FileName    [ CheckerGame_private.h ]

  PackageName [ game.walkers ]

  Synopsis    [ Private and protected interface of class 'CheckerGame'. ]

  Description [ This file can be included only by derived and friend classes. ]

  SeeAlso     [ CheckerGame.h ]

  Author      [ Andrei Tchaltsev ]

  Copyright   [
  This file is part of the ``game.walkers'' package of
  NuGaT. Copyright (C) 2010 by FBK-irst.

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

  Revision    [$Id: CheckerGame_private.h,v 1.1.2.2 2010-02-08 15:28:10 nusmv Exp $]

******************************************************************************/

#ifndef __CHECKER_GAME_PRIVATE_H__
#define __CHECKER_GAME_PRIVATE_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "CheckerGame.h"

#include "compile/type_checking/checkers/CheckerBase.h"
#include "compile/type_checking/checkers/CheckerBase_private.h"
#include "utils/utils.h"

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

  Synopsis    [ CheckerGame class definition derived from class
                CheckerBase. ]

  Description [ ]

  SeeAlso     [ Base class CheckerBase ]

******************************************************************************/
typedef struct CheckerGame_TAG
{
  /* this MUST stay on the top */
  INHERITS_FROM(CheckerBase);

  /* -------------------------------------------------- */
  /*                  Private members                   */
  /* -------------------------------------------------- */

  /* -------------------------------------------------- */
  /*                  Virtual methods                   */
  /* -------------------------------------------------- */

} CheckerGame;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ Short way of calling tc_set_expression_type. ]

  Description [ Use this macro to set an expression type within the
                master type checker. Must be used from within a
                method. This can be used when expressions that are
                node_ptr. ]

  SeeAlso     [ ]

******************************************************************************/
#define _SET_TYPE(expr, type)                                                 \
  tc_set_expression_type(TYPE_CHECKER(NODE_WALKER(self)->master), expr, type)

/**Macro***********************************************************************

  Synopsis    [ Short way of calling tc_lookup_expr_type. ]

  Description [ Use this macro to get an expression type from the
                master type checker. Must be used from within a
                method. This can be used when expressions that are
                node_ptr. ]

  SeeAlso     [ ]

******************************************************************************/
#define _GET_TYPE(expr)                                              \
  tc_lookup_expr_type(TYPE_CHECKER(NODE_WALKER(self)->master), expr)

/**Macro***********************************************************************

  Synopsis    [ Short way of calling checker_base_manage_violation. ]

  Description [ Use this macro to manage a violation at the master
                type checker level. Must be used from within a
                method. This can be used when expressions that are
                node_ptr. ]

  SeeAlso     [ ]

******************************************************************************/
#define _VIOLATION(viol_id, expr)                                  \
  checker_base_manage_violation(CHECKER_BASE(self), viol_id, expr)

/**Macro***********************************************************************

  Synopsis    [ Short way of calling type_checker_print_error_message. ]

  Description [ Use this macro to recursively call
                type_checking_check_expression into violation
                handlers. This can be used when expressions that are
                node_ptr. ]

  SeeAlso     [ ]

******************************************************************************/
#define _PRINT_ERROR_MSG(exp, is_error)                                     \
  type_checker_print_error_message(TYPE_CHECKER(NODE_WALKER(self)->master), \
                                   exp,                                     \
                                   is_error)

/* ---------------------------------------------------------------------- */
/* Private methods to be used by derivated and friend classes only        */
/* ---------------------------------------------------------------------- */
EXTERN void checker_game_init ARGS((CheckerGame_ptr self));
EXTERN void checker_game_deinit ARGS((CheckerGame_ptr self));

#endif /* __CHECKER_GAME_PRIVATE_H__ */
