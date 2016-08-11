/**CFile***********************************************************************

FileName    [ TypeCheckerGame.c ]

PackageName [ game ]

Synopsis    [ Type checking of game stuff not handled by walkers. ]

Description [ ]

SeeAlso     [ TypeCheckerGame.h, TypeChecker.c ]

Author      [ Andrei Tchaltsev, Roberto Cavada, Viktor Schuppan ]

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

#include "PropGame.h"
#include "parser/game_symbols.h"

#include "compile/type_checking/TypeChecker.h"
#include "node/node.h"
#include "opt/opt.h"
#include "prop/Prop.h"
#include "utils/utils.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: TypeChecker.c,v 1.1.2.56.4.14 2010-01-11 15:07:54 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

extern int nusmv_yylineno;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Checks that the expression constituting the property is
                correctly typed]

  Description [ If some of expressions violates the type system, the
                type checker's violation handler is invoked. See
                checkers into the checkers sub-package for more info.

                The type checker remebers all the checked expressions
                and their types, thus TypeChecker_get_expression_type
                uses memoizing to return the type of already checked
                expressions.

                If the property violates the type system, the false
                value is return, and true value otherwise. ]

   SideEffects [ ]

   SeeAlso     [ TypeChecker_check_property ]

******************************************************************************/
boolean TypeCheckerGame_check_property(TypeChecker_ptr self,
                                       Prop_ptr property)
{
  int kind;
  boolean isOK;
  node_ptr exp;

  const NuSMVEnv_ptr env = EnvObject_get_environment(ENV_OBJECT(self));
  const NodeMgr_ptr nodemgr = NODE_MGR(NuSMVEnv_get_value(env, ENV_NODE_MGR));
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  StreamMgr_ptr streams = STREAM_MGR(NuSMVEnv_get_value(env, ENV_STREAM_MANAGER));
  OStream_ptr errostream = StreamMgr_get_error_ostream(streams);

  TYPE_CHECKER_CHECK_INSTANCE(self);

  switch (Prop_get_type(property)) {
  case Prop_NoType: nusmv_assert(false); /* incorrect property */
  case PropGame_ReachTarget: kind = REACHTARGET; break;
  case PropGame_AvoidTarget: kind = AVOIDTARGET; break;
  case PropGame_BuchiGame: kind = BUCHIGAME; break;
  case PropGame_LtlGame: kind = LTLGAME; break;
  case PropGame_GenReactivity: kind = GENREACTIVITY; break;

    /* expression is Nil. so return success */
  case PropGame_ReachDeadlock:
  case PropGame_AvoidDeadlock:
    nusmv_assert(Nil ==  Prop_get_expr(property));
    return true;

  default: nusmv_assert(false);
  } /* switch */

  nusmv_yylineno = node_get_lineno(Prop_get_expr(property));
  exp = find_node(nodemgr,kind, Prop_get_expr(property), Nil);

  isOK = TypeChecker_is_specification_wellformed(self, exp);

  if (opt_verbose_level_gt(opts, 3)) {
    if (isOK) {
      /* the property is not yet inserted to database => there is no index */
      OStream_printf(errostream, "Successful type-checking of a property\n");
    }
  }

  return isOK;
}

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/
