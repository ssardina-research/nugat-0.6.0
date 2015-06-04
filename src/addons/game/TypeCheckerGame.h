/**CHeaderFile*****************************************************************

  FileName    [ TypeCheckerGame.h ]

  PackageName [ game ]

  Synopsis    [ ]

  Description [ See TypeCheckerGame.c ]

  SeeAlso     [ TypeCheckerGame.c, TypeChecker.h ]

  Author      [ Andrei Tchaltsev, Viktor Schuppan ]

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

  Revision    [$Id: TypeChecker.h,v 1.1.2.17.6.4 2009-11-06 19:03:34 nusmv Exp $]

******************************************************************************/

#ifndef __TYPE_CHECKER_GAME_H__
#define __TYPE_CHECKER_GAME_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

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

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/
EXTERN boolean TypeCheckerGame_check_property ARGS((TypeChecker_ptr self,
                                                    Prop_ptr property));

/**AutomaticEnd***************************************************************/

#endif /* __TYPE_CHECKER_GAME_H__ */
