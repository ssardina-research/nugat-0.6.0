/**CHeaderFile*****************************************************************

  FileName    [ CheckerGame.h ]

  PackageName [ game.walkers ]

  Synopsis    [ Public interface of class 'CheckerGame' ]

  Description [ ]

  SeeAlso     [ CheckerGame.c ]

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

  Revision    [$Id: CheckerGame.h,v 1.1.2.2 2010-02-08 15:28:10 nusmv Exp $]

******************************************************************************/

#ifndef __CHECKER_GAME_H__
#define __CHECKER_GAME_H__

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

/**Type***********************************************************************

  Synopsis    [ Definition of the public accessor for class CheckerGame. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct CheckerGame_TAG* CheckerGame_ptr;

/*---------------------------------------------------------------------------*/
/* Structure declarations                                                    */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macros**********************************************************************

  Synopsis    [ To cast and check instances of class CheckerGame. ]

  Description [ These macros must be used respectively to cast and to
                check instances of class CheckerGame. ]

  SeeAlso     [ ]

******************************************************************************/
#define CHECKER_GAME(self) ((CheckerGame_ptr) self)
#define CHECKER_GAME_CHECK_INSTANCE(self) \
         (nusmv_assert(CHECKER_GAME(self) != CHECKER_GAME(NULL)))

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/
EXTERN CheckerGame_ptr CheckerGame_create ARGS((void));

/**AutomaticEnd***************************************************************/

#endif /* __CHECKER_GAME_H__ */
