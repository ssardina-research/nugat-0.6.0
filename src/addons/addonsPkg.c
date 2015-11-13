/**CFile***********************************************************************

  FileName    [ addonsPkg.c ]

  PackageName [ addons ]

  Synopsis    [ Initialization/quit routines for addons sub-packages. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Marco Roveri ]

  Copyright   [
  This file is part of the ``addons'' package of NuGaT.
  Copyright (C) 2010 Fondazione Bruno Kessler.

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

#if HAVE_GAME
# include "game/game.h"
#endif

#include "utils/utils.h"

static char rcsid[] UTIL_UNUSED = "$Id: addonsPkg.c,v 1.1.2.21 2010-02-22 12:27:03 nusmv Exp $";

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


/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Initializes the NuGaT-specific addons. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void NuGaTAddons_Init(void) 
{
#if HAVE_GAME
   Game_Init();
#endif
}

/**Function********************************************************************

  Synopsis    [ Quits the NuGaT-specific addons. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void NuGaTAddons_Quit(NuSMVEnv_ptr env)
{
#if HAVE_GAME
   Game_Quit(env);
#endif
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/
