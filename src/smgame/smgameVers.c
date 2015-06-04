/**CFile***********************************************************************

  FileName    [ smgameVers.c ]

  PackageName [ smgame ]

  Synopsis    [ Supplies the compile date and version information. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Marco Roveri, Viktor Schuppan ]

  Copyright   [
  This file is part of the ``smgame'' package of NuGaT.
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
# include "config.h"
#endif

#include "utils/utils.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: smVers.c,v 1.3.6.2.4.2.6.1 2007-12-20 17:12:03 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/
#ifndef PACKAGE_BUILD_DATE
#define PACKAGE_BUILD_DATE "<compile date not supplied>"
#endif

#ifndef PACKAGE_STRING
#define PACKAGE_STRING "NuGaT 0.5.0"
#endif


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Returns the current NuGaT version. ]

  Description [ Returns a static string giving the NuGaT version
                and compilation timestamp. The user should not free
                this string. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
char* Smgame_NuGaTReadVersion()
{
  static char version[1024];

  (void) sprintf(version,
                 "%s (compiled on %s)",
                 PACKAGE_STRING,
                 PACKAGE_BUILD_DATE);
  return version;
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/
