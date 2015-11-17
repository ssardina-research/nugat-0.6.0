/**CHeaderFile*****************************************************************

  FileName    [ addons.h ]

  PackageName [ addons ]

  Synopsis    [ ]

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

  Revision    [$Id: addons.h,v 1.1.2.1 2007-08-12 10:05:20 nusmv Exp $]

******************************************************************************/

#ifndef _NuGaT_ADDONS
#define _NuGaT_ADDONS

#if HAVE_CONFIG_H
#include "config.h"
#endif


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

EXTERN void NuGaTAddons_Init ARGS((NuSMVEnv_ptr env));
EXTERN void NuGaTAddons_Quit ARGS((NuSMVEnv_ptr env));

/**AutomaticEnd***************************************************************/

#endif /* _NuGaT_ADDONS */
