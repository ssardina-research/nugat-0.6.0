/**CHeaderFile*****************************************************************

  FileName    [ smgameInt.h ]

  PackageName [ smgame ]

  Synopsis    [ Internal declarations for the main package. ]

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

  Revision    [$Id: smInt.h,v 1.10.2.12.4.8.4.5 2009-07-23 07:44:29 nusmv Exp $]

******************************************************************************/

#ifndef __SMGAME_INT_H__
#define __SMGAME_INT_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "utils/utils.h"

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Constants declarations                                                    */
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


/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/
EXTERN void Smgame_Init ARGS((void));
EXTERN void Smgame_End ARGS((void));
EXTERN void Smgame_Reset ARGS((void));
EXTERN void Smgame_BatchMain ARGS(());
EXTERN void Smgame_AddCmd ARGS((void));
EXTERN char* Smgame_NuGaTReadVersion ARGS((void));

#endif /* __SMGAME_INT_H__ */
