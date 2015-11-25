/**CHeaderFile*****************************************************************

  FileName    [ PrinterSexpGame_private.h ]

  PackageName [ game.walkers ]

  Synopsis    [ Private and protected interface of class
                'PrinterSexpGame'. ]

  Description [ This file can be included only by derived and friend
                classes. ]

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

  Revision    [$Id: PrinterGame_private.h,v 1.1.2.2 2010-02-08 14:39:01 nusmv Exp $]

******************************************************************************/

#ifndef __PRINTER_SEXP_GAME_PRIVATE_H__
#define __PRINTER_SEXP_GAME_PRIVATE_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "PrinterSexpGame.h"

#include "node/printers/PrinterBase.h"
#include "node/printers/PrinterBase_private.h"
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

  Synopsis    [ PrinterSexpGame class definition derived from class
                PrinterBase. ]

  Description [ ]

  SeeAlso     [ Base class PrinterBase ]

******************************************************************************/
typedef struct PrinterSexpGame_TAG
{
  /* this MUST stay on the top */
  INHERITS_FROM(PrinterBase);

  /* -------------------------------------------------- */
  /*                  Private members                   */
  /* -------------------------------------------------- */

  /* -------------------------------------------------- */
  /*                  Virtual methods                   */
  /* -------------------------------------------------- */

} PrinterSexpGame;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/* ---------------------------------------------------------------------- */
/* Private methods to be used by derivated and friend classes only        */
/* ---------------------------------------------------------------------- */
EXTERN void printer_sexp_game_init ARGS((NuSMVEnv_ptr env,PrinterSexpGame_ptr self,
                                         const char* name,
                                         int low,
                                         size_t num));

EXTERN void printer_sexp_game_deinit ARGS((PrinterSexpGame_ptr self));

EXTERN int printer_sexp_game_print_node ARGS((PrinterBase_ptr self,
                                              node_ptr n,
                                              int priority));

#endif /* __PRINTER_SEXP_GAME_PRIVATE_H__ */
