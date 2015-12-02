/**CHeaderFile*****************************************************************

  FileName    [ gameCheckLTLSF07_gba_wring.h ]

  PackageName [ game ]

  Synopsis    [ Implements a simple interface to the Wring LTL to
                generalized B\"uchi automaton translator. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Viktor Schuppan ]

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

  Revision    [$Id: gameCheckLTLSF07_gba_wring.h,v 1.1.2.1 2010-01-11 15:23:12 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_CHECKLTLSF07_GBA_WRING_H__
#define __GAME_CHECKLTLSF07_GBA_WRING_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "gameCheckLTLSF07_gba.h"

#include "node/node.h"
#include "utils/utils.h"

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ Definition of the public accessor for Game_SF07_gba_wring. ]

  Description [ ]

  SeeAlso     [ ]

******************************************************************************/
typedef struct Game_SF07_gba_wring_TAG *Game_SF07_gba_wring_ptr;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ To cast and check instances of Game_SF07_gba_wring. ]

  Description [ These macros must be used respectively to cast and to
                check instances of Game_SF07_gba_wring. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
#define GAME_SF07_GBA_WRING(x) ((Game_SF07_gba_wring_ptr) x)
#define GAME_SF07_GBA_WRING_CHECK_INSTANCE(x) \
  { \
    nusmv_assert(GAME_SF07_GBA_WRING(x) != GAME_SF07_GBA_WRING(NULL)); \
    nusmv_assert((self->po_size_line == 0) || \
                 (self->po_line != (char *) NULL)); \
    nusmv_assert((self->po_size_s == 0) || \
                 (self->po_s != (char *) NULL)); \
  }

/*---------------------------------------------------------------------------*/
/* Public Interface                                                          */
/*---------------------------------------------------------------------------*/

EXTERN Game_SF07_gba_ptr Game_SF07_gba_wring_ltl2gba
ARGS((NuSMVEnv_ptr env,node_ptr formula));

EXTERN Game_SF07_gba_wring_ptr Game_SF07_gba_wring_create ARGS(());

EXTERN void Game_SF07_gba_wring_destroy
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self));

EXTERN void Game_SF07_gba_wring_set_formula
ARGS((Game_SF07_gba_wring_ptr self, node_ptr formula));

EXTERN void Game_SF07_gba_wring_set_binary_file_name
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, const char *binary_file_name));

EXTERN void Game_SF07_gba_wring_set_input_file_name
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, const char *input_file_name));

EXTERN void Game_SF07_gba_wring_set_output_file_name
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self, const char *output_file_name));

EXTERN Game_SF07_gba_ptr Game_SF07_gba_wring_get_gba
ARGS((Game_SF07_gba_wring_ptr self));

EXTERN void Game_SF07_gba_wring_write_input_file
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self));

EXTERN int Game_SF07_gba_wring_execute
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self));

EXTERN void Game_SF07_gba_wring_parse_output_file
ARGS((NuSMVEnv_ptr env,Game_SF07_gba_wring_ptr self));

#endif /* __GAME_CHECKLTLSF07_GBA_WRING_H__ */
