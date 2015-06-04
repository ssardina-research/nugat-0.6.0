/**CHeaderFile*****************************************************************

  FileName    [ symbols.h ]

  PackageName [ game.parser ]

  Synopsis    [ Parse-tree symbols set required by GAME package ]

  Description [ This file defines an enum containing all the GAME
                parse tree symbols set ]

  SeeAlso     [ ]

  Author      [ ]

  Copyright   [
  This file is part of the ``game.parser'' package of NuGaT.
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

  Revision    [$Id: game_symbols.h,v 1.1.2.4 2010-02-08 14:24:28 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_PARSER_SYMBOLS_H__
#define __GAME_PARSER_SYMBOLS_H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

enum {
  NUSMV_GAME_SYMBOL_FIRST = 2000, /* Do not touch this */
  /* ---------------------------------------------------------------------- */

  GAME,

  REACHTARGET,
  AVOIDTARGET,
  REACHDEADLOCK,
  AVOIDDEADLOCK,
  BUCHIGAME,
  LTLGAME,
  GENREACTIVITY,

  NUSMV_GAME_STATEMENTS_SYMBOL_LAST,
  /* ---------------------------------------------------------------------- */


  /* ---------------------------------------------------------------------- */
  NUSMV_GAME_EXPR_SYMBOL_FIRST,

  GAME_SPEC_WRAPPER,  /* game specs are wrapped in this node by game
                         flattener */
  GAME_EXP_LIST,      /* one exp list */
  GAME_TWO_EXP_LISTS, /* two exp lists */

  NUSMV_GAME_EXPR_SYMBOL_LAST,
  /* ---------------------------------------------------------------------- */

  NUSMV_GAME_SYMBOL_LAST
};

#endif /* __GAME_PARSER_SYMBOLS_H__ */
