/**CHeaderFile*****************************************************************

  FileName    [ GamePlayer.h ]

  PackageName [ game ]

  Synopsis    [ Public interface of class 'GamePlayer' ]

  Description [ ]

  SeeAlso     [ ]

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

  Revision    [$Id: GamePlayer.h,v 1.1.2.1 2010-02-05 17:19:08 nusmv Exp $]

******************************************************************************/

#ifndef __GAME_PLAYER__H__
#define __GAME_PLAYER__H__

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include "utils/utils.h"
#include "utils/ustring.h"

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**Type************************************************************************

  Synopsis    [ An enumeration to distinguish players. ]

  Description [ This enumeration is often used as type of a variable
                or a parameter to distinguish which player is to be
                dealt with. ]

  SeeAlso     [ ]

******************************************************************************/
enum GamePlayer_TAG {
  PLAYER_1,
  PLAYER_2
};
typedef enum GamePlayer_TAG GamePlayer;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**Macro***********************************************************************

  Synopsis    [ Strings representing the players\' names in the input files. ]

  Description [ Note that these strings cannot be met as identifiers
                in an input file because they are also keywords. This
                fact is used when player definitions are converted
                into module definitions during parsing.

                For developers: make sure that these strings are the
                same as in the grammar.y, i.e. names of the players'
                modules. ]

  SeeAlso     [ ]

******************************************************************************/
#define PLAYER_NAME_1 "PLAYER_1"
#define PLAYER_NAME_2 "PLAYER_2"

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

EXTERN string_ptr Game_PlayerToStr ARGS((NuSMVEnv_ptr env,GamePlayer player));
EXTERN GamePlayer Game_StrToPlayer ARGS((NuSMVEnv_ptr env,string_ptr str));

/**AutomaticEnd***************************************************************/

#endif /* __GAME_PLAYER__H__ */
