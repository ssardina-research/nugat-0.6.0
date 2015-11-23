/**CFile***********************************************************************

  FileName    [ smgameInit.c ]

  PackageName [ smgame ]

  Synopsis    [ Initializes and ends NuGaT. ]

  Description [ ]

  SeeAlso     [ ]

  Author      [ Viktor Schuppan ]

  Copyright   [
  This file is part of the ``smgame'' package of NuGaT.
  Copyright (C) 2010 FBK-irst.

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

#include "smgameInt.h"

#include "addons/addons.h"
#include "opt/opt.h"
#include "cinit/cinit.h"//#include "sm/sm.h"
#include "cinit/cinitInt.h"
#include "utils/utils.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: smInit.c,v 1.4.2.22.2.3.2.20.4.18 2009-12-14 17:12:12 nusmv Exp $";

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
EXTERN FILE* nusmv_stderr;

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Shuts down and restarts the system. ]

  Description [ Takes care of the game specific parts. The rest is
                deferred to sm. ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Smgame_Reset(NuSMVEnv_ptr env)
{
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));

  if (opt_verbose_level_gt(opts, 1)) {
    fprintf(nusmv_stderr, "Shutting down the game part...\n");
  }
  NuGaTAddons_Quit(env);
  if (opt_verbose_level_gt(opts, 2)) {
    fprintf(nusmv_stderr, "Done\n");
  }

  CInit_reset_first(env);
  CInit_reset_last(env);

  if (opt_verbose_level_gt(opts, 1)) {
    fprintf(nusmv_stderr, "Starting the game part...\n");
  }
  NuGaTAddons_Init(env);
  if (opt_verbose_level_gt(opts, 2)) {
    fprintf(nusmv_stderr, "Done\n");
  }

  if (opt_verbose_level_gt(opts, 1)) {
    fprintf(nusmv_stderr, "The game part is now up and ready\n");
  }
}

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Starts the system. ]

  Description [ Takes care of the game specific parts. The rest is
                deferred to sm. ]

  SideEffects [ ]

  SeeAlso     [ Smgame_End ]

******************************************************************************/
void Smgame_Init(NuSMVEnv_ptr env)
{
  OptsHandler_ptr opts = OPTS_HANDLER(NuSMVEnv_get_value(env, ENV_OPTS_HANDLER));
  //CInit_init(); //this is already called by NuSMVCore init
  set_pgm_name(opts, PACKAGE_NAME);
  //NuGaTAddons_Init();
  Smgame_AddCmd(env);
}

/**Function********************************************************************

  Synopsis    [ Shuts down the system. ]

  Description [ Takes care of the game specific parts. The rest is
                deferred to sm. ]

  SideEffects [ ]

  SeeAlso     [ Smgame_Init ]

******************************************************************************/
void Smgame_End(NuSMVEnv_ptr env)
{
  NuGaTAddons_Quit(env);
  CInit_end(env);
}
