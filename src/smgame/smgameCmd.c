/**CFile***********************************************************************

  FileName    [ smgameCmd.c ]

  PackageName [ smgame ]

  Synopsis    [ Interface of the smgame package with the shell. ]

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

#include "smgame/smgameInt.h"

#include "cmd/cmd.h"
#include "opt/opt.h"
#include "utils/utils.h"
#include "utils/ucmd.h"

#include <stdio.h>

static char rcsid[] UTIL_UNUSED = "$Id: smCmd.c,v 1.11.2.20.4.2 2006-05-15 09:06:16 nusmv Exp $";

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
EXTERN FILE* nusmv_stderr;


/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/
static int CommandGameReset(int argc, char **argv);
static int UsageGameReset ARGS((void));

/**AutomaticEnd***************************************************************/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [ Replaces the standard with the game-specific reset command. ]

  Description [ ]

  SideEffects [ ]

  SeeAlso     [ ]

******************************************************************************/
void Smgame_AddCmd(void){
  boolean res;

  res = Cmd_CommandRemove("reset");
  nusmv_assert(res);
  Cmd_CommandAdd("reset", CommandGameReset, 0, false);
}


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis           [ Implements the reset command. ]

  CommandName        [ reset ]

  CommandSynopsis    [ Resets the whole system. ]

  CommandArguments   [ \[-h\] ]

  CommandDescription [ Resets the whole system, in order to read in
                       another model and to perform verification on
                       it. <p>

  Command options:<p>
  <dl>
    <dt> -h
       <dd> Prints the command usage.
  </dl>]

  SideEffects        [ ]

  SeeAlso            [ ]

******************************************************************************/
static int CommandGameReset(int argc, char ** argv)
{
  int c;

  util_getopt_reset();
  while ((c = util_getopt(argc, argv, "h")) != EOF) {
    switch (c) {
    case 'h':
      goto CommandGameReset_return_usage;
    default:
      goto CommandGameReset_return_usage;
    }
  }
  if (argc != util_optind) {
    goto CommandGameReset_return_usage;
  }

  Smgame_Reset();

  /* Avoid compiler warning. */
  goto CommandGameReset_return_0;

 CommandGameReset_return_0:
  return 0;

 CommandGameReset_return_usage:
  return UsageGameReset();
}

static int UsageGameReset()
{
  fprintf(nusmv_stderr, "usage: reset [-h]\n");
  fprintf(nusmv_stderr, "   -h \t\tPrints the command usage.\n");
  return 1;
}
