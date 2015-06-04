/**CFile***********************************************************************

  FileName    [ smgameDummyMac.c ]

  PackageName [ smgame ]

  Synopsis    [ This is a hack, i.e. an auxiliary dummy file to make 'ar'
                work under Mac OS X. ]

  Description [ Under Mac OS X the source of libnusmv_la_SOURCES (in
                nugat/Makefile.am) requires at least one object
                file. But under Linux, functions of such an object
                file (specified as the source of libnugat_la_SOURCES)
                somehow are not accessible from other files.  So, a
                dummy object file was created and specified as the
                source of libnugat_la_SOURCES, and no function from
                this dummy file is used. ]

  Author      [ Andrei Tchaltsev ]

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
/* See the Description above. */
void smgame_dummy_function_to_make_ar_work_under_mac_os_x_DO_NOT_USE_THIS_FUNCTION()
{
}
