# FileName    [ Makefile ]
#
# PackageName [ NuGaT ]
#
# Synopsis    [ Package-wide Makefile ]
#
# Description [ ]
#
# Author      [ Roberto Cavada ]
#
# Copyright   [ Copyright (C) 2010 by FBK-irst ]
#
# NuGaT is free software; you can redistribute it and/or 
# modify it under the terms of the GNU Lesser General Public 
# License as published by the Free Software Foundation; either 
# version 2.1 of the License, or (at your option) any later version.
#
# NuGaT is distributed in the hope that it will be useful, 
# but WITHOUT ANY WARRANTY; without even the implied warranty of 
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU 
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public 
# License along with this library; if not, write to the Free Software 
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307  USA.
#
# For more information on NuGaT see <http://es.fbk.eu/tools/nugat>
# or email to <nugat-users@list.fbk.eu>.
# Please report bugs to <nugat-users@list.fbk.eu>.
#
# To contact the NuGaT development board, email to <nugat@list.fbk.eu>.]

CUDD_DIR = $(cudd_dir)
NUSMV_DIR = $(nusmv_dir)


INCLUDES = -I$(top_srcdir)/src -I$(CUDD_DIR)/include -I$(NUSMV_DIR)/code/nusmv/core -I$(NUSMV_DIR)/code/nusmv/shell -I$(NUSMV_DIR)/code/nusmv -I$(NUSMV_DIR)/code -I$(NUSMV_DIR)

SUBDIRS = contrib examples src test


TESTS = ${top_srcdir}/test/test.sh

# ----------------------------------------------------------------------

bin_PROGRAMS = NuGaT

lib_LTLIBRARIES = libnugat.la

# ----------------------------------------------------------------------
# The NuGaT executable
NuGaT_SOURCES = $(top_srcdir)/src/smgame/smgameMain.c
NuGaT_LDADD = libnugat.la #(NUSMV_DIR)/libnusmvcore.la $(NUSMV_DIR)/librbcdag.la NOT EXISTS
# ----------------------------------------------------------------------

# lib for external linking:
libnugat_la_SOURCES = src/smgame/smgameDummyMac.c  # to make 'ar' work on mac osx. See sm/smDummyMac.c for more details.
libnugat_la_LIBADD = \
	$(top_builddir)/src/libnugatsrc.la

libnugat_la_DEPENDENCIES = \
	$(top_builddir)/src/libnugatsrc.la

# ----------------------------------------------------------------------
dist-hook:      
	rm -rf `find $(distdir) -name CVS`
	rm -rf `find $(distdir) -name ".svn"`
	rm -rf `find $(distdir) -name '*~'`     
	cd $(distdir)/src/parser && \
	  rm -f grammar.h grammar.c grammar.y input.c input.l
