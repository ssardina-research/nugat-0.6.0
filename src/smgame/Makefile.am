# FileName	[ Makefile ]
#
# PackageName	[ smgame ]
#
# Synopsis	[ Package-wide Makefile ]
#
# Description	[ ]
#
# Author	[ Roberto Cavada ]
#
# Copyright	[ Copyright (C) 2010 by FBK-irst ]
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

AUTOMAKE_OPTIONS = subdir-objects

CUDD_DIR = $(cudd_dir)
NUSMV_DIR = $(nusmv_dir)

INCLUDES = -I$(top_srcdir)/src -I$(CUDD_DIR)/include -I$(NUSMV_DIR)/code/nusmv/core -I$(NUSMV_DIR)/code/nusmv/shell -I$(NUSMV_DIR)/code/nusmv -I$(NUSMV_DIR)/code -I$(NUSMV_DIR)/build -I$(NUSMV_DIR)/build/code -I$(NUSMV_DIR)


AM_CPPFLAGS = -DDATADIR=\"$(datadir)\" @CPPFLAGS@

PKG_SOURCES = gameInt.h \
	      smgameCmd.c \
	      smgameInit.c \
	      smgameMisc.c \
	      smgameVers.c

smgamedir = $(includedir)/nugat/smgame
smgame_HEADERS =

# -------------------------------------------------------

noinst_LTLIBRARIES = libsmgame.la
libsmgame_la_SOURCES = $(PKG_SOURCES)
libsmgame_la_LIBADD =