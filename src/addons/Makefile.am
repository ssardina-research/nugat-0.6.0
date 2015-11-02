# FileName    [ Makefile ]
#
# PackageName [ addons ]
#
# Synopsis    [ Package-wide Makefile ]
#
# Description [ ]
#
# Author      [ Marco Roveri ]
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
#
# Revision	[1.1.2.4 2003/08/04 11:29:51]

AUTOMAKE_OPTIONS = subdir-objects

## enable or disable the GAME package 
if HAVE_GAME
 game_libs = game/libgame.la
 _GAME = game
else
 game_libs = 
endif

## -------------------------------------------------------
SUBDIRS = $(_GAME)

#SUBDIRS = $(ADDONS_PKGS)
# This is done to force distribution of only configured addons
DIST_SUBDIRS = $(SUBDIRS) 

CUDD_DIR = $(cudd_dir)
NUSMV_DIR = $(nusmv_dir)


INCLUDES = -I$(top_srcdir)/src -I$(CUDD_DIR)/include -I$(NUSMV_DIR)/code/nusmv/core -I$(NUSMV_DIR)/code/nusmv/shell -I$(NUSMV_DIR)/code/nusmv -I$(NUSMV_DIR)/code -I$(NUSMV_DIR)/build -I$(NUSMV_DIR)

PKG_SOURCES = addonsPkg.c
addonsdir = $(includedir)/nusmv/addons
addons_HEADERS = addons.h

## -------------------------------------------------------
## NuGaT's addons library:

# lib_LTLIBRARIES = libaddons.la	
noinst_LTLIBRARIES = libaddons.la
libaddons_la_SOURCES = $(PKG_SOURCES)
libaddons_la_LIBADD =    \
	$(game_libs)
