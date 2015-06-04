# FileName    [ Makefile ]
#
# PackageName [ parser ]
#
# Synopsis    [ Package-wide Makefile ]
#
# Description [ ]
#
# Author      [ Roberto Cavada, Viktor Schuppan ]
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
NUSMV_PARSER = $(NUSMV_DIR)/src/parser

INCLUDES = -I$(top_srcdir)/src -I$(top_builddir)/src -I$(CUDD_DIR)/include \
	   -I$(NUSMV_DIR)/src -I$(NUSMV_DIR)

GRAMMAR_START = game_begin # initial nugat grammar non-terminal symbol

BUILT_SOURCES = grammar.h grammar.c grammar.y \
	        grammar.y.1 grammar.y.2 grammar.y.3 \
                input.c input.l input.l.1 input.l.2 input.l.3

MOSTLYCLEANFILES = grammar.h grammar.c grammar.y \
	           grammar.y.1 grammar.y.2 grammar.y.3 \
		   input.c input.l input.l.1 input.l.2 input.l.3

AM_YFLAGS = -d
AM_LFLAGS = -l

PKG_SOURCES = grammar.y.1.55 grammar.y.2.55 input.l.2.55 grammar.y input.l

parserdir = $(includedir)/nugat/parser
parser_HEADERS =  

# -------------------------------------------------------

noinst_LTLIBRARIES = libparser.la

libparser_la_SOURCES = $(PKG_SOURCES)

# -------------------------------------------------------
# rules to compose grammar out of its parts

#
# [VS] Ideally the following would be used below. Not doing this for
# now as compatibility with auto tools is not positively clarified.
#
#define mergesubsections
#rm -f $@.tmp;
#for f in $^; do                           \
#  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
#  cat $$f >> $@.tmp;                      \
#  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
#done;
#mv $@.tmp $@;
#endef

input.l.1 : ${NUSMV_PARSER}/input.l.1.50
	rm -f $@.tmp;
	for f in $^; do                           \
	  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
	  cat $$f >> $@.tmp;                      \
	  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
	done;
	mv $@.tmp $@;

input.l.2 : ${NUSMV_PARSER}/input.l.2.25 \
	    ${NUSMV_PARSER}/input.l.2.50 \
            input.l.2.55                 \
            ${NUSMV_PARSER}/input.l.2.75
	rm -f $@.tmp;
	for f in $^; do                           \
	  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
	  cat $$f >> $@.tmp;                      \
	  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
	done;
	mv $@.tmp $@;

input.l.3 : ${NUSMV_PARSER}/input.l.3.50
	rm -f $@.tmp;
	for f in $^; do                           \
	  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
	  cat $$f >> $@.tmp;                      \
	  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
	done;
	mv $@.tmp $@;

input.l : input.l.1 input.l.2 input.l.3 
	rm -f $@.tmp;
	cat input.l.1 >> $@.tmp;
	echo "%%" >> $@.tmp;
	cat input.l.2 >> $@.tmp;
	echo "%%" >> $@.tmp;
	cat input.l.3 >> $@.tmp;
	mv $@.tmp $@;

grammar.y.1 : ${NUSMV_PARSER}/grammar.y.1.50 grammar.y.1.55
	rm -f $@.tmp;
	for f in $^; do                           \
	  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
	  cat $$f >> $@.tmp;                      \
	  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
	done;
	mv $@.tmp $@;

grammar.y.2 : ${NUSMV_PARSER}/grammar.y.2.50 grammar.y.2.55
	rm -f $@.tmp;
	for f in $^; do                           \
	  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
	  cat $$f >> $@.tmp;                      \
	  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
	done;
	mv $@.tmp $@;

grammar.y.3 : ${NUSMV_PARSER}/grammar.y.3.50
	rm -f $@.tmp;
	for f in $^; do                           \
	  echo "  /* BEGINS: $${f} */" >> $@.tmp; \
	  cat $$f >> $@.tmp;                      \
	  echo "  /* ENDS: $${f} */" >> $@.tmp;   \
	done;
	mv $@.tmp $@;

grammar.y : grammar.y.1 grammar.y.2 grammar.y.3
	rm -f $@.tmp;
	cat grammar.y.1 >> $@.tmp;
	echo "%%" >> $@.tmp;
	cat grammar.y.2 >> $@.tmp;
	echo "%%" >> $@.tmp;
	cat grammar.y.3 >> $@.tmp;
	${SED} -i -e 's/@start@/${GRAMMAR_START}/' $@.tmp;
	mv $@.tmp $@;
