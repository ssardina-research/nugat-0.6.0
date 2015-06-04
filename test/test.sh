#!/bin/sh

# FileName    [ test.sh ]
#
# PackageName [ NuGaT ]
#
# Synopsis    [ Ad-hoc script to run a few tests. ]
#
# Description [ ]
#
# Author      [ Viktor Schuppan ]
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

NuGaT=../NuGaT

cd test
${NuGaT} test_no_ltlgame.smv
res=$?
if [ "${res}" -eq 0 ]; then
  echo "================================================================================"
  echo "Testing non-LTLGAME properties successful."
  echo "================================================================================"
else
  echo "================================================================================"
  echo "Testing non-LTLGAME properties failed."
  echo "================================================================================"
  cd ..
  exit 1
fi

${NuGaT} test_ltlgame.smv
res=$?
if [ "${res}" -eq 0 ]; then
  echo "================================================================================"
  echo "Testing LTLGAME properties successful."
  echo "================================================================================"
else
  echo "================================================================================"
  echo "Testing LTLGAME properties failed."
  echo "================================================================================"
  cd ..
  exit 1
fi
cd ..

exit 0
