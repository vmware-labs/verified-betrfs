# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

cd disk-betree
../tools/rename.sh MapSpec.s.dfy
../tools/rename.sh ThreeStateVersionedMap.s.dfy
../tools/rename.sh ThreeStateVersioned.s.dfy
../tools/rename.sh AsyncDiskModel.s.dfy
../tools/rename.sh UI.s.dfy
../tools/rename.sh UIStateMachine.s.dfy
cd ..

cd lib
../tools/rename.sh NativeTypes.s.dfy
../tools/rename.sh Maps.s.dfy
../tools/rename.sh Option.s.dfy
../tools/rename.sh total_order.s.dfy
../tools/rename.sh sequences.s.dfy
cd ..

cd disk-betree
echo *.dfy| tr ' ' '\n'  | grep -v '\.[is].dfy$' | sed 's#^./##' | sed 's#.dfy$#.i.dfy#' | xargs -n 1 ../tools/rename.sh
cd ..

cd lib
echo *.dfy| tr ' ' '\n'  | grep -v '\.[is].dfy$' | sed 's#^./##' | sed 's#.dfy$#.i.dfy#' | xargs -n 1 ../tools/rename.sh
cd ..

