#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

# example: rename.sh MapSpec.s.dfy
newname=$1
basename=`echo $newname | sed s/\.[is].dfy$/.dfy/`
find /home/jonh/veribetrfs -type f -name \*.dfy | xargs sed -i "s/$basename/$newname/g"
mv $basename $newname
git rm $basename
git add $newname
git add --all
