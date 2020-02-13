#!/bin/bash

set -e
set -x

USER=`id -u -n`
GROUP=`id -g -n`

sudo cgcreate -a $USER:$GROUP -t $USER:$GROUP -g memory:VeribetrfsExp
