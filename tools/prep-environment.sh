#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

#
# Run this script as root (sudo tools/prep-environment) to install a recent
# version of mono and a few other necessary tools.

apt-get update
apt-get install -y ca-certificates gnupg2
apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF
apt-get install make wget
dafny_server/mono-official-stable.list 
cat > /etc/apt/sources.list.d/mono-official-stable.list <<__EOF__
deb https://download.mono-project.com/repo/ubuntu stable-bionic main
__EOF__
apt-get update
apt-get install -y mono-runtime mono-mcs mono-devel make wget unzip
pip3 install toposort

tools/install-dafny.sh
