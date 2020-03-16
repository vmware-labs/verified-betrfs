#!/bin/bash

g++ -o tools/clear-os-page-cache tools/clear-os-page-cache.cpp

echo "requesting sudo access to give tools/clear-os-page-cache script root privileges"
sudo tools/set-privileges-on-script.sh
echo "done"
