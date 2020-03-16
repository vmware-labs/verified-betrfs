#!/bin/bash

set -e

tools/configure-cgroups.sh

echo "Clearing page cache (requesting sudo access) ..."
sudo tools/clear-os-page-cache.sh
echo "Page cache cleared."

cgexec -g memory:VeribetrfsExp "$@"
