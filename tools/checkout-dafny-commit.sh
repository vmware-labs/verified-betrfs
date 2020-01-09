#! /bin/bash

### Update this commit hash in order to update the version of dafny
### to build Veribetrfs with.

set -e
set -x

# https://github.com/secure-foundations/dafny.git
# cpp branch
git checkout 11b2cba54aae8bb115407a68903dc37797f776ce
