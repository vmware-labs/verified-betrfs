#! /bin/bash

docker run --rm --cap-add SYS_ADMIN -it -v `pwd`:/veribetrfs utaal/dotnet-core-sdk-make-perf /bin/bash /veribetrfs/tools/run-perf-docker-internal.sh $@

