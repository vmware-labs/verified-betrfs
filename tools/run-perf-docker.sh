#! /bin/bash

# NOTE: pass the sampling rate (Hz) as first argument, followed by parameters to the benchmarker (i.e. ./tools/run-perf-docker.sh 1000 --benchmark=random-inserts)
# 1000Hz is a good choice for longer experiments (a few minutes), higher rates are recommended for shorter experiments
# if you don't see enough detail, try and increase the sampling rate

echo "==== capturing at frequency $1 ===="

echo "==== making the cs bundle ===="
make build/Bundle.cs

echo "==== running docker ===="
docker run --rm --cap-add SYS_ADMIN -it -v `pwd`:/veribetrfs utaal/dotnet-core-sdk-make-perf /bin/bash /veribetrfs/tools/run-perf-docker-internal.sh $@

