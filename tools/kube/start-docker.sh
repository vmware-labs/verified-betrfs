# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause

docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/tutorial,type=bind --workdir /home/dafnyserver/tutorial jonhdotnet/veribetrfs:1.0 /bin/bash
