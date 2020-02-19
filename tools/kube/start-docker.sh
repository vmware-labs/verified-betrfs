docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/tutorial,type=bind --workdir /home/dafnyserver/tutorial jonhdotnet/veribetrfs:1.0 /bin/bash
