1. Allocate a CloudLab machine (currently I'm testing with c6220 since it is two socket and generally available).
2. ssh to the machine.
3. git clone git@github.com:rstutsman/verified-betrfs.git 
4. cd verified-betrfs
5. git checkout concurrency-experiments
6. ./concurrency/node-replication/cloudlab-setup
7. cd concurrency/node-replication
8. python3 bench.py

