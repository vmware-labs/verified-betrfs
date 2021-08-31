found in [06d34c3f111a229cd8dffcbc382c6b9c2c1c5928](https://github.com/vmware-labs/verified-betrfs/tree/06d34c3f111a229cd8dffcbc382c6b9c2c1c5928) / [node-replication-buggy-model](https://github.com/vmware-labs/verified-betrfs/releases/tag/node-replication-buggy-model)

with W1, R1, R2: W1 concurrent with R1, R1 completes before R2 starts, W1 completes before R2 starts
R1 can see W1, R2 cannot, but R1 R2 should be linearized in this order

Got fixed in the impl here: https://github.com/vmware/node-replication/pull/17