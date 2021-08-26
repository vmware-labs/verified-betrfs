found in [536a20227fbfb517221cc397b46a6125ad1fae52](https://github.com/vmware-labs/verified-betrfs/tree/536a20227fbfb517221cc397b46a6125ad1fae52)

with W1, R1, R2: W1 concurrent with R1, R1 completes before R2 starts, W1 completes before R2 starts
R1 can see W1, R2 cannot, but R1 R2 should be linearized in this order