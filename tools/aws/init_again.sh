#! /bin/bash

mkfs.ext4 /dev/xvde
mount /mnt/xvde
chown ubuntu:ubuntu /mnt/xvde
cgcreate -a ubuntu:ubuntu -t ubuntu:ubuntu -g memory:VeribetrfsExp
