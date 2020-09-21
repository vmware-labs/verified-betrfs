# Setup

Get a copy of veribetrfsbastion.pem from Andrea or someone else
and write it to ~/.ssh/veribetrfsbastion.pem .

```
chmod 400 ~/.ssh/veribetrfsbastion.pem

cat > ~/.ssh/config <<__EOF__
Host bastion
   HostName 3.21.176.58
   User ubuntu
   IdentityFile /home/jonh/.ssh/veribetrfsbastion.pem
__EOF__
```

# List instances
```
ssh bastion veribetrfs/tools/aws/describe-instances.py --running
```

# Scale up spinny-disk workers to 4.
Note that '4' here is a desired state parameter -- if you already
have 3 workers, this command will only spool up one more.
```
ssh bastion veribetrfs/tools/aws/scale-workers.py --scale-up 4
```

# Running an experiment suite.
Edit suite configuration in launch-experiments.py, and run that.
