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

# Pull a new branch to the workers
./run-all.py '(cd veribetrfs; git checkout row-cache-adventure; git pull; tools/update-submodules.sh)'

# Running an experiment suite.
Edit suite configuration in launch-experiments.py, and run that.

------------------------------------------------------------------------------

# How We Build It Documentation

A VMware employee needs to get VMware's AWS console access through
this UI:

https://console.cloudgate.vmware.com/

Select Get PowerUser Access.

## AWS Management Console

Pay attention to: EC2, Billing (search in search bar)
Click Billing/Bills
  CloudWatch: $33
  GuardDuty: $8
    -- just "taxes" based on VMware's config?
  EC2 idle costs: $.10/GB/Mo for the SSD EBS
  EC2 bastion costs seem to be getting absorbed
    into "Compute Savings Plan" and reserved instance applied.

EC2 -> top bar, select Ohio.

### Andrea made more worker instances by...

Each instance has an EBS volume attached.
Snapshotting one of the volumes, then launching 

Select veri-worker-b06, right click,
  (Image and templates -> Launch more like this (uses image from months ago))
  better yet -> Create image (create AMI from the EBS)
  although in practice the template sure missed a bunch of stuff; it managed
  to delete the public IP configuration

We think the ssd instances are identical to the hd instances, just the
instance config is different.

Instance names are just values assigned to tag Name

### Decomissioning

Select a bunch, terminate instance.

### bastion delegation strategy

IAM - Identity and Access Management:
We created a role: (IAM/Roles, or role in instance view.)
verifbetrfs-bastion-role -- that gave bastion the opportunity to
DescribeInstances, StartInstances, StopInstances.

### Security groups

Say which ports are open.
