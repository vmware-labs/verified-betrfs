#!/usr/bin/python3
import urllib, json, sys
import argparse
import boto3
import pprint
from collections import namedtuple
from botocore.exceptions import ClientError

parser = argparse.ArgumentParser()
parser.add_argument('--scale-up', type=int, help='scale up to target worker count')
parser.add_argument('--scale-down', type=int, help='scale down to target worker count')
parser.add_argument('--ssd', action='store_true', help='act on the ssd cluster')
parser.add_argument('--dry-run', action='store_true')

args = parser.parse_args()

print("Args: ", args)

print("Fetching instances.")

Instance = namedtuple('Instance', ['Name', 'InstanceId', 'PublicIpAddress', 'State'])

def extract_salient(inst):
    return Instance(
            Name=[x for x in inst['Tags'] if x['Key'] == 'Name'][0]['Value'],
            InstanceId=inst['InstanceId'],
            PublicIpAddress=inst.get('PublicIpAddress'),
            State=inst['State']['Name'])

try:
    ec2_connection = boto3.client('ec2', region_name='us-east-2')
    response = ec2_connection.describe_instances()
except ClientError as e:
    print(e)
    sys.exit(-1)

insts = [extract_salient(x) for reservation in response['Reservations'] for x in reservation['Instances']]
insts.sort(key=lambda x: x.Name)
insts = [x for x in insts if x.Name.startswith('veri-ssd' if args.ssd else 'veri-worker')]

print("Found instances:")
pprint.pprint(insts, indent=2)

instance_ids = [x.InstanceId for x in insts]

if args.scale_up is None and args.scale_down is None:
    print("either --scale-up or --scale-down is required")
    sys.exit(-1)

if args.scale_up is not None:
    to_start = instance_ids[:args.scale_up]
    print("starting instances:", to_start)

    if not args.dry_run:
        try:
            response = ec2_connection.start_instances(InstanceIds=to_start)
            pprint.pprint(response, indent=2)
        except ClientError as e:
            print(e)

elif args.scale_down is not None:
    to_stop = instance_ids[args.scale_down:]
    print("stopping instances:", to_stop)

    if not args.dry_run:
        try:
            response = ec2_connection.stop_instances(InstanceIds=to_stop)
            pprint.pprint(response, indent=2)
        except ClientError as e:
            print(e)


