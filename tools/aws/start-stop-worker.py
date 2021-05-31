#!/usr/bin/python3
import urllib, json, sys
import argparse
import boto3
import pprint
import time
from collections import namedtuple
from botocore.exceptions import ClientError

parser = argparse.ArgumentParser()
parser.add_argument('--start', action='store_true', help='start instance')
parser.add_argument('--stop', action='store_true', help='stop instance')
parser.add_argument('--retry-start', action='store_true', help='retry every 10sec for about 2 minutes')
parser.add_argument('NAME', help='machine name')

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
insts = [x for x in insts if x.Name == args.NAME]

print("Found instances:")
pprint.pprint(insts, indent=2)
if len(insts) != 1:
    print("Too few/many instances found. Aborting.")
    sys.exit(-1)

instance_ids = [x.InstanceId for x in insts]

if args.start is False and args.stop is False:
    print("either --start or --stop is required")
    sys.exit(-1)


if args.start:
    to_start = instance_ids
    print("starting instances:", to_start)

    if args.retry_start:
        attempts = 0
        while attempts < 12:
            try:
                response = ec2_connection.start_instances(InstanceIds=to_start)
                pprint.pprint(response, indent=2)
                sys.exit(0)
            except ClientError as e:
                print("start failed, retrying in 10 sec")
                time.sleep(10)
                attempts += 1
        print("start failed for two minutes, giving up")
        sys.exit(-1)

    else:
        try:
            response = ec2_connection.start_instances(InstanceIds=to_start)
            pprint.pprint(response, indent=2)
        except ClientError as e:
            print(e)
            sys.exit(-1)

elif args.stop:
    to_stop = instance_ids
    print("stopping instances:", to_stop)

    try:
        response = ec2_connection.stop_instances(InstanceIds=to_stop)
        pprint.pprint(response, indent=2)
    except ClientError as e:
        print(e)
        sys.exit(-1)


