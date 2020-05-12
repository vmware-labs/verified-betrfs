#!/usr/bin/python3
import argparse
import urllib, json, sys
import boto3
import pprint
from collections import namedtuple
from botocore.exceptions import ClientError

parser = argparse.ArgumentParser()
parser.add_argument('--all', action='store_true')
parser.add_argument('--ssh', action='store_true')
args = parser.parse_args()

Instance = namedtuple('Instance', ['Name', 'InstanceId', 'PublicIpAddress', 'State'])

ec2_connection = boto3.client('ec2', region_name='us-east-2')
try:
    response = ec2_connection.describe_instances()
    # print(prettyResponse(response))

    def extract_salient(inst):
        return Instance(
                Name=[x for x in inst['Tags'] if x['Key'] == 'Name'][0]['Value'],
                InstanceId=inst['InstanceId'],
                PublicIpAddress=inst['PublicIpAddress'],
                State=inst['State']['Name'])
    insts = [extract_salient(x) for reservation in response['Reservations'] for x in reservation['Instances']]
    insts.sort(key=lambda x: x.Name)
    if not args.all:
        insts = [x for x in insts if x.Name.startswith('veri-worker')]
    if args.ssh:
        for ist in insts:
            print("\033[1m{}\033[0m \x1b[34m{}\033[0m\tssh ubuntu@{}".format(ist.Name, ist.State, ist.PublicIpAddress))
    else:
        pprint.pprint(insts, indent = 2)
except ClientError as e:
    print(e)

