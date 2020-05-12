#!/usr/bin/python3
import urllib, json, sys
import boto3
import pprint
from botocore.exceptions import ClientError

instance_ids = [
    'i-0ef45a89f48487fce',
    'i-006858073c1785f92',
    'i-0070ff5413bf8eed4',
    'i-0119b98c9b74ffaea'
]

def prettyResponse(response):
    return pprint.pprint(response, indent=2)

ec2_connection = boto3.client('ec2', region_name='us-east-2')
try:
    response = ec2_connection.describe_instances()
    print(prettyResponse(response))
except ClientError as e:
    print(e)

