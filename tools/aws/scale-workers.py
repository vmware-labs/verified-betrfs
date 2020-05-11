import urllib, json, sys
import argparse
import boto3
from botocore.exceptions import ClientError

instance_ids = [
    'i-0ef45a89f48487fce',
    'i-006858073c1785f92',
    'i-0070ff5413bf8eed4',
    'i-0119b98c9b74ffaea'
]

parser = argparse.ArgumentParser()
parser.add_argument('--scale-up', type=int, help='scale up to target worker count')
parser.add_argument('--scale-down', type=int, help='scale down to target worker count')
parser.add_argument('--dry-run', action='store_true')

args = parser.parse_args()

print(args)

if args.scale_up is None and args.scale_down is None:
    print("either --scale-up or --scale-down is required")
    sys.exit(-1)

if args.scale_up is not None:
    to_start = instance_ids[:args.scale_up]
    print("starting instances:", to_start)

    if not args.dry_run:
        ec2_connection = boto3.client('ec2', region_name='us-east-2')
        try:
            response = ec2_connection.start_instances(InstanceIds=to_start)
            print(response)
        except ClientError as e:
            print(e)

elif args.scale_down is not None:
    to_stop = instance_ids[args.scale_down:]
    print("stopping instances:", to_stop)

    if not args.dry_run:
        ec2_connection = boto3.client('ec2', region_name='us-east-2')
        try:
            response = ec2_connection.stop_instances(InstanceIds=to_stop)
            print(response)
        except ClientError as e:
            print(e)


