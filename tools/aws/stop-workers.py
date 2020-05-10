import urllib, json, sys
import getpass
# import requests # 'pip install requests'
import boto3 # AWS SDK for Python (Boto3) 'pip install boto3'
from botocore.exceptions import ClientError

ec2_connection = boto3.client('ec2', region_name='us-east-2')

try:
    response = ec2_connection.stop_instances(InstanceIds=[
        'i-0417debb8c8b1f5f6'
        ])
    print(response)
except ClientError as e:
    print(e)


