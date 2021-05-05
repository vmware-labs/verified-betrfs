# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import github_token
import boto3
from github import Github

def authenticate():
    token = github_token.Token().get_token()
    return Github(token)

veribetrfs_repository_id = 192590105
veribetrfs_branch = 'master'
verichecks_branch = 'verichecks/verichecks'
instance_id = 'i-0e6292e04ef4e0d53'

def start_worker():
    try:
        ec2_connection = boto3.client('ec2', region_name='us-east-2')
        response = ec2_connection.start_instances(InstanceIds=[instance_id])
        print('started worker')
        return 'success'
    except Exception as e:
        print(e)
        return 'failure'

def handle_check_suite_requested(repository_id, head_branch, head_sha):
    gh = authenticate()
    if repository_id != veribetrfs_repository_id:
        print('refusing to run for repository_id {}'.format(repository_id))
        return 'only veribetrfs'
    repo = gh.get_repo(veribetrfs_repository_id)
    if head_branch == verichecks_branch:
        print('commit to {}'.format(verichecks_branch))
        branch = repo.get_branch(verichecks_branch)
        try:
            requests = repo.get_contents(path='requested/status', ref=verichecks_branch)
            request_names = [c.name for c in requests if c.name != '.gitkeep' and c.name != 'master']
            print('active requests: {}'.format(request_names))
            if len(request_names) > 0:
                print('there are active requests, starting worker')
                start_worker()
        except Exception as e:
            print(e)
        return 'self'
    else:
        if head_branch != veribetrfs_branch:
            print('refusing to run for branch {}'.format(head_branch))
            return 'only ' + veribetrfs_branch
        branch = repo.get_branch(head_branch)
        commit = branch.commit
        print('using branch {}'.format(branch.name))
        try:
            repo.create_file(
                    path = 'requested/status/{}'.format(branch.name),
                    message = 'Github requested check suite of {}'.format(branch.name),
                    content = '',
                    branch = verichecks_branch)
            print('request created, starting worker')
            start_worker()
        except Exception as e:
            print(e)


