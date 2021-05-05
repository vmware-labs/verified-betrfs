# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import datetime
import time
from enum import Enum
from typing import List

import jwt
import requests

__author__ = "@Wietze, @utaal"
__copyright__ = "Copyright 2019"

class Token():
    def __init__(self):
        # Set constants
        self.NAME = 'Verichecks' 
        self.APP_ID = '100068'
        self.BASE_API = 'https://api.github.com'
        self.USER_AGENT = 'Verichecks'
        pk_location = 'verichecks.2021-02-11.private-key.pem'
        with open(pk_location) as pk:
            self.PRIVATE_KEY = pk.read()

        self.repo_id = '192590105'
        self.installation_id = '14677620'
        # Parse incoming information
        # check_suite = incoming_data.get('check_suite') or incoming_data.get('check_run', {}).get('check_suite')
        # self.head_sha = check_suite.get('head_sha')
        # self.owner, self.repo = incoming_data['repository']['full_name'].split('/')
        # self.repo_id = incoming_data['repository']['id']
        # self.branch = check_suite['head_branch']
        # self.installation_id = incoming_data['installation']['id']
        # self.git_url = incoming_data['repository']['git_url']

    def get_bearer_token(self, duration: int = 60) -> str:
        timestamp = int(self.now('UNIX'))
        payload = {'iat': timestamp, 'exp': timestamp + duration, 'iss': self.APP_ID}
        return jwt.encode(payload, self.PRIVATE_KEY, algorithm='RS256')

    def get_token(self) -> str:
        headers = {'Accept': 'application/vnd.github.v3+json', 'User-Agent': self.USER_AGENT, 'Authorization': 'Bearer {}'.format(self.get_bearer_token())}
        # data = {"repository_ids": [self.repo_id], "permissions": {"checks": "write"}}
        data = {"repository_ids": [self.repo_id]}
        response = requests.post("{base_api}/app/installations/{installation_id}/access_tokens".format(base_api=self.BASE_API, installation_id=self.installation_id), headers=headers, json=data)
        result = response.json()
        if response.status_code != 201:
            raise Exception('Unexpected status code {}'.format(response.status_code), result.get('message'))
        return result['token']

    @staticmethod
    def now(date_type: str = 'ISO') -> str:
        if date_type == 'ISO':
            return datetime.datetime.now().isoformat() + 'Z'
        if date_type == 'UNIX':
            return time.time()
        raise Exception('Invalid date type')
