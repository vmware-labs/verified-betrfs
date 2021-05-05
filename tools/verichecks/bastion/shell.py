# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import github_token
from github import Github

veribetrfs_repository_id = 192590105

def g():
    t = github_token.Token().get_token()
    g = Github(t)
    r = g.get_repo(veribetrfs_repository_id)
    return (g, r)
