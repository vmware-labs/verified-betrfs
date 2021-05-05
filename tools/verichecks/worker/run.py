# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import subprocess
import os
import sys
import github_token
import traceback
from github import Github, GithubException

veribetrfs_repository_id = 192590105
verichecks_branch = 'verichecks/verichecks'
timeout_seconds = 60 * 30 # minutes

class Runner:
    def __init__(self):
        self.token = github_token.Token().get_token()
        self.github = Github(self.token)
        self.repo = self.github.get_repo(veribetrfs_repository_id)

    def run(self):
        while True:
            print('querying for requests')
            requests = [
                    f for f in
                    self.repo.get_contents('requested/status', verichecks_branch)
                    if f.name != '.gitkeep']
            # def get_branch(n):
            #     try:
            #         return self.repo.get_branch(n)
            #     except GithubException:
            #         return None
            def get_commit(n):
                try:
                    return (n, self.repo.get_commit(n.name))
                except GithubException:
                    return None
            # branches = [b for b in (get_branch(n) for n in requests) if b is not None]
            commits = [c for c in (get_commit(n) for n in requests) if c is not None]
            print('requested commits: {}'.format(commits))
            if len(commits) == 0:
                print('nothing to do')
                return

            request_name, commit = commits[0]
            print('running request {}'.format(request_name))
            self.repo.delete_file(path=request_name.path, message='Request for {} received'.format(commit.sha), sha=request_name.sha, branch='verichecks/verichecks')
            print('request removed')

            cr = self.create_check_run(request_name, commit)
            conclusion, output = self.run_task(request_name, commit)
            self.complete_check_run(cr, request_name, commit, conclusion, output)

    def create_check_run(self, request_name, commit):
        print('running commit {}'.format(commit))
        external_id = 'verichecks-alpha-status-{}'.format(commit.sha)
        cr_output = {
            'title': 'Started',
            'summary': 'The worker has started'
        }
        cr = self.repo.create_check_run('Status',
                head_sha=commit.sha,
                status='in_progress',
                external_id=external_id,
                output=cr_output)
        print('created check run {}'.format(cr))
        return cr

    def complete_check_run(self, cr, request_name, commit, conclusion, cr_output):
        cr.edit(status='completed',
                conclusion=conclusion,
                output=cr_output)
        print('completed check run {}'.format(cr))

    def run_task(self, request_name, commit):
        make_cp = None
        try:
            def try_run(res):
                if res.returncode != 0:
                    print('process returned status code {}'.format(res.returncode))
                    raise Exception('process returned status code {}'.format(res.returncode))
                return res
            if os.path.exists('worker-dir/clones/{}'.format(commit.sha)):
                try_run(subprocess.run(['rm', '-Rf', commit.sha], cwd='worker-dir/clones'))
            try_run(subprocess.run(['git', 'clone', '--depth', '1',
                'git@github.com:splatlab/veribetrfs.git',
                '--single-branch', '--branch', 'master', commit.sha],
                cwd='worker-dir/clones'))
            try_run(subprocess.run(['git', 'fetch', 'origin', commit.sha],
                cwd='worker-dir/clones/{}'.format(commit.sha)))
            try_run(subprocess.run(['git', 'checkout', commit.sha],
                cwd='worker-dir/clones/{}'.format(commit.sha)))
            try_run(subprocess.run(['./tools/install-dafny.sh'],
                cwd='worker-dir/clones/{}'.format(commit.sha)))
            make_cp = subprocess.run(
                ['bash', '-c', '. /root/venv3-veribetrfs/bin/activate && make -j7 verichecks-status'],
                cwd='worker-dir/clones/{}'.format(commit.sha),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=timeout_seconds)
            time_outs_in_output = subprocess.run(
                ['grep', '-R', 'timed out after', 'build/'],
                cwd='worker-dir/clones/{}'.format(commit.sha),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT)
            assertion_violations_in_output = subprocess.run(
                ['grep', '-R', 'assertion violation', 'build/'],
                cwd='worker-dir/clones/{}'.format(commit.sha),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT)
            try:
                outcome_status_dirs = self.repo.get_contents(path='outcomes/status/{}'.format(commit.sha), ref='verichecks/verichecks')
            except GithubException as e:
                outcome_status_dirs = []
            for outcome_status_dir in outcome_status_dirs:
                self.repo.delete_file(path=outcome_status_dir.path, message='Cleanup', sha=outcome_status_dir.sha, branch='verichecks/verichecks')
            # with open('worker-dir/clones/{}/build/Impl/Bundle.i.syntax-status.pdf'.format(commit.sha), 'rb') as syntax_status_file:
            #     syntax_status_content = syntax_status_file.read()
            # syntax_status_file = self.repo.create_file(
            #         path='outcomes/status/{}/Bundle.i.syntax-status.pdf'.format(commit.sha),
            #         message='Completed syntax check of {}'.format(commit.sha),
            #         content=syntax_status_content,
            #         branch=verichecks_branch)['content']
            if make_cp.returncode == 0: # success
                with open('worker-dir/clones/{}/build/Impl/Bundle.i.status.pdf'.format(commit.sha), 'rb') as status_file:
                    status_content = status_file.read()
                status_file = self.repo.create_file(
                        path='outcomes/status/{}/Bundle.i.status.pdf'.format(commit.sha),
                        message='Completed verification check of {}'.format(commit.sha),
                        content=status_content,
                        branch=verichecks_branch)['content']

                time_outs_file = self.repo.create_file(
                        path='outcomes/status/{}/time_outs_in_output.txt'.format(commit.sha),
                        message='Completed verification check of {}'.format(commit.sha),
                        content=time_outs_in_output.stdout.decode('utf-8'),
                        branch=verichecks_branch)['content']

                assertion_violations_file = self.repo.create_file(
                        path='outcomes/status/{}/assertion_violations_in_output.txt'.format(commit.sha),
                        message='Completed verification check of {}'.format(commit.sha),
                        content=assertion_violations_in_output.stdout.decode('utf-8'),
                        branch=verichecks_branch)['content']

                print('status uploaded')
                output = {
                    'title': 'Complete',
                    'summary': """
Verification summary: {}

Timeouts: {}

Assertion violations: {}
""".format(status_file.html_url, time_outs_file.html_url, assertion_violations_file.html_url)
                }
                return ('neutral', output)
            else: # failure
                subprocess.run(['killall', '-s', '9', 'dotnet'])
                subprocess.run(['killall', '-s', '9', 'dafny'])
                subprocess.run(['killall', '-s', '9', 'z3'])
                log_file = self.repo.create_file(
                    path='outcomes/status/{}/log.txt'.format(commit.sha),
                    message='Failed verification check of {}'.format(commit.sha),
                    content=make_cp.stdout.decode('utf-8'),
                    branch=verichecks_branch)['content']
                print('status uploaded')
                output = {
                    'title': 'Failed',
                    'summary': """
Log: {}
""".format(log_file.html_url)
                }
                return ('failure', output)

        except Exception as e:
            print(repr(e))
            traceback.print_tb(e.__traceback__)
            try:
                if make_cp is not None and make_cp.stdout is not None:
                    log_file = self.repo.create_file(
                        path='outcomes/status/{}/log.txt'.format(commit.sha),
                        message='Failed verification check of {}'.format(commit.sha),
                        content=make_cp.stdout.decode('utf-8'),
                        branch=verichecks_branch)['content']
            except Exception as e2:
                print(repr(e2))
                traceback.print_tb(e2.__traceback__)
            subprocess.run(['killall', '-s', '9', 'dotnet'])
            subprocess.run(['killall', '-s', '9', 'dafny'])
            subprocess.run(['killall', '-s', '9', 'z3'])
            output = {
                'title': 'Exception',
                'summary': (repr(e) + '|'.join(traceback.format_tb(e.__traceback__)))
            }
            return ('failure', output)


if __name__ == '__main__':
    Runner().run()
