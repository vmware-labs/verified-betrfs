import os
from github import Github, GithubException

print("Reporting result to Github actions")

token = os.environ['GITHUB_TOKEN']
gh = Github(token)

sha_env = os.environ['GITHUB_SHA']
repo_env = os.environ['GITHUB_REPOSITORY']

repo = gh.get_repo(repo_env)
commit = repo.get_commit(sha_env)

print("for repository {}, commit {}".format(repo, commit))

cr_output = {
    'title': 'Completed',
    'summary': 'Placeholder text'
}

repo.create_check_run('status',
        head_sha=commit.sha,
        status='completed',
        external_id='{}-{}-{}'.format(sha_env, repo_env, 'status'),
        conclusion='neutral',
        output=cr_output)

