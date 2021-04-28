import github_token
from github import Github

def authenticate():
    token = github_token.Token().get_token()
    return Github(token)

veribetrfs_repository_id = 192590105
veribetrfs_branch = 'master-verichecks'

def handle_check_suite_requested(repository_id, head_branch, head_sha):
    gh = authenticate()
    if repository_id != veribetrfs_repository_id:
        print('refusing to run for repository_id {}'.format(repository_id))
        return 'only veribetrfs'
    repo = gh.get_repo(veribetrfs_repository_id)
    if head_branch != veribetrfs_branch:
        print('refusing to run for branch {}'.format(head_branch))
        return 'only ' + veribetrfs_branch
    branch = repo.get_branch(head_branch)
    commit = branch.commit
    print('using commit ' + commit.sha)
    external_id = 'verichecks-alpha-status-{}-{}'.format(head_branch, commit.sha)
    cr_output = {
        'title': 'Verification Status',
        'summary': 'Waiting for runner to pick up the task'
    }
    cr = repo.create_check_run('Status (Alpha)', head_sha=commit.sha, status='queued', external_id=external_id, output=cr_output)
    print('created check run {}'.format(cr))
    return 'success'

