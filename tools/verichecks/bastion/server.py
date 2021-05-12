from flask import Flask, make_response, request

import signature
import requestrun

__author__ = "@Wietze, @utaal"
__copyright__ = "Copyright 2019"

app = Flask(__name__)

@app.before_request
def require_valid_token():
    if not request.headers.get('X-HUB-SIGNATURE') or not signature.verify_signature(request):
        return make_response("", 403)

@app.route("/event_handler", methods=["POST"])
def message_actions():
    github_request = request.get_json()
    print(github_request)
    if github_request.get('action'):
        if github_request.get('action') in ['requested', 'rerequested']:
            head_sha = github_request.get('check_suite').get('head_sha')
            head_branch = github_request.get('check_suite').get('head_branch')
            repository_id = github_request.get('repository').get('id')
            print('check suite requested: {} {} {}'.format(repository_id, head_branch, head_sha))
            requestrun.handle_check_suite_requested(repository_id, head_branch, head_sha)
    return make_response("", 201)
    # return make_response("", 500)

if __name__ == "__main__":
    from waitress import serve
    serve(app, host='0.0.0.0', port='4331') #, ssl_context=('cert.pem', 'key.pem'))
