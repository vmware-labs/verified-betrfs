SSH_ID_PEM="~/veribetrfsbastion.pem"

import json
import subprocess
import time

def retrieve_running_workers():
    workers_pipe = subprocess.Popen("ssh bastion veribetrfs/tools/aws/describe-instances.py --running --json".split(), stdout=subprocess.PIPE)
    workers_json,_ = workers_pipe.communicate()
    workers = json.loads(workers_json)
    return workers

def ssh_preamble():
    return "ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no -i".split() + [SSH_ID_PEM]

def ssh_target_for_worker(worker):
    return"ubuntu@%s" % worker["PublicIpAddress"]

def ssh_cmd_for_worker(worker):
    return ssh_preamble() + [ssh_target_for_worker(worker)]

def scan_worker_pipes(worker_pipes):
    num_running = 0
    for worker_pipe in worker_pipes:
        worker_pipe.poll()
        if worker_pipe.returncode == None:
            num_running += 1
    return num_running

def monitor_worker_pipes(worker_pipes):
    last_num_running = None
    while True:
        num_running = scan_worker_pipes(worker_pipes)
        if num_running != last_num_running:
            print("%s jobs running" % num_running)
            last_num_running = num_running
        if num_running == 0: break
        time.sleep(1)

