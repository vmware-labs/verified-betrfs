SSH_ID_PEM="~/veribetrfsbastion.pem"

import json
import subprocess
import time
import select
import sys
import os
import fcntl
import termcolor    # pip3 install termcolor

logfile = None

def set_logfile(path):
    if os.path.exists(path):
        sys.stderr.write("logfile %s exists; change experiment label?\n" % path)
        sys.exit(-1)
    global logfile
    logfile = open(path, "w")

def log(msg):
    sys.stdout.write(msg + "\n")
    sys.stdout.flush()
    if logfile:
        logfile.write(msg + "\n")
        logfile.flush()

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

next_index = 0
def get_index():
    global next_index
    result = next_index
    next_index = next_index + 1
    return result

spectrum = ["red", "yellow", "green", "cyan", "blue", "magenta"]

class WorkerMonitor:
    def __init__(self, worker, cmd):
        self.worker = worker
        self.cmd = cmd
        self.running = True
        self.index = get_index()

    def set_pipe(self, pipe):
        self.pipe = pipe
        fd = self.pipe.stdout.fileno()
        flags = fcntl.fcntl(fd, fcntl.F_GETFL)
        fcntl.fcntl(fd, fcntl.F_SETFL, flags | os.O_NONBLOCK)

    def __repr__(self):
        return self.worker["Name"]

    def linetag(self):
        return termcolor.colored("[%s]" % self, spectrum[self.index % len(spectrum)])

    def set_dead(self):
        if self.running:
            log("%s WORKER_ENDS" % self.linetag())
        self.running = False

def running(monitors):
    return [m for m in monitors if m.running]

def monitor_worker_pipes(monitors):
    last_num_running = None
    polling = select.poll()
    fdmap = {}
    for monitor in monitors:
        monitor.fd = monitor.pipe.stdout.fileno()
        polling.register(monitor.pipe.stdout)
        fdmap[monitor.fd] = monitor

    while len(running(monitors)) > 0:
        #print ("num_running", len(running(monitors)))
        # scan for stdout
        snooze = 1
        for fd,event in polling.poll(1):
            monitor = fdmap[fd]
            if not monitor.running:
                continue
            snooze = 0
            #log("%s event %s %s" % (monitor.linetag(), event, [select.POLLIN, select.POLLHUP]))
            if event & select.POLLIN:
                while True:
                    line = monitor.pipe.stdout.readline()
                    if len(line) == 0: break
                    line = line.decode("utf-8").strip()
                    log("%s %s" % (monitor.linetag(), line))
            else:
                # Don't process POLLHUP until there's no POLLIN left to read.
                if event & select.POLLHUP:
                    monitor.set_dead()

        time.sleep(snooze)
    log("All jobs complete.")

def launch_worker_pipes(workers, ntasks, lam, dry_run=False):
    assert ntasks <= len(workers)
    monitors = []
    for idx in range(ntasks):
        worker = workers[idx]
        cmd = lam(idx, worker)
        monitor = WorkerMonitor(worker, cmd)
        log("%s LAUNCH_CMD %s" % (monitor.linetag(), " ".join(cmd)))
        if not dry_run:
            monitor.set_pipe(subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT))
            monitors.append(monitor)
    return monitors
        
