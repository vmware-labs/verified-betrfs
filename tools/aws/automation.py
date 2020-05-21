SSH_ID_PEM="~/.ssh/veribetrfsbastion.pem"

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
        if "index" not in worker:
            worker["index"] = get_index()
        self.index = worker["index"]

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
        self.running = False

    def launch(self):
        log("%s LAUNCH_CMD %s" % (self.linetag(), self.cmd.text_cmd_line()))
        self.set_pipe(subprocess.Popen(self.cmd.cmd_ary, stdout=subprocess.PIPE, stderr=subprocess.STDOUT))

def running(monitors):
    return [m for m in monitors if m.running]

def poll_monitors(monitors):
    """returns the set of still-active monitors."""
    polling = select.poll()
    fdmap = {}
    for monitor in running(monitors):
        monitor.fd = monitor.pipe.stdout.fileno()
        polling.register(monitor.pipe.stdout)
        fdmap[monitor.fd] = monitor

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
                if monitor.running:
                    log("%s WORKER_ENDS" % monitor.linetag())
                monitor.set_dead()
    # If nothing happened, kill a little time before returning to outer loop.
    time.sleep(snooze)
    return running(monitors)

def monitor_worker_pipes(monitors):
    lastSize = None
    while len(running(monitors)) > 0:
        sys.stdout.flush()
        monitors = poll_monitors(monitors)
        sys.stdout.flush()
        size = len(running(monitors))
        if size != lastSize:
            log("PROGRESS %d workers remaining" % size)
            lastSize = size
    log("All jobs complete.")

class Command:
    def __init__(self, label, cmd_ary):
        self.label = label
        self.cmd_ary = cmd_ary

    def __repr__(self):
        return self.label

    def text_cmd_line(self):
        return " ".join(self.cmd_ary)

def launch_worker_pipes(workers, ntasks, lam, dry_run=False):
    if ntasks > len(workers):
        raise Exception("Requested %d tasks for %d workers" % (ntasks, len(workers)))
    monitors = []

    for idx in range(ntasks):
        worker = workers[idx]
        cmd = lam(idx, worker)
        monitor = WorkerMonitor(worker, cmd)
        log("%s ASSIGN_CMD %s" % (monitor.linetag(), cmd))
        if not dry_run:
            monitors.append(monitor)

    for monitor in monitors:
        monitor.launch()
    return monitors

def sequenced_launcher(workers, ntasks, lam, dry_run=False):
    idle_resources = workers
    next_task_idx = 0
    monitors = []

    def dispatch_one(idx):
        worker = idle_resources.pop()
        cmd = lam(idx, worker)
        monitor = WorkerMonitor(worker, cmd)
        log("%s ASSIGN_CMD %s" % (monitor.linetag(), cmd))
        if dry_run:
            monitor.set_dead()
        else:
            monitor.launch()
        return monitor

    while len(monitors)>0 or next_task_idx<ntasks:
        # assign until we have no more idle resources or work to do
        while len(idle_resources)>0 and next_task_idx<ntasks:
            monitor = dispatch_one(next_task_idx)
            next_task_idx += 1
            monitors.append(monitor)
        
        # wait for something to finish
        prevSize = len(running(monitors))
        if not dry_run:
            surviving_monitors = poll_monitors(monitors)
        else:
            surviving_monitors = []
        for monitor in monitors:
            if monitor not in surviving_monitors:
                idle_resources.insert(0, monitor.worker)
        monitors = surviving_monitors
        curSize = len(running(monitors))
        if curSize!=prevSize:
            log("PROGRESS %d tasks ready; %d tasks running" % (ntasks - next_task_idx, len(running(monitors))))
    log("All jobs complete.")
