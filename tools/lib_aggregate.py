# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

import sys
import re

# report file types
SYNCHK = "synchk"
VERCHK = "verchk"

class DafnyCondition:
    def __init__(self, level, is_success, result, style):
        self.level = level
        self.result = result
        self.style = style
        self.verchk = None # to be filled in after
        self.is_success = is_success

    def __lt__(self, other):
        return self.level < other.level

    def __repr__(self):
        return self.result

    def json(self):
        return {
            'file': self.verchk,
            'level': self.level,
            'result': self.result,
            'is_success': self.is_success,
        }

class DafnyParseError(DafnyCondition):
    def __init__(self):
        super().__init__(0, False, "parse error", "fillcolor=red; shape=trapezium")

class DafnyTypeError(DafnyCondition):
    def __init__(self):
        super().__init__(1, False, "type error", "fillcolor=orange; shape=parallelogram")

class DafnyVerificationError(DafnyCondition):
    def __init__(self):
        super().__init__(2, False, "verification error", "fillcolor=yellow; shape=doubleoctagon")

class DafnyAssumeError(DafnyCondition):
    def __init__(self):
        super().__init__(3, False, "untrusted file contains assumptions", "fillcolor=cyan; shape=octagon")

class DafnyTimeoutError(DafnyCondition):
    def __init__(self):
        super().__init__(4, False, "verification timeout", "fillcolor=\"#555555\"; fontcolor=white; shape=octagon")

class DafnyRlimitError(DafnyCondition):
    def __init__(self):
        super().__init__(4, False, "exceeded rlimit", "fillcolor=\"#666666\"; fontcolor=white; shape=octagon")

class DafnyDynamicFrames(DafnyCondition):
    def __init__(self):
        super().__init__(5, True, "dynamic frames", "fillcolor=blue; shape=egg")

class DafnyVerified(DafnyCondition):
    def __init__(self):
        super().__init__(6, True, "verified successfully", "fillcolor=green; shape=ellipse")

class DafnySyntaxOK(DafnyCondition):
    def __init__(self):
        super().__init__(7, True, "syntax ok", "fillcolor=green; shape=ellipse")

allConditions=[DafnyParseError(), DafnyTypeError(), DafnyVerificationError(), DafnyAssumeError(), DafnyTimeoutError(), DafnyRlimitError(), DafnyDynamicFrames(), DafnyVerified(), DafnySyntaxOK()]
badConditions=[DafnyParseError(), DafnyTypeError(), DafnyVerificationError(), DafnyAssumeError(), DafnyTimeoutError(), DafnyRlimitError()]

def dafnyFromVerchk(verchk):
    return verchk.replace("build/", "./").replace(".verchk", ".dfy").replace(".synchk", ".dfy")

def verchkFromDafny(dafny, reportType):
    return "build/" + dafny.replace(".dfy", "."+reportType)

def hasDisallowedAssumptions(verchk):
    dfy = dafnyFromVerchk(verchk)
    if dfy.endswith(".s.dfy"):
        return False
    for line in open(dfy).readlines():
        # TODO: Ignore multiline comments. Requires fancier parsing.
        # TODO: or maybe instead use /noCheating!?
        line = re.sub("//.*$", "", line)    # ignore single-line comments
        if "assume" in line:
            return True
    return False

def hasDynamicFrames(verchk):
    dfy = dafnyFromVerchk(verchk)
    for line in open(dfy).readlines():
        if re.compile("^\s*modifies").search(line):
            return True
        if re.compile("^\s*reads").search(line):
            return True
    return False

def extractCondition(reportType, report, content):
    # Extract Dafny verification result
    if re.compile("parse errors detected in").search(content) != None:
        return DafnyParseError()
    if re.compile("resolution/type errors detected in").search(content) != None:
        return DafnyTypeError()

    err_types = [(re.compile("Dafny program verifier finished with.*(\d+) error"), DafnyVerificationError()),
                 (re.compile("Dafny program verifier finished with.*(\d+) time out"), DafnyTimeoutError()),
                 (re.compile("Dafny program verifier finished with.*(\d+) inconclusive"), DafnyRlimitError()),
                 (re.compile("Dafny program verifier finished with.*(\d+) out of resource"), DafnyRlimitError())]
    for (matcher, err) in err_types:
        match = matcher.search(content)
        if not match is None and int(match.group(1)) > 0:
            return err

    if hasDisallowedAssumptions(report):
        return DafnyAssumeError()

    match = re.compile("Dafny program verifier finished with (?P<verified>\d+) verified").search(content)
    if not match is None:
        return DafnyVerified()

    if reportType==VERCHK:
        raise Exception("build system error: couldn't summarize %s\n" % report)
    elif reportType==SYNCHK:
        #  Report assumes even in syntax-only mode.
        if hasDisallowedAssumptions(report):
            return DafnyAssumeError()
        if hasDynamicFrames(report):
            return DafnyDynamicFrames()
        return DafnySyntaxOK()
    else:
        raise Exception("build system error: unknown report type %s\n" % reportType)


def summarize_verbose(reportType, verchk):
    content = open(verchk).read()

    # Extract time
    mo = re.compile("^([0-9.]+)user", re.MULTILINE).search(content)
    if mo != None:
        userTimeSec = float(mo.group(1))
    else:
        userTimeSec = None

    condition = extractCondition(reportType, verchk, content)
    condition.userTimeSec = userTimeSec
    condition.filename = dafnyFromVerchk(verchk)
    condition.verchk = verchk

    return content, condition

def summarize(reportType, verchk):
    _, condition = summarize_verbose(reportType, verchk)
    return condition
