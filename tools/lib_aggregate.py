import sys
import re

# report file types
SYNCHK = "synchk"
VERCHK = "verchk"

class DafnyCondition:
    def __init__(self, level, result, style):
        self.level = level
        self.result = result
        self.style = style

    def __lt__(self, other):
        return self.level < other.level

    def __repr__(self):
        return self.result

class DafnyParseError(DafnyCondition):
    def __init__(self):
        super().__init__(0, "parse error", "fillcolor=red; shape=trapezium")

class DafnyTypeError(DafnyCondition):
    def __init__(self):
        super().__init__(1, "type error", "fillcolor=orange; shape=parallelogram")

class DafnyVerificationError(DafnyCondition):
    def __init__(self):
        super().__init__(2, "verification error", "fillcolor=yellow; shape=doubleoctagon")

class DafnyAssumeError(DafnyCondition):
    def __init__(self):
        super().__init__(3, "untrusted file contains assumptions", "fillcolor=cyan; shape=octagon")

class DafnyTimeoutError(DafnyCondition):
    def __init__(self):
        super().__init__(4, "verification timeout", "fillcolor=\"#555555\"; fontcolor=white; shape=octagon")

class DafnyVerified(DafnyCondition):
    def __init__(self):
        super().__init__(5, "verified successfully", "fillcolor=green; shape=ellipse")

class DafnySyntaxOK(DafnyCondition):
    def __init__(self):
        super().__init__(6, "syntax ok", "fillcolor=green; shape=ellipse")

def dafnyFromVerchk(verchk):
    return verchk.replace("build/", "./").replace(".verchk", ".dfy").replace(".synchk", ".dfy")

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

def extractCondition(reportType, report, content):
    # Extract Dafny verification result
    if re.compile("parse errors detected in").search(content) != None:
        return DafnyParseError()
    if re.compile("resolution/type errors detected in").search(content) != None:
        return DafnyTypeError()
    mo = re.compile("Dafny program verifier finished with (\d+) verified, (\d+) error(.*(\d+) time out)?").search(content)
    if mo != None:
        rawVerifCount,rawErrorCount,dummy,rawTimeoutCount = mo.groups()
        verifCount = int(rawVerifCount)
        errorCount = int(rawErrorCount)
        if errorCount > 0:
            return DafnyVerificationError()
        if hasDisallowedAssumptions(report):
            return DafnyAssumeError()
        if rawTimeoutCount != None and int(rawTimeoutCount) > 0:
            return DafnyTimeoutError()
        return DafnyVerified()
    if reportType==VERCHK:
        raise Exception("build system error: couldn't summarize %s\n" % report)
    elif reportType==SYNCHK:
        #  Report assumes even in syntax-only mode.
        if hasDisallowedAssumptions(report):
            return DafnyAssumeError()
        return DafnySyntaxOK()
    else:
        raise Exception("build system error: unknown report type %s\n" % reportType)

def summarize(reportType, verchk):
    content = open(verchk).read()

    # Extract time
    mo = re.compile("^([0-9.]+)user", re.MULTILINE).search(content)
    if mo != None:
        userTimeSec = float(mo.group(1))
    else:
        userTimeSec = None

    condition = extractCondition(reportType, verchk, content)
    condition.userTimeSec = userTimeSec
    condition.verchk = verchk
    return condition
