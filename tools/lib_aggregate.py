import sys
import re

class DafnyCondition:
    def __init__(self, level, result, color):
        self.level = level
        self.result = result
        self.color = color

    def __lt__(self, other):
        return self.level < other.level

    def __repr__(self):
        return self.result

class DafnyParseError(DafnyCondition):
    def __init__(self):
        super().__init__(0, "parse error", "red")

class DafnyTypeError(DafnyCondition):
    def __init__(self):
        super().__init__(1, "type error", "orange")

class DafnyVerificationError(DafnyCondition):
    def __init__(self):
        super().__init__(2, "verification error", "yellow")

class DafnyAssumeError(DafnyCondition):
    def __init__(self):
        super().__init__(3, "untrusted file contains assumptions", "cyan")

class DafnyVerified(DafnyCondition):
    def __init__(self):
        super().__init__(4, "verified successfully", "green")

def dafnyFromVerchk(verchk):
    return verchk.replace("/build/", "/").replace(".verchk", ".dfy")

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

def extractCondition(verchk, content):
    # Extract Dafny verification result
    if re.compile("parse errors detected in").search(content) != None:
        return DafnyParseError()
    if re.compile("resolution/type errors detected in").search(content) != None:
        return DafnyTypeError()
    mo = re.compile("Dafny program verifier finished with (\d+) verified, (\d+) error").search(content)
    if mo != None:
        verifCount,errorCount = map(int, mo.groups())
        if errorCount > 0:
            return DafnyVerificationError()
        if hasDisallowedAssumptions(verchk):
            return DafnyAssumeError()
        return DafnyVerified()
    raise Exception("build system error: aggregate-verchk couldn't summarize %s\n" % verchk)

def summarize(verchk):
    content = open(verchk).read()

    # Extract time
    mo = re.compile("^([0-9.]+)user", re.MULTILINE).search(content)
    if mo != None:
        userTimeSec = float(mo.group(1))
    else:
        userTimeSec = None

    condition = extractCondition(verchk, content)
    condition.userTimeSec = userTimeSec
    return condition
