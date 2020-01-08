import collections
import lib_deps
import json

def loadReport(iref):
    fp = open(lib_deps.targetName(iref, ".lc"))
    values = json.load(fp)
    values["source"] = iref.normPath
    return values

def gatherReports(input):
    TOP=lib_deps.IncludeReference(None, 0, input)
    targets = [TOP] + lib_deps.depsFromDfySource(TOP)
    reports = [loadReport(target) for target in targets]
    return reports

# I should probably just dump stuff into an in-memory sqlite, huh?
def accumulate(reports, select):
    counter = collections.Counter()
    for report in reports:
        #print(report)
        if select(report):
            counter.update(report)
    return counter

def report(input, output):
    reports = gatherReports(input)

    all = accumulate(reports, lambda r: True)
    fp = open(output, "w")
    json.dump(all, fp, sort_keys=True, indent=2)
    fp.write("\n")
    fp.close()

