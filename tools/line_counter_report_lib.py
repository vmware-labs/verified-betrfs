import collections
import lib_deps
import json
import os

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
def accumulate(reports, mapper):
    counters = {}
    def getCounter(report):
        key = mapper(report)
        if key not in counters:
            counters[key] = collections.Counter()
        return counters[key]
    for report in reports:
        getCounter(report).update(report)
    for counter in counters.values():
        del counter["source"]
    return counters

def write_table(fp, counters):
    def write_row(key, rowdata):
        fp.write("# %-20s %5s %5s %5s\n" % (key,
                rowdata["spec"],
                rowdata["impl"],
                rowdata["proof"]))
    keys = list(counters.keys())
    keys.sort()
    write_row("", {"spec":"spec", "impl":"impl", "proof":"proof"})
    for key in keys:
        write_row(key, counters[key])

def report(input, output):
    reports = gatherReports(input)

    counters = accumulate(reports, lambda r: "all")
    def categorize(report):
        source = report["source"]
        dirpart = os.path.dirname(source)
        if dirpart == "Impl":
            base = source.split(".")[0]
            if base.endswith("Model"):
                return "Impl-Model"
            elif base.endswith("Impl"):
                return "Impl-Impl"
            else:
                return "Impl-Misc"
        else:
            return dirpart
    counters.update(accumulate(reports, categorize))
    fp = open(output, "w")
    json.dump(counters, fp, sort_keys=True, indent=2)
    fp.write("\n")
    write_table(fp, counters)
    fp.close()

