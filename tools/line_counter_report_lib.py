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
        key = mapper.key(report)
        if key not in counters:
            counters[key] = collections.Counter()
        return counters[key]
    for report in reports:
        getCounter(report).update(report)
    for counter in counters.values():
        del counter["source"]
    return counters

row_labels = {
    "ManualMapper-map": "Map, 3States\\template{Map}",
    "ManualMapper-abstractbetree": "Abstract{\\beptree}",
    "ManualMapper-betree": "{\\beptree}",
    "ManualMapper-compositeviewmap": "CompositeViewMap",
    "ManualMapper-betreejournaliosystem": "{\\beptree}{\iosystem}",
    "ManualMapper-concreteiosystem": "Concrete{\iosystem}",
    "ManualMapper-impl": "implementation code",
    "ManualMapper-lib": "libraries",
        }

def write_tex_table(fp, counters):
    fp.write("\\begin{tabular}{|l|rrr|}\n")
    fp.write("\\hline\n")
    fp.write("Major component & spec & impl & proof \\\\\n")
    fp.write("\\hline\n")

    def write_row(label, rowdata):
        fp.write("%s & %d & %d & %d \\\\\n" % (
                label,
                rowdata["spec"],
                rowdata["impl"],
                rowdata["proof"]
                ))

    keys = list(counters.keys())
    keys.sort()
    for key,label in row_labels.items():
        if key in row_labels and key in counters:
            label = row_labels[key]
            write_row(label, counters[key])
    fp.write("\\hline\n")
    write_row("total", counters["AllMapper-all"])
    fp.write("\\hline\n")
    fp.write("\\end{tabular}\n")

def write_table(fp, counters):
    def write_row(key, rowdata):
        fp.write("%% %-30s %5s %5s %5s\n" % (key,
                rowdata["spec"],
                rowdata["impl"],
                rowdata["proof"]))
    keys = list(counters.keys())
    keys.sort()
    write_row("", {"spec":"spec", "impl":"impl", "proof":"proof"})
    for key in keys:
        write_row(key, counters[key])

class Mapper:
    def __init__(self):
        self.categ = self.__class__.__name__

    def key(self, report):
        return "%s-%s" % (self.categ, self.map(report))

class AllMapper(Mapper):
    def __init__(self):
        super().__init__()

    def map(self, path):
        return "all"

class DirMapper(Mapper):
    def __init__(self):
        super().__init__()

    def map(self, report):
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

class ManualMapper(Mapper):
    def __init__(self):
        super().__init__()
        self.mapping = {}
        for line in open("docs/file-classifications.txt").readlines():
            categ,path = line.split()
            if path.startswith("./"):
                path = path[2:]
            self.mapping[path] = categ

    def map(self, report):
        source = report["source"]
        if source not in self.mapping:
            print("unmapped: ", source)
        return self.mapping.get(report["source"], "unmapped")

def report(input, output):
    reports = gatherReports(input)

    counters = accumulate(reports, AllMapper())
    counters.update(accumulate(reports, DirMapper()))
    counters.update(accumulate(reports, ManualMapper()))
    fp = open(output, "w")
#    json.dumps(counters, fp, sort_keys=True, indent=2)
#    fp.write("\n")
    write_tex_table(fp, counters)
    write_table(fp, counters)
    fp.close()

