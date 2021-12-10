import collections
import lib_deps
import json
import os

# make build/Impl/Bundle.i.lcreport -j4
# (incremental report redraw:)
# tools/line_counter.py --mode report --input Impl/Bundle.i.dfy --output build/Impl/Bundle.i.lcreport
# cp build/Impl/Bundle.i.lcreport ../veripapers/osdi2020/data/line-counts.tex

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

class DebugTable:
    def __init__(self):
        self.rows = []

    def add(self, mapper, key, report):
        justTheData = dict(report)
        del justTheData["source"]
        self.rows.append((key, report["source"], justTheData))

    def display(self, fp):
        for row in sorted(self.rows):
            fp.write(f"{row[0]:40} {row[1]:70} {row[2]}\n")

# I should probably just dump stuff into an in-memory sqlite, huh?
def accumulate(reports, mapper, debugTable):
    counters = {}
    def getCounter(report):
        key = mapper.key(report)
        debugTable.add(mapper, key, report)
        if key not in counters:
            counters[key] = collections.Counter()
        return counters[key]
    for report in reports:
        getCounter(report).update(report)
    for counter in counters.values():
        del counter["source"]
    return counters

class Row:
    def __init__(self, type, label, counter_key = None, impl = False):
        self.type = type
        self.label = label
        self.impl = impl    # if False, impl lines suspended here and added into later impl row.
        if self.type=="data":
          assert counter_key
          self.counter_key = counter_key
        else:
          assert self.type=="header"

    #Row("data", "foo", "ManualMapper-ignore"),
row_descriptors = [
    Row("header", "Atomic Hashtable"),
      Row("data", "Trusted spec", "ManualMapper-htatomic-spec"),
      Row("data", "IO LTS", "ManualMapper-htatomic-lts"),
      Row("data", "refinement proof", "ManualMapper-htatomic-refinementproof"),
      Row("data", "implementation", "ManualMapper-htatomic-impl", impl=True),

    Row("header", "Hand-over-hand Hashtable"),
      Row("data", "Trusted spec", "ManualMapper-hthh-spec"),
      Row("data", "IO LTS", "ManualMapper-hthh-lts"),
      Row("data", "refinement proof", "ManualMapper-hthh-refinementproof"),
      Row("data", "implementation", "ManualMapper-hthh-impl", impl=True),

    Row("header", "Node Replication"),
      Row("data", "Trusted spec", "ManualMapper-nr-spec"),
      Row("data", "IO LTS", "ManualMapper-nr-lts"),
      Row("data", "refinement proof", "ManualMapper-nr-refinementproof"),
      Row("data", "guard: cyclic buffer", "ManualMapper-nr-guard-cyclicbuffer"),
      Row("data", "guard: flat combiner", "ManualMapper-nr-guard-fc"),
      Row("data", "implementation", "ManualMapper-nr-impl", impl=True),
      Row("data", "guard: rwlock", "ManualMapper-nr-rwlock-guard"),
      Row("data", "rwlock implementation", "ManualMapper-nr-rwlock-impl", impl=True),

    Row("header", "Splinter Cache"),
      Row("data", "Trusted spec", "ManualMapper-scache-spec"),
      Row("data", "IO LTS", "ManualMapper-scache-lts"),
      Row("data", "refinement proof", "ManualMapper-scache-refinementproof"),
      Row("data", "implementation", "ManualMapper-scache-impl"),
      Row("data", "guard: rwlock", "ManualMapper-scache-rwlock-guard", impl=True),

    Row("header", "Shared"),
      Row("data", "Trusted Framework", "ManualMapper-framework", impl = True),
      Row("data", "Library", "ManualMapper-library", impl = True),
]

def write_tex_table(fp, counters):
    fp.write("\\begin{tabular}{|ll|rrr|}\n")
    fp.write("\\hline\n")

    fp.write("\multicolumn{2}{|l|}{Major component} & model & impl & verif. time\\\\\n")
    fp.write("\\hline\n")

    def write_row(label, rowdata):
      def dropzero(d, suffix=""):
        return "" if d == 0 else str(d)+suffix

      assert label=="total" or rowdata["spec"]==0 or rowdata["proof"]==0  # collapsing model && spec into a column; alarm if data overlaps
      model = dropzero(rowdata["spec"] + rowdata["proof"])
      fp.write("& %s & %s & %s & %s\\\\\n" % (
              label,
              model,
              dropzero(rowdata["impl"]),
              dropzero(int(rowdata["time"]), suffix="~s"),
              ))

    keys = list(counters.keys())
    keys.sort()
    deferred_impl = 0
    # add up totals here rather than using AllMapper to get desired 'trusted' total layout (and allmapper includes ignored row)
    total_counter = collections.Counter()
    for row in row_descriptors:
      if row.type == "header":
        fp.write("\\multicolumn{2}{|l|}{%s} &&& \\\\\n" % row.label)
      elif row.type == "data":
        if row.counter_key in counters:
          local_counter = dict(counters[row.counter_key])
          total_counter.update(local_counter)
          if row.impl:
            local_counter["impl"] += deferred_impl
            deferred_impl = 0
          else:
            deferred_impl += local_counter["impl"]
            local_counter["impl"] = 0
          write_row(row.label, local_counter)
        else:
          print("Warning: missing counter for %s" % row.counter_key)
    assert deferred_impl == 0   # Don't let any fall off the end.
    fp.write("\\hline\n")
    write_row("Trusted total", dict([(k,v if k == "spec" else 0) for k,v in total_counter.items()]))
        #{"spec": total_counter["spec"], "proof":0, "impl":0, "time":0})
    write_row("Verified total", dict([(k,v if k != "spec" else 0) for k,v in total_counter.items()]))
    fp.write("\\hline\n")
    fp.write("\\end{tabular}\n")

def write_compact_table(fp, counters):
    def write_row(key, rowdata):
        fp.write("%% %-48s %5s %5s %5s\n" % (key,
                rowdata["spec"],
                rowdata["impl"],
                rowdata["proof"]))
    keys = list(counters.keys())
    keys.sort()
    fp.write("% write_compact_table()\n")
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
          if line.startswith("#"): continue
          if line.strip() != '':
            categ,path = line.split()
            if path.startswith("./"):
                path = path[2:]
            self.mapping[path] = categ

    def map(self, report):
        source = report["source"]
        if source not in self.mapping:
            print("unmapped: ", source)
        return self.mapping.get(report["source"], "unmapped")

def emit_tex_commented(fp, multiline_string):
    for line in multiline_string.split("\n"):
        fp.write("% "+line+"\n")
    
def report(input, output):
    debugTable = DebugTable()
    reports = gatherReports(input)
    counters = accumulate(reports, AllMapper(), debugTable)
    counters.update(accumulate(reports, DirMapper(), debugTable))
    counters.update(accumulate(reports, ManualMapper(), debugTable))
    debugTable.display(open("/tmp/debugtable", "w"))
    fp = open(output, "w")
    write_tex_table(fp, counters)
    emit_tex_commented(fp, "%%%% reports")
    emit_tex_commented(fp, json.dumps(reports, sort_keys=True, indent=2))
    emit_tex_commented(fp, "%%%% counters")
    emit_tex_commented(fp, json.dumps(counters, sort_keys=True, indent=2))
    write_compact_table(fp, counters)
    fp.close()

