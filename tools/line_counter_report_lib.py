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
    counters = collections.defaultdict(lambda: collections.Counter())
    for report in reports:
      for key in mapper.keys(report):
        debugTable.add(mapper, key, report)
        counters[key].update(report)
      # add each report only once into the total line, even if it contributes to multiple rows above.
      if not key.endswith("ignore"):
        counters["total"].update(report)
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

#row_descriptors = [
#    Row("data",  "Bank~\\autoref{sec:core}", "ManualMapper-bank"),
#    Row("data", "RHHT Hash Table~\\autoref{sec:spec:refinement}", "ManualMapper-htatomic"),
#    #Row("data", "Hand-over-hand~\\autoref{sec:handoverhand}", "ManualMapper-hthh"),
#    Row("data", "Node Replication~\\autoref{sec:nr}", "ManualMapper-nr"),
#    Row("data", "SplinterCache~\\autoref{sec:cache}", "ManualMapper-scache"),
#    Row("data", "Seagull Framework~\\autoref{sec:formalism}", "ManualMapper-framework"),
#]


row_descriptors = [
    Row("header", "Common"),
    Row("data", "LTS def. \\& ghost axioms",  "ManualMapper-framework"),
    Row("data", "Memory Primitives",  "ManualMapper-framework-mem"),
    Row("data", "Libraries",  "ManualMapper-framework-lib", impl=True),

    Row("header", "Bank~\\autoref{sec:core}"),
    Row("data", "Spec", "ManualMapper-bank-spec"),
    Row("data", "LTS", "ManualMapper-bank-sm"),
    Row("data", "Impl", "ManualMapper-bank", impl=True),

    Row("header", "RHHT Hash Table~\\autoref{sec:spec:refinement}"),
    Row("data", "Spec",  "ManualMapper-htatomic-spec"),
    Row("data", "LTS",  "ManualMapper-htatomic-lts"),
    Row("data", "Refinement Proofs",  "ManualMapper-htatomic-ref"),
    Row("data", "Impl",  "ManualMapper-htatomic-impl", impl=True),

    Row("header", "Node Replication~\\autoref{sec:nr}"),
    Row("data", "Spec",  "ManualMapper-nr-spec"),
    Row("data", "\\UnboundedLog LTS",  "ManualMapper-nr-log"),
    Row("data", "\\FlatCombine LTS",  "ManualMapper-nr-fc"),
    Row("data", "\\CyclicBuffer LTS",  "ManualMapper-nr-cyclic"),
    Row("data", "\\DistRwLock LTS",  "ManualMapper-nr-rw"),
    Row("data", "Refinement Proofs",  "ManualMapper-nr-ref"),
    Row("data", "Impl",  "ManualMapper-nr-impl", impl=True),

    Row("header", "SplinterCache~\\autoref{sec:cache}"),
    Row("data", "Spec",  "ManualMapper-scache-spec"),
    Row("data", "Disk Model and API",  "ManualMapper-scache-disk"),
    Row("data", "\\Cache LTS",  "ManualMapper-scache-sm"),
    Row("data", "\\CacheRwLock LTS",  "ManualMapper-scache-rw"),
    Row("data", "Refinement Proofs",  "ManualMapper-scache-ref"),
    Row("data", "Impl",  "ManualMapper-scache-impl", impl=True),
]

def write_tex_table(fp, counters):
    fp.write("\\begin{center}\n")
    fp.write("\\setlength{\\tabcolsep}{5pt}\n")
    fp.write("\\begin{tabular}{|l|rrrr|}\n")
    fp.write("\\hline\n")

    fp.write("Major component & trusted & impl & proof & verif\\\\\n")
    fp.write("& {\\small LOC} & {\\small LOC} & {\\small LOC} & time\\\\\n")
    fp.write("\\hline\n")

    def write_row(label, rowdata):
      def dropzero(d, suffix=""):
        return "" if d == 0 else str(d)+suffix

      fp.write("%s & %s & %s & %s & %s\\\\\n" % (
              label,
              dropzero(rowdata["spec"]),
              dropzero(rowdata["impl"]),
              dropzero(rowdata["proof"]),
              #dropzero(int(rowdata["time"]), suffix="s"),
              dropzero("%.1f" % (rowdata["time"]/60), suffix=" min"),
              ))

    keys = list(counters.keys())
    keys.sort()
    for row in row_descriptors:
      if row.type == "data":
        if row.counter_key in counters:
          local_counter = counters[row.counter_key]
          write_row(row.label, local_counter)
        else:
          print("Warning: missing counter for %s" % row.counter_key)
      elif row.type == "header":
        fp.write("\\textbf{" + row.label + "} & &  &  & \\\\")
      else:
        assert False
    fp.write("\\hline\n")
    write_row("Total", counters["total"])
    fp.write("\\hline\n")
    fp.write("\\end{tabular}\n")
    fp.write("\\end{center}\n")

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

    def keys(self, report):
        rc = ["%s-%s" % (self.categ, key) for key in self.map(report)]
        return rc

class AllMapper(Mapper):
    def __init__(self):
        super().__init__()

    def map(self, path):
        return ["all"]

class DirMapper(Mapper):
    def __init__(self):
        super().__init__()

    def map(self, report):
        source = report["source"]
        dirpart = os.path.dirname(source)
        if dirpart == "Impl":
            base = source.split(".")[0]
            if base.endswith("Model"):
                return ["Impl-Model"]
            elif base.endswith("Impl"):
                return ["Impl-Impl"]
            else:
                return ["Impl-Misc"]
        else:
            return [dirpart]

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
            if path not in self.mapping:
                self.mapping[path] = set()
            self.mapping[path].add(categ)

    def map(self, report):
        source = report["source"]
        if source not in self.mapping:
            print("unmapped: ", source)
        return self.mapping.get(report["source"], ["unmapped"])

def emit_tex_commented(fp, multiline_string):
    for line in multiline_string.split("\n"):
        fp.write("% "+line+"\n")

def emit_tidy_table(reports):
    selected = [report for report in reports if report["source"].endswith(".s.dfy")]
    selected.sort(key=lambda report: -report["spec"])
    s = ""
    for report in selected:
        s += "%5d %s\n" % (report["spec"], report["source"])
    return s

def highlights(reports, counters):
    s = ""
    count_under_minute = len([report for report in reports if report["time"]<60.0])
    pctFilesUnderOneMinute = count_under_minute / len(reports) * 100.0
    s += "\\newcommand{\\dataPctFilesUnderOneMinute}{%d}\n" % int(pctFilesUnderOneMinute)
    slowestFileSec = sorted(reports, key=lambda r: r["time"])[-1]["time"]
    s += "\\newcommand{\\dataSlowestFileSec}{%d}\n" % int(slowestFileSec)
    slowestFileMin = int(slowestFileSec) / 60 + 1
    s += "\\newcommand{\\dataSlowestFileMin}{%d}\n" % int(slowestFileMin)
    frameworkImplLoc = counters["ManualMapper-framework"]["impl"]
    s += "\\newcommand{\\dataFrameworkImplLoc}{%d}\n" % frameworkImplLoc
    caseStudyImplLoc = counters["total"]["impl"] - frameworkImplLoc
    s += "\\newcommand{\\dataCaseStudyImplLoc}{%d}\n" % caseStudyImplLoc
    allProof = counters["total"]["proof"]
    s += "\\newcommand{\\dataAllProof}{%d}\n" % allProof
    try:
      proofCodeRatio = allProof / counters["total"]["impl"]
    except:
      proofCodeRatio = -1
    s += "\\newcommand{\\dataProofCodeRatio}{%.1f}\n" % proofCodeRatio
    s += "\\newcommand{\\dataTrustedLoc}{%d}\n" % counters["total"]["spec"]
    s += "\\newcommand{\\dataTrustedFrameworkLoc}{%d}\n" % counters["ManualMapper-framework"]["spec"]
    trustedAppLines = [counter["spec"] for k,counter in counters.items() if "ignore" not in k and "total" not in k and "framework" not in k]
    if len(trustedAppLines) > 0:
        s += "\\newcommand{\\dataMinTrustedAppLines}{%d}\n" % min(trustedAppLines)
        s += "\\newcommand{\\dataMaxTrustedAppLines}{%d}\n" % max(trustedAppLines)
    else:
        s += "\\newcommand{\\dataMinTrustedAppLines}{none}\n"
        s += "\\newcommand{\\dataMaxTrustedAppLines}{none}\n"
    return s

def report(input, output):
    debugTable = DebugTable()
    reports = gatherReports(input)
#    counters = accumulate(reports, AllMapper(), debugTable)
#    counters.update(accumulate(reports, DirMapper(), debugTable))
#    counters.update(accumulate(reports, ManualMapper(), debugTable))
    counters = accumulate(reports, ManualMapper(), debugTable)
    debugTable.display(open("/tmp/debugtable", "w"))
    fp = open(output, "w")
    emit_tex_commented(fp, f"autogenerated with make {output}")
    emit_tex_commented(fp, "%%%% highlights")

    fp.write("\\ifx\\tablemode\\undefined\n")
    fp.write(highlights(reports, counters))
    fp.write("\\else\n")
    write_tex_table(fp, counters)
    fp.write("\\fi\n")

    emit_tex_commented(fp, "%%%% reports")
    emit_tex_commented(fp, json.dumps(reports, sort_keys=True, indent=2))
    emit_tex_commented(fp, "%%%% counters")
    emit_tex_commented(fp, json.dumps(counters, sort_keys=True, indent=2))
    emit_tex_commented(fp, "%%%% tidy table")
    emit_tex_commented(fp, emit_tidy_table(reports))
    write_compact_table(fp, counters)
    fp.close()

