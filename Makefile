##############################################################################
# System configuration

# You can build anything reachable from these root files.
DAFNY_ROOTS=Impl/Bundle.i.dfy build-tests/test-suite.i.dfy

DAFNY_ROOT?=.dafny/dafny/
DAFNY_CMD=$(DAFNY_ROOT)/Binaries/dafny
DAFNY_BINS=$(wildcard $(DAFNY_ROOT)/Binaries/*)
DAFNY_FLAGS=

ifndef TL
	TL=0
endif
ifeq "$(TL)" "0"
  TIMELIMIT=
else
  TIMELIMIT=/timeLimit:$(TL)
endif

POUND_DEFINES=
ifdef LOG_QUERY_STATS
	POUND_DEFINES += -DLOG_QUERY_STATS
endif

CC=clang++
STDLIB=-stdlib=libc++

# Uncomment to enable gprof
#GPROF_FLAGS=-pg

WANT_UNVERIFIED_ROW_CACHE=false
ifeq "$(WANT_UNVERIFIED_ROW_CACHE)" "true"
	UNVERIFIED_ROW_CACHE_DEFINE=-DUSE_UNVERIFIED_ROW_CACHE
else
	UNVERIFIED_ROW_CACHE_DEFINE=
endif

WANT_MALLOC_ACCOUNTING=false
ifeq "$(WANT_MALLOC_ACCOUNTING)" "true"
	MALLOC_ACCOUNTING_DEFINE=-DMALLOC_ACCOUNTING=1
else
	MALLOC_ACCOUNTING_DEFINE=
endif

WANT_DEBUG=false
ifeq "$(WANT_DEBUG)" "true"
	DBG_SYMBOLS_FLAG=-g
	OPT_FLAG=-O0
else
	DBG_SYMBOLS_FLAG=
	OPT_FLAG=-O3
endif

# _LIBCPP_HAS_NO_THREADS makes shared_ptr faster
# (but also makes stuff not thread-safe)
# Note: this optimization only works with stdlib=libc++
OPT_FLAGS=$(MALLOC_ACCOUNTING_DEFINE) \
          $(UNVERIFIED_ROW_CACHE_DEFINE) \
          $(DBG_SYMBOLS_FLAG) \
          $(OPT_FLAG) \
          -D_LIBCPP_HAS_NO_THREADS \
          $(GPROF_FLAGS)

##############################################################################
# Automatic targets

all: build/osdi20-artifact/paper.pdf

clean:
	rm -rf build
	@$(MAKE) -C ycsb clean

##############################################################################
# Build dir and dependency setup

.PRECIOUS: build/. build%/.
# .SECONDEXPANSION Needed to make $$(@D) trick work.
# http://ismail.badawi.io/blog/2017/03/28/automatic-directory-creation-in-make/
.SECONDEXPANSION:

# Make build/ directory
build/.:
	mkdir -p $@

# Ensure deps gets rebuilt if someone changes DAFNY_ROOTS
build/roots: | $$(@D)/.
	echo $(DAFNY_ROOTS) > $@

# Make generated build/deps file.
build/deps: tools/veridepend.py tools/lib_deps.py build/roots | build/.
	tools/veridepend.py $(DAFNY_ROOTS)

include build/deps

# Make build/ subdirectories, as demanded by rules in generated build/deps file.
build%/.:
	mkdir -p $@

##############################################################################
# Helpers for rules.

# tee_capture lets us see the output of commands during the make, but also
# capture it in the build/ result file. It's trickier than you'd think,
# because we need to:
# (a) cause the rule to fail if the command fails. By default, the shell
# reports whether 'tee' failed.
# (b) not create the output file if the command fails, hence the TMPNAME.
# Use bash so PIPESTATUS works
SHELL=/bin/bash
define tee_capture
	$(eval TMPNAME=$(patsubst build/%,build/tmp/%,$1))
	mkdir -p $(shell dirname $(TMPNAME))
	$(2) 2>&1 | tee $(TMPNAME); test $${PIPESTATUS[0]} -eq 0
	mv $(TMPNAME) $1
endef

# This version only breaks on abnormal exits, e.g. segfaults
define tee_capture_allow_errors
	$(eval TMPNAME=$(patsubst build/%,build/tmp/%,$1))
	mkdir -p $(shell dirname $(TMPNAME))
	$(2) 2>&1 | tee $(TMPNAME); test $${PIPESTATUS[0]} -lt 128
	mv $(TMPNAME) $1
endef


##############################################################################
##############################################################################
# Special top-level targets

##############################################################################
# Verification status page

.PHONY: status
status: build/deps build/Impl/Bundle.i.status.pdf

.PHONY: faststatus
syntax-status: build/deps build/Impl/Bundle.i.syntax-status.pdf

.PHONY: verify-ordered
verify-ordered: build/deps build/Impl/Bundle.i.okay

##############################################################################
# C# executables

FRAMEWORK_SOURCES=framework/Framework.cs framework/Benchmarks.cs framework/Crc32.cs

.PHONY: exe
exe: build/Veribetrfs.exe

build/Impl/Bundle.i.exe: build/Impl/Bundle.i.cs $(FRAMEWORK_SOURCES)
	csc $^ /optimize /r:System.Numerics.dll /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /unsafe /out:$@

.PHONY: exe-roslyn
exe-roslyn: build/Impl/Bundle.i.roslyn.exe

build/Impl/Bundle.i.roslyn.exe:build/Impl/Bundle.i.cs $(FRAMEWORK_SOURCES)
	tools/roslyn-csc.sh $^ /optimize /nowarn:CS0162 /nowarn:CS0164 /unsafe /t:exe /out:$@
#eval trick to assign make var inside rule
	$(eval CONFIG=$(patsubst %.roslyn.exe,%.roslyn.runtimeconfig.json,$@))
	tools/roslyn-write-runtimeconfig.sh > $(CONFIG)

build/Veribetrfs.exe: build/Impl/Bundle.i.exe
	cp $< $@

##############################################################################
# C++ executables

.PHONY: allcpp
allcpp: build/Impl/Bundle.i.cpp

.PHONY: allo
allo: build/Impl/Bundle.i.o

.PHONY: elf
elf: build/Veribetrfs

##############################################################################
##############################################################################
# Pattern rules

# This was cool until someone tried to run it on MacOS.
#TIME=time -f "real %es cpu %Us"
#TIME=/usr/bin/time --format '%Uuser'
TIME=/usr/bin/time

##############################################################################
# Dummy dependency chains, so that a rule that depends on a top-level .dfy
# file can be made to depend on all of the included dfys reachable from there.
build/%.dummydep: %.dfy | $$(@D)/.
	touch $@

##############################################################################
# .synchk: Dafny syntax check
build/%.synchk: %.dfy $(DAFNY_BINS) | $$(@D)/.
	$(call tee_capture_allow_errors,$@,$(TIME) $(DAFNY_CMD) /compile:0 /dafnyVerify:0 $<)

##############################################################################
# .verchk: Dafny file-local verification
build/%.verchk: %.dfy $(DAFNY_BINS) | $$(@D)/.
	$(call tee_capture_allow_errors,$@,$(TIME) $(DAFNY_CMD) /compile:0 /trace $(TIMELIMIT) $<)

##############################################################################
# .okay: Dafny file-level verification, no time limit,
# verifies in dependency order.
# This is currently Travis's favorite build rule.

build/%.okay: %.dfy | $$(@D)/.
	$(TIME) $(DAFNY_CMD) /compile:0 $<
	touch $@

##############################################################################
# .verified: Aggregate result of verification for this file and
# its dependencies.
.PRECIOUS: build/%.verchk
AGGREGATE_TOOL=tools/aggregate-verchk.py
build/%.verified: build/%.verchk $(AGGREGATE_TOOL) | $$(@D)/.
	$(call tee_capture,$@,$(AGGREGATE_TOOL) $^)

# Syntax is trivial from synchk file, just a marker.
# (We need the .syntax target to get a recursive dependency computation.)
build/%.syntax: build/%.synchk $(AGGREGATE_TOOL) | $$(@D)/.
	touch $@

##############################################################################
# .status.pdf: a dependency graph of .dfy files labeled with verification result status.
#
STATUS_TOOL=tools/dep-graph.py
STATUS_DEPS=tools/lib_aggregate.py
build/%.status.pdf: %.dfy build/%.verified $(STATUS_TOOL) $(STATUS_DEPS) build/deps | $$(@D)/.
	@$(eval DOTNAME=$(patsubst %.status.pdf,%.dot,$@))	 #eval trick to assign make var inside rule
	$(STATUS_TOOL) verchk $< $(DOTNAME)
	@tred < $(DOTNAME) | dot -Tpdf -o$@

# A syntax-only version of the tree so I can play around without waiting for
# a complete verification.
build/%.syntax-status.pdf: %.dfy build/%.syntax $(STATUS_TOOL) $(STATUS_DEPS) build/deps | $$(@D)/.
	$(eval DOTNAME=$(patsubst %.status.pdf,%.dot,$@))	 #eval trick to assign make var inside rule
	$(STATUS_TOOL) synchk $< $(DOTNAME)
	@tred < $(DOTNAME) | dot -Tpdf -o$@

##############################################################################
# .lcreport: Tabular data on line counts of {spec, impl, proof}
#.PRECIOUS: build/%.lc --Why isn't this necessary?
LC_TOOL=tools/line_counter.py
LC_DEPS=tools/line_count_lib.py tools/lib_aggregate.py tools/lib_deps.py
build/%.lc: %.dfy build/%.syntax $(LC_TOOL) $(LC_DEPS)
		$(LC_TOOL) --mode count --input $< --output $@

LC_REPORT_DEPS=tools/line_counter_report_lib.py
build/%.lcreport: %.dfy build/%.lc $(LC_TOOL) $(LC_DEPS) $(LC_REPORT_DEPS)
		$(LC_TOOL) --mode report --input $< --output $@

##############################################################################
# .cs: C-Sharp output from compiling a Dafny file (which includes all deps)
# In principle, building code should depend on .verified! But we want
# to play with perf with not-entirely-verifying trees.
build/%.cs: %.dfy $(DAFNY_BINS) | $$(@D)/.
#eval trick to assign make var inside rule
# Dafny irritatingly removes the '.i' presuffix, and has a weird behavior where it duplicates prefixes of relative paths. Bizarre.
	$(eval TMPNAME=$(abspath $(patsubst %.s.cs,%-s.cs,$(patsubst %.i.cs,%-i.cs,$@))))
	pwd
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPNAME) $<
	mv $(TMPNAME) $@

##############################################################################
# .cpp: C++ output from compiling a Dafny file (which includes all deps)
# Slow, but useful for iterating when working on the cpp compiler.
build/%.cpp build/%.h: %.dfy $(DAFNY_BINS) | $$(@D)/.
#eval trick to assign make var inside rule
	$(eval CPPNAME=$(abspath build/$*.cpp))
	$(eval TMPCPPNAME=$(abspath $(patsubst build/%,build/tmp/%,build/$*.cpp)))
	$(eval HNAME=$(abspath build/$*.h))
	$(eval TMPHNAME=$(abspath $(patsubst build/%,build/tmp/%,build/$*.h)))
	mkdir -p $(shell dirname $(TMPCPPNAME))
# Dafny irritatingly removes the '.i' presuffix.
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPCPPNAME) /compileTarget:cpp $< Framework.h
	mv $(TMPCPPNAME) $(CPPNAME)
	mv $(TMPHNAME) $(HNAME)

# Build the main cpp file without building all the partial cpp files.
build/Bundle.cpp: Impl/Bundle.i.dfy build/Impl/Bundle.i.dummydep $(DAFNY_BINS) | $$(@D)/.
#eval trick to assign make var inside rule
	$(eval TMPNAME=$(abspath $(patsubst %.cpp,%-i.cpp,$@)))
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPNAME) /compileTarget:cpp $< Framework.h
	mv $(TMPNAME) $@

build/Bundle.i.h: build/Bundle.cpp
# this is build automatically when we build Bundle.cpp
	touch build/Bundle.i.h

##############################################################################
# C++ object files

CPP_DEP_DIR=build/cppdeps
GEN_H_FILES=build/Bundle.i.h

WARNINGS=-Wall -Wsign-compare

build/%.o: build/%.cpp $(GEN_H_FILES) | $$(@D)/.
	@mkdir -p $(CPP_DEP_DIR)/$(basename $<)
	$(CC) $(STDLIB) -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I framework/ -std=c++17 -msse4.2 $(POUND_DEFINES) -MMD -MP -MF "$(CPP_DEP_DIR)/$(<:.cpp=.d)" $(CCFLAGS) $(OPT_FLAGS) $(WARNINGS)

build/framework/%.o: framework/%.cpp $(GEN_H_FILES) | $$(@D)/.
	@mkdir -p $(CPP_DEP_DIR)/$(basename $<)
	$(CC) $(STDLIB) -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I framework/ -I build/ -std=c++17 -march=native -msse4.2 $(POUND_DEFINES) -MMD -MP -MF "$(CPP_DEP_DIR)/$(<:.cpp=.d)" $(CCFLAGS) $(OPT_FLAGS) $(WARNINGS) -Werror

# the BundleWrapper.cpp file includes the auto-generated Bundle.cpp
build/framework/BundleWrapper.o: framework/BundleWrapper.cpp build/Bundle.cpp $(GEN_H_FILES) | $$(@D)/.
	@mkdir -p $(CPP_DEP_DIR)/$(basename $<)
# No -Werror
	$(CC) $(STDLIB) -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I framework/ -I build/ -std=c++17 -march=native -msse4.2 -MMD -MP -MF "$(CPP_DEP_DIR)/$(<:.cpp=.d)" $(CCFLAGS) $(OPT_FLAGS) $(WARNINGS)

# Include the .h depencies for all previously-built .o targets. If one of the .h files
# changes, we'll rebuild the .o
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))
-include $(call rwildcard,$(CPP_DEP_DIR)/,*.d)

VERIBETRFS_AUX_FILES=\
	build/framework/Benchmarks.o \
	build/framework/BundleWrapper.o \
	build/framework/Crc32.o \
	build/framework/UnverifiedRowCache.o \
	build/framework/Framework.o \
	build/framework/MallocAccounting.o \
	build/framework/NativeArrays.o \

VERIBETRFS_O_FILES=\
	$(VERIBETRFS_AUX_FILES)\
	build/framework/Main.o \

LDFLAGS=-msse4.2

# On linux we need the -lrt (for aio functions),
# but on mac it doesn't exist.
UNAME := $(shell uname)
ifeq ($(UNAME), Darwin)
else
LDFLAGS += -lrt
endif

build/Veribetrfs: $(VERIBETRFS_O_FILES)
	$(CC) $(STDLIB) -o $@ $(VERIBETRFS_O_FILES) $(LDFLAGS) $(GPROF_FLAGS)

##############################################################################
# YCSB

VERIBETRFS_YCSB_O_FILES=\
	$(VERIBETRFS_AUX_FILES)\
	build/framework/leakfinder.o \

# Ideally, we'd fix this to build these in the top-level build directory.
libycsbc: ycsb/build/libycsbc-libcpp.a \
				  ycsb/build/libycsbc-default.a

ycsb/build/libycsbc-libcpp.a:
	STDLIB=libcpp $(MAKE) -C ycsb build/libycsbc-libcpp.a

ycsb/build/libycsbc-default.a:
	STDLIB=default $(MAKE) -C ycsb build/libycsbc-default.a

NEED_TO_REBUILD_LIBROCKSDB=$(shell $(MAKE) -q -C vendor/rocksdb static_lib; echo "$?")

ifeq ($(NEED_TO_REBUILD_LIBROCKSDB),1)
.PHONY: vendor/rocksdb/librocksdb.a
endif

vendor/rocksdb/librocksdb.a:
	@env \
		ROCKSDB_DISABLE_BZIP=1 \
		ROCKSDB_DISABLE_ZLIB=1 \
		ROCKSDB_DISABLE_LZ4=1 \
		ROCKSDB_DISABLE_ZSTD=1 \
		ROCKSDB_DISABLE_JEMALLOC=1 \
		ROCKSDB_DISABLE_SNAPPY=1 \
		$(MAKE) -C vendor/rocksdb static_lib

.PHONY: libycsbc 

# The dependency on libycsbc is just to force some headers to be copied into place
build/YcsbMain.o: ycsb/YcsbMain.cpp ycsb/build/libycsbc-default.a
	$(CC) $(STDLIB) -c -o $@ \
			-I ycsb/build/include \
			-I $(DAFNY_ROOT)/Binaries/ \
			-I framework/ \
			-I build/ \
			-I vendor/hdrhist/ \
			-I vendor/rocksdb/include/ \
			-Winline -std=c++17 $(O3FLAG) \
			-D_YCSB_VERIBETRFS \
			$(POUND_DEFINES) \
			$(MALLOC_ACCOUNTING_DEFINE) \
			$(DBG_SYMBOLS_FLAG) \
			$(GPROF_FLAGS) \
			$^

build/VeribetrfsYcsb: $(VERIBETRFS_YCSB_O_FILES) ycsb/build/libycsbc-libcpp.a build/YcsbMain.o
	# NOTE: this uses c++17, which is required by hdrhist
	$(CC) $(STDLIB) -o $@ \
			-Winline -std=c++17 $(O3FLAG) \
			-L ycsb/build \
			-L vendor/rocksdb \
			$(DBG_SYMBOLS_FLAG) \
			$(VERIBETRFS_YCSB_O_FILES) \
			build/YcsbMain.o \
			-lycsbc-libcpp -lpthread -ldl $(LDFLAGS)

build/RocksYcsb: ycsb/build/libycsbc-default.a vendor/rocksdb/librocksdb.a ycsb/YcsbMain.cpp
	$(CC) -o $@ \
			-L ycsb/build \
			-L vendor/rocksdb \
			-I ycsb/build/include \
			-I $(DAFNY_ROOT)/Binaries/ \
			-I framework/ \
			-I build/ \
			-I vendor/hdrhist/ \
			-I vendor/rocksdb/include/ \
			-Winline -std=c++17 $(O3FLAG) \
			-D_YCSB_ROCKS \
			$(POUND_DEFINES) \
			ycsb/YcsbMain.cpp \
			-lycsbc-default -lrocksdb -lpthread -ldl $(LDFLAGS) \

vendor/kyoto/kyotocabinet/libkyotocabinet.a:
	(cd vendor/kyoto/kyotocabinet; CXX=clang++ CXXFLAGS=$(STDLIB) ./configure; make)

build/KyotoYcsb: ycsb/YcsbMain.cpp ycsb/build/libycsbc-libcpp.a vendor/kyoto/kyotocabinet/libkyotocabinet.a
	# NOTE: this uses c++17, which is required by hdrhist
	$(CC) \
      $(STDLIB) \
      -o $@ \
			-Winline -std=c++17 $(O3FLAG) \
			-L ycsb/build \
			-I ycsb/build/include \
			-I $(DAFNY_ROOT)/Binaries/ \
			-I framework/ \
			-I build/ \
			-I vendor/hdrhist/ \
			-I vendor/kyoto/kyotocabinet \
			-L vendor/kyoto/kyotocabinet \
			$(DBG_SYMBOLS_FLAG) \
			-D_YCSB_KYOTO \
			ycsb/YcsbMain.cpp \
			vendor/kyoto/kyotocabinet/libkyotocabinet.a \
			-lycsbc-libcpp -lpthread -ldl -lz $(LDFLAGS)

# Requires libdb-stl-dev to be installed (on debian, libdbb5.3-stl-dev)
build/BerkeleyYcsb: ycsb/YcsbMain.cpp ycsb/build/libycsbc-libcpp.a
	# NOTE: this uses c++17, which is required by hdrhist
	$(CC) \
      $(STDLIB) \
      -o $@ \
			-Winline -std=c++17 $(O3FLAG) \
			-L ycsb/build \
			-I ycsb/build/include \
			-I $(DAFNY_ROOT)/Binaries/ \
			-I framework/ \
			-I build/ \
			-I vendor/hdrhist/ \
			$(DBG_SYMBOLS_FLAG) \
			-D_YCSB_BERKELEYDB \
			ycsb/YcsbMain.cpp \
			-lycsbc-libcpp -lpthread -ldl -lz -ldb_stl $(LDFLAGS)


ycsb: build/VeribetrfsYcsb build/RocksYcsb build/KyotoYcsb build/BerkeleyYcsb

##############################################################################
# Verification time and automation study results

build/verification-times.tgz: build/Impl/Bundle.i.verified
	tar cvzf $@ `find build -name "*.verchk"`

build/verification-times.pdf: build/verification-times.tgz
	./tools/plot/plot-verification-time.py

# Hrm. Not clear how to depend on all source files, so we just depend on
# this verification result, which transitively depends on all sources.
build/automation-figure.pdf: build/Impl/Bundle.i.verified
	./tools/automation-study.py

build/linear-line-counts.tex build/linear-line-count-table.tex: tools/linear_line_counts.py lib/DataStructures/BtreeModel.i.dfy lib/DataStructures/MutableBtree.i.dfy lib/DataStructures/MutableMapModel.i.dfy lib/DataStructures/MutableMapImpl.i.dfy
	./tools/linear_line_counts.py

##############################################################################
# Linear/Dynamic Frames benchmarks of hashtable and btree

build/bench/run-mutable-map.o: bench/run-mutable-map.cpp build/bench/MutableMap.h
	$(CC) -c $< -o $@ $(STDLIB) -I build -I .dafny/dafny/Binaries/ -I framework -std=c++17 -O3

build/bench/run-mutable-map: build/bench/run-mutable-map.o build/bench/MutableMap.o build/framework/NativeArithmetic.o 
	$(CC)    $^ -o $@ $(STDLIB)

build/mutable-map-benchmark.data: build/bench/run-mutable-map
	$(call tee_capture,$@,$< 17 false)

build/mutable-map-benchmark.csv: build/mutable-map-benchmark.data tools/mutablemap-cook.sh
	$(call tee_capture,$@,tools/mutablemap-cook.sh $<)

build/bench/run-mutable-btree.o: bench/run-mutable-btree.cpp build/lib/DataStructures/MutableBtree.i.h
	$(CC) -c $< -o $@ $(STDLIB) -I build -I .dafny/dafny/Binaries/ -I framework -std=c++17 -O3

build/bench/run-mutable-btree: build/bench/run-mutable-btree.o build/lib/DataStructures/MutableBtree.i.o build/framework/NativeArithmetic.o build/framework/NativeArrays.o
	$(CC)    $^ -o $@ $(STDLIB)

build/mutable-btree-benchmark.data: build/bench/run-mutable-btree
	$(call tee_capture,$@,$< 17 64000000 false)

build/mutable-btree-benchmark.csv: build/mutable-btree-benchmark.data tools/mutablebtree-cook-2.sh
	$(call tee_capture,$@,tools/mutablebtree-cook-2.sh 64000000 $<)

##############################################################################
# YCSB benchmark runs

build/VeribetrfsYcsb.data: build/VeribetrfsYcsb ycsb/workloada-onefield.spec ycsb/workloada-onefield.spec ycsb/workloadb-onefield.spec ycsb/workloadc-onefield.spec ycsb/workloadd-onefield.spec ycsb/workloadf-onefield.spec ycsb/workloadc-uniform.spec
	rm -f build/veribetrkv.img
	$(call tee_capture,$@,./build/VeribetrfsYcsb build/veribetrkv.img ycsb/workloada-onefield.spec ycsb/workloada-onefield.spec ycsb/workloadb-onefield.spec ycsb/workloadc-onefield.spec ycsb/workloadd-onefield.spec ycsb/workloadf-onefield.spec ycsb/workloadc-uniform.spec)
	rm -f build/veribetrkv.img

build/RocksYcsb.data: build/RocksYcsb ycsb/workloada-onefield.spec ycsb/workloada-onefield.spec ycsb/workloadb-onefield.spec ycsb/workloadc-onefield.spec ycsb/workloadd-onefield.spec ycsb/workloadf-onefield.spec ycsb/workloadc-uniform.spec
	rm -rf build/RocksYcsb.db
	mkdir build/RocksYcsb.db
	$(call tee_capture,$@,./build/RocksYcsb build/RocksYcsb.db ycsb/workloada-onefield.spec ycsb/workloada-onefield.spec ycsb/workloadb-onefield.spec ycsb/workloadc-onefield.spec ycsb/workloadd-onefield.spec ycsb/workloadf-onefield.spec ycsb/workloadc-uniform.spec)
	rm -rf build/RocksYcsb.db

build/BerkeleyYcsb.data: build/BerkeleyYcsb ycsb/workloada-onefield.spec ycsb/workloada-onefield.spec ycsb/workloadb-onefield.spec ycsb/workloadc-onefield.spec ycsb/workloadd-onefield.spec ycsb/workloadf-onefield.spec ycsb/workloadc-uniform.spec
	rm -f build/berkeley.db
	$(call tee_capture,$@,./build/BerkeleyYcsb build/berkeley.db ycsb/workloada-onefield.spec ycsb/workloada-onefield.spec ycsb/workloadb-onefield.spec ycsb/workloadc-onefield.spec ycsb/workloadd-onefield.spec ycsb/workloadf-onefield.spec ycsb/workloadc-uniform.spec)
	rm -f build/berkeley.db

build/%Ycsb.csv: build/%Ycsb.data
	$(call tee_capture,$@,./tools/ycsb-cook.sh $<)

##############################################################################
# Build a PDF summarizing results

build/osdi20-artifact/paper.pdf: osdi20-artifact/paper.tex build/Impl/Bundle.i.lcreport build/linear-line-counts.tex build/verification-times.pdf build/automation-figure.pdf build/mutable-map-benchmark.csv build/mutable-btree-benchmark.csv build/Impl/Bundle.i.status.pdf build/VeribetrfsYcsb.csv build/RocksYcsb.csv build/BerkeleyYcsb.csv 
	mkdir -p build/osdi20-artifact
	pdflatex -shell-escape -output-directory build/osdi20-artifact $<
	pdflatex -shell-escape -output-directory build/osdi20-artifact $<
