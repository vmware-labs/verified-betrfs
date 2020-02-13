##############################################################################
# System configuration

# You can build anything reachable from these root files.
DAFNY_ROOTS=Impl/Bundle.i.dfy build-tests/test-suite.i.dfy

DAFNY_ROOT?=.dafny/dafny/
DAFNY_CMD=$(DAFNY_ROOT)/Binaries/dafny
DAFNY_BINS=$(wildcard $(DAFNY_ROOT)/Binaries/*)

ifndef TL
	TL=20
endif
ifeq "$(TL)" "0"
  TIMELIMIT=
else
  TIMELIMIT=/timeLimit:$(TL)
endif

CC=g++

##############################################################################
# Automatic targets

all: status exe

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
	$(eval TMPNAME=$(patsubst %.verified,%.verified-tmp,$1))
	$(2) 2&>1 | tee $(TMPNAME); test $${PIPESTATUS[0]} -eq 0
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
	$(eval TMPNAME=$(patsubst %.synchk,%.synchk-tmp,$@))
	( $(TIME) $(DAFNY_CMD) /compile:0 /dafnyVerify:0 $< ) 2>&1 | tee $(TMPNAME)
	mv $(TMPNAME) $@

##############################################################################
# .verchk: Dafny file-local verification
build/%.verchk: %.dfy $(DAFNY_BINS) | $$(@D)/.
	$(eval TMPNAME=$(patsubst %.verchk,%.verchk-tmp,$@))
	( $(TIME) $(DAFNY_CMD) /compile:0 $(TIMELIMIT) $< ) 2>&1 | tee $(TMPNAME)
	mv $(TMPNAME) $@

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
build/%.cpp: %.dfy $(DAFNY_BINS) | $$(@D)/.
#eval trick to assign make var inside rule
	$(eval TMPNAME=$(abspath $(patsubst %.cpp,%-i.cpp,$@)))
# Dafny irritatingly removes the '.i' presuffix.
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPNAME) /compileTarget:cpp $< Framework.h
	mv $(TMPNAME) $@

# Build the main cpp file without building all the partial cpp files.
build/Bundle.cpp: Impl/Bundle.i.dfy build/Impl/Bundle.i.dummydep $(DAFNY_BINS) | $$(@D)/.
#eval trick to assign make var inside rule
	$(eval TMPNAME=$(abspath $(patsubst %.cpp,%-i.cpp,$@)))
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPNAME) /compileTarget:cpp $< Framework.h
	mv $(TMPNAME) $@

##############################################################################
# C++ object files

CPP_DEP_DIR=build/cppdeps
GEN_H_FILES=build/Bundle.i.h

WARNINGS=-Wall -Wsign-compare

build/%.o: build/%.cpp $(GEN_H_FILES) | $$(@D)/.
	@mkdir -p $(CPP_DEP_DIR)/$(basename $<)
	$(CC) -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I framework/ -std=c++14 -msse4.2 -MMD -MP -MF "$(CPP_DEP_DIR)/$(<:.cpp=.d)" $(CCFLAGS) $(WARNINGS)

# _LIBCPP_HAS_NO_THREADS makes shared_ptr faster
# (but also makes stuff not thread-safe)
#OPT_FLAG=-O2 -D_LIBCPP_HAS_NO_THREADS
OPT_FLAG=-O0 -g

build/framework/%.o: framework/%.cpp $(GEN_H_FILES) | $$(@D)/.
	@mkdir -p $(CPP_DEP_DIR)/$(basename $<)
	$(CC) -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I framework/ -I build/ -std=c++14 -msse4.2 -MMD -MP -MF "$(CPP_DEP_DIR)/$(<:.cpp=.d)" $(CCFLAGS) $(OPT_FLAG) $(WARNINGS) -Werror

# the BundleWrapper.cpp file includes the auto-generated Bundle.cpp
build/framework/BundleWrapper.o: framework/BundleWrapper.cpp build/Bundle.cpp $(GEN_H_FILES) | $$(@D)/.
	@mkdir -p $(CPP_DEP_DIR)/$(basename $<)
# No -Werror
	$(CC) -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I framework/ -I build/ -std=c++14 -msse4.2 -MMD -MP -MF "$(CPP_DEP_DIR)/$(<:.cpp=.d)" $(CCFLAGS) $(OPT_FLAG) $(WARNINGS)

# Include the .h depencies for all previously-built .o targets. If one of the .h files
# changes, we'll rebuild the .o
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))
-include $(call rwildcard,$(CPP_DEP_DIR)/,*.d)

VERIBETRFS_O_FILES=build/framework/BundleWrapper.o build/framework/Framework.o build/framework/Crc32.o build/framework/Main.o build/framework/Benchmarks.o

LDFLAGS=-msse4.2

# On linux we need the -lrt (for aio functions),
# but on mac it doesn't exist.
UNAME := $(shell uname)
ifeq ($(UNAME), Darwin)
else
LDFLAGS += -lrt
endif

build/Veribetrfs: $(VERIBETRFS_O_FILES)
	$(CC) -o $@ $(VERIBETRFS_O_FILES) $(LDFLAGS)

##############################################################################
# YCSB

VERIBETRFS_YCSB_O_FILES=build/framework/BundleWrapper.o build/framework/Framework.o build/framework/Crc32.o build/framework/leakfinder.o

libycsbc:
	@$(MAKE) -C ycsb build/libycsbc.a

librocksdb:
	@env ROCKSDB_DISABLE_BZIP=1 ROCKSDB_DISABLE_ZLIB=1 $(MAKE) -C vendor/rocksdb static_lib

.PHONY: libycsbc

#SUPEROPT_FLAG=-O3
SUPEROPT_FLAG=-O0 -g
build/VeribetrfsYcsb: $(VERIBETRFS_YCSB_O_FILES) libycsbc librocksdb ycsb/YcsbMain.cpp
	# NOTE: this uses c++17, which is required by hdrhist
	g++ -o $@ \
			-Lycsb/build -Lvendor/rocksdb \
			-Iycsb/build/include -I$(DAFNY_ROOT)/Binaries/ -I framework/ -I build/ -I vendor/hdrhist/ -I vendor/rocksdb/include/ \
			-std=c++17 $(SUPEROPT_FLAG) $(VERIBETRFS_YCSB_O_FILES) ycsb/YcsbMain.cpp \
			-lycsbc -lrocksdb -lpthread -ldl -Winline $(LDFLAGS)

