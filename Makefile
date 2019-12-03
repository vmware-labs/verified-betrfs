##############################################################################
# System configuration

# You can build anything reachable from these root files.
DAFNY_ROOTS=Impl/Bundle.i.dfy build-tests/test-suite.i.dfy

DAFNY_ROOT?=".dafny/dafny/"
DAFNY_CMD="$(DAFNY_ROOT)/Binaries/dafny"

##############################################################################
# Automatic targets

all: status exe

clean:
	rm -rf build

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
	$(eval CONFIG=$(patsubst %.roslyn.exe,%.roslyn.runtimeconfig.json,$@))	 #eval trick to assign make var inside rule
	tools/roslyn-write-runtimeconfig.sh > $(CONFIG)

build/Veribetrfs.exe: build/Impl/Bundle.i.exe
	cp $< $@

##############################################################################
# C++ executables

.PHONY: allcpp
allcpp: build/Impl/Bundle.i.cpp

.PHONY: allo
allo: build/Impl/Bundle.i.o

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
build/%.synchk: %.dfy | $$(@D)/.
	$(eval TMPNAME=$(patsubst %.synchk,%.synchk-tmp,$@))
	( $(TIME) $(DAFNY_CMD) /compile:0 /dafnyVerify:0 $< ) 2>&1 | tee $(TMPNAME)
	mv $(TMPNAME) $@

##############################################################################
# .verchk: Dafny file-local verification
build/%.verchk: %.dfy | $$(@D)/.
	$(eval TMPNAME=$(patsubst %.verchk,%.verchk-tmp,$@))
	( $(TIME) $(DAFNY_CMD) /compile:0 /timeLimit:20 $< ) 2>&1 | tee $(TMPNAME)
	mv $(TMPNAME) $@

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
# .cs: C-Sharp output from compiling a Dafny file (which includes all deps)
# In principle, building code should depend on .verified! But we want
# to play with perf with not-entirely-verifying trees.
build/%.cs: %.dfy | $$(@D)/.
#eval trick to assign make var inside rule
	# Dafny irritatingly removes the '.i' presuffix, and has a weird behavior where it duplicates prefixes of relative paths. Bizarre.
	$(eval TMPNAME=$(abspath $(patsubst %.s.cs,%-s.cs,$(patsubst %.i.cs,%-i.cs,$@))))
	pwd
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPNAME) $<
	mv $(TMPNAME) $@

##############################################################################
# .cpp: C++ output from compiling a Dafny file (which includes all deps)
build/%.cpp: %.dfy | $$(@D)/.
#eval trick to assign make var inside rule
	$(eval TMPNAME=$(abspath $(patsubst %.cpp,%-i.cpp,$@)))
# Dafny irritatingly removes the '.i' presuffix.
	$(TIME) $(DAFNY_CMD) /compile:0 /noVerify /spillTargetCode:3 /countVerificationErrors:0 /out:$(TMPNAME) /compileTarget:cpp $< MainDiskIOHandler.h
	mv $(TMPNAME) $@

##############################################################################
# C++ object files
build/%.o: build/%.cpp framework/Framework.h | $$(@D)/.
	g++ -c $< -o $@ -I$(DAFNY_ROOT)/Binaries/ -I Impl/ -std=c++14 -include framework/Framework.h
