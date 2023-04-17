##############################################################################
# System configuration

# You can build anything reachable from these root files.
DAFNY_ROOTS=concurrency/SeagullBundle.i.dfy

DAFNY_ROOT?=.dafny/dafny/
DAFNY_CMD=$(DAFNY_ROOT)/Scripts/dafny
DAFNY_BINS=$(wildcard $(DAFNY_ROOT)/Binaries/*)
DAFNY_FLAGS=
DAFNY_GLOBAL_FLAGS=

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
STDLIB?=-stdlib=libc++

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

all: concurrency-status

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
	$(eval TMPNAME=$(patsubst %,%-tmp,$1))
	$(2) 2>&1 | tee $(TMPNAME); test $${PIPESTATUS[0]} -eq 0
	mv $(TMPNAME) $1
endef

##############################################################################
##############################################################################
# Special top-level targets

##############################################################################
# Verification status page

#.PHONY: status
#status: build/deps build/Impl/Bundle.i.status.pdf
scache-status: build/concurrency/scache/Bundle.i.status.pdf
nr-status: build/concurrency/node-replication/Interface.i.status.pdf
hash-status: build/concurrency/hashtable/Interface.i.status.pdf
hoh-status: build/concurrency/handoverhand/Interface.i.status.pdf
bank-status: build/concurrency/bank-paper/Impl.i.status.pdf

og-status: build/concurrency/og_counter/Impl.i.status.pdf
queue-status: build/concurrency/spsc-queue/QueueImpl.i.status.pdf

concurrency-status: scache-status nr-status hash-status hoh-status bank-status

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
	( $(TIME) $(DAFNY_CMD) $(DAFNY_GLOBAL_FLAGS) $(DAFNY_FLAGS) /compile:0 $(TIMELIMIT) $< ) 2>&1 | tee $(TMPNAME)
	mv $(TMPNAME) $@

### Establish Dafny flag defaults

# this flag means _NO_ non-linear arithmetic
# unfortunately it can only be set on a per-file basis?

NONLINEAR_FLAGS = /noNLarith

# Only use auto-induction when specified, across all files.
# To enable auto-induction, add {:induction true} to your source file.

INDUCTION_FLAGS = /induction:1

OTHER_PROVER_FLAGS =

### Adjust defaults for a couple of files
# (It would be nice if we could do this in the source instead.)

# enable nonlinear arithmetic for some files
# Note: Nonlinear.i.dfy and Math.i.dfy are designed to use nonlinear arith.
# The other files are legacy'ed in, but it's no big deal as long
# as they verify.
build/concurrency/Math/Nonlinear.i.verchk: NONLINEAR_FLAGS=
build/concurrency/spsc-queue/QueueMultiRw.i.verchk: NONLINEAR_FLAGS=
build/lib/Math/Nonlinear.i.verchk: NONLINEAR_FLAGS=
build/lib/Base/mathematics.i.verchk: NONLINEAR_FLAGS=
build/lib/Base/SetBijectivity.i.verchk: NONLINEAR_FLAGS=
build/lib/Marshalling/GenericMarshalling.i.verchk: NONLINEAR_FLAGS=
build/lib/Base/sequences.i.verchk: NONLINEAR_FLAGS=

### Put all the flags together

DAFNY_FLAGS = $(NONLINEAR_FLAGS) $(INDUCTION_FLAGS) $(OTHER_PROVER_FLAGS)

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
	$(AGGREGATE_TOOL) verchk $^ > $@

# Syntax is trivial from synchk file, just a marker.
# (We need the .syntax target to get a recursive dependency computation.)
build/%.syntax: build/%.synchk $(AGGREGATE_TOOL) | $$(@D)/.
	$(AGGREGATE_TOOL) synchk $^ > $@

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
build/%.lc: %.dfy build/%.verchk $(LC_TOOL) $(LC_DEPS)
		$(LC_TOOL) --mode count --input $< --output $@

LC_REPORT_DEPS=tools/line_counter_report_lib.py docs/file-classifications.txt
build/%.lcreport: %.dfy build/%.lc $(LC_TOOL) $(LC_DEPS) $(LC_REPORT_DEPS)
		$(LC_TOOL) --mode report --input $< --output $@
