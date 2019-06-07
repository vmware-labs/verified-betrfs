TARGETDLLS=
TARGETEXES=BtreeBenchmark.exe

all: $(TARGETDLLS) $(TARGETEXES)

DAFNY=dafny

#####################################
######## Automatic cleanups #########
#####################################

# Set this if you want make to remember what it builds so "make clean"
# will work auto-magically.  You SHOULD NOT add this directory to
# your version control system.
BUILDINFO_DIR?=.build_info
MD5SUM_PATH?=$(shell which md5sum md5 | head -1)

ifdef BUILDINFO_DIR
$(shell if [ ! -d $(BUILDINFO_DIR) ]; then mkdir $(BUILDINFO_DIR); fi)
record_build=$(shell echo $(1) > $(BUILDINFO_DIR)/`echo $(1) | $(MD5SUM_PATH) | cut -f1 -d" "`)
buildinfo_files=$(wildcard $(BUILDINFO_DIR)/*)
else
record_build=$(shell exit 0)
endif

clean:
ifdef BUILDINFO_DIR
	for i in $(buildinfo_files); do rm `cat $$i`; done
	rm -rf $(BUILDINFO_DIR)
endif

###############################################
######## Automatic dafny dependencies #########
###############################################

include $(TARGETDLLS:.dll=.deps) $(TARGETEXES:.exe=.deps)

%.deps: %.dfy
	@echo Generating dependencies for $<
	@$(DAFNY) /printIncludes:Transitive $< > ${@:.deps=.includes} || ($(DAFNY) $<; exit 1) # If dafny fails, then run it again to show error to user, and then force failure.
	$(call record_build, ${@:.deps=.includes})
	@if (grep " " ${@:.deps=.includes}); then $(DAFNY) $<; exit 1; else exit 0; fi # If there are any spaces in the dafny output, show the user dafny's output and abort
	@cat ${@:.deps=.includes} | grep ";" | grep -v "^roots;" | sed "s/\(^[^;]*\).dfy;/\1.dll \1.exe: /" | sed "s/\.dfy;*/.dll /g" | sed "s,$(PWD)/,,g" > $@
	$(call record_build, $@)
	@cat ${@:.deps=.includes} | grep -v ";" | sed "s,$(PWD)/,,g" | sed "s,^,$@: ," >> $@

############################################
######## Generic dafny build rules #########
############################################

%.exe: %.dfy
	$(DAFNY) $<
	$(call record_build, $@)
	$(call record_build, $@.mdb)

%.dll: %.dfy 
	$(DAFNY) $<
	$(call record_build, $@)
	$(call record_build, $@.mdb)

