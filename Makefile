<<<<<<< HEAD
ROOT=./
TARGETS=

include $(ROOT)/tools/Makefile.template
=======
#TARGETDLLS=a.dll b.dll
#TARGETEXES=tttree.exe

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
	$(DAFNY) /printIncludes:Transitive $< | grep ";" | grep -v "^roots;" | sed "s/\(^[^;]*\);/\1: /" | sed "s/;/ /g" | sed "s/.dfy/.dll/g" | sed "s,$(PWD)/,,g" > $@
	$(DAFNY) /printIncludes:Transitive $< | grep -v ";" | sed "s,$(PWD)/,,g" | sed "s,^,$@: ," >> $@
	$(call record_build, $@)

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

build/Bundle.cs: $(shell find . -name '*.dfy')
	mkdir -p build
	dafny disk-betree/Bundle.dfy /spillTargetCode:3 /noVerify /compile:0 /out:build/Bundle.cs /countVerificationErrors:0

build/Veribetrfs.exe: disk-betree/Framework.cs build/Bundle.cs
	csc build/Bundle.cs disk-betree/Framework.cs /r:System.Numerics.dll /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /out:build/Veribetrfs.exe
<<<<<<< HEAD
>>>>>>> Makefile rule for Veribetrfs.exe
=======
>>>>>>> 651111facaaeaf3d4669528afd32ea4fdb268042
