#TARGETDLLS=tttree.dll
TARGETEXES=tttree.exe

all: $(TARGETDLLS) $(TARGETEXES)

DAFNY=dafny

%.dll: %.dfy
	$(DAFNY) $<


clean:
	rm -f *.dll *.exe


# This is a bit of a hack to automatically compute dependencies

include $(TARGETDLLS:.dll=.deps)

%.deps: %.dfy
	$(DAFNY) /printIncludes:Transitive $< | grep ";" | grep -v "^roots;" | sed "s/\(^[^;]*\);/\1: /" | sed "s/;/ /g" | sed "s/.dfy/.dll/g" | sed "s,$(PWD)/,,g" > $@

