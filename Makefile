#TARGETDLLS=a.dll b.dll
TARGETEXES=tttree.exe

all: $(TARGETDLLS) $(TARGETEXES)

DAFNY=dafny

%.exe: %.dfy
	$(DAFNY) $<

%.dll: %.dfy 
	$(DAFNY) $<


clean:
	rm -f *.dll *.dll.mdb *.exe *.exe.mdb


include $(TARGETDLLS:.dll=.deps) $(TARGETEXES:.exe=.deps)

%.deps: %.dfy
	$(DAFNY) /printIncludes:Transitive $< | grep ";" | grep -v "^roots;" | sed "s/\(^[^;]*\);/\1: /" | sed "s/;/ /g" | sed "s/.dfy/.dll/g" | sed "s,$(PWD)/,,g" > $@
	$(DAFNY) /printIncludes:Transitive $< | grep -v ";" | sed "s,$(PWD)/,,g" | sed "s,^,$@: ," >> $@
