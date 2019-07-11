ROOT=./
TARGETS=

include $(ROOT)/tools/Makefile.template

build/Bundle.cs: $(shell find . -name '*.dfy')
	mkdir -p build
	dafny disk-betree/Bundle.dfy /spillTargetCode:3 /noVerify /compile:0 /out:build/Bundle.cs /countVerificationErrors:0

build/Veribetrfs.exe: disk-betree/Framework.cs build/Bundle.cs
	csc build/Bundle.cs disk-betree/Framework.cs /r:System.Numerics.dll /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /out:build/Veribetrfs.exe
