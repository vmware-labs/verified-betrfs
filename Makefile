ROOT=./
TARGETS=

include $(ROOT)/tools/Makefile.template

BUNDLE_SOURCE=build/Bundle.cs
$(BUNDLE_SOURCE): $(shell find . -name '*.dfy')
	mkdir -p build
	$(DAFNY_CMD) disk-betree/Bundle.i.dfy /spillTargetCode:3 /noVerify /compile:0 /out:build/Bundle.cs /countVerificationErrors:0

FRAMEWORK_SOURCES=disk-betree/Framework.cs disk-betree/Benchmarks.cs disk-betree/Crc32.cs
build/Veribetrfs.exe: $(FRAMEWORK_SOURCES) $(BUNDLE_SOURCE)
	csc $(BUNDLE_SOURCE) $(FRAMEWORK_SOURCES) /r:System.Numerics.dll /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /out:build/Veribetrfs.exe
