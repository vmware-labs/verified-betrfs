ROOT=./
TARGETS=

include $(ROOT)/tools/Makefile.template

BUNDLE_SOURCE=build/Bundle.cs
$(BUNDLE_SOURCE): $(shell find . -name '*.dfy')
	mkdir -p build
	$(DAFNY_CMD) disk-betree/Bundle.i.dfy /spillTargetCode:3 /noVerify /compile:0 /out:build/Bundle.cs /countVerificationErrors:0

FRAMEWORK_SOURCES=disk-betree/Framework.cs disk-betree/Benchmarks.cs disk-betree/Crc32.cs
build/Veribetrfs.exe: $(FRAMEWORK_SOURCES) $(BUNDLE_SOURCE)
	csc $(BUNDLE_SOURCE) $(FRAMEWORK_SOURCES) /optimize /r:System.Numerics.dll /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /unsafe /out:build/Veribetrfs.exe

build/roslyn-veribetrfs.exe: $(FRAMEWORK_SOURCES) $(BUNDLE_SOURCE)
	./tools/roslyn-csc.sh $(BUNDLE_SOURCE) $(FRAMEWORK_SOURCES) /optimize /nowarn:CS0162 /nowarn:CS0164 /unsafe /t:exe /out:build/roslyn-veribetrfs.exe
	./tools/roslyn-write-runtimeconfig.sh > build/roslyn-veribetrfs.runtimeconfig.json

