TARGET_SRCS=Bundle.i.dfy Main.s.dfy

include ../tools/Makefile.template

FRAMEWORK_SOURCES=Framework.cs Benchmarks.cs Crc32.cs

$(BUILD_DIR)/disk-betree/Bundle.i.exe:$(BUILD_DIR)/disk-betree/Bundle.i.cs $(FRAMEWORK_SOURCES)
	csc $^ /optimize /r:System.Numerics.dll /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /unsafe /out:$@

$(BUILD_DIR)/disk-betree/Bundle.i.roslyn.exe:$(BUILD_DIR)/disk-betree/Bundle.i.cs $(FRAMEWORK_SOURCES)
	$(ROOT)/tools/roslyn-csc.sh $^ /optimize /nowarn:CS0162 /nowarn:CS0164 /unsafe /t:exe /out:$@
	$(eval CONFIG=$(patsubst %.roslyn.exe,%.roslyn.runtimeconfig.json,$@))	 #eval trick to assign make var inside rule
	$(ROOT)/tools/roslyn-write-runtimeconfig.sh > $(CONFIG)

BUNDLE_SOURCE=$(BUILD_DIR)/Bundle.cs

$(BUNDLE_SOURCE): $(shell find .. -name '*.dfy')
	$(DAFNY_CMD) Bundle.i.dfy /spillTargetCode:3 /noVerify /compile:0 /out:$(BUILD_DIR)/Bundle.cs /countVerificationErrors:0

$(BUILD_DIR)/Veribetrfs.exe: $(FRAMEWORK_SOURCES) $(BUNDLE_SOURCE)
	csc $(BUNDLE_SOURCE) $(FRAMEWORK_SOURCES) /optimize /r:System.Numerics.dll /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /unsafe /out:$(BUILD_DIR)/Veribetrfs.exe

exe: $(BUILD_DIR)/Veribetrfs.exe
exe-roslyn: $(BUILD_DIR)/disk-betree/Bundle.i.roslyn.exe

allcpp: $(BUILD_DIR)/disk-betree/Bundle.i.cpp

.PHONY: exe exe-roslyn
