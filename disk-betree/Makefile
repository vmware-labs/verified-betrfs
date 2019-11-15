TARGET_SRCS=Bundle.i.dfy Main.s.dfy

include ../tools/Makefile.template

FRAMEWORK_SOURCES=Framework.cs Benchmarks.cs Crc32.cs

all: status exe

$(BUILD_DIR)/disk-betree/Bundle.i.exe:$(BUILD_DIR)/disk-betree/Bundle.i.cs $(FRAMEWORK_SOURCES)
	csc $^ /optimize /r:System.Numerics.dll /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /unsafe /out:$@

$(BUILD_DIR)/disk-betree/Bundle.i.roslyn.exe:$(BUILD_DIR)/disk-betree/Bundle.i.cs $(FRAMEWORK_SOURCES)
	$(ROOT)/tools/roslyn-csc.sh $^ /optimize /nowarn:CS0162 /nowarn:CS0164 /unsafe /t:exe /out:$@
	$(eval CONFIG=$(patsubst %.roslyn.exe,%.runtimeconfig.json,$@))	 #eval trick to assign make var inside rule
	./tools/roslyn-write-runtimeconfig.sh > $(CONFIG)

exe: $(BUILD_DIR)/disk-betree/Bundle.i.exe

status: $(BUILD_DIR)/disk-betree/Bundle.i.status.pdf
