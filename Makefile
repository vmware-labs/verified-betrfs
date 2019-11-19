include tools/Makefile.template

all: status exe

FRAMEWORK_SOURCES=$(ROOT)/disk-betree/Framework.cs $(ROOT)/disk-betree/Benchmarks.cs $(ROOT)/disk-betree/Crc32.cs

# Targets in other directories must 'make -C' over there to generate &
# incorporate its dir.deps.
$(BUILD_DIR)/disk-betree/Bundle.i.cs:
	make -C $(ROOT)/disk-betree $@

$(BUILD_DIR)/disk-betree/Bundle.i.exe:$(BUILD_DIR)/disk-betree/Bundle.i.cs $(FRAMEWORK_SOURCES)
	csc $^ /optimize /r:System.Numerics.dll /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /unsafe /out:$@

$(BUILD_DIR)/disk-betree/Bundle.i.roslyn.exe:$(BUILD_DIR)/disk-betree/Bundle.i.cs $(FRAMEWORK_SOURCES)
	$(ROOT)/tools/roslyn-csc.sh $^ /optimize /nowarn:CS0162 /nowarn:CS0164 /unsafe /t:exe /out:$@
	$(eval CONFIG=$(patsubst %.roslyn.exe,%.roslyn.runtimeconfig.json,$@))	 #eval trick to assign make var inside rule
	$(ROOT)/tools/roslyn-write-runtimeconfig.sh > $(CONFIG)

$(BUILD_DIR)/Veribetrfs.exe: $(BUILD_DIR)/disk-betree/Bundle.i.exe
	cp $< $@

exe: $(BUILD_DIR)/Veribetrfs.exe

exe-roslyn: $(BUILD_DIR)/disk-betree/Bundle.i.roslyn.exe

# Targets in other directories must 'make -C' over there to generate &
# incorporate its dir.deps.
$(BUILD_DIR)/disk-betree/Bundle.i.status.pdf:
	make -C $(ROOT)/disk-betree $@

status: $(BUILD_DIR)/disk-betree/Bundle.i.status.pdf

# Targets in other directories must 'make -C' over there to generate &
# incorporate its dir.deps.
$(BUILD_DIR)/disk-betree/Bundle.i.cpp:
	make -C $(ROOT)/disk-betree $@

allcpp: $(BUILD_DIR)/disk-betree/Bundle.i.cpp

.PHONY: exe exe-roslyn

