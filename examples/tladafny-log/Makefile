dfys := $(patsubst src/%.dfy,dfy/%.dfy,$(wildcard src/*.dfy))
targets := $(patsubst src/%.dfy,build/%.success,$(wildcard src/*.dfy))

all: $(targets)

build/dfys.built: $(dfys)
	mkdir -p build
	date > build/dfys.built

dfy/%.dfy: src/%.dfy
	mkdir -p dfy
	cp $< $@

build/%.success: dfy/%.dfy build/dfys.built
	mkdir -p build
	(cd dfy; dafny /compile:0 $(<F)) && date > $@

clean:
	- rm -R dfy
	- rm -R build
