dfys := $(wildcard src/*.dfy)
targets := $(patsubst src/%.dfy,build/%.dll,$(wildcard src/*.dfy))

all: build/Log.exe

build/Log.exe: build/okay.okay
	# (cd src; dafny Mkfs.dfy /spillTargetCode:3 /noVerify /out:Mkfs.cs)
	(cd src; dafny Impl.dfy /spillTargetCode:3 /noVerify /out:Impl.cs)
	# csc Mkfs.cs
	(cd src; csc Framework.cs /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168 /out:Log.exe)

build/okay.okay: $(targets)
	touch build/okay.okay

build/%.dll: src/%.dfy
	mkdir -p build
	(cd src; dafny /compile:0 $(<F)) && touch build/$(@F).okay

clean:
	- rm -R build
