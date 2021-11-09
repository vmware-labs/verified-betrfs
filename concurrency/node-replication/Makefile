all: app

########################################

# options for `DATA_STRUCTURE` are USE_COUNTER | USE_VSPACE
DATA_STRUCTURE := USE_VSPACE

# options for `DATA_STRUCTURE_NAME` are Counter | VSpace ... 
#
# (a) this should be defined automatically based on DATA_STRUCTURE but 
# the make `ifeq` was behaving strange.
# (b) You might wonder, why we need both variables: we can't just do -DVSpace 
# because that's the name of the C++ struct -- we can't rename the dafny files 
# because that looks ugly
DATA_STRUCTURE_NAME=VSpace

########################################

BUNDLE_DAFNY=Bundle$(DATA_STRUCTURE_NAME).i.dfy
BUNDLE_CPP=Bundle$(DATA_STRUCTURE_NAME).i.cpp
BUNDLE_H=Bundle$(DATA_STRUCTURE_NAME).i.h

CFLAGS := -g -O3 -std=c++17 \
	-I ../../.dafny/dafny/Binaries/ -I ../framework/ -D$(DATA_STRUCTURE)

HEADERS := \
	../framework/Extern.h \
	../framework/LinearExtern.h \
	$(BUNDLE_H) \
	nr.h \
	thread_pin.h \
	vspace_glue.h

LIBS := \
	-lpthread \
	-lnuma \
	-lvspace \
	-ldl # rust needs this :/

$(BUNDLE_CPP) $(BUNDLE_H): *.dfy rwlock/*.dfy ../framework/*.dfy ../../lib/Base/*.dfy vspace_glue.h ./vspace/target/cxxbridge/vspace/src/lib.rs.h
	$(eval TMPNAME=$(abspath $(patsubst %.s.cs,%-s.cs,$(patsubst %.i.cs,%-i.cs,$@))))
	# Dafny currently produces Bundle$(DATA_STRUCTURE_NAME).i.cpp, but it returns an error code
	# since not everything verifies. Augment the next lines so that they don't
	# ignore failures once things are supposed to verify.
	-dafny /trace /compile:0 /induction:1 /noNLarith /noVerify /spillTargetCode:3 /compileTarget:cpp /countVerificationErrors:0 $(BUNDLE_DAFNY) Extern.h LinearExtern.h ./vspace_glue.h /out:$(TMPNAME)
	-mv $(TMPNAME) $@

./vspace/target/release/libvspace.a ./vspace/target/cxxbridge/vspace/src/lib.rs.cc ./vspace/target/cxxbridge/vspace/src/lib.rs.h: ./vspace/src/lib.rs ./vspace/Cargo.toml ./vspace/build.rs
	cd vspace && cargo build --release

Bundle.o: $(BUNDLE_CPP) $(HEADERS)
	g++ $(CFLAGS) -c -o $@ $<

main.o: main.cpp $(HEADERS)
	g++ $(CFLAGS) -c -o $@ $<

vspace_glue.o: ./vspace/target/cxxbridge/vspace/src/lib.rs.cc $(HEADERS)
	g++ $(CFLAGS) -c -o $@ $<

app: main.o Bundle.o vspace_glue.o ./vspace/target/release/libvspace.a
	g++ -g -o app Bundle.o vspace_glue.o main.o -L ./vspace/target/release/ $(LIBS)

.PHONY: clean

clean:
	-rm -f app *.o Bundle*.i.cpp Bundle*.i.h
	-rm -rf ./vspace/target/
