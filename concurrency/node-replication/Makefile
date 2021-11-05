all: app

CFLAGS := -g -O0 -std=c++17 \
	-I ../../.dafny/dafny/Binaries/ -I ../framework/

HEADERS := \
	../framework/Extern.h \
	../framework/LinearExtern.h \
	Bundle.i.h \
	nr.h \
	nrconstants.h \
	thread_pin.h

LIBS := \
	-lpthread \
	-lnuma

Bundle.i.cpp Bundle.i.h: *.dfy rwlock/*.dfy ../framework/*.dfy ../../lib/Base/*.dfy
	$(eval TMPNAME=$(abspath $(patsubst %.s.cs,%-s.cs,$(patsubst %.i.cs,%-i.cs,$@))))
	# Dafny currently produces Bundle.i.cpp, but it returns an error code
	# since not everything verifies. Augment the next lines so that they don't
	# ignore failures once things are supposed to verify.
	-dafny /trace /compile:0 /induction:1 /noNLarith /noVerify /spillTargetCode:3 /compileTarget:cpp /countVerificationErrors:0 Bundle.i.dfy Extern.h LinearExtern.h /out:$(TMPNAME)
	-mv $(TMPNAME) $@

Bundle.o: Bundle.i.cpp $(HEADERS)
	g++ $(CFLAGS) -c -o $@ $<

main.o: main.cpp $(HEADERS)
	g++ $(CFLAGS) -c -o $@ $<

app: main.o Bundle.o
	g++ -g -o app Bundle.o main.o $(LIBS)

.PHONY: clean

clean:
	-rm app *.o Bundle.i.cpp Bundle.i.h
