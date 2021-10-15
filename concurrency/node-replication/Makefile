all: app

Bundle.i.cpp: *.dfy rwlock/*.dfy ../framework/*.dfy ../../lib/Base/*.dfy
	$(eval TMPNAME=$(abspath $(patsubst %.s.cs,%-s.cs,$(patsubst %.i.cs,%-i.cs,$@))))
	dafny /trace /compile:0 /induction:1 /noNLarith /noVerify /spillTargetCode:3 /compileTarget:cpp /countVerificationErrors:0 Bundle.i.dfy Extern.h LinearExtern.h /out:$(TMPNAME)
	mv $(TMPNAME) $@

Bundle.o: Bundle.i.cpp ../framework/Extern.h ../framework/LinearExtern.h
	g++ -c -o Bundle.o Bundle.i.cpp -I ../../.dafny/dafny/Binaries/ -I ../framework/ -std=c++17 -O2

main.o: main.cpp ../framework/Extern.h ../framework/LinearExtern.h Bundle.i.cpp
	g++ -c -o main.o main.cpp -I ../../.dafny/dafny/Binaries/ -I ../framework/ -std=c++17 -O2

app: main.o Bundle.o
	g++ -o app Bundle.o main.o -lpthread
