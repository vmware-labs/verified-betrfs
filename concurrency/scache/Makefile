all: app

Application.i.cpp: *.dfy cache/*.dfy rwlock/*.dfy ../framework/*.dfy ../../lib/Base/*.dfy
	dafny /trace /compile:0 /induction:1 /noNLarith /noVerify /spillTargetCode:3 /compileTarget:cpp /countVerificationErrors:0 Application.i.dfy Extern.h LinearExtern.h DiskExtern.h

Application.o: Application.i.cpp ../framework/Extern.h ../framework/LinearExtern.h ../framework/DiskExtern.h
	g++ -c -o Application.o Application.i.cpp -I ../../.dafny/dafny/Binaries/ -I ../framework/ -std=c++17 -O2

main.o: main.cpp ../framework/Extern.h ../framework/LinearExtern.h ../framework/DiskExtern.h Application.i.cpp
	g++ -c -o main.o main.cpp -I ../../.dafny/dafny/Binaries/ -I ../framework/ -std=c++17 -O2

app: main.o Application.o
	g++ -o app Application.o main.o
