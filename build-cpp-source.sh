#!/bin/bash

### build SplinterCache source

cd concurrency/scache
../../tools/local-dafny.sh /trace /compile:0 /induction:1 /noNLarith /noVerify /spillTargetCode:3 /compileTarget:cpp /countVerificationErrors:0 Application.i.dfy Extern.h LinearExtern.h DiskExtern.h

mkdir -p ../../build/cache-source/
cp Application.i.cpp ../../build/cache-source/
cp Application.i.h ../../build/cache-source/

### build NR source

cd ../node-replication
