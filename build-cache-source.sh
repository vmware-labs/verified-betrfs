#!/bin/bash

cd concurrency/scache
dafny /trace /compile:0 /induction:1 /noNLarith /noVerify /spillTargetCode:3 /compileTarget:cpp /countVerificationErrors:0 Application.i.dfy Extern.h LinearExtern.h DiskExtern.h
cp Application.i.cpp ../../build/
cp Application.i.h ../../build/
