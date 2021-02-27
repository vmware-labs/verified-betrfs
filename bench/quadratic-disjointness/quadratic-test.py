#!/usr/bin/python3

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: MIT

import time
import os
import subprocess

def chain(n, fmtStr):
    return "".join([fmtStr % i for i in range(n)])

def name_file(n):
    return "quadratic-%d.dfy" % n

def emit_test(n):
    fp = open(name_file(n), "w")
    nl = "\n"
    fp.write(f"""\
include "quadratic-A.dfy"

class Owner {{
  var x : A;    // the mutating field
  // the non-conflicting fields:
{chain(n, "  var a%d : A;"+nl)}
  ghost var Repr : set<object>;

  predicate Inv()
    reads this, this.Repr
  {{
    && x in Repr
{chain(n, "    && a%d in Repr"+nl)}
    && Repr == {{this}}
      + x.Repr
{chain(n, "      + a%d.Repr"+nl)}
    && {{this}}
      !! x.Repr {chain(n, " !! a%d.Repr")}
    && x.Inv()
{chain(n, "    && a%d.Inv()"+nl)}
  }}

  constructor()
    ensures Inv()
  {{
    x := new A();
{chain(n, "    a%d := new A();"+nl)}
    new;
    Repr := {{this}} + x.Repr{chain(n, " + a%d.Repr")};
  }}

  method MethodUnderTest()
    requires Inv()
    modifies x.Repr
  {{
    a0.establishSomething();
    assert a0.Something();
    assert {{this}} !! x.Repr {chain(n, " !! a%d.Repr")};
    x.changeSomething();
    assert {{this}} !! x.Repr {chain(n, " !! a%d.Repr")};
    assert a0.Something();
  }}
}}
""")
    fp.close()

def run_test(n, datafp):
    emit_test(n)
    start = time.time()
    subprocess.call(["dafny", "/compile:0", name_file(n)])
    end = time.time()
    datafp.write("%d, %s\n" % (n, end-start))
    os.remove(name_file(n))

def main():
    datafp = open("result-data.csv", "w")
    datafp.write("size, time\n")
    for n in range(1,100):
        run_test(n, datafp)
        datafp.flush()
    datafp.close()

main()
