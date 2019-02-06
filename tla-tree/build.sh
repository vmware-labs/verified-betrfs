#!/bin/bash
dafny KVTypes.dfy
dafny Disk.dfy
dafny CrashableMap.dfy
dafny CrashSafeLog.dfy
dafny CrashSafeLogInv.dfy
dafny CrashSafeLogRefinement.dfy
