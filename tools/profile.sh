#!/bin/bash
dafny /z3opt:smt.qi.profile=true /z3opt:smt.qi.profile_freq=100 /timeLimit:20 "$@"
