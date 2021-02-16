#!/bin/bash
dafny /proverOpt:O:smt.qi.profile=true /proverOpt:O:smt.qi.profile_freq=100 /timeLimit:20 "$@"
