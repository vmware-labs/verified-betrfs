#!/bin/bash

# Copyright 2018-2021 VMware, Inc.
# SPDX-License-Identifier: BSD-2-Clause


dafny Mkfs.dfy /spillTargetCode:3 /noVerify
csc Mkfs.cs Framework.cs /r:System.Numerics.dll /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168
