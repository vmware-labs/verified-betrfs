#!/usr/bin/env python3

with open(".vericache", "w") as f:
  t = "0" * 4096
  for i in range(1000000):
    f.write(t)
