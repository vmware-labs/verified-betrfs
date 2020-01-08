from __future__ import print_function

with open("build/Bundle.cpp") as f:
  count = 0
  for line in f:
    if line == "namespace Options_Compile  {\n":
      count += 1
    if count == 2:
      print(line, end="")
    if line == "}// end of namespace Options_Compile  datatype declarations\n":
      break 

with open("build/Bundle.cpp") as f:
  count = 0
  for line in f:
    if line == "namespace UI_Compile  {\n":
      count += 1
    if count == 2:
      print(line, end="")
    if line == "}// end of namespace UI_Compile  datatype declarations\n":
      break 
