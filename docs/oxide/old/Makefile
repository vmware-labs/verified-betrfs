# Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
# SPDX-License-Identifier: BSD-2-Clause

all: build/main.pdf

build/main.tex: main.md
	- mkdir -p build/
	pandoc -s -N \
		 --bibliography biblio.bib \
         -f markdown -t latex+yaml_metadata_block+raw_tex+tex_math_dollars+citations -o build/main.tex main.md

build/main.pdf: build/main.tex
	- mkdir -p build/
	cd build; latexmk --pdf main.tex 

clean:
	- rm -R build/
