all: build/main.pdf

build/main.tex: main.md
	- mkdir -p build/
	pandoc -s -N \
		 --bibliography biblio.bib \
         -f markdown -t latex+yaml_metadata_block+raw_tex+tex_math_dollars+citations+backtick_code_blocks --listings -o build/main.tex main.md

build/main.pdf: build/main.tex
	- mkdir -p build/
	cd build; latexmk --pdf main.tex 

clean:
	- rm -R build/
