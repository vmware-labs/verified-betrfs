all: build/main.pdf

build/main.tex: main.md
	- mkdir -p build/
	pandoc -s --natbib -N \
         -f markdown -t latex+yaml_metadata_block+raw_tex+tex_math_dollars+citations -o build/main.tex main.md

build/main.pdf: build/main.tex
	- mkdir -p build/
	cd build; latexmk --pdf main.tex 

clean:
	- rm -R build/
