TEX_FILES := $(shell find . -name "*.tex" -not -path "*/excluded drafts/*")
BIB_FILES := $(shell find . -name "*.bib")

default: main.pdf

%.pdf: %.tex $(TEX_FILES) $(BIB_FILES)
	python3 ./latexrun $< -o $@

outline.pdf: outline.md
	pandoc --template eisvogel outline.md -o outline.pdf

abstract.txt: abstract.tex
	cat $< | \
		pandoc - -f latex -t markdown --wrap=none -o abstract.txt

clean:
	python3 ./latexrun --clean

.PHONY: clean

