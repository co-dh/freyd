# The sheet imports Freyd/note/cheatsheet/style.typ, which lives outside this directory, so the
# compile sets the repository as the Typst root and every import path is root-relative.
ROOT := ..

all: AoP.pdf

AoP.pdf: AoP.typ bdm.typ $(wildcard ch*/body.typ)
	typst compile --root $(ROOT) $<

clean:
	rm -f AoP.pdf

.PHONY: all clean
