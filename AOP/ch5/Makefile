# One body, two page shapes.  The sheet imports Freyd/note/cheatsheet/style.typ, which
# lives outside this directory, so every compile sets the repository as the Typst root.
ROOT := ../..

all: Ch5.pdf Ch5-2col.pdf

Ch5.pdf: Ch5.typ body.typ
	typst compile --root $(ROOT) $<

Ch5-2col.pdf: Ch5-2col.typ body.typ
	typst compile --root $(ROOT) $<

clean:
	rm -f Ch5.pdf Ch5-2col.pdf

.PHONY: all clean
