# One body, two page shapes.  The sheet imports AOP/bdm.typ, which lives outside this
# directory, so every compile sets the repository as the Typst root.
ROOT := ../..

all: Ch7.pdf Ch7-2col.pdf

Ch7.pdf: Ch7.typ body.typ
	typst compile --root $(ROOT) $<

Ch7-2col.pdf: Ch7-2col.typ body.typ
	typst compile --root $(ROOT) $<

clean:
	rm -f Ch7.pdf Ch7-2col.pdf

.PHONY: all clean
