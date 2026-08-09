# One body, two page shapes.  The sheet imports AOP/bdm.typ, which lives outside this
# directory, so every compile sets the repository as the Typst root.
ROOT := ../..

all: Ch6.pdf Ch6-2col.pdf

Ch6.pdf: Ch6.typ body.typ
	typst compile --root $(ROOT) $<

Ch6-2col.pdf: Ch6-2col.typ body.typ
	typst compile --root $(ROOT) $<

clean:
	rm -f Ch6.pdf Ch6-2col.pdf

.PHONY: all clean
