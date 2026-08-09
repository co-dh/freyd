# One source, two contents. The default build is the Rel-focused sheet; `--input full=1` sets
# `full` in style.typ, which is what `fullonly` in the part files tests, so the same sources
# also produce the whole of chapter 1. Only Cheatsheet-full.pdf passes the flag.
SRC := style.typ body.typ part-1.4.typ part-1.5.typ part-1.6.typ part-1.7.typ part-1.8.typ part-1.9.typ

all: Cheatsheet.pdf Cheatsheet-2col.pdf Cheatsheet-full.pdf

Cheatsheet.pdf: Cheatsheet.typ $(SRC)
	typst compile $<

Cheatsheet-2col.pdf: Cheatsheet-2col.typ $(SRC)
	typst compile $<

Cheatsheet-full.pdf: Cheatsheet-full.typ $(SRC)
	typst compile --input full=1 $<

clean:
	rm -f Cheatsheet.pdf Cheatsheet-2col.pdf Cheatsheet-full.pdf

.PHONY: all clean
