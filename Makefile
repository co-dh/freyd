# `make p` — the notes' PDFs, pictures and all.
#
# NOT a lake target.  `lakefile.toml` has no script section, and a lake script would have to shell
# out to `typst` anyway: typst is not a Lean artefact and lake would not know when to rerun it.
# Lake's half of this is `diag-export`, which make calls below.
#
# TWO notes: allegory-axioms states the laws, allegory2 works the proofs.  They share
# diag/note-style.typ, and both are compiled by `make p` — a split whose second half only builds
# when someone remembers to name it is a split that rots.

TYP   := diag/allegory-axioms.typ diag/allegory2.typ
PDF   := $(TYP:.typ=.pdf)
LEAN  := $(wildcard diag/*.lean diag/tool/*.lean)
# One file standing for all of diag/generated: `diag-regen` deletes and rewrites the pictures
# themselves, so nothing in there can be a prerequisite by name.
STAMP := diag/generated/.drawn

.PHONY: p w

# The typst compile is UNCONDITIONAL, and only the redraw behind it is gated.  An edit that lands in
# the same second as the last build is invisible to make's mtime comparison, and `make p` answering
# "nothing to be done" while the PDF still shows the old page is a worse trade than one second of
# typst.  The expensive half — a Lean elaboration per picture — is what `$(STAMP)` protects.
p: $(STAMP)
	for t in $(TYP); do typst compile $$t $${t%.typ}.pdf || exit 1; done

# `make w` — recompile on every save, with the viewer following along.  `typst watch` follows the
# note's imports, so a redrawn picture in diag/generated rebuilds too, and zathura reloads a file
# that changed under it IN PLACE, keeping the page and scroll position.  Chrome does not, which is
# why this is not a browser.  Ctrl-C closes both.
#
# ONE note at a time: `typst watch` takes one input, and watching the pair would need two watchers
# and two viewers.  `make w NOTE=diag/allegory2.typ` for the proofs.
NOTE ?= diag/allegory-axioms.typ
w: p
	@zathura $(NOTE:.typ=.pdf) & \
	  v=$$!; trap "kill $$v 2>/dev/null" EXIT INT TERM; \
	  typst watch $(NOTE) $(NOTE:.typ=.pdf)

# The pictures are exported from the Lean STATEMENTS, so only the Lean makes them stale.  NOT the
# note: `diag-regen` reads its list off the note's imports, but editing prose changes no picture,
# and hanging the redraw on the note put a whole Lean elaboration behind every typo fix.  Add an
# import and the typst compile says which file is missing.
$(STAMP): $(LEAN)
	./scripts/cap lake build diag-export
	./scripts/diag-regen
	@touch $@
