# `make p` — the note's PDF, pictures and all.
#
# NOT a lake target.  `lakefile.toml` has no script section, and a lake script would have to shell
# out to `typst` anyway: typst is not a Lean artefact and lake would not know when to rerun it.
# Lake's half of this is `diag-export`, which make calls below.

TYP   := diag/allegory-axioms.typ
PDF   := $(TYP:.typ=.pdf)
LEAN  := $(wildcard diag/*.lean diag/tool/*.lean)
# One file standing for all of diag/generated: `diag-regen` deletes and rewrites the pictures
# themselves, so nothing in there can be a prerequisite by name.
STAMP := diag/generated/.drawn

.PHONY: p w

p: $(PDF)

# `make w` — recompile on every save, with the viewer following along.  `typst watch` follows the
# note's imports, so a redrawn picture in diag/generated rebuilds too, and zathura reloads a file
# that changed under it IN PLACE, keeping the page and scroll position.  Chrome does not, which is
# why this is not a browser.  Ctrl-C closes both.
w: $(PDF)
	@zathura $(PDF) & \
	  v=$$!; trap "kill $$v 2>/dev/null" EXIT INT TERM; \
	  typst watch $(TYP) $(PDF)

$(PDF): $(TYP) diag/strdiag.typ $(STAMP)
	typst compile $< $@

# The pictures are exported from the Lean STATEMENTS, so only the Lean makes them stale.  NOT the
# note: `diag-regen` reads its list off the note's imports, but editing prose changes no picture,
# and hanging the redraw on the note put a whole Lean elaboration behind every typo fix.  Add an
# import and the typst compile says which file is missing.
$(STAMP): $(LEAN)
	./scripts/cap lake build diag-export
	./scripts/diag-regen
	@touch $@
