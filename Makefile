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
BOOK  := Freyd.lean $(wildcard AOP/*.lean Freyd/*.lean Freyd/tool/*.lean leet/*.lean rel/*.lean)
# One file standing for all of diag/generated: `diag-regen` deletes and rewrites the pictures
# themselves, so nothing in there can be a prerequisite by name.
STAMP := diag/generated/.drawn
DB    := .lake/build/refactor-index.db
SLICE := diag/circuit-slice.typ

.PHONY: p w cite spell scan scan-strict cover diagram slice circuit books hm-check hm-sigs

# The typst compile is UNCONDITIONAL, and only the redraw behind it is gated.  An edit that lands in
# the same second as the last build is invisible to make's mtime comparison, and `make p` answering
# "nothing to be done" while the PDF still shows the old page is a worse trade than one second of
# typst.  The expensive half — a Lean elaboration per picture — is what `$(STAMP)` protects.
# No `--root`: typst's default root is the input file's own directory, and every import the two
# notes make now lives inside diag/.  The flag was here while allegory-axioms borrowed the zigzag
# box and wires from notation_as_a_tool_of_thought_adjunction.typ at the repository root; §1 carries
# its own copy of those, so nothing reaches above diag/ any more.
# The note is indexed RIGHT AFTER its compile (`book grep -b axioms`, `book pic`), so the index never
# lags the PDF; `embed` stays in `books` — nobody `sim`s the note between two edits of it.
p: $(STAMP) slice circuit cite spell
	for t in $(TYP); do typst compile $$t $${t%.typ}.pdf || exit 1; done
	./scripts/book ingest diag/allegory-axioms.pdf
	./scripts/book pics

# The circuit generator's acceptance render.  `--slice` writes the whole .typ itself — header,
# import, rows — so nothing in it is hand-kept, and the compile is the check that it still parses.
slice:
	./scripts/circuit --slice
	typst compile $(SLICE) $(SLICE:.typ=.pdf)

# The note's own `#cpanel(…)` literals, each rebuilt from its `cert:` and diffed against the text.
# BEFORE the compile and without typst: a pasted circuit the generator no longer draws is drift,
# and `./scripts/circuit --write` splices the rebuilt one over it.
circuit:
	./scripts/circuit --compare diag/allegory-axioms.typ

# The notes' `lean:<decl>@<key>` markers against the statements they cite.  BEFORE the typst compile:
# a note whose display has drifted from its Lean proof should not produce a PDF that looks fine.
cite: $(DB)
	./scripts/cite-check $(TYP)

# Every string a `cert:` states, parsed and written back: `spell(parse(x)) == x`.  BESIDE `cite`
# and before the compile for the same reason — a formula the parser cannot reproduce is a formula
# `scanline` is only guessing at, and a hand-spaced alias is how that drift gets in.  It pays a
# `typst query`, which `scan` refuses to; this one reads the note's STRINGS, not its geometry, and
# the strings are what every other check quotes.
spell:
	./scripts/scanline --spell diag/allegory-axioms.typ

# The displays that carry NO `lean:` marker, each with the statements worth reading against it.
# A PROMPT, not a check: it never passes or fails and nothing depends on it, because what it asks
# for — is this display the same claim as that theorem? — only a person can answer.  `--unmarked`
# for the work left, `--label X` for one display.
cover: $(DB)
	./scripts/cite-cover $(TYP)

# The reference PDFs as text: `./scripts/book find 3.1a IntroString`, `book grep`, `book page`.
# NO prerequisites and no `book-index.db` target: the PDFs are downloads, not build products, so
# mtimes say nothing about them; `ingest` hashes each file and re-reads only what changed (~1 s).
# `embed` is likewise incremental — it vectorises only paragraphs `vec_para` has no row for.
books:
	./scripts/book ingest
	./scripts/book embed

# The scan line over every panel that emits its lists as metadata.  NOT a prerequisite of `p`:
# `typst query` is a second full compile of the note, and `p` already pays for one.  Run it after
# editing a panel's argument lists — that is when the picture can stop saying what the row says.
scan:
	./scripts/scanline diag/allegory-axioms.typ

# The same sweep with crossings fatal.  A SEPARATE TARGET and not a flag on `scan`: the note has
# crossings today, so `scan` must stay green while this one names the work still to do.
scan-strict:
	./scripts/scanline diag/allegory-axioms.typ --strict

# `scan` run backwards: the panel a formula denotes.  The target is the ROUND TRIP — every panel
# whose `cert:` states an `expect` is redrawn from that formula alone and swept again, and the
# composite must come back the same.  A generator that cannot reproduce the note's own pictures is
# a generator no one should paste from.  `./scripts/diagram --show` prints the calls it makes,
# `--compare` puts each beside the note's own, and `--src`/`--tgt` draw one formula by hand.
diagram:
	./scripts/diagram --roundtrip diag/allegory-axioms.typ

# `diagram` run against the BOOK: each fixture in `diag/pairs/` is one of IntroString's own
# formula/picture pairs, and the panel our generator draws for the formula must have the book's port
# graph — boundary order, and every bead's arms and legs.  `--verify-fixtures` is NOT in the target:
# it shells out to pdftocairo to count the page's strokes and dots against the fixture, which is the
# check on the TRANSCRIPTION and only needs running when a fixture is written or edited.
hm-check:
	./scripts/hm-check
	./scripts/hm-check --laws

# The bead signatures `scripts/diagram` draws from, against the Lean declarations they were read
# off.  A SEPARATE target for the same reason `--verify-fixtures` is one: it needs the index.
hm-sigs: $(DB)
	./scripts/hm-check --verify-sigs

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

# The index carries the statement keys the markers are checked against, so it is stale the moment any
# Lean source is.  Re-extraction is per module — one edited file costs seconds, not the full 84.
$(DB): $(BOOK) $(LEAN)
	./scripts/cap lake build
	./scripts/lean-refactor index
