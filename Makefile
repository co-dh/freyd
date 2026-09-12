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
STRSEL := .lake/build/string-selectors
STRREC := .lake/build/string-records.jsonl
DB    := .lake/build/refactor-index.db
SLICE := diag/circuit-slice.typ

# ONE CHAPTER, ONE VARIABLE: `make c CH=13`, `make cite CH=13`, `make scan-generated CH=13` compile,
# query and scan chapter 13's file and nothing else — the whole note costs about 13 GiB and 40s of
# layout and every gate paid it.  `CH` is EXPORTED, so `./scripts/string-check`, `cd-check`,
# `circuit-check` and every python gate resolve the same chapter from the environment and need no
# flag of their own; `scripts/notesplit.py`'s `note_root` is the one resolution behind all of them.
# `make ch N=13` is the same variable under the name that target has always taken.
# A chapter that does not exist STOPS make here, naming it: a gate that fell back to the whole book
# would check something else and exit 0.
CH ?= $(N)
export CH
ifeq ($(strip $(CH)),)
NOTESRC := diag/allegory-axioms.typ
CITESRC := $(TYP)
else
# The resolver's own message goes to make's stderr, naming the chapters there are; it prints no path
# when it fails, and one file when it succeeds, so anything else stops make here.
NOTESRC := $(shell ./scripts/note-files --ch $(CH))
CITESRC := $(NOTESRC)
ifneq ($(words $(NOTESRC)),1)
$(error CH=$(CH): ./scripts/note-files --ch $(CH) named no chapter file — its message is above)
endif
endif
NOTEPDF := $(NOTESRC:.typ=.pdf)

.PHONY: p c w labels cite spell scan scan-full scan-strict scan-generated types cd-check circuit-check string-check cover diagram slice circuit books hm-check hm-sigs v

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
p: $(STAMP) slice circuit pairs cite spell scan-strict scan-generated hm-sigs
	@test -z "$(strip $(CH))" || { echo "make p is the whole book, both notes and the book index:" \
	  " one chapter is 'make ch N=$(CH)' for its pdf and 'make c CH=$(CH)' for its gates"; exit 1; }
	for t in $(TYP); do typst compile $$t $${t%.typ}.pdf || exit 1; done
	./scripts/labelfit
	./scripts/inkfit
	./scripts/framefit
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
	./scripts/circuit --compare $(NOTESRC)

# Two panels either side of a step sign are one statement: unequal boxes read as different arrows,
# and a bead they share must sit at the same height or the picture claims it moved.  BEFORE the
# compile, next to `circuit`, so a misaligned pair never produces a PDF that looks fine.
pairs:
	./scripts/diagram --pairs $(NOTESRC)

# No two labels inside one panel may touch, measured off the COMPILED page — the check that makes
# `scripts/diagram`'s vertical unit a measured number instead of a guess, and keeps it one.  It
# needs the PDF, so unlike its neighbours it pays a typst compile when the note is newer; `p` calls
# it straight after its own compile instead, and pays nothing extra.
# The three read `CH` themselves, so they measure the CHAPTER's pages when one is named: the page
# numbers they report are then the chapter pdf's, which is the file the author has open.
labels: $(NOTEPDF)
	./scripts/labelfit
	./scripts/inkfit
	./scripts/framefit

# `--root .`: a chapter sits one directory below the prelude it imports, and the note's own imports
# resolve the same either way.
$(NOTEPDF): $(NOTESRC) $(wildcard diag/*.typ)
	typst compile --root . $(NOTESRC) $@

# The notes' `lean:<decl>@<key>` markers against the statements they cite.  BEFORE the typst compile:
# a note whose display has drifted from its Lean proof should not produce a PDF that looks fine.
cite: $(DB)
	./scripts/cite-check $(CITESRC)

# Every string a `cert:` states, parsed and written back: `spell(parse(x)) == x`.  BESIDE `cite`
# and before the compile for the same reason — a formula the parser cannot reproduce is a formula
# `scanline` is only guessing at, and a hand-spaced alias is how that drift gets in.  It pays a
# `typst query`, which `scan` refuses to; this one reads the note's STRINGS, not its geometry, and
# the strings are what every other check quotes.
spell:
	./scripts/scanline --spell $(NOTESRC)

# The displays that carry NO `lean:` marker, each with the statements worth reading against it.
# A PROMPT, not a check: it never passes or fails and nothing depends on it, because what it asks
# for — is this display the same claim as that theorem? — only a person can answer.  `--unmarked`
# for the work left, `--label X` for one display.
cover: $(DB)
	./scripts/cite-cover $(CITESRC)

# The reference PDFs as text: `./scripts/book find 3.1a IntroString`, `book grep`, `book page`.
# NO prerequisites and no `book-index.db` target: the PDFs are downloads, not build products, so
# mtimes say nothing about them; `ingest` hashes each file and re-reads only what changed (~1 s).
# `embed` is likewise incremental — it vectorises only paragraphs `vec_para` has no row for.
books:
	./scripts/book ingest
	./scripts/book embed

# The scan line over every panel that emits its lists as metadata.  Cached on a hash of every
# `dpanel`/`cpanel`/`tpan` call: unchanged since the last clean pass skips the `typst query`
# that dominates its cost; `scan-full` bypasses the cache.
scan:
	./scripts/scanline $(NOTESRC)

scan-full:
	./scripts/scanline $(NOTESRC) --full

# The same sweep with crossings fatal, and the one `p` runs.  A wire is a functor and horizontal
# composition has no swap, so a crossing claims a symmetry that is not there and there is no
# acceptable one.  `--strict` never reads the literal cache, so `p` pays one `typst query` a build.
scan-strict:
	./scripts/scanline $(NOTESRC) --strict

# Every picture `diag/string-panels.txt` names, drawn from LEAN and swept against it.  The
# manifest's SELECTORS are the obligations, never the files on disk: diag/generated is gitignored,
# so a fresh clone had nothing to sweep and this passed, and deleting a picture dropped an
# obligation instead of failing.  `string-check --selectors` is the manifest's ONE reader, so the
# two gates cannot come to disagree about what it names.  Each panel's `cert: lean:` is its
# certificate: `scanline` asks `diag-export --string --sigs` for its bead types at check time, so a
# picture the declaration no longer draws fails here.  `diag-export --records` draws every panel AND
# prints its bead types in one run, so `scanline --records` reads them back instead of starting the
# exporter a second time — one Lean process for the whole target, the way `string-check` already does.
scan-generated: $(STAMP)
	./scripts/string-check --selectors > $(STRSEL)
	@test -s $(STRSEL) || { echo "$(STRSEL): diag/string-panels.txt names no selector to draw"; exit 1; }
	tr '\n' '\0' < $(STRSEL) | xargs -0 ./scripts/diag-export --string --records > $(STRREC)
	./scripts/scanline --strict --records $(STRREC)

# Every commutative panel of `diag/cd-panels.txt`, redrawn from LEAN and held to the drawing in the
# note it answers.  The PANELS are the obligations, and so are the note's reference drawings: one
# that no panel names fails here rather than sitting unchecked.
cd-check: $(STAMP)
	./scripts/cd-check

# Every CIRCUIT panel the note draws, redrawn from LEAN and held to the note's own picture.  The
# note's panels are the obligations — read back from its `cpanel` metadata, not from its text — and
# `diag/circuit-panels.txt` must answer one for one.
circuit-check: $(STAMP)
	./scripts/circuit-check

# Every string panel of `diag/string-panels.txt` — that is, every Hinze–Marsden panel the note draws
# — redrawn from LEAN and held to the note's own panel by SVG.  The DISPLAYS are the obligations:
# one the file does not name fails here rather than going unchecked.
string-check: $(STAMP)
	./scripts/string-check

# Every type cell `diag-export --type` has written, rewritten from LEAN.  The FILES are the
# obligations and each one's basename IS the declaration it renders, so a cell whose declaration
# changed type is regenerated here rather than staying at what it said when it was first written.
# One exe run for all of them: the environment is imported once per process.
# No name reaches the shell through make's own splice: `Freyd.Alg.Λ_eps_eq'` carries a prime and a
# guillemet name carries whatever it likes, so `find`/`xargs -0` hands them over byte for byte.
types: $(STAMP)
	@n=$$(find diag/generated/type -maxdepth 1 -name '*.typ' 2>/dev/null | wc -l); \
	  test "$$n" -gt 0 || \
	  { echo "no diag/generated/type/*.typ — write one with ./scripts/diag-export --type"; exit 1; }
	find diag/generated/type -maxdepth 1 -name '*.typ' -print0 | xargs -0 basename -a -s .typ \
	  | tr '\n' '\0' | xargs -0 ./scripts/diag-export --type

# The sub-second edit loop: everything `make p` checks, with neither typst compile nor `book pics`.
# Those two are 26s of layout for the PDF itself; nothing here needs a rendered page.
c: circuit pairs labels cite spell scan-strict hm-sigs

# One section rendered to a fixed path, for the edit-and-look loop; the whole note is `make p`.
# No viewer is launched: the author keeps diag/.view.pdf open and it reloads itself.
v:
	./scripts/scanline $(NOTESRC) --view $(SEC)

# `scan` run backwards: the panel a formula denotes.  The target is the ROUND TRIP — every panel
# whose `cert:` states an `expect` is redrawn from that formula alone and swept again, and the
# composite must come back the same.  A generator that cannot reproduce the note's own pictures is
# a generator no one should paste from.  `./scripts/diagram --show` prints the calls it makes,
# `--compare` puts each beside the note's own, and `--src`/`--tgt` draw one formula by hand.
diagram:
	./scripts/diagram --roundtrip $(NOTESRC)

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

# ONE CHAPTER'S PDF: `make ch N=13`.  N is the chapter's position among the level-1 headings, which
# is the number its displays already carry (`13.4.3c` is in chapter 13); `CH ?= $(N)` at the top of
# this file makes it the same variable every gate takes, and `./scripts/note-files --ch` the one
# thing that turns it into a file, so a renamed heading needs no edit here.
ch:
	@test -n "$(strip $(CH))" || { echo "make ch N=13 — the chapter's number among the level-1 headings"; exit 1; }
	typst compile --root . $(NOTESRC) $(NOTEPDF)

w: p
	@zathura $(NOTE:.typ=.pdf) & \
	  v=$$!; trap "kill $$v 2>/dev/null" EXIT INT TERM; \
	  typst watch $(NOTE) $(NOTE:.typ=.pdf)

# The pictures are exported from the Lean STATEMENTS, so only the Lean makes them stale.  NOT the
# note: `diag-regen` reads its list off the note's imports, but editing prose changes no picture,
# and hanging the redraw on the note put a whole Lean elaboration behind every typo fix.  Add an
# import and the typst compile says which file is missing.
# `$(BOOK)` too, and not `$(LEAN)` alone: the statements drawn are the library's — AOP, Freyd, rel
# — so an edit to the declaration a picture is exported FROM left the picture at what it said.
$(STAMP): $(LEAN) $(BOOK)
	./scripts/cap lake build diag-export
	./scripts/diag-regen
	@touch $@

# The index carries the statement keys the markers are checked against, so it is stale the moment any
# Lean source is.  Re-extraction is per module — one edited file costs seconds, not the full 84.
$(DB): $(BOOK) $(LEAN)
	./scripts/cap lake build
	./scripts/lean-refactor index
