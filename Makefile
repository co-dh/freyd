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

# ONE CHAPTER, ONE VARIABLE: `make c CH=13`, `make cite CH=13`, `make panels CH=13` compile,
# query and scan chapter 13's file and nothing else — the whole note costs about 24 GiB and 35s of
# layout and every gate paid it.  `CH` is EXPORTED, so `./scripts/cd-check` and every python gate
# resolve the same chapter from the environment and need no flag of their own;
# `scripts/notesplit.py`'s `note_root` is the one resolution behind all of them.
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

# A LAYOUT IS THE MEMORY: one chapter peaks at 7 GiB and the whole note at 24, on a machine with 30.
# Chapters share the lock and the whole note takes it alone, so three agents' chapter gates run side
# by side and none of them meets a whole-note compile.  HERE and not in the caller: a second `flock`
# wrapped around `make` holds the file on another descriptor and the two wait on each other forever.
LOCK := flock $(if $(strip $(CH)),-s,-x) $(HOME)/.cache/freyd-note.lock

.PHONY: p c w labels cite panels cd-check cover books v exe

# ONE link of the exe before the gates fan out.  Under `-j` the stamp, `panels` and `$(DB)` each ran
# their own `lake build`, and two of them linking `diag-export` at once left one reading the binary
# the other was replacing: "no such file or directory: .lake/build/bin/diag-export".  Order-only
# (`| exe`) so the exe's timestamp never makes the others rebuild.
exe:
	./scripts/cap lake build diag-export diag.StrDiagNames

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
# `.WAIT`: the stamp's redraw DELETES and rewrites every picture, and under `-j` `cd-check` compiled the
# note while that was half done — an old-format panel beside a new `cdpanel.typ` — and `panels` redrew
# a file the full redraw had just deleted.  Everything right of the stamp waits for it.
p: $(STAMP) .WAIT panels cite cd-check
	@test -z "$(strip $(CH))" || { echo "make p is the whole book, both notes and the book index:" \
	  " one chapter is 'make ch N=$(CH)' for its pdf and 'make c CH=$(CH)' for its gates"; exit 1; }
# The WHOLE repository: every other gate builds only what `diag-export` imports, so a module
# nothing draws from can be broken with all of them green.
	./scripts/cap lake build
	for t in $(TYP); do $(LOCK) typst compile $$t $${t%.typ}.pdf || exit 1; done
	./scripts/labelfit
	./scripts/inkfit
	./scripts/dispfit
	./scripts/book ingest diag/allegory-axioms.pdf
	./scripts/book pics

# No two labels inside one panel may touch, and ink stays inside its frame, measured off the
# COMPILED page.  It needs the PDF, so unlike its neighbours it pays a typst compile when the note
# is newer; `p` calls it straight after its own compile instead, and pays nothing extra.
# Both read `CH` themselves, so they measure the CHAPTER's pages when one is named: the page
# numbers they report are then the chapter pdf's, which is the file the author has open.
labels: $(NOTEPDF)
	./scripts/labelfit
	./scripts/inkfit
	./scripts/dispfit

# `--root .`: a chapter sits one directory below the prelude it imports, and the note's own imports
# resolve the same either way.
# `| panels`: a name just written into the note has no file until `panels` draws it, and under a
# parallel make the compile started first and failed on the missing include.
# UNCONDITIONAL, as `p`'s compile is: `panels` rewrites files under diag/generated that no rule can
# name, so an mtime test left a chapter pdf showing the old pictures after an exporter change.
$(NOTEPDF): FORCE | panels
	$(LOCK) typst compile --root . $(NOTESRC) $@
FORCE:

# The notes' `lean:<decl>@<key>` markers against the statements they cite.  BEFORE the typst compile:
# a note whose display has drifted from its Lean proof should not produce a PDF that looks fine.
cite: $(DB)
	./scripts/cite-check $(CITESRC)

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

# Every picture the notes draw and have no file for — a `#lean(...)` selector, or an `#import` — drawn
# from LEAN.  The NOTE is the list of obligations, so adding a picture is writing its name in the note
# and nothing else; a name already drawn is left alone unless its statement, a theorem it cites or
# the exporter changed since (`diag-export --stale`), which is what keeps this in the edit loop.
panels: | exe
	./scripts/diag-regen --missing

# Every commutative panel of `diag/cd-panels.txt`, redrawn from LEAN and held to the drawing in the
# note it answers.  The PANELS are the obligations, and so are the note's reference drawings: one
# that no panel names fails here rather than sitting unchecked.
# `panels`, NOT `$(STAMP)`: the gate exports its own commutative panels and only COMPILES the note, so
# it needs every import to exist and none to be fresh — the stamp redrew all 500 pictures of every
# route, five minutes under the note lock, in front of a check that takes thirteen seconds.
cd-check: panels
	./scripts/cd-check

# The sub-second edit loop: everything `make p` checks, with neither typst compile nor `book pics`.
# Those two are 26s of layout for the PDF itself; nothing here needs a rendered page.
c: panels labels cite cd-check

# One section rendered to a fixed path, for the edit-and-look loop; the whole note is `make p`.
# No viewer is launched: the author keeps diag/.view.pdf open and it reloads itself.
v:
	./scripts/note-view $(NOTESRC) $(SEC)

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
	$(LOCK) typst compile --root . $(NOTESRC) $(NOTEPDF)

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
$(STAMP): $(LEAN) $(BOOK) | exe
	./scripts/diag-regen
	@touch $@

# The index carries the statement keys the markers are checked against, so it is stale the moment any
# Lean source is.  Re-extraction is per module — one edited file costs seconds, not the full 84.
# UNCONDITIONAL: `scripts/diag-export` re-indexes after building only the exe's imports, so the db's
# mtime says nothing about a module nothing draws from; lake and the index each skip what is current.
$(DB): FORCE | exe
	./scripts/cap lake build
	./scripts/lean-refactor index
