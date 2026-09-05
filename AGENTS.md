This project explain the book Categories, Allegories of Freyd.

## Directory layout (reorg 2026-07-10) — four Lean lib roots, siblings at repo root
- `Freyd/`  — the Freyd book core: `Sa_bc.lean` book sections + support (`Locale`, `WellOrdering`,
  `RelCat`, `MapCat`, `Slice*`, `Capitalization*`, `Exacts`, …). Modules `Freyd.*`.
- `AOP/`    — the Bird & de Moor Algebra-of-Programming layer: chapter files `A<ch>_*.lean`
  (`A4_*`..`A10_*`) + infra (`A6_GenFold`, `A6_GenHylo`, `A6_ConsList`, `A6_HashMap`, `A6_Heap`,
  `A6_BinSearch`, `A6_1_RelSet`, …) + `Deriv*`. Modules `AOP.*`.
- `leet/`   — LeetCode case studies `L<n>.lean` and derivations `L<n>_derived.lean`. Modules `leet.*`.
- `rel/`    — the relation-algebra interpreter `RelInterp` + case studies (`UnixPipe`, `ShellCommands`)
  + the auto-derivation drivers (`AutoDerive*`). Modules `rel.*`.
- `Freyd/note/` — the author's own `.typ`/`.pdf` section notes and diagrams (non-Lean).
Imports cross libs freely within the one Lake package (e.g. `leet.L20` imports `AOP.A6_GenFold`).
lakefile: `AOP`/`leet`/`rel` are glob'd (all their files are in the default build); `Freyd` keeps the
curated `Freyd.lean` aggregator (no glob — do not force-build the deliberately un-imported orphan core).

You should should any 3+ digits sections of the book into `Freyd/Sa_bc.lean`. e.g. section 1.123 in Freyd/S1_12.lean.
The code should follow the book's terminology, wording, convension.
Write composition in diagram order, by juxtaposition: `xy` means first x then y (the book's convention).
Juxtaposition is composition and nothing else, so APPLYING an operator takes parentheses: `E(R)`,
`P(f)`, `Λ(R)`, `F(𝟙)`, `F(outl)`, `T(R)`, `tri(f)` — never B&dM's `ER`/`Pf`. The one bare form is a
single object name (`P A`, `T A`, `F A`), which no reader can take for a composite; anything longer
is parenthesised (`F(P B)`, never `F P B`). Pointwise evaluation is NOT outside this: a map applied
to a point takes parentheses too — `f(a)`, `tip(f(a))`, `min(xs)`, `takewhile(p)(x)`, never `f a`. The
one form that keeps its own brackets is an argument already delimited by them, written with no space:
`E[A]`, `tri(f)[a₀,…,aₙ]`, `min{x+y∣x∈xs}`.
Use the global book notation `𝟙 A` for the categorical identity `Cat.id A`; do not spell identities
as `Cat.id A` in new code.
**When a converse has a name of its own, write the name, not the `°`.** `≥`, never `≤°`; `∈`, never
`∋°`; `⊒`, never a conversed `⊑`. The `°` is one level of indirection the reader has to undo, and
`est(≥)` says which end is meant where `est(≤°)` makes him work it out. This binds Lean and the note
alike. `R°` for an abstract `R` stays — there is no other name for it — and so does the one line that
defines the named form (`∈ ≜ ∋°`).
Use the shortest unambiguous book name in signatures and prose. Once its namespace is deliberately
opened, write `SmallRegCat`, for example, rather than `Freyd.S2_154.SmallRegCat`; keep full
qualification only where ambiguity or declaration syntax requires it.
A repeated qualifier is noise: `open` the namespace at the top of the file instead of writing the
prefix at every use (`open SymMonCat`, not 226 × `SymMonCat.`), and prefer `open N` over
`open scoped N` — it activates the scoped notations too. Two places still need the prefix: the class
name itself (`extends SymMonCat.{v} 𝒞`), and uses inside a `structure`/`class` body, where a bare
inherited field name resolves to a local of the structure elaborator instead of the global constant
(that is also why go-to-definition is dead on those).
Always prefer the book's definition over ad-hoc simplifications — even if the
book version requires more typeclasses (e.g., `Entire R := 1_A ≤ R°R` via
`compose` rather than `∃ h, h ≫ R.colA = id_A`).
If a proof used theorem from other section but not defined yet, prove them in $a_bc.lean.
Make the prove constructive: do not use atom of choice unless unavoidable.
feel free to copy ideas from Mathlib, but do not bring in them as dependency.
  STRICTLY MATHLIB-FREE, NO EXCEPTIONS. The repo has ZERO external dependencies:
  `lake-manifest.json` lists no packages and no `Freyd/*.lean` imports anything outside
  Lean 4 core (`Init`) and `Freyd.*`. The §1.543 transfinite-recursion work that once
  earmarked mathlib's ordinals was hand-built instead (`Freyd/WellOrdering.lean`, Zermelo
  from `Classical.choice`); order/lattice/Frame machinery is hand-rolled too (`Locale.lean`,
  `S1_72`). Never add a `require` and never `import Mathlib`/`Batteries`/`Aesop`/`Std` — keep
  the repo self-contained so builds stay fast and clones stay tiny.
DRY as much as possible.
For stronger/weaker near-clone theorems, prefer one canonical stronger proof in the earliest legal
book module and define the weaker theorem by projection or specialization. Move genuinely shared
prerequisites to that legal home instead of keeping parallel case splits; judge the refactor by net
duplication/line reduction, not merely by replacing a few conclusions inside both proofs.

For Lean source refactors, use the `lean-refactor` tool through `scripts/lean-refactor` instead of
making mechanical edits by hand. The tool has its own repository — `git@github.com:co-dh/lean-refactor.git`,
checked out as a sibling of this one — because nothing in it is book-specific; `scripts/lean-refactor`
runs it against this repository. If the tool cannot safely express the required refactor, improve it
there first, verify it with `./scripts/cap lake build` in that checkout, and then use the new operation.
Refactor operations must preview by default and restore the original source when elaboration or the
capped repository build fails.

Before starting a large change, commit all current work as a checkpoint unless the user explicitly
asks not to commit it.

Before every `git add`, `git commit`, or `git push`, verify the current branch explicitly. Never use
the standing approvals for these commands on `master`; mutations of `master` require a separate,
action-specific user request.

After a DRY pull request is merged, continue the DRY plan from the updated `master` on a fresh
non-`master` branch and open the next review pull request without waiting for another request.

## Book notation pitfalls (OCR drops bold)
- **Follow the book's names strictly.** Never coin your own name for a functor/object and never
  reuse a book symbol for a different thing. In particular `Δ` is the *diagonal* functor `𝐀 → 𝐀/B`
  (book §1.53, [1.44]); the endofunctor `B×−` is the composite `Σ∘Δ` and is **never** written `Δ`.
- **Bold `𝐀` = the category; plain `A`, `B`, … = its objects.** The OCR loses bold, so a category
  `𝐀` shows up as plain `A`. In `𝐀/B` the `𝐀` is the *category* and `B ∈ 𝐀` is an *object* — read it
  as "the category `𝐀` sliced over the object `B`", never "object A over object B".
- **`𝐀/B`: one definition, two presentations; one `Δ`, two readings.** RULE: (1) `𝐀/B` always means
  the full slice — objects are ALL arrows `X → B`, never only the `B×A → B`. (2) `Δ` is the one
  diagonal functor `A ↦ (B×A → B)`, `f ↦ 1×f` (§1.44). §1.544 re-presents the same category over the
  inflation `𝐀'` (objects = finite sequences, product = concatenation, strict cancellation
  `B×A = B×A' ⟹ A = A'`) and renames the image of `Δ` to `𝐀`, making `Δ` injective on objects, so
  `𝐀 ⊆ 𝐀/B` is a subcategory (Freyd's stated purpose) — in force from §1.544 on, needed wherever `𝐀`
  must sit inside `𝐀/B` (capitalization towers and their unions, §1.545–6). Both presentations are
  equivalent categories; slice statements (e.g. §1.63's `Sub` iso) quantify over ALL slice objects.
  (3) On subobjects: `Sub_{𝐀/B}(ΔA) = Sub_𝐀(B×A)`, `Δ` acting by `A' ↦ B×A'` (= `π^#`).
  (4) `Δ` the diagonal *functor* ≠ `⟨1,1⟩` the diagonal *morphism* (§1.535 flags the name clash).
  Factorisation: `(B×−) = Σ∘Δ`, with `Δ: 𝐀 → 𝐀/B` the diagonal
  (`A ↦ (B×A → B)`) and `Σ: 𝐀/B → 𝐀` forgetful (`(X→B) ↦ X`, so `Σ(B×A→B) = B×A`). The §1.53 facts
  Freyd actually proves: Σ preserves/reflects covers & pullbacks, Δ a pre-regular representation,
  Δ faithful iff B well-supported — all argued *directly*, NOT via an adjunction. The adjoint chain
  `Σ ⊣ Δ ⊣ Π` is Freyd's §1.854 (not §1.53), and it IS formalised in Lean: `Σ ⊣ Δ` is
  `sigma_adj_delta` (`S1_85.lean`, axioms `{propext}`, fully constructive; Lean's `Δ` is the mirror
  `Y ↦ ⟨Y×B, snd⟩`), `Δ ⊣ Π` is `sliceForallAdj` (`f* ⊣ Π_f`, `SlicePi.lean`). Σ's §1.531
  preservation/reflection facts are separate (`SliceRegular`/`SliceTopos`).

## Writing explanations / notes
Introduce a concept before its first use. Order sections, paragraphs, and figures so every term, object,
or notation is defined or explained before it appears in another argument. If a later section uses a thing
(e.g. the swap `ℤ/2`-set as a counterexample), the section that says what that thing *is* must come first.
Prefer relative cross-references ("the next subsection", "above") over hard-coded section numbers, which
break when sections are reordered. Avoid unexplained field-specific notation (e.g. `Bℤ/2`, `π₁`); spell it
out ("the one-object category of `ℤ/2`") unless the term has already been introduced.

**Banned words, in chat and in the note alike.** No eponyms for a result — never "Lambek"; say the
property ("`α` is an iso"). None of B&dM's Greek scheme names — no catamorphism, anamorphism,
hylomorphism, paramorphism; `⦇R⦈` is "the fold", `⟦R⟧` an "unfold", a hylomorphism "an unfold then a
fold". A technical term keeps the note's own English spelling inside a Chinese sentence (`path`, never
路径), because a word the reader has not met in the note or the book reads as invented even when it is
in B&dM.

**A formula heading a table gets ONE sentence saying what it is about.** Every `Thm[...]` cell, and any
other table header that is a formula, carries a single `#src` line glossing it — what the equation says,
in words, checkable against the symbols term by term. Not the law's name, not a restatement of the
formula: what it means. One sentence, no more.

**NEVER ADD A PARAGRAPH TO `diag/allegory-axioms.typ` UNLESS ASKED.** No new prose, no restated
conventions, no framing or linking sentences. Answer in chat instead; put durable know-how in the
relevant skill (Hinze–Marsden conventions go to `string-diagram`, circuit ones to `circuit-diagram`) or
in a `//` comment in the drawing file.
Adding a picture, fixing wrong wording, or cutting text is fine — adding explanation nobody asked for
is not.

**NEVER HAND-DRAW A PICTURE. Every panel in the note is emitted by `scripts/diagram` or
`scripts/circuit` from its formula and carries the `cert:` they write.** A hand-laid drawing has no
`cert:`, so `scripts/scanline` cannot read it back, `--compare` cannot catch it drifting from the
formula, and its port types are checked by nobody — which is how a bead ends up on a wire that is not
its source. When the generator cannot draw a panel, extend the generator (parser, `hm-sigs.json`,
`dpanel.typ`) first and then generate; a one-off `cetz` file is never the answer.

**ALWAYS PROVE IT IN LEAN.** A type the note writes, the naturality a bead's dot claims, the equation
a table row states — each is backed by a Lean declaration cited by its `lean:` marker (a signature row
carries `lean` and `nat-lean`, in `hm-sigs.json` or in the panel's own `cert:`), because a claim checked
only by eye is how a bead landed on a wire that was not its source, and `cite-check` and `hm-check
--verify-sigs` can only hold what has a declaration behind it. No declaration, no dot, no claim: a
transformation with no naturality proof draws as a spider, a type with no Lean spelling is not written.

## Searching the book text
The greppable book prose lives in `/home/dh/anki/typst-book/chapters/<a.b>/section-<a.b>.typ`
(and the `section-*.fixed.md` siblings — cleaned OCR). ALWAYS grep there.
`/home/dh/repo/freyd/book-all.typ` is only a 63-line wrapper that `#include`s those chapter
files — grepping it alone finds NOTHING. To search the whole book:
`grep -rni "<term>" /home/dh/anki/typst-book/chapters/`.

## Searching the reference PDFs
Do NOT open a PDF page as an image to find something, and do NOT run `pdftotext | grep` loops. Every
third-party PDF in the repo is indexed in `book-index.db` (gitignored — it holds the books' full text);
`./scripts/book` queries it and costs no image tokens. `make books` rebuilds (sha256 skips unchanged
files, so a no-op run is under a second).

```
./scripts/book ls                                    # what is indexed, and each book's page offset
./scripts/book find 3.1a IntroString                 # exact label: theorem/example/equation tags
./scripts/book grep -b algprog catamorphism fusion   # BM25 over paragraphs, ranked, with snippets
./scripts/book sim why is a monad a monoid           # embedding KNN — paraphrase, not keywords
./scripts/book page IntroString 64                   # printed page; `pdf:79` for the raw index
./scripts/book grep -b axioms takewhile              # the note itself is `axioms`, re-indexed by `make p`
./scripts/book pic takewhile                         # a display's page + crop box, and the pdftoppm that cuts it
```

Which one: `find` for a numbered tag, `grep` when you know the words the page uses, `sim` when you know
only what it means. `grep` is the default — `sim` wins on well-formed prose stating a concept and loses on
OCR fragments. Math operators (`∘`, `⦇`) are dropped by the tokenizer, so those still need a real grep.
Page answers print `p.N (pdf M)`; a book whose numbering could not be pinned says `printed=?` rather than
guessing.

## Searching the Lean declarations
Do NOT grep `*.lean` to find a declaration. The whole corpus — every `Freyd`, `AOP`, `leet`, `rel`
declaration with its statement text and source line — is indexed in one sqlite database,
`.lake/build/refactor-index.db` (rebuilt by `./scripts/lean-refactor index`, which `make` runs as a
prerequisite of `cite`/`cover`). Query it, then read the source only to check the hypotheses of the
one hit you are about to use — the indexed statement omits `variable`-bound hypotheses.

```
sqlite3 -readonly .lake/build/refactor-index.db "
  select i.module, i.user_name, printf('%08x', i.stmt_key & 4294967295), m.source, r.sl1+1, i.stmt
  from decl_info i join module m on m.name = i.module
  left join decl_range r on r.name = i.name and r.module = i.module
  where i.internal = 0 and i.module like 'AOP.A5%' and i.stmt like '%Λ%'"
```

`decl_info(name, user_name, module, kind, internal, stmt, stmt_key, skel, skel_size)`,
`module(name, source)`, `decl_range(name, module, sl1)`. Always keep `internal = 0`: it drops the
compiler's own declarations. `sl1` is 0-based, hence the `+1`. Give the ABSOLUTE path from a
worktree — a worktree has no `.lake` of its own.
That `printf` is the `lean:<Mod>.<decl>@<key>` marker's key: the low 32 bits of `stmt_key`, the same
number `scripts/cite-check` recomputes when it re-verifies a citation in the notes.
