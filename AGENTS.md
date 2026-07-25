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
Use the global book notation `𝟙 A` for the categorical identity `Cat.id A`; do not spell identities
as `Cat.id A` in new code.
Use the shortest unambiguous book name in signatures and prose. Once its namespace is deliberately
opened, write `SmallRegCat`, for example, rather than `Freyd.S2_154.SmallRegCat`; keep full
qualification only where ambiguity or declaration syntax requires it.
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

For Lean source refactors, use `Freyd/tool/LeanRefactor.lean` through
`scripts/lean-refactor` instead of making mechanical edits by hand. If the tool cannot safely express
the required refactor, improve the tool first, verify the tool with `./scripts/cap lake build
lean-refactor`, and then use the new operation. Refactor operations must preview by default and restore
the original source when elaboration or the capped repository build fails.

Before starting a large change, commit all current work as a checkpoint unless the user explicitly
asks not to commit it.

Before every `git add`, `git commit`, or `git push`, verify the current branch explicitly. Never use
the standing approvals for these commands on `master`; mutations of `master` require a separate,
action-specific user request.

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

## Searching the book text
The greppable book prose lives in `/home/dh/anki/typst-book/chapters/<a.b>/section-<a.b>.typ`
(and the `section-*.fixed.md` siblings — cleaned OCR). ALWAYS grep there.
`/home/dh/repo/freyd/book-all.typ` is only a 63-line wrapper that `#include`s those chapter
files — grepping it alone finds NOTHING. To search the whole book:
`grep -rni "<term>" /home/dh/anki/typst-book/chapters/`.
