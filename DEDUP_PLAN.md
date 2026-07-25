# Remaining DRY work — codex handoff plan

Every item below is a self-contained task. Facts are verified (file:line, use counts, common-ancestor
homes) as of branch `dedup-defs` at `7470157`. Hand items to codex one at a time, in the order given
within each section; items in different sections are independent.

## Standing constraints — prepend to every task

```
Repo /home/dh/repo/freyd: Lean 4 formalization of Freyd & Scedrov, *Categories and Allegories*.
STRICTLY mathlib-free: never add a `require`, never import Mathlib/Std/Batteries/Aesop.
Build with `./scripts/cap lake build Freyd` — ALWAYS via ./scripts/cap (12 GB per-process cap; an
uncapped runaway OOM-killed this machine at 18.3 GB on 2026-07-25).
Composition is diagram order (`x ≫ y` is the book's `xy`); write `𝟙 A`, never `Cat.id A`, in new code.
`Cat.assoc f g h : (f ≫ g) ≫ h = f ≫ (g ≫ h)`.
Never add an `axiom`; never weaken a statement to `: True`; never replace a compile error with
`sorry`. If an edit introduces an error, REVERT it before trying another approach — never leave the
build red. No state-changing git commands (no commit, checkout, stash, branch, reset).
```

## Three traps that have already cost real work — state these in every collapse task

1. **Pick the survivor from the book, not from the import graph.** Choosing by "which file can import
   which" put §1.28's `Idempotent` in the §1.429 file, and made the misnamed `YonedaEmbedding`
   canonical over 9 sites. Before collapsing: grep the book
   (`grep -rni "<term>" /home/dh/anki/typst-book/chapters/`) and confirm the surviving name denotes
   that object and not a neighbouring one. **A book-defined role name is not a duplicate merely
   because its implementation is definitionally equal to a generic type or function.** In particular,
   keep named functor components such as §1.332's `powerSetObj` for `P(S)`: replacing it with the
   generic predicate-set type `Sub` erases the book's definition and is forbidden. Treat scanner
   “alias” classifications as presumptively intentional until the book proves otherwise.
2. **A collapse across independent files needs a common-ancestor MOVE, and the shared prerequisite may
   have no legal home.** Both large collapses so far needed a brand-new leaf file (`S1_28.lean`,
   `S1_241.lean`) because the book's section-numbered home was *downstream* of the users. Compute the
   common ancestor first; if the book home is downstream, create a leaf importing only what it needs.
   A previous agent, told to put a definition where its prerequisite wasn't reachable, invented a
   *second* `Cat (Type v)` instance — worse than the duplicate, because the instance appears in the
   type and splits downstream code into two incompatible worlds.
3. **The weaker-hypothesis trap.** A lemma declared after a file-level `variable [PreLogos 𝒞]`
   silently carries that instance. A downstream "duplicate" stated with a weaker class is often
   load-bearing, and collapsing it fails with `failed to synthesize instance`. Try the collapse, build,
   and revert on a synthesis failure rather than fighting it.

---

## Section 1 — Two mutually-derivable theorem pairs (ready to run)

### 1A. `entire_id_le` / `entire_le` → `Freyd/S2_1.lean`

Same statement about entire morphisms, in two files that do not import each other:

| where | statement | uses |
|---|---|---|
| `Freyd/S2_16c.lean:93` | `theorem entire_id_le {a b : 𝒜} {f : a ⟶ b} (hf : Entire f) : Cat.id a ⊑ f ≫ f°` (namespace `Freyd.Alg`) | 1 |
| `Freyd/S2_154_CategoriesIso.lean:64` | `theorem entire_le {a b : 𝒜} {R : a ⟶ b} (h : Alg.Entire R) : Cat.id a ⊑ R ≫ R°` | ~6 |

**Home:** `Freyd/S2_1.lean` — defines both ingredients (`Entire` at 408, `inter_lb_right` at 116) and
is a verified common ancestor. Place the survivor immediately after `Entire`.

**Survivor:** keep the name `entire_id_le` in namespace `Freyd.Alg`. Do **not** keep `entire_le`: the
repo has an unrelated family about the top *subobject* `entire` (`le_entire`, `sub_le_entire`,
`entire_le_invImage_entire`), and `entire_le` reads as one of those. Delete `S2_154.entire_le`, repoint
its uses.

**Verify:** `grep -rn 'theorem entire_id_le' Freyd/` → one hit, in `S2_1.lean`; `grep -rnw 'entire_le'`
→ no hit naming the deleted theorem.

### 1B. `mapTo_botDom_iso` / `prelogos_bottom_strict` → `Freyd/S1_61.lean`

"Every map into the bottom subobject's domain is an iso", twice, plus a specialisation:

| where | statement | uses |
|---|---|---|
| `Freyd/S1_75.lean:141` | `theorem mapTo_botDom_iso [hPL : PreLogos 𝒞] {Z P : 𝒞} (j : Z ⟶ (PreLogos.bottom P).dom) : IsIso j` | 3 |
| `Freyd/S1_621_ColimitPositive.lean:140` | `theorem prelogos_bottom_strict {𝒞 : Type u} [Cat.{v} 𝒞] (h : PreLogos 𝒞) (B : 𝒞) : StrictCoterminator (h.bottom B).dom` | 3 |
| `Freyd/S1_944_ToposStrictZero.lean` | `strict_coterminator_bottomSub_one` — scanner says derivable from both, nothing to discharge | 5 |

`StrictCoterminator Z := ∀ {X : 𝒞} (f : X ⟶ Z), IsIso f` (`Freyd/S1_58.lean:55`) — so the second is
exactly the first behind a named predicate.

**Home:** `Freyd/S1_61.lean` (has `any_map_to_zero_is_iso` at 75; verified common ancestor of all
three files). **First check that `StrictCoterminator` (S1_58) is reachable from S1_61**; if not, use
the deepest common ancestor of the three that does see S1_58, and say which.

**Survivor:** `prelogos_bottom_strict` — the named-predicate form is reusable. Delete
`mapTo_botDom_iso`, repoint its 3 uses. **Binder difference:** the survivor takes `PreLogos 𝒞`
explicitly as `(h : …)`, the deleted one took it as an instance `[hPL : …]`, so call sites must pass it
by name.

**Then judge `strict_coterminator_bottomSub_one`:** if it is exactly `prelogos_bottom_strict` at
`B := one`, delete it and repoint its 5 uses — this repo forbids one-liner wrapper theorems, so do not
leave a delegating alias. If it is not that instance, keep it and state the difference.

### 1C. Explicitly OUT of scope — do not "fix"

`eqToHom_comp_eqToHom_symm` / `eqToHom_symm_comp_eqToHom` (`Freyd/S1_36.lean:71,74`). Mutually
derivable only by substituting `e := e.symm`; they state *different* equations (`𝟙 X` vs `𝟙 Y`) needed
for rewriting in both directions; 9 and 10 uses. Collapsing forces `e.symm.symm` coercions at every
site to save two lines.

---

## Section 2 — Definition-level duplicates (new; from the now-working `dep_dup.py`)

Run `./scripts/cap python3 scripts/dep_dup.py` to regenerate this list. One task per row.

| group | verdict | action |
|---|---|---|
| `uniformPinEqualizers` (S1_547:78, 2 uses) / `ratCapImgPinEq` (S1_543_RatCapImages:32, 1) / `fibrePinEqualizers` (S1_546:58, 0) | three identical `local instance (priority := 10000) … : HasEqualizers 𝒞` | tool suggests home `Freyd.S1_52`. Low value: a shared instance still needs `attribute [local instance]` per file, so the saving is 2 lines per site. **Do the pullback twin at the same time or not at all.** |
| `uniformPinPullbacks` (S1_547:80, 21) / `fibrePinPullbacks` (S1_546:60, 9) / `ratCapImgPinPb` (S1_543_RatCapImages:34, 1) | same, for `HasPullbacks` | as above |
| `Rcat.prNd0` / `Rcat.prNdA` (`S1_572b_NotEffective.lean:384,386`, `Nat → Nat → Nat`, 5 uses each) | **same file**, identical key | easiest win in this section: read both, keep one, repoint |
| `RegBundle` (S1_543_Capitalization:831, 5 uses) / `S2_154.SmallRegCat` (S2_154:759, 47 uses) | identical `Type (u+1)` inductives — a bundled regular category, twice | needs a common-ancestor move; survivor is probably `SmallRegCat` on use count, but check the book's term for the bundled object first |
| `Alg.VW.Point9` / `Alg.VW.Line9` (`S2_157h_VeblenWedderburn.lean:146,149`) | same abbrev twice, same file | read: if `Point9` and `Line9` are meant to be the *same* 9-element type used in two roles, keeping both names may be deliberate (duality). Judge and report |
| `powerSetObj` (S1_33:158) / `Sub` (S1_543_WellOrdering:44) | both `α → Prop` — a **fourth** copy of the predicate-set type, after three were merged into `Freyd.Sub` | codex classified this as an alias (naming a term). I read it as a real copy: `Sub S` *is* the power set of `S`. Retype `powerSetMap : Sub T → Sub S` and delete `powerSetObj`, or record why not |
| `OppCat` / `Alg.MapObj` / `Alg.Downdeal` | identity type synonyms, same key, deliberately distinct tags | **false positive — do not touch** |
| `Quant` (S1_38b:42) / `QSeq139.Bar` | same-shape enums, unrelated meanings; `QSeq139` is an orphan that does not build | **false positive — do not touch** |
| `QSeq139.satMon_pair_iff_monicPair` / `satMon_is_meaning` | real theorem duplicate, but inside `Freyd/tool/QSeq139.lean`, one of 8 orphan modules excluded from the build | skip unless the orphans are being revived |

---

## Section 3 — Re-run the widened scanners and triage

Both scanners now accept `.defnInfo` (commit `7470157`) but have not been run since.

1. `./scripts/cap lake env lean --run scripts/ProofSkeleton.lean` — ~2 min. Value-skeleton hashing;
   now covers defs, so it should find copy-pasted *definitions*, which no pass has ever reported.
2. `./scripts/cap lake env lean --run scripts/SpecScan.lean` — **~70 min**, writes `graph/spec.tsv`.
   Its previous output is stale: 11 of 141 rows reference declarations deleted today. Note 45 rows
   came from the `solveByElim` fallback and have **never been triaged** — precision there is unknown.
3. Triage the fresh output. Mutually-derivable pairs first (strongest signal), then cross-file rows
   with nothing to discharge, then the `solveByElim` rows.

---

## Section 4 — Two lints that would have prevented today's two errors

Implemented in the AST/environment-aware `Freyd/tool/LeanRefactor.lean`:
`./scripts/cap lake exe lean-refactor lint-book --glob 'Freyd/S*.lean'`.  The driver forks once per
file so elaborated environments do not accumulate in memory.  Findings are review output (exit 1),
not automatic rewrites.

1. **Range-aware section-home lint.** For each declaration whose docstring cites `§a.bc`, check the
   file's banner-declared section range contains it. A naive version is useless (1393 of 3171 "fail",
   because files legitimately cover ranges); the range-aware version gives **356 hits** and flags the
   real error class — e.g. `§1.28 SplitIdempotent` sitting in `S1_39.lean`, `§1.42 HasFiniteProducts`
   in `S1_43.lean`.
2. **Name-vs-type lint.** Flag declarations whose name ends `Functor`/`Embedding`/`Representation`
   but whose type is not a `Functor`. **22 hits**, including both misnomers caught today
   (`YonedaEmbedding`, `RepresentableFunctor`, each `: 𝒞 → 𝒞 → Type v`). Noisy enough to need one
   human pass, small enough that that is fine.

---

## Section 5 — Parallel developments (major; not dedup)

These are the last two known clusters, and they are a **different kind of work**: abstracting two
developments over a common interface, not deleting a copy. Sizes from `graph/decls.tsv`:

| cluster | declarations | files |
|---|---|---|
| `Rcat` (recursive functions) | 389, 269 qualified refs | `S1_572_Recursive.lean`, `S1_572b_NotEffective.lean` |
| `Pcat` (primitive recursive) | 123, 5 qualified refs | `S1_573_PrimRec.lean` |
| `Colim` | 196, 165 refs | `S1_543_*` |
| `LaxColim` | 248, 10 refs | `S1_543_*` |

**Do not attempt a wholesale merge.** They are deliberately parallel — recursive vs
primitive-recursive, lax vs strict colimit — and the two members of each pair are genuinely different
mathematical objects. The tractable approach, in this order:

1. Run `ProofSkeleton.lean`'s near-clone pass (Jaccard ≥ 0.75) and enumerate the concrete
   `Rcat.x` ~ `Pcat.x` and `Colim.x` ~ `LaxColim.x` pairs. Known from an earlier run:
   `Rcat.Recursive1.finTable` ~ `Pcat.PrimRec1.finTable` (J=76%, 694 nodes), `isMor_finite` ~
   `isPMor_finite`.
2. For each pair, decide whether the *shared* content is a statement about a common structure. Only
   where several pairs share one structure is an abstraction worth introducing.
3. Introduce the common interface for that one structure, port both sides to it, build, commit — one
   structure per commit. Stop when the remaining pairs no longer share anything.

Expect most pairs to resist: if the shared part is only "the same proof shape over different
recursion schemes", there is nothing to extract and the correct answer is to leave them.

---

## Section 6 — Known-blocked; do not retry without a new idea

- `entire_le_inverseImage_entire` (S1_72:480) vs `entire_le_invImage_entire` (S1_62:609). Identical
  statement and proof. The S1_62 original inherits the file-level `variable [PreLogos 𝒞]` and `Logos`
  does **not** supply `PreLogos` here (`failed to synthesize instance PreLogos 𝒞`). Hoisting the S1_62
  copy needs an explicit `[HasPullbacks 𝒞]` in a file whose own comment (near line 620) documents an
  instance diamond with `DisjointBinaryCoproduct.toPreLogos` for exactly that move. **Reverted twice.**
- `sub_le_entire` (S1_62) vs `le_entire` (S1_72). Same trap, same reason.
- `graph/decls.tsv` / `graph/deps.tsv` regeneration drops the dependency edges of 8 orphan modules
  that do not compile (`S1_35`, `S1_49`, six `Freyd.tool.QSeq*`), so a refreshed file is *poorer* than
  the committed one. Either revive or delete the orphans before treating regenerated graph data as
  authoritative.
