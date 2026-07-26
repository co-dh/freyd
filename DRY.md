# DRY guide

This file records the working rules learned while deduplicating the Freyd
formalization. Its purpose is to make future refactors safer, faster, and
faithful to the book.

## The first rule: preserve the book

The book's definition, terminology, notation, and conceptual boundaries come
before syntactic similarity. Two declarations are not interchangeable merely
because their Lean types or proofs look alike.

- Keep a book-facing theorem when it names a real step in the exposition. Make
  its proof a short specialization of a shared result instead of erasing the
  book's vocabulary.
- Put a shared theorem under the shortest unambiguous book name. Do not invent a
  name from an implementation detail.
- Share a proof across symmetric cases only when the symmetry is explicit in
  the formula or in the book.
- Do not merge separate geometric incidence cases, construction stages, or
  universal properties just because they use the same tactic skeleton.
- Prefer the canonical stronger theorem in the earliest legal book module;
  derive weaker statements by projection or specialization.

## Classify a match before changing it

Near-clone reports contain several different kinds of evidence:

1. **Exact declaration duplicates.** Same normalized type and body. These are
   the highest-confidence removals.
2. **Specializations.** One theorem follows from another after instantiating
   universes, objects, hypotheses, or parameters. Generalize the canonical
   theorem when that remains book-faithful, then delete or shorten the port.
3. **Shared proof bodies.** The statements remain useful book-facing names, but
   their bodies can call one general theorem.
4. **Analogies.** The code has a similar shape while expressing different
   mathematics. Leave these separate unless a genuine book-level abstraction
   exists.

The specialization scan is candidate generation, not a refactoring decision.
For every hit, inspect its statement, book source, imports, and downstream uses.

## Three traps

### Semantic collapse

A shorter proof is wrong if it silently replaces the book's definition with an
ad-hoc equivalent. Preserve the book's hypotheses and construction even when a
weaker Lean fact would prove the immediate goal.

### Dependency inversion

A general theorem in a later module cannot justify an earlier specialization.
Move genuinely shared prerequisites to the earliest legal module or leave the
proofs separate. Never create an import cycle merely to save lines.

### Instance drift

Repeated high-priority local instances often select one path through an
instance diamond; they are not necessarily new mathematical structures.
Centralize such a selector as a scoped instance beside the class that owns it,
then use `open scoped` only in affected files. Do not make it globally active
and change unrelated instance search.

## Patterns that have worked

- Generalize universe binders on the canonical declaration and remove later
  primed or cross-universe ports.
- Derive named corollaries through a shared theorem, as with Ω extensionality,
  while retaining useful names from the book.
- Derive symmetric Horn cases through explicit symmetries, while retaining the
  distinct nonsymmetric incidence cases.
- Centralize repeated instance pins as narrowly activated scoped instances.
- Move a reusable containment lemma to its genuine construction, then make
  downstream variants specialize it.
- Prefer one established name over aliases such as `invImage_mono` and
  `inverseImage_mono`.

## Patterns that have not justified merging

- The large §2.157 `cP_*` and `cL_*` leaves represent distinct incidence cases.
- Semisimplicity obtained from splittability and from tabularity are distinct
  book arguments.
- Natural-number-object and free-action constructions are analogous, not the
  same construction.
- `capData_of_cofinalSystem` and `capData_exists` operate at different assembly
  levels.
- A strict-initial coterminator cannot be routed through a later general
  strict-coterminator theorem when doing so reverses the legal dependency
  direction.

Record rejected candidates with their reason. Otherwise the same false
positive will be audited repeatedly.

## Refactoring workflow

1. Grep the actual book under
   `/home/dh/anki/typst-book/chapters/`.
2. Locate declarations and uses with `rg`.
3. Check the import direction and choose the canonical declaration.
4. Preview the mechanical change with `scripts/lean-refactor`.
5. If the operation is missing, improve `Freyd/tool/LeanRefactor.lean`, build
   `lean-refactor`, and then use the new operation.
6. Apply the refactor only through the tool. Its apply mode must restore the
   source if elaboration or the capped build fails.
7. Build the combined branch, not only each isolated worktree.
8. Refresh and inspect the knowledge graph after source changes.
9. Report source-line savings separately from graph artifacts and changes to
   `Freyd/tool/LeanRefactor.lean`.

Useful checks:

```sh
./scripts/cap lake build
./scripts/cap lake env lean --run scripts/ExtractGraph.lean
./scripts/cap lake env lean --run scripts/SpecScan.lean
python3 scripts/dep_dup.py
```

The graph extractor depends on built `.olean` files. Build intended orphan/tool
roots explicitly when they belong in graph coverage, and compare declaration,
edge, and module counts before accepting a refresh. A lower count can mean
missing build coverage rather than successful deduplication.

## Measuring a refactor

Line count is evidence, not the objective. A useful change removes duplicated
reasoning, establishes one canonical dependency, and keeps the book readable.
A coherent refactor may add a small shared theorem while removing several long
proofs.

When reporting results, distinguish:

- Lean source additions and deletions;
- net change excluding `Freyd/tool/LeanRefactor.lean`;
- generated graph changes;
- exact duplicates remaining;
- specialization candidates remaining.

Run parallel audits in separate worktrees, grouped by independent dependency
clusters. Integrate only successful, book-faithful commits on a non-`master`
branch, then run the full capped build because isolated builds do not test their
interaction.
