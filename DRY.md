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
Its primary `graph/spec.tsv` contains direct theorem specializations. Matches
that require a local-context elimination search are retained separately in
`graph/spec-derived.tsv`, and exact definition signature/value matches in
`graph/spec-defs.tsv`; these two classes are useful audit evidence but are not
direct theorem-specialization work. For every hit, inspect its statement, book
source, imports, and downstream uses.

## Three traps

### Semantic collapse

A shorter proof is wrong if it silently replaces the book's definition with an
ad-hoc equivalent. Preserve the book's hypotheses and construction even when a
weaker Lean fact would prove the immediate goal.

### Dependency inversion

Prove the general theorem first in the earliest legal common home, move its
genuinely shared prerequisites there, and remove the special case. The current
file order is not a reason to retain duplication. If moving the theorem exposes
a real mathematical dependency, reorganize that dependency explicitly; never
hide the problem with an import cycle or a second proof.

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
- The general strict-coterminator theorem belongs before the strict-initial
  specialization; move it earlier instead of preserving two proofs.

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

## Remaining DRY plan

This is the handoff backlog after PR #24. It is deliberately more conservative
than the raw graph reports: every task below states the intended canonical
direction and the conditions under which an agent should abandon the refactor.

### Baseline and acceptance gates

The scan baseline at this point is:

- 8,604 declarations and 118,231 dependency edges from 230 built modules;
- zero exact theorem-duplicate groups;
- 44 direct theorem-specialization candidates in `graph/spec.tsv`;
- 20 local-context-derived matches in `graph/spec-derived.tsv`;
- 28 definition matches in `graph/spec-defs.tsv`;
- 89 cross-file proof near-clone pairs, of which 86 are notation/parser
  declarations and only three are ordinary Lean declarations.

The ordinary proof near-clones are already one-line book-facing specializations:

- `Rcat.isMor_finite` / `Pcat.isPMor_finite`;
- `Rcat.Recursive1.const` / `Rcat.Recursive3.const`;
- `Rcat.Recursive2.const` / `Rcat.Recursive1.const`.

Do not abstract these unless a new shared construction removes code after their
documentation and names are retained. The previous audit found no such
net-reducing abstraction.

For every work package below:

#### Standing constraints

- Search the book prose under `/home/dh/anki/typst-book/chapters/` before
  changing a book-facing declaration.
- Prove the general result first in the earliest legal module. Move genuinely
  shared prerequisites there; do not solve import direction by importing a later
  chapter.
- Preserve useful book-facing names as short corollaries or delegating
  definitions. Removing a duplicate proof does not require erasing the book's
  vocabulary.
- Use `scripts/lean-refactor` for Lean source refactors. Improve
  `Freyd/tool/LeanRefactor.lean` first if the operation cannot be expressed
  safely.
- Require a net reduction in duplicated reasoning and normally a net Lean
  source-line reduction. Count graph artifacts separately.
- Work on a non-`master` branch in an isolated worktree. Run the affected build
  before committing and the full capped build after integration.

#### Three traps

- **Semantic collapse:** identical Lean shapes may express different book
  concepts. Preserve the book definition and hypotheses.
- **Dependency inversion:** a later general-looking theorem is not a legal
  dependency for an earlier special case. Move the actual general theorem and
  prerequisites to their earliest home.
- **Instance drift:** do not replace local or scoped instance selection with a
  globally active instance.

#### Required handoff

Report the canonical declaration, declarations shortened or removed, import
changes, Lean-only additions/deletions, affected builds, full-build result, and
the regenerated scan deltas. Record rejected candidates and the reason in this
file.

### Work package A — recursive internal accessors

**Target:** `Rcat.cmpFnd` and `Rcat.prNd0` in
`Freyd/S1_572b_NotEffective.lean`.

The two definitions currently have the same signature and value. They denote
the first child used by different encodings, so neither implementation-specific
name should become the canonical dependency of the other.

Plan:

1. Inspect every use and the book terminology for the corresponding child
   index.
2. Introduce one neutral internal accessor beside `kidsAt`/`rdN`, in the same
   earliest module; a name such as `firstChild` is acceptable only if it matches
   the surrounding terminology.
3. Make the comp- and primitive-recursion-facing declarations short delegating
   definitions if their names clarify the encoding, or replace them and remove
   them if they are purely private plumbing.
4. Regenerate `spec-defs.tsv`; the bidirectional pair should disappear because
   the bodies now depend on the shared accessor.

Stop if the two child positions cease to be definitionally the same after their
respective encoding invariants are made explicit. Do not reuse `cmpFnd` in the
primitive-recursion proof merely because it already exists.

### Work package B — monotonicity of `Allows`

**Targets:** `allows_mono` in `Freyd/S1_91.lean` and
`Frobenius.allows_of_le` in `Freyd/S1_59_10_Frobenius.lean`.

These independently prove the same elementary factorization lemma. The general
fact belongs beside `Allows`/`Subobject.le`, before both §1.59(10) and §1.91.

Plan:

1. Locate the earliest module that defines `Allows` and already has the required
   category/composition API.
2. Move or prove one root theorem there under the shortest unambiguous name
   `allows_of_le`.
3. Replace both proof bodies with that theorem. Retain `allows_mono` only if the
   §1.914 prose genuinely benefits from the local name; otherwise replace its
   callers and remove it.
4. Do not put the canonical theorem in the `Frobenius` namespace: monotonicity
   of allowance does not depend on Frobenius reciprocity.

Acceptance requires eliminating the parallel factorization proofs without
adding an import from §1.91 to §1.59(10) or conversely.

### Work package C — §2.157 idempotent wrappers

**Targets in `Freyd/S2_157_ProjectivePlane.lean`:**

- `meet_pt_pt_self` and `meet_ln_ln_self` versus `meet_idem`;
- `join_pt_pt_self` and `join_ln_ln_self` versus `join_idem`.

These are useful typed geometric statements, so the default action is to retain
their names and derive their bodies from the canonical idempotence theorems.

Plan:

1. Verify that each wrapper expresses exactly the same point/line operation,
   not a coercion-specific fact used to guide elaboration.
2. Replace each independent proof body with the matching general theorem.
3. Keep the point and line names if they occur in the book argument or improve
   later incidence proofs.
4. Remove a wrapper only when it is unused and not a named book step.

This package may remove specialization rows without deleting declarations,
because the proof-dependency filter will recognize the canonical call. Reject
the package if retaining clear typed wrappers plus their documentation makes
the source longer than the current direct proofs.

### Work package D — §2.157 Horn families

**Large direct-candidate clusters:**

- the `cP_*` and `htA_cP` leaves versus `hornConc_pt_ln`;
- the `cL_*`, `htA_cL`, and `bigshape_lnln` leaves versus
  `hornConc_ln_ln`;
- `hornConc_a₁_topc`, `hornConc_b₁_topc`, `hornConc_a₂_topc`, and
  `hornConc_b₂_topc` versus `hornConc_top_col`.

The leaves are distinct incidence cases and must keep their names. The only
acceptable DRY result is shared proof infrastructure or short derivations from
a legal earlier general theorem.

Plan:

1. Map the import chain
   `S2_157_ProjectivePlane → S2_157c_Converse → S2_157d_HornTop →
   S2_157e_HornCenter → S2_157f_HornLine`.
2. List the prerequisites of each `hornConc_*` general theorem. Several
   current candidates point from an earlier leaf to a later theorem, which is
   not a legal dependency.
3. Decide whether the general Horn calculation and its prerequisites have a
   genuine earlier home. Move them only if their statement does not depend on
   the later geometric construction.
4. Retain every nonsymmetric incidence leaf. Derive symmetric cases only
   through an explicit point/line or endpoint symmetry already present in the
   book.
5. Measure net proof-body reduction across the whole cluster; replacing a
   two-line leaf with a longer transport term is not a win.

This is high-risk work. A candidate row alone is not evidence that a leaf
should disappear. If the general theorem intrinsically belongs to the later
Horn-center construction, record the cluster as rejected and leave the earlier
proofs independent.

### Work package E — projective-plane joins

Audit these separately from the large Horn cluster:

- `join_ln_pt_incid` versus `join_eq_of_le_left`;
- `join_pt_ln_incid` versus `join_eq_of_le_right`;
- `join_ln_top_of_le` versus `join_ln_top_of_not_le`;
- `join_ln_pt_not` versus `join_ln_left_top_of_not_le`;
- the derived-only `join_ln_ln_ne` comparison.

The incidence and non-incidence hypotheses differ, and some apparent
specializations are consequences of the local projective-plane context rather
than the same theorem.

Plan:

1. Write the exact hypotheses side by side before editing.
2. Look for one lattice-level join theorem that precedes the geometric cases.
3. Keep positive-incidence and negative-incidence book statements separate.
4. Treat any match requiring `solveByElim` as low-confidence unless a direct
   explicit derivation can be written.

### Work package F — scanner expansion for deeper clones

The default proof scan has nearly exhausted cross-file Jaccard ≥ 0.75 matches.
The next useful discovery work is to improve coverage rather than lower quality
silently.

Plan:

1. Run a focused lower-threshold report without replacing the canonical graph
   artifact:

   ```sh
   ./scripts/cap lake env lean --run scripts/ProofSkeleton.lean \
     --min-nodes 40 --min-jaccard 0.60 \
     --output /tmp/proof-near-clones-60.tsv
   ```

2. Rank by node count first. Audit large proofs before small notation or
   one-line wrappers.
3. Extend `scripts/ProofSkeleton.lean` with an explicit
   `--include-same-file` CLI flag. The current scanner intentionally reports
   cross-file pairs only and therefore misses copy/paste within large files.
   Preserve cross-file-only behavior as the default.
4. Add a declaration-class filter or a separate output for notation/parser
   declarations. Do not delete that evidence; keep it out of the ordinary
   proof backlog, as `SpecScan` already does for definition and derived-context
   matches.
5. If a new scanner option becomes part of the standard workflow, document its
   CLI and regenerate a tracked, clearly named artifact.

Any scanner change must compile standalone, retain deterministic ordering, and
show measured recall/precision effects in the PR description.

### Work package G — remaining direct candidates outside §2.157

Audit these one at a time; they are not one coherent refactor:

- `corEmb_faithful` / `splEmb_faithful`: distinct embeddings in the same
  section. Seek a shared embedding-faithfulness lemma, but retain both names.
- `splObj_semiSimple` / `tabular_is_semiSimple`: previously judged distinct
  book arguments. Leave separate unless a stronger common theorem preserves
  both constructions.
- `Pcat.phat_idem_split` / `equalizers_split_idempotents`: retain the
  primitive-recursive statement; derive it only if the required equalizer
  instance is already legal and constructive.
- `cover_id` / `Rep646.isIso_of_section_of_mono`: likely a contextual
  specialization. Keep `cover_id` if it is the book's capitalization step.
- `GElt.zero_add_zero` / `GElt.zero_add`: the current theorem is already a
  one-line named group identity. No further abstraction is expected.
- `nabla_equalizer`, `nabla_terminator` / `isomorphic_refl`: false structural
  matches; the assembly isomorphisms contain meaningful maps and should stay.
- `positiveReflectionEmbed_injective` /
  `globalCompletionEmbed_injective`: distinct embeddings; do not collapse one
  into the other without a shared embedding constructor.
- `nno_is_free_one_action` / `free_action_exists`: intentional book
  progression from the one-action case to the general result.
- `strict_coterminator_bottomSub_one` / `prelogos_bottom_strict`: different
  hypotheses and constructions; preserve both.
- `Rcat.rFactorization` / `ac_factorization`: the former is constructive
  recursive infrastructure, while the latter assumes the regular/image
  structure it helps construct. Reusing the latter would invert dependencies.
- `capData_of_cofinalSystem` / `capData_exists`: different capitalization
  assembly levels; preserve both.
- `forgetSlice_invImage_le` and `le_forgetSlice_invImage` /
  `Subobject.le_refl`: scanner artifacts caused by definitional reduction.
  They are the two substantive directions of the inverse-image comparison.

### Work package H — definition-match audit

The definition report is informational. Use these dispositions:

**Possible internal consolidation**

- `Rcat.cmpFnd` / `Rcat.prNd0`: Work package A.

**Intentional book-facing aliases or distinct presentations — retain**

- `Sub` / `powerSetObj`;
- `IsInitial` / `PreLogosHorn.IsInitialObj`;
- `SplitIdempotent` / `Alg.CatSplits`;
- `nablaAsm` / `Alg.AsmTwo.setLikeOf`;
- `OppCat` / `Alg.MapObj` / `Alg.Downdeal`;
- `Rep646.coideal` / `listSubset`;
- the Veblen–Wedderburn `Point9`/`Line9`, `infPt`/`infLine`,
  `slopePt`/`vert`, and `aff`/`lineMB` pairs.

These names mark different book objects, presentations, or geometric roles.
Their equal Lean representations are not sufficient reason to delete them.

**Already audited — no current action**

- `LaxColim.advIso` / `LaxColim.alignGerm`: `alignGerm` is the earlier legal
  implementation in the capitalization development, while both names support
  substantial distinct book-facing APIs.
- `UniformCap.instHasEqualizers` /
  `PreRegularCategory.pinnedEqualizers`: the local name participates in the
  scoped instance selection; do not make the selector global.

### Work package I — derived-context report

`graph/spec-derived.tsv` is evidence for manual review, not a deletion queue.
The current rows mostly compare unrelated injectivity, faithfulness, equality,
or order lemmas because local hypotheses allow `solveByElim` to close the
leftover binder.

Default disposition:

- preserve `OPred.le_refl`, `Opens.le_top`, `Opens.le_refl`, and the
  faithfulness/injectivity theorems;
- preserve `eq_sharpHom`, `embEq_id`, `relMap_Phi_Psi`, and
  `b_recip_recip`, which concern different representations;
- preserve `isMor_finite` and `IsPMor.isMor`, which live in different
  recursive classes;
- revisit a row only when a direct proof term from the proposed canonical
  theorem can be written without `solveByElim`.

Do not reduce this file's row count by weakening the scanner. Its purpose is to
retain the low-confidence evidence outside the primary queue.

### Integration checklist

After integrating any combination of packages:

```sh
./scripts/cap lake build
./scripts/cap lake build \
  Freyd.tool.QSeqRender Freyd.tool.QSeqMonic \
  Freyd.tool.QSeq139Render Freyd.tool.QSeq139 Freyd.tool.HornToQSeq
./scripts/cap lake env lean --run scripts/ExtractGraph.lean
python3 scripts/dep_dup.py
./scripts/cap lake env lean --run scripts/ProofSkeleton.lean
./scripts/cap lake env lean --run scripts/SpecScan.lean
git diff --check
```

The graph extractor may warn about deliberately unbuilt orphan/tool modules.
Compare the missing-module list and module/declaration counts with the baseline
above; investigate any new omission. Before `git add`, `git commit`, or
`git push`, verify the branch explicitly and never perform those mutations on
`master`.
