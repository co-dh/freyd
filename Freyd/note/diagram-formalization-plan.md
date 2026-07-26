# Plan: the diagrammatic calculus, formalized (`diag`) and drawn (Typst)

Goal, from `Freyd/note/diagrams-for-aop.md`: Algebra of Programming, drawn — wires are sets, boxes are relations —
with the diagram laws *proved sound* for the repo's `Rel(Set)` (`AOP/A6_1_RelSet.lean`). Acceptance criterion: the
theory built here must prove the allegory results, not merely picture them. The Lean side lives in a new lib root
`diag/`; the visual side in a reusable Typst/cetz module plus two tools.

Constraints in force throughout: mathlib-free (Lean core + this repo only), diagram-order composition `≫`,
constructive with axioms ⊆ {`propext`, `Quot.sound`} except where explicitly flagged (phase 9), no one-liner
wrappers, declarations named and doc-cited after their sources.

## The lib root: `diag`

A sibling of `Freyd/`, `AOP/`, `leet/`, `rel/`; lowercase like `leet`/`rel`; glob'd in `lakefile.toml` and in
`defaultTargets`. Module layout mirrors the paper tower (each layer keeps the one below):

Papers are cited by FILE NAME, never arXiv id. The short forms below are exact prefixes of the file names at the repo
root; the full mapping is the legend in the Sources section of `Freyd/note/diagrams-for-aop.md`.

| module                      | layer                                     | source                                        | phase |
| --------------------------- | ----------------------------------------- | --------------------------------------------- | ----- |
| `diag/Basic.lean`           | poset-enriched category (done)            | `functorialSemantics` Def. 4.1                 | 0     |
| `diag/Monoidal.lean`        | poset-enriched symmetric monoidal (done)  | `functorialSemantics` Def. 4.1                 | 1     |
| `diag/CB.lean`              | cartesian bicategory of relations (done)  | `functorialSemantics` Def. 4.1                 | 1     |
| `diag/CB_Derived.lean`      | converse, `∩`, `⊤`, maps — all theorems   | `functorialSemantics` §4, pp. 18–22            | 3     |
| `diag/RelSetCB.lean`        | `RelSet` instance + operation agreement   | `functorialSemantics` p. 18                    | 4     |
| `diag/CB_Allegory.lean`     | CB ⟹ `Allegory`; modular law as a theorem | CW87 Rem. 2.9(ii)                              | 5     |
| `diag/Tape.lean`            | fb-cb rig — `∪`, `⊥`                      | `TapeDiagrams` Def. 7.1                        | 8     |
| `diag/FO.lean`              | linear bicategory, complement, residuals  | `DiagrammaticAlgebraOfFirstOrderLogic` §5–6    | 9     |
| `diag/tool/DiagExport.lean` | Lean → Typst exporter (exe `diag-export`) | —                                              | 7     |

Deliberately NOT built: the free syntactic props `CB_Σ` / `TCB_Σ` and any completeness theorem. We need soundness
of diagram reasoning for `Rel(Set)`; completeness (`TapeDiagrams` Thm. 7.5) needs free constructions and hypergraph
combinatorics that buy nothing toward the acceptance criterion.

## Phase 0 — skeleton (DONE in this session)

`diag/Basic.lean` holds the one piece every layer shares: `class OrderedCat` (hom partial order `le`, `comp_mono`)
plus the `LE` instance so paper inequations read as written. The order is primitive here — unlike the allegory's
derived `R ⊑ S := R ∩ S = R` (`Freyd/S2_10.lean:75`) — because in this presentation `∩` is not a generator but the
derived convolution (`functorialSemantics` p. 22). Registered in `lakefile.toml` (`globs = ["diag.+"]`, added to
`defaultTargets`). Verified: `./scripts/cap lake build diag` succeeds.

## Phase 1 — the cartesian-bicategory classes (`diag/CB.lean`)

Goal: state `functorialSemantics` Definition 4.1 (pp. 17–18) faithfully — the paper's definition, not a simplification.

Declarations:

- `class SymMonCat` extends `OrderedCat`: tensor `⊗` on objects and arrows (monotone), unit object `I`,
  associator/unitor/symmetry isos with the standard naturality and coherence laws. Non-strict, because `Rel(Set)`'s
  cartesian product is not strictly associative in Lean (the papers hide this by working with props, whose objects
  are `ℕ`); prefer the full source definition (CW87 Def. 1, as stated in `Frobenius.pdf` Def. 1) over an ad-hoc
  strict variant.
- `class CartBicat` extends `SymMonCat`, per Def. 4.1: generator fields `copy` (`Δ : n ⟶ n⊗n`), `discard`
  (`! : n ⟶ I`), `merge` (`∇ : n⊗n ⟶ n`), `unit` (`? : I ⟶ n`); cocommutative-comonoid equations for `(Δ,!)` and
  commutative-monoid equations for `(∇,?)` (Example 2.3, eqs. (5)–(10), pp. 7–8); the four adjunction inequations
  (37)–(40) (`Δ ⊣ ∇`, `! ⊣ ?`); the Frobenius equation (41); the lax comonoid-homomorphism inequations (42)–(43)
  for every arrow — these are exactly eq. (3) on p. 4, and the book already holds both halves product-free
  (assessment note, "Equation (3) is not new mathematics").

Field names are descriptive (`copy`, `merge_copy_frob`, `lax_copy`, `lax_discard`, …); every docstring carries the
paper equation number and page. The special law `Δ;∇ = id` is NOT a field: the paper derives it from (38) plus
Frobenius (p. 18, the displayed derivation after (41)).

Notation: scoped postfix `†` for the phase-3 converse, matching the paper — `°` stays reserved for
`Allegory.recip`, and `functorialSemantics`'s own `(−)°` means colour swap, which is NOT order-reversing (§7, p. 37); never
conflate them.

Acceptance: `./scripts/cap lake build diag` green; `#print axioms` on the classes' constructors shows none.
Risk: coherence bookkeeping for the non-strict tensor. Mitigation: state the standard coherence fields up front,
and record (in docstrings) which of them later proofs actually consume; do not invent a bespoke weaker structure.

**DONE.** Split across two files: `diag/Monoidal.lean` (`SymMonCat` — tensor, associator, unitors, symmetry,
pentagon/triangle/hexagon, `tensHom_mono`) and `diag/CB.lean` (`CartBicat` — Def. 4.1 items 1–4 field for field:
`cop`/`dis`/`mer`/`un`, the comonoid and monoid equations (5)–(10), inequations (37)–(41), and the lax
inequations (42)–(43)). Build green. `CartBicat.special` — the special law `Δ;∇ = 𝟙`, eq. (12) — is proved, not
assumed: `𝟙 ≤ Δ;∇` is (38); the converse weakens one strand of the bubble to `!;?` by (40), then collapses with
the counit law (10) and the unit law (7), exactly the paper's displayed derivation on p. 18.
`#print axioms Freyd.Diag.CartBicat.special` → `[propext]`.

One deviation from the plan, recorded in `diag/CB.lean`'s header: Carboni & Walters also require the Frobenius
structure to be the *unique* comonoid per object (`Frobenius.pdf` Def. 1 clause 2), which equationally means
`Δ_{a⊗b}`/`!_{a⊗b}` are the shuffled products of the components. Def. 4.1 as printed omits it and nothing so far
needs it, so it is deferred to the first proof that uses `Δ` at a composite object — where the shuffle must be
written out. Do not treat its absence as an oversight.

## Phase 2 — tool (b): render the papers' axiom figures (`scripts/paper-figs`)

Goal: every Lean axiom checkable side by side against the source picture, *before* the risky proofs start.

Concrete I/O: a manifest `Freyd/note/paperfigs/manifest.tsv` with columns
`pdf  page  x  y  w  h  name  lean_decl`; the script `scripts/paper-figs` (shell, like `scripts/lean-graph`) runs
`pdftoppm -f p -l p -r 150 -x -y -W -H -png` per row, writes `Freyd/note/paperfigs/<name>.png`, and generates
`Freyd/note/axiom-crosscheck.typ` — one row per axiom: source clip | Lean field name | docstring citation.

Initial manifest coverage:

| paper                                  | figures                                                    |
| -------------------------------------- | ---------------------------------------------------------- |
| `functorialSemantics`                  | eq. (3) p. 4; eqs. (5)–(19) pp. 7–8; ineqs. (37)–(43) pp. 17–18 |
| `DiagrammaticAlgebraOfFirstOrderLogic` | Figs. 2, 3, 4, 5; Fig. 9 (App. B, the complete term system) |
| `TapeDiagrams`                         | Figs. 1, 2, 3                                              |

Acceptance: every `CartBicat` field has a manifest row; the crosscheck page compiles with `typst compile`.
Risk: none technical; crop coordinates need hand-tuning once.

## Phase 3 — derived structure, all theorems (`diag/CB_Derived.lean`)

Goal: the operations AOP needs, derived — nothing added as an axiom.

- `special_of_frobenius`: `Δ;∇ = 𝟙` (`functorialSemantics` p. 18, derivation after (41), from (38) + Frobenius).
- converse `†` as wire-bending: `def conv R := (cup ⊗ 𝟙);(𝟙 ⊗ R ⊗ 𝟙);(𝟙 ⊗ cap)` with `cup := ?;Δ`,
  `cap := ∇;!` (p. 19, "Compact closed structure"); theorems = Lemma 4.2 (i)–(iv): identity, contravariant
  functoriality, `⊗`-compatibility, monotonicity; plus involutivity (snake/yanking).
- convolution `∩`: `def convolution R S := Δ;(R ⊗ S);∇` (p. 22); Lemma 4.11: associative, commutative,
  idempotent (needs lax (42) + Frobenius), unital with `⊤ := !;?`; then: convolution is the greatest lower bound
  in the hom poset (p. 22, "every hom-set is a meet semi-lattice").
- maps: `def SingleValued` (SV), `def Total` (TOT) (p. 20); `lemma_4_4` — the four adjoint characterisations
  (46)–(49); `cor_4_5` — two maps with `R ≤ S` are equal (p. 21); `lemma_4_8` — `R` is a map iff it has a right
  adjoint, and the adjoint is `R†` (p. 21; B&dM's shunting rule). Comap characterisation Cor. 4.9: deferred —
  no AOP consumer.

Acceptance: build green; `#print axioms` on each theorem: none (abstract, class-parameterised).
Risk: yanking equalities are where non-strict associators bite first. Mitigation: prove the snake lemmas once,
under their own names, and never unfold `cup`/`cap` afterwards.

## Phase 4 — `Rel(Set)` is a cartesian bicategory (`diag/RelSetCB.lean`)

Goal: soundness — every abstract CB theorem instantiates to the repo's own `Rel(Set)`.

- `instance : SymMonCat RelSet` — `⊗` := carrier product with the existing action `rprodMap`
  (`AOP/A6_1_RelSet.lean:249`), `I := ⟨PUnit⟩`; structural isos are graphs of the obvious bijections
  (`graph_map`, `A6_1_RelSet.lean:104`, discharges all map obligations).
- `instance : CartBicat RelSet` — `Δ := graph (fun x => (x,x))`, `! := graph (fun _ => PUnit.unit)`,
  `∇ := Δ°`, `? := !°`, exactly as `functorialSemantics` p. 18 lists for `Rel`; all inequations pointwise.
- Agreement theorems, the load-bearing step: `convolution R S = R ∩ S` (the existing `Allegory RelSet` inter,
  `A6_1_RelSet.lean:58`), `conv R = R°`, `top = ⊤`. These make CB theorems interoperable with the whole
  existing AOP corpus without translation.

Acceptance: `#print axioms` ⊆ {`propext`, `Quot.sound`} (pointwise proofs use `propext`/`funext` only —
the repo's standard budget). Build green.

Do first: **`rprodMap` is universe-pinned.** `AOP/A6_1_RelSet.lean:249` and `rprodMap_recip` `:254` are stated for
`RelSet.{0}`, while every other declaration in that file — `Allegory` `:58`, `TabularAllegory` `:195`,
`UnitaryAllegory` `:214`, `graph_map` `:104`, `sumCop` `:259` — is `RelSet.{u}`. The bridge in phase 5 has to agree
with the polymorphic instances, so generalize `rprodMap`/`rprodMap_recip` to `.{u}` rather than pinning the new
`SymMonCat` instance to `.{0}`: normalize the outlier, do not special-case around it. The proofs are pointwise and
should generalize unchanged; verify with `./scripts/cap lake build AOP` before phase 4 proper.

Risk: low; mechanical. The only tedium is associator plumbing on nested products.

## Phase 5 — the bridge: CB ⟹ Allegory, modular law as a THEOREM (`diag/CB_Allegory.lean`)

Goal: the acceptance criterion. Every cartesian bicategory of relations yields Freyd's `Allegory`, so all of
`S2_10.lean`'s theorems (and everything downstream in AOP chapter 4) hold in the diagrammatic setting.

- `theorem semidistrib_of_lax`: `R(S ∩ T) ≤ RS ∩ RT` — from lax copy (42) + `comp_mono` + glb.
- `theorem modular_of_frobenius`: `RS ∩ T ≤ (R ∩ T S†) S`. This must be DERIVED, never assumed. Which axioms
  feed it: the Frobenius equation (41) is the engine — `Frobenius.pdf` p. 4 (proof plan of its Prop. 6) states
  "The Frobenius law implies the modular law [CW87, remark 2.9(ii)]" — supported by the adjunction inequations
  (37)–(40) (inserting/removing dots), the special law (phase 3), the snake lemmas, and monotonicity of `≫`/`⊗`.
- `def allegoryOfCartBicat (𝒞) [CartBicat 𝒞] : Allegory 𝒞` — `recip := conv`, `inter := convolution`; a `def`,
  not a global instance, to avoid diamonds with existing `Allegory` instances (precedent:
  `semiSimpleAllegory_of_tabular`, `Freyd/S2_10.lean:594`). Freyd's `modular` field takes the equality form
  `RS ∩ T = (RS ∩ T) ∩ (R ∩ TS°)S`; convert from the `≤` form as `S2_10`'s `modular_le` does in reverse.

MAIN TECHNICAL RISK of the whole plan: CW87 is not local ("unverified" in the assessment's source table), so the
Remark 2.9(ii) derivation must be reconstructed from scratch. Mitigations, in order: (1) phase 4 is already done,
so every candidate intermediate lemma can be falsified instantly in `RelSet` before attempting an abstract proof;
(2) phase 6's diagrams double as the proof-search notebook — each rewrite step is one picture; (3) the fallback
route in `Frobenius.pdf`'s Prop. 6 proof (via hom-poset meets + Lemma 4.3 "wrong way" + the Lemma 4.4 adjoint
forms) is equational and known to work. NOT acceptable as a fallback: adding modularity as a class field — that
would make the bridge circular; if truly stuck, stop and surface the blocker.

Acceptance: build green; `#print axioms Freyd.Diag.modular_of_frobenius` — none; and the composite check that
`allegoryOfCartBicat` applied to `RelSet`'s CB instance agrees with the hand-built `Allegory RelSet` on `inter`
and `recip` (via phase 4's agreement theorems).

## Phase 6 — Typst module + the first AOP diagrams (`Freyd/note/strdiag.typ`)

Goal: see AOP theorems as diagrams. cetz 0.3.4 (already the repo standard — `Freyd/note/1.272.typ` etc.).

Helpers (one module, reused by hand-written notes AND the phase-7 exporter): `wire`, `gbox` (labelled box), the
four Frobenius dots `copy`/`merge`/`discard`/`unit`, `cup`/`cap`, `conv` (box with both wires bent), `meet` (the
convolution combinator), `tape` (rounded wrapper + fork/join, for phase 8), `cut` (colour-switch region for
phase 9's complement). The AI-written `AllegoryStringDiagrams.typ` already contains working cetz code for the
first six — salvage the drawing code, discard the prose (it is not a source and must never be cited).

First diagrams, highest payoff first (chosen from what the repo's own AOP proofs actually use):

1. `map_shunt_left` / `map_shunt_right` (`AOP/A4_2.lean:239,221`) — B&dM's workhorse rule; diagrammatically the
   unit/counit triangle of Lemma 4.8's adjunction.
2. `Entire` / `Simple` / `Map` (`Freyd/S2_10.lean:408,417,420`) as (TOT)/(SV) with the four adjoint forms
   (46)–(49) — the map dictionary every derivation quotes.
3. `simple_dist_inter` (`Freyd/S2_10.lean:476`, §2.136) — eq. (3) tightened to equality.
4. the modular law (`Freyd/S2_10.lean:62`) with `modular_sym` / `modular_le_right` (`AOP/A4_1.lean`) — drawing
   it is the phase-5 debugging tool.
5. `dom` and `dom_UP` (`Freyd/S2_10.lean:322`, `AOP/A4_2.lean:147`) — the coreflexive-as-dot idiom.
6. `Tabulates` / `tabulates_monic_pair` (`Freyd/S2_10.lean:502,521`).
7. `le_div_iff` (`Freyd/S2_30.lean:54`) as a two-sided rule — both sides of the iff are drawable now; the
   residual as a first-class box waits for phase 9.

Acceptance: one demo page embedding all seven compiles with `typst compile`; visual conventions match the papers
(left-to-right = `≫`, vertical stacking = `⊗`, black dots = Frobenius structure).
Risk: low; cetz layout only.

## Phase 7 — tool (a): Lean → diagram exporter (`diag/tool/DiagExport.lean`, exe `diag-export`)

Goal: given a declaration name, emit the Typst/cetz picture of its *statement* (not its proof).

I/O contract: `./scripts/cap lake exe diag-export Freyd.Alg.simple_dist_inter` writes
`Freyd/note/generated/Freyd.Alg.simple_dist_inter.typ` (importing `../strdiag.typ`) and prints the path.
Mechanism: load the environment (ONE environment per process — the `lean-refactor` OOM lesson), look up
`ConstantInfo.type`, walk the `Expr`: `Cat.comp` → horizontal juxtaposition, `Allegory.inter` → `meet`,
`Allegory.recip` → `conv`, `⊑`/`le` → two canvases joined by `≤`, `dom` → its `1 ∩ RR°` picture, `graph f` and
any unrecognised subterm → an opaque labelled box. Terms are trees, so layout is compositional — no graph-layout
pass needed.

Hooks and precedent: CLI + `supportInterpreter = true` exe shape from `Freyd/tool/LeanRefactor.lean` +
`scripts/lean-refactor`; environment-walking from `scripts/ExtractGraph.lean` + `scripts/lean-graph`; register in
`lakefile.toml` as `[[lean_exe]] name = "diag-export", root = "diag.tool.DiagExport", supportInterpreter = true`;
add a `scripts/diag-export` wrapper.

Acceptance: exporter output for the seven phase-6 statements compiles under Typst and visually matches the
hand-drawn versions; `./scripts/cap lake build diag-export` green.
Risk: medium — pretty-layout quality; contained, since unknown subterms degrade gracefully to boxes.

## Phase 8 — the tape layer: `∪` and `⊥` (`diag/Tape.lean`)

Goal: the §2.2 operations, per `TapeDiagrams` — the one place union is genuinely diagrammatic.

- `class FbCbRig` (Def. 7.1): a rig category where `⊗` carries a `CartBicat` and `⊕` is a finite biproduct,
  plus the adjointness axioms of Fig. 2 (axioms for plain tapes are Fig. 1; the ordered layer Figs. 2–3).
- theorem: hom-sets acquire `∪` (via the `⊕`-codiagonal) and `⊥` (the zero arrow), and
  `distributiveAllegoryOfFbCb` extends phase 5's `def` to `DistributiveAllegory` (`Freyd/S2_20.lean`).
- `instance : FbCbRig RelSet` — `⊕ := Sum`, precedent `sumCop` (`AOP/A6_1_RelSet.lean:259`).
- Deferred: tapes as syntax (`TCB_Σ`, Example 6.12) and completeness (Thm. 7.5 / Cor. 7.8 — sound AND complete
  for the positive fragment of the calculus of relations, i.e. exactly Freyd §2.2); we take the axioms and
  soundness only. Kleene star / trace: named by the paper as future work; out of scope.

Acceptance: build green, axioms ⊆ {`propext`, `Quot.sound`}, `∪`-agreement with `DistributiveAllegory RelSet`.
Risk: high tedium — two interacting monoidal structures with distributors; scope strictly to what the `∪`/`⊥`
derivation consumes.

## Phase 9 — the fo layer: residuals and complement (`diag/FO.lean`)

Goal: the §2.31 operations, per `DiagrammaticAlgebraOfFirstOrderLogic` — residuals exist because the calculus leaves the monotone fragment
(an order-reversing generator plus a second composition; assessment note, "How this escapes the variance
obstruction").

- `class LinearBicat` (Def. 5.1, Fig. 4): second composition `,•` with its own identity, linear distributivities;
  closed (Def. 5.5): linear adjoints `(−)⊥`; `class CocartBicat` (Fig. 3); `class FOBicat` (Fig. 5 interactions).
- `lemma_5_4_residuation` (§5): `a ≤ b iff id° ≤ b ,• a⊥` — a numbered deliverable, stated under its own name.
- `RelSet` semantics, in a separate file `diag/RelSetFO.lean`: complement is `¬ R x y`, so the fo-instance NEEDS
  excluded middle — `Classical.choice` enters. Containment: the abstract layer stays axiom-free; the classical
  instance is quarantined in its own file with the axiom named in the header; the repo's constructive `div`
  (`AOP/A6_1_RelSet.lean:134`, a direct `∀`) remains the canonical division for AOP work, and the fo-layer
  residual is proved to agree with it classically.
- Deliberately NOT attempted: any Lean statement equating fo-bicategories with division/Peirce allegories — see
  open problems.

Acceptance: abstract layer builds with no axioms; `lemma_5_4_residuation` axiom-free; `RelSetFO` flagged.
Risk: high; scheduled last. Committed deliverables are the abstract classes + Lemma 5.4 only.

## The converse bridge direction (recorded, deferred)

Allegory ⟹ CB needs Freyd's unitary and pre-tabular conditions (book §2.148 for the unitary representation;
`UnitaryAllegory` at `Freyd/S2_10.lean:549`, `PreTabularAllegory` at `:556`): the tensor is rebuilt from
tabulations of `⊤` and products in `Map(𝒜)` (`Frobenius.pdf` Props. 2 and 6). The known correspondence is
cartesian bicategory ≃ unitary PRETABULAR allegory (`DiagrammaticAlgebraOfFirstOrderLogic` §10, citing Carboni–Walters) — no more than that.
A future `cartBicatOfUnitaryPretabular` is legal mathematics but serves no phase above; do not build it until a
consumer exists.

## Open problems — do not attempt yet

- `Λ` / power transpose (Freyd §2.4, B&dM ch. 4.6): needs the power object; none of the three calculi has it.
  Since `A R := R /ₛ ∋ b` (`AOP/A4_6.lean`), phase-9 division diagrams plus an opaque `∋` box can DISPLAY
  Λ-statements, but there is no diagrammatic axiomatisation to prove them in.
- folds, hylomorphisms, `μ`: absent from every language in the tower — these papers present theories and logical
  fragments, not recursion schemes. The tape paper names Kleene star via an `⊕`-trace as future work. Getting a
  hylo and a relational composite into one picture is the actual open problem of this programme.
- fo-bicategory ↔ division/Peirce allegory: explicitly open — `DiagrammaticAlgebraOfFirstOrderLogic` §10 only *suggests* the connection to
  Peirce allegories (Olivier–Serrato); never state it as a Lean theorem or instance.
- tapes' `∪` (second monoidal product) vs fo-bicategories' `∪` (cocartesian in one layer): nothing published
  reconciles the two presentations. Phases 8 and 9 stay independent class hierarchies; never merge them.
