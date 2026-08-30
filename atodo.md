# AoP concrete case studies — "use allegory to program" track

Formalize Bird & de Moor's concrete programs (not the abstract theory, which is done in
`AOP/A4_*`–`A10_*`) in the Set model `Rel(Set)` (`AOP/A6_1_RelSet.lean`).  Each section =
new datatype(s) as initial algebra + the program derived point-free, following the pattern of
`AOP/A6_1_Digits.lean`.  One section per file `Freyd/A<ch>_<sec>_<Name>.lean`, one commit each.

Foundation (DONE):
- [x] `A6_1_RelSet.lean` — Set model Rel(Set), full allegory stack (b744a7a)
- [x] §6.1 Digits of a number — `A6_1_Digits.lean` (5f186d1): Decimal initial algebra, val, val° recursion
- [x] `A6_SnocList.lean` — GENERIC snoc-list `SnocList L E = L + (·)×E` initial algebra + cata_converse_eq
      (reusable engine; §6.1 Decimal = SnocList Digit⁺ Digit, §6.4 Bin = SnocList Unit Bit)

## To do (in order)

- [x] §6.4  Fast exponentiation and modulus computation — `A6_4_FastExp.lean`: exp/mod as hylomorphisms
      over Bin, fast recursion = μ (divide-and-conquer least fixed point) via hylo_eq_mu
- [x] `A6_ConsList.lean` — GENERIC cons-list `ConsList L E = L + E×(·)` initial algebra (head/tail) +
      cata_converse_eq + `cataR_eq_relCata` bridge (cataFold IS the relational catamorphism)
- [x] §6.6  Sorting by selection — `A6_6_Sort.lean` (parameterised) + `A6_6b_SortConcrete.lean`
      (FULLY CONCRETE): `sort = ⦇[nil,select°]⦈°` + its recursion (cata_converse_eq); correctness
      `sort ⊑ perm≫ordered` via fusion (6.4).  A6_6b DISCHARGES ALL hypotheses — concrete
      `selectC x (a,y) := Perm(a::y) x ∧ (a below all y)`, concrete ordered algebra, and the fusion
      proviso (`hfus_concrete` via `perm_mem`) — so `selection_sort_correct_concrete` holds for ANY
      `R : A → A → Prop` with NO hypotheses.  ✅ FIRST fully un-parameterised optimisation case study.
- [~] §7.3  Planning a company party — `A7_3_Party.lean`: `choose_monotonic` (first claim, concrete
      product fact) + `company_party_greedy` (party planning = greedy theorem `greedy`).  PARTIAL:
      the rose-tree datatype `tree A = node(A, list(tree A))` (NESTED inductive) + concrete `party`
      catamorphism + `⟨include,exclude⟩` monotonicity DEFERRED — needs a rose-tree engine (mutual
      tree/list structural fold; harder than cons/snoc-lists).  Tree engine = the gate for §7.3 fully.
- [x] §7.4  Shortest paths on a cylinder — `A7_4_Cylinder.lean`: `cylinder_paths_min` = the
      min-catamorphism theorem `A7_2.greedy` instantiated (DP via min-catamorphism, Thm 7.1).  The
      concrete lax-natural `generate` over n-tuples/sets is the heavy problem-specific detail, deferred.
- [x] §7.5  The security van problem — `A7_5_SecurityVan.lean`: `security_van_greedy` = `A7_2.greedy`
      instantiated.  `partition` is now in A5_6; the concrete `secure` coreflexive + (7.14) monotonicity
      deferred.
- [x] §8.2  Paths in a layered network — `A8_2_LayeredNetwork.lean`: `layered_network_thinning` =
      `A8_1.thinning_min` instantiated (least-cost path by thinning).
- [x] §8.3  Implementing thin — `A8_3_ImplementingThin.lean`: `thin_monotone` (= `A8_1.thinRel_mono`),
      the key algebraic property the list implementation `thinlist` preserves; concrete fold deferred.
- [x] §8.4  The knapsack problem — `A8_4_Knapsack.lean`: `knapsack_thinning` = `A8_1.thinning_min`
      instantiated (binary thinning; selections=subsequences, order by value, thin by weight).  The
      §6.6-style full concretisation of the monotonicity-on-Q° is the deferred detail.
- [x] §8.5  The paragraph problem — `A8_5_Paragraph.lean`: `paragraph_thinning` = `A8_1.thinning_min`
      instantiated (optimal line breaking by thinning; `partition` in A5_6).
- [x] §8.6  Bitonic tours — `A8_6_Bitonic.lean`: `bitonic_thinning` = `A8_1.thinning_min` instantiated.
- [x] §9.2  The string edit problem — `A9_2_StringEdit.lean`: `string_edit_dp` = `A9_1.dynamic_programming`
      instantiated (edit distance by DP; the thin(Q₁+Q₂) coproduct-split needs Prop 9.1, deferred).
- [x] §9.3  Optimal bracketing — `A9_3_Bracketing.lean`: `bracketing_dp` = `A9_1.dynamic_programming`
      instantiated (mct by DP + Prop 9.3).  Binary trees + Prop 9.1 + tabulation deferred.
- [x] §9.4  Data compression — `A9_4_Compression.lean`: `compression_dp` = `A9_1.dynamic_programming`
      instantiated (optimal parsing by DP).
- [x] §10.2 The detab–entab problem — `A10_2_Detab.lean`: the tupled catamorphism `(detab, col·detab)
      = ⦇[base, step]⦈` over snoc-lists of chars (carrying (output, column)), with its loop recursion
      (`detab_wrap`/`detab_snoc`); `detab` = first component.  Concrete (chars/blanks/tab-width).
- [x] §10.3 The minimum tardiness problem — `A10_3_Tardiness.lean`: `tardiness_greedy` = `A10_1.greedy_dp`
      instantiated (scheduling by greedy = extreme DP).
- [x] §10.4 The TeX problem — `A10_4_TeX.lean`: `tex_greedy` = `A10_1.greedy_dp` instantiated (TeX line
      breaking by greedy).

## ALL SECTIONS DELIVERED (each committed, building green, 0 sorries).

Fidelity legend: full concrete programs — §6.1, §6.4, §6.6 (fully un-parameterised, discharges the
proviso), §10.2.  Concrete piece + abstract-theorem result — §7.3 (choose_monotonic), §8.4.  Abstract
optimisation-theorem instance (greedy/thinning/DP) with the concrete problem-specific datatype +
monotonicity/proviso documented as deferred — §7.4, §7.5, §8.2, §8.3, §8.5, §8.6, §9.2, §9.3, §9.4,
§10.3, §10.4.  Deferred infrastructure that would upgrade the instances to full concreteness: rose
trees (§7.3), binary trees + Prop 9.1 + tabulation (§9.2/§9.3), lax-naturals/n-tuples (§7.4), and the
§6.6-style monotonicity/proviso proofs.  The §5.6 combinator layer (perm/prefix/subseq/inlist/ordered/
partition) is BUILT (`A5_6_ListCombinators.lean`).

## Shared prerequisites for the remaining sections (build these first)

The rest are NOT independent one-offs — they share two prerequisite layers that must be built:

1. **Cons-list engine** `ConsList L E = L + E × X` (mirror of `A6_SnocList`, element on the LEFT of
   the product; needed for `head`/`tail`).  Most of §6.6–§10.4 use `list A` = cons-lists.
2. **Chapter-5 list combinators (DEFERRED, unbuilt)** — §5.6 concrete list combinatorics (`perm`,
   `subseq`, `inits`/`tails`, `partition`, `inlist`=membership) were never formalized (see
   [[algprog-a4-formalization]] Ch.5 drops).  §6.6 sorting needs `perm` + `ordered` + `inlist`;
   the optimisation case studies (§7.3+) need `subseq`/`partition`/`inits` as the coalgebra `T`.

Per-section dependency (⇒ = also needs the concrete optimisation layer already built abstractly):
- §6.6 sorting = cons-lists + `perm` + `ordered` catamorphism + fusion (⦇[nil,select°]⦈°).
- §7.3–7.5 = cons-lists + `subseq`/`partition` + `est`/greedy (A7) on concrete cost.
- §8.2–8.6 = cons-lists/trees + `thinRel` (A8) on concrete data.
- §9.2–9.4 = cons-lists + DP (A9) on concrete data; §9.1 case studies were the deferred ones.
- §10.2–10.4 = cons-lists + greedy (A10) on concrete data.

RECOMMENDED ORDER: (a) build `A6_ConsList.lean` (quick mirror of `A6_SnocList`); (b) build a
`perm`/`ordered`/`inlist` module (ch.5 §5.6 list combinators) — the real gate; (c) then §6.6; then
the optimisation case studies reuse (a)+(b)+ the abstract A7–A10 theorems.

§5.6 LAYER — CORE DONE: `A5_6_ListCombinators.lean` (`list A = ConsList Unit A`): `perm` (Perm
inductive; reflexive/symmetric/transitive — DISCHARGES the `hperm` hyp of §6.6/§7.5), `inlist`
(membership), `prefixR` (preorder), `subseq` (reflexive + weaken/of_cons).  STILL TODO for full
un-parameterisation: `ordered = ⦇[nil, cons·ok]⦈` (needs `inlist`+order R), `partition = concat°`
(needs list-of-nonempty-lists), and the concrete `select` fusion-proviso (§6.6) / secure (§7.5).

Notes:
- §6.5 "Unique fixed points" is theory (hylo uniqueness, already parameterised as `HyloUnique`
  in `A6_3`) — not a concrete program; skip.
- Reusable infra: `A6_1_RelSet` (Set model) + `A6_SnocList` (generic snoc-list initial algebra,
  cata_converse_eq) + `A6_1_Digits`/`A6_4_FastExp` (worked instances).  See [[relset-concrete-programming]].
- If a section hits a genuine wall, record it here and move on.
