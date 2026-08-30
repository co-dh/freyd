/-
  Toward a PURE-FUSION maximum-segment-sum (MSS) derivation, over snoc-lists.

  The classical Bird–de Moor MSS derivation is
      mss  = max · map sum · segs
      segs = concat · map inits · tails
  and its calculational heart is HORNER'S RULE, which replaces `max · map sum · (init/tail
  segments)` by a single scan whose step algebra is `a ⊗ x = (a + x) ↑ 0` (add, then clamp
  at `0`).  This file carries the pure-FUSION route as far as the current mathlib-free
  infrastructure genuinely allows, using the refinement fusion law `comp_le_relCata`
  (Bird–de Moor (6.5), already in `AOP.A6_2`) and the equational `cata_fusion` (`AOP.Deriv1`).

  What is DERIVED here (all Sorry-free, over `SnocList Unit Int`):

  * `mssuf` — the Horner max-suffix-sum fold, defined as the catamorphism of the algebra
    `[ _ ↦ 0 , (a,x) ↦ (a+x) ↑ 0 ]`; its recursion equations `mssuf_wrap`/`mssuf_snoc` are
    delivered (definitionally) by the catamorphism engine, not written by hand.

  * `Ssuf` — the NONDETERMINISTIC suffix-sum relation, the relational catamorphism of the
    algebra `[ _ ↦ {0} , (a,x) ↦ {a+x, 0} ]`; `Ssuf` relates a list to any of its suffix
    sums (the empty suffix contributing `0`).

  * `mssuf_le_Ssuf` — **ACHIEVABILITY by pure fusion**: `mssuf ⊑ Ssuf`.  The deterministic
    Horner algebra POINTWISE-refines the nondeterministic one (`imax (a+x) 0` is always one
    of `a+x`, `0`), so `relCata`-monotonicity (`relCata_mono`, itself built on the least-
    prefixed-point law `relCata_le_of_prefixed`) lifts that to the folds.  No induction on
    lists: the Horner fold is shown to always return an ACTUAL suffix sum by fixed-point
    reasoning alone.

  * `mapSnoc` + `map_reduce_fusion` — **the MAP-PROMOTION law** `map f · reduce ψ = cata ψ'`
    the MSS derivation needs (Bird's "map promotion"), derived from the equational
    `cata_fusion`.  `mapSnoc f` is the element-map catamorphism; `map_reduce_fusion` fuses it
    into any downstream catamorphism `cataR ψ` by relabelling the element slot of `ψ`.

  The remaining GAP to the full point-free `mss` is stated precisely at the end of the file
  (`GAP` section): which combinator relators (`inits`/`tails`/`concat`) and promotion law
  (`reduce · concat = reduce · map reduce`) are missing, with their exact Lean types.  The
  OPTIMISATION half — that the Horner fold DOMINATES every suffix sum, i.e. computes the
  `≤`-maximum — is already fully proved via the greedy theorem in `leet.L53`
  (`solve_correct`) and `AOP.A7_4_Horner`; the point of this file is the FUSION route.

  Mathlib-free.  `#print axioms` at the end of the module.
-/
module

public import AOP.Deriv1

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Fuse

open Freyd Freyd.Alg Freyd.Alg.RelSet.SL

/-! ## Integer `max` (mathlib-free) -/

/-- `imax a b` = the larger of `a`, `b`.  Local (the `L*` leetcode files each keep their own
    copy of this one-liner; there is no shared home to reuse). -/
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ############################################################################
    ## The Horner max-suffix-sum fold `mssuf`
    ############################################################################ -/

/-- The Horner algebra `[ _ ↦ 0 , (a,x) ↦ (a+x) ↑ 0 ]` as a function `F Int → Int`. -/
def mssufAlg : (Fobj Unit Int (⟨Int⟩ : RelSet.{0})).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr p => imax (p.1 + p.2) 0

/-- The Horner max-suffix-sum fold: the catamorphism of `mssufAlg`. -/
def mssuf : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0}) := cataR (graph mssufAlg)

/-- Base equation, delivered by the catamorphism engine (definitional). -/
theorem mssuf_wrap (u : Unit) (r : Int) : mssuf (SnocList.wrap u) r ↔ r = 0 := Iff.rfl

/-- Step equation = Horner's rule for `max`: extend the running best-ending-here by the new
    element and clamp at `0`.  Definitional. -/
theorem mssuf_snoc (xs : SnocList Unit Int) (x r : Int) :
    mssuf (SnocList.snoc xs x) r ↔ ∃ r', mssuf xs r' ∧ r = imax (r' + x) 0 := Iff.rfl

/-! ############################################################################
    ## The nondeterministic suffix-sum relation `Ssuf`
    ############################################################################ -/

/-- The nondeterministic suffix-sum algebra `[ _ ↦ {0} , (a,x) ↦ {a+x, 0} ]`: from a running
    suffix sum `a` and a new last element `x`, either extend the suffix (`a+x`) or start the
    empty suffix afresh (`0`). -/
def SsufAlg : Fobj Unit Int (⟨Int⟩ : RelSet.{0}) ⟶ (⟨Int⟩ : RelSet.{0}) :=
  fun u v => match u with
    | Sum.inl _ => v = 0
    | Sum.inr p => v = p.1 + p.2 ∨ v = 0

/-- The suffix-sum relation: `Ssuf xs v` iff `v` is the sum of some (possibly empty) suffix of
    `xs`.  Defined as the relational catamorphism of `SsufAlg`. -/
def Ssuf : dSL Unit Int ⟶ (⟨Int⟩ : RelSet.{0}) := cataR SsufAlg

theorem Ssuf_wrap (u : Unit) (r : Int) : Ssuf (SnocList.wrap u) r ↔ r = 0 := Iff.rfl

theorem Ssuf_snoc (xs : SnocList Unit Int) (x r : Int) :
    Ssuf (SnocList.snoc xs x) r ↔ ∃ r', Ssuf xs r' ∧ (r = r' + x ∨ r = 0) := Iff.rfl

/-! ############################################################################
    ## Achievability by pure fusion:  `mssuf ⊑ Ssuf`
    ############################################################################ -/

/-- The deterministic Horner algebra POINTWISE-refines the nondeterministic suffix-sum
    algebra: `imax (a+x) 0` is always one of `a+x`, `0`, and `0 = 0` on the leaf. -/
theorem mssufAlg_le_SsufAlg :
    (graph mssufAlg : Fobj Unit Int (⟨Int⟩ : RelSet.{0}) ⟶ (⟨Int⟩ : RelSet.{0})) ⊑ SsufAlg := by
  rw [le_iff]
  rintro u v hv
  cases u with
  | inl u0 =>
      -- `hv : v = mssufAlg (inl _) = 0`;  goal `SsufAlg (inl _) v = (v = 0)`
      show v = 0
      exact hv
  | inr p =>
      -- `hv : v = imax (p.1+p.2) 0`;  goal `v = p.1+p.2 ∨ v = 0`
      show v = p.1 + p.2 ∨ v = 0
      rcases imax_eq_or (p.1 + p.2) 0 with h | h
      · exact Or.inl (hv.trans h)
      · exact Or.inr (hv.trans h)

/-- **ACHIEVABILITY, by pure fusion.**  The Horner max-suffix fold always returns an ACTUAL
    suffix sum: `mssuf ⊑ Ssuf`.  Derived with no induction on lists — the pointwise algebra
    refinement `mssufAlg_le_SsufAlg` is lifted to the folds by `relCata`-monotonicity
    (`relCata_mono`, built on the least-prefixed-point law `relCata_le_of_prefixed`). -/
theorem mssuf_le_Ssuf : mssuf ⊑ Ssuf := by
  show cataR (graph mssufAlg) ⊑ cataR SsufAlg
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact relCata_mono (initial Unit Int) mssufAlg_le_SsufAlg

/-! ############################################################################
    ## Map promotion (map-reduce fusion), from the equational `cata_fusion`
    ############################################################################ -/

/-- The element-map algebra `[ u ↦ wrap u , (xs,x) ↦ snoc xs (f x) ]` as a function into the
    list itself; `mapSnoc f` is its catamorphism, i.e. `map f`. -/
def mapAlg (f : Int → Int) :
    (Fobj Unit Int (dSL Unit Int)).carrier → SnocList Unit Int
  | Sum.inl u => SnocList.wrap u
  | Sum.inr p => SnocList.snoc p.1 (f p.2)

/-- `map f` over snoc-lists, as the catamorphism of `mapAlg f`. -/
def mapSnoc (f : Int → Int) : dSL Unit Int ⟶ dSL Unit Int := cataR (graph (mapAlg f))

/-- Relabel the element slot of an algebra `ψ` by `f`: `[ u ↦ ψ (inl u) , (r,x) ↦ ψ (r, f x) ]`.
    The `F`-shape action of `f` on the element component. -/
def relabel (f : Int → Int) {c : RelSet.{0}} (ψ : Fobj Unit Int c ⟶ c) :
    Fobj Unit Int c ⟶ c :=
  fun u v => match u with
    | Sum.inl u0 => ψ (Sum.inl u0) v
    | Sum.inr p => ψ (Sum.inr (p.1, f p.2)) v

/-- The fusion condition for map promotion: pushing `cataR ψ` through the map algebra equals
    the `F`-lifted `cataR ψ` followed by the element-relabelled algebra. -/
theorem mapAlg_fusion_cond (f : Int → Int) {c : RelSet.{0}} (ψ : Fobj Unit Int c ⟶ c) :
    graph (mapAlg f) ≫ cataR ψ
      = (F Unit Int).map (cataR ψ) ≫ relabel f ψ := by
  apply hom_ext
  rintro u r
  cases u with
  | inl u0 =>
      constructor
      · rintro ⟨_, rfl, hwr⟩
        -- `hwr : cataR ψ (mapAlg f (inl u0)) r`  (= `ψ (inl u0) r`)
        exact ⟨Sum.inl u0, rfl, hwr⟩
      · rintro ⟨v, hv, hvr⟩
        cases v with
        | inl v0 =>
            -- `hv : Fmap (cataR ψ) (inl u0) (inl v0) = (u0 = v0)`
            cases hv
            exact ⟨SnocList.wrap u0, rfl, hvr⟩
        | inr vp => exact (hv : False).elim
  | inr p =>
      constructor
      · rintro ⟨_, rfl, hwr⟩
        -- `hwr : cataR ψ (snoc p.1 (f p.2)) r = ∃ s, cataR ψ p.1 s ∧ ψ (inr (s, f p.2)) r`
        obtain ⟨s, hs, hsr⟩ := hwr
        exact ⟨Sum.inr (s, p.2), ⟨hs, rfl⟩, hsr⟩
      · rintro ⟨v, hv, hvr⟩
        cases v with
        | inl v0 => exact (hv : False).elim
        | inr vp =>
            -- `hv : cataR ψ p.1 vp.1 ∧ p.2 = vp.2`;  `hvr : ψ (inr (vp.1, f vp.2)) r`
            obtain ⟨hs, hx⟩ := hv
            refine ⟨SnocList.snoc p.1 (f p.2), rfl, vp.1, hs, ?_⟩
            -- goal: `ψ (inr (vp.1, f p.2)) r`;  rewrite `p.2 → vp.2` to match `hvr`
            rw [hx]
            exact hvr

/-- **MAP PROMOTION (map-reduce fusion).**  Post-composing any catamorphism `cataR ψ` after the
    element-map `mapSnoc f` is itself a catamorphism — of the element-relabelled algebra
    `relabel f ψ`: `map f · reduce ψ = cata (relabel f ψ)`.  This is Bird's map-promotion law,
    derived here purely from the equational fold-fusion `cataR_fusion` (`AOP.Deriv1`), no
    induction. -/
theorem map_reduce_fusion (f : Int → Int) {c : RelSet.{0}} (ψ : Fobj Unit Int c ⟶ c) :
    mapSnoc f ≫ cataR ψ = cataR (relabel f ψ) :=
  Deriv.cataR_fusion (graph (mapAlg f)) (cataR ψ) (relabel f ψ) (mapAlg_fusion_cond f ψ)

/-! ############################################################################
    ## GAP to the full point-free `mss` (precise, honest)
    ############################################################################

  What is PROVED above: the Horner fold `mssuf` and its ACHIEVABILITY `mssuf ⊑ Ssuf` by pure
  fusion, and the MAP-PROMOTION law `map_reduce_fusion`.  What remains for the FULL point-free
  `mss = max · map sum · concat · map inits · tails` (all mathlib-free, over `SnocList`):

  1. **`tails`, `inits` as relators / catamorphisms.**  Missing.  Required type, e.g.
        `tails : dSL Unit Int ⟶ dSL Unit (SnocList Unit Int)`
        `inits : dSL Unit Int ⟶ dSL Unit (SnocList Unit Int)`
     each a catamorphism of a scan-style algebra.  (`AOP.A5_6_ListCombinators` has `prefixR`
     and `subseq` as RELATIONS but not the list-of-all-prefixes list-VALUED `inits`/`tails`.)

  2. **`concat` and the REDUCE-PROMOTION law.**  `AOP.A5_6_ListCombinators.cconcat` exists
     for cons-lists; the promotion law needed is
        `reduce ⊕ · concat = reduce ⊕ · map (reduce ⊕)`      (Bird p. ~119)
     as a fold identity over a SECOND functor layer `F Unit (SnocList Unit Int)` (lists of
     lists).  It is provable from `cataR_fusion` ONCE `concat`/`map` over that layer are
     defined, but that layer is not built.

  3. **The Horner step, EQUATIONAL form.**  `max · map sum · inits = ⦇ mssufAlg ⦈ = mssuf`.
     The `⊑` half is `mssuf_le_Ssuf` (achievability, above); the reverse (DOMINATION, i.e.
     `mssuf` is the `≤`-MAX suffix sum) is the greedy content, ALREADY proved via the greedy
     theorem in `leet.L53.solve_correct` / `AOP.A7_4_Horner.horner_correct`.  Restating it
     as a pure `comp_le_relCata` step needs the est universal property
     `le_Λ_comp_est_iff` (`A7_4_Horner`) plus the monotonicity of `mssufAlg` on `≤`
     (`MonotonicAlg (graph mssufAlg) (leR : Int ⟶ Int)`), which is exactly the greedy
     hypothesis — so this route re-derives, rather than avoids, the greedy theorem.

  Bottom line: the pure-fusion route DERIVES the Horner fold, its achievability, and map
  promotion Sorry-free; the missing pieces are the list-of-lists combinator layer
  (`inits`/`tails`/`concat`/`map` over `SnocList (SnocList ...)`) and the reduce-promotion law,
  whose exact types are listed above. -/

end Freyd.Alg.RelSet.Fuse
