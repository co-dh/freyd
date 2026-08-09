/-
  Freyd & Scedrov, *Categories and Allegories* §2.437.

  The one-object allegory `A` of RECURSIVELY ENUMERABLE relations on ℕ, and two
  classical corollaries.  Freyd:

    "Let A be the one-object allegory of recursively enumerable relations on the
     natural numbers.  … there exists a morphism T such that for any recipe for a
     recursively enumerable set A there exists n such that A = { m | n T m }.  …
     Hence A cannot be a division allegory.  … Thus there are recursively
     enumerable sets which are not recursive."

  This file builds:

  * **Layer 1** — the r.e. relations on ℕ form a one-object `Allegory`
    (`Freyd.Alg.Allegory REObj`).  A relation is r.e. when its graph, read through
    the Cantor pairing `cp`, is the domain of a total-recursive semi-test:
    `IsRE R := ∃ t, Recursive2 t ∧ ∀ a b, R a b ↔ ∃ y, t y (cp a b) = 0`.
    Closure under relational composition, intersection, converse and the diagonal
    is pure algebra on the recursive tests — the dovetailing is hidden in the
    `∃ y` projection.  Every allegory axiom is a relation identity (all of `Rel`
    satisfies them), proved by extensionality.

  * **Layer 2** — the universal morphism `T` (`reT`), r.e. via the universal
    machine `cU` of `Freyd.S2_153b_RecursiveModulus.universal_genuine`, together
    with its universality on r.e. SETS: every r.e. set is a row `{ m | n T m }`
    (`re_set_is_row_of_reT`).

  * **Layer 4** — the corollary `exists_re_not_recursive`: there is an r.e. set
    (`Kc`, the diagonal halting set of §1.572b) that is not recursive, by
    `K_not_recursive`.

  Layer 3 (`A` is not a division allegory) is discussed at the module tail: it is
  the §2.436 pre-power-allegory inconsistency and needs the map operation `R ↦ R̂`
  (an s-m-n / parametrization theorem), which is not yet in the repo; it is left
  open rather than asserted with a hole.

  MATHLIB-FREE.  Composition in DIAGRAM ORDER (`R ≫ S` = first `R` then `S`).
-/
module

public import Freyd.S2_153b_RecursiveModulus
public import Freyd.S2_31

namespace Freyd.REAlleg

open Freyd.Rcat Freyd.Alg

/-! ## Layer 1a: r.e. relations on ℕ and their closure -/

/-- The raw relational operations on ℕ (identity, composition in diagram order,
    converse, intersection, empty, union). -/
@[expose] public def relId (a b : Nat) : Prop := a = b
@[expose] public def relComp (R S : Nat → Nat → Prop) (a c : Nat) : Prop := ∃ b, R a b ∧ S b c
@[expose] public def relConv (R : Nat → Nat → Prop) (a b : Nat) : Prop := R b a
@[expose] public def relInter (R S : Nat → Nat → Prop) (a b : Nat) : Prop := R a b ∧ S a b
@[expose] public def relZero (_ _ : Nat) : Prop := False
@[expose] public def relUnion (R S : Nat → Nat → Prop) (a b : Nat) : Prop := R a b ∨ S a b

/-- A relation on ℕ is RECURSIVELY ENUMERABLE when its graph, seen through the
    Cantor pairing, is the domain of a total-recursive semi-test. -/
@[expose] public def IsRE (R : Nat → Nat → Prop) : Prop :=
  ∃ t : Nat → Nat → Nat, Recursive2 t ∧ ∀ a b, R a b ↔ ∃ y, t y (cp a b) = 0

/-! ### Elementary packing lemmas for the `∃`-projections -/

/-- A single existential splits along the Cantor pairing. -/
public theorem exists_split2 {P Q : Nat → Prop} :
    (∃ z, P (cfst z) ∧ Q (csnd z)) ↔ (∃ x, P x) ∧ (∃ y, Q y) := by
  constructor
  · rintro ⟨z, hp, hq⟩; exact ⟨⟨_, hp⟩, ⟨_, hq⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨cp x y, by rw [cfst_cp]; exact hx, by rw [csnd_cp]; exact hy⟩

/-- A single existential splits into a triple along nested Cantor pairing. -/
public theorem exists_split3 {P : Nat → Nat → Nat → Prop} :
    (∃ z, P (cfst z) (cfst (csnd z)) (csnd (csnd z))) ↔ (∃ a b c, P a b c) := by
  constructor
  · rintro ⟨z, h⟩; exact ⟨_, _, _, h⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨cp a (cp b c), by simp only [cfst_cp, csnd_cp]; exact h⟩

/-- A disjunctive existential splits along the Cantor pairing. -/
public theorem exists_split2_or {P Q : Nat → Prop} :
    (∃ z, P (cfst z) ∨ Q (csnd z)) ↔ (∃ x, P x) ∨ (∃ y, Q y) := by
  constructor
  · rintro ⟨z, hp | hq⟩
    · exact Or.inl ⟨_, hp⟩
    · exact Or.inr ⟨_, hq⟩
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · exact ⟨cp x 0, Or.inl (by rw [cfst_cp]; exact hx)⟩
    · exact ⟨cp 0 y, Or.inr (by rw [csnd_cp]; exact hy)⟩

/-- Sum of two naturals is 0 iff both are. -/
public theorem add_eq_zero {x y : Nat} : x + y = 0 ↔ x = 0 ∧ y = 0 := by omega

/-! ### Closure of `IsRE` -/

/-- The diagonal is r.e. -/
public theorem isRE_id : IsRE relId := by
  refine ⟨fun _ n => (cfst n - csnd n) + (csnd n - cfst n),
    Recursive2.ofSnd (Recursive1.add (Recursive1.sub Recursive1.cfst Recursive1.csnd)
      (Recursive1.sub Recursive1.csnd Recursive1.cfst)), ?_⟩
  intro a b
  simp only [relId, cfst_cp, csnd_cp]
  constructor
  · intro h; exact ⟨0, by omega⟩
  · rintro ⟨_, hy⟩; omega

/-- Converse of an r.e. relation is r.e. -/
public theorem isRE_conv {R : Nat → Nat → Prop} (hR : IsRE R) : IsRE (relConv R) := by
  obtain ⟨tR, hRc, hRs⟩ := hR
  refine ⟨fun y n => tR y (cp (csnd n) (cfst n)),
    Recursive2.comp2 hRc (show Recursive2 fun a _ => a from RecursiveV.proj 0)
      (Recursive2.ofSnd (Recursive1.comp2 Recursive2.cp Recursive1.csnd Recursive1.cfst)), ?_⟩
  intro a b
  show relConv R a b ↔ ∃ y, tR y (cp (csnd (cp a b)) (cfst (cp a b))) = 0
  simp only [relConv, cfst_cp, csnd_cp]
  exact hRs b a

/-- Intersection of two r.e. relations is r.e. -/
public theorem isRE_inter {R S : Nat → Nat → Prop} (hR : IsRE R) (hS : IsRE S) :
    IsRE (relInter R S) := by
  obtain ⟨tR, hRc, hRs⟩ := hR
  obtain ⟨tS, hSc, hSs⟩ := hS
  refine ⟨fun z n => tR (cfst z) n + tS (csnd z) n,
    Recursive2.comp2 Recursive2.add
      (Recursive2.comp2 hRc (Recursive2.ofFst Recursive1.cfst) (show Recursive2 fun _ b => b from RecursiveV.proj 1))
      (Recursive2.comp2 hSc (Recursive2.ofFst Recursive1.csnd) (show Recursive2 fun _ b => b from RecursiveV.proj 1)), ?_⟩
  intro a b
  show relInter R S a b ↔ ∃ z, tR (cfst z) (cp a b) + tS (csnd z) (cp a b) = 0
  simp only [relInter, add_eq_zero]
  rw [hRs a b, hSs a b]
  exact exists_split2.symm

/-- Composition (diagram order) of two r.e. relations is r.e. -/
public theorem isRE_comp {R S : Nat → Nat → Prop} (hR : IsRE R) (hS : IsRE S) :
    IsRE (relComp R S) := by
  obtain ⟨tR, hRc, hRs⟩ := hR
  obtain ⟨tS, hSc, hSs⟩ := hS
  refine ⟨fun z n => tR (cfst (csnd z)) (cp (cfst n) (cfst z))
      + tS (csnd (csnd z)) (cp (cfst z) (csnd n)),
    Recursive2.comp2 Recursive2.add
      (Recursive2.comp2 hRc (Recursive2.ofFst (Recursive1.comp Recursive1.csnd Recursive1.cfst))
        (Recursive2.comp2 Recursive2.cp (Recursive2.ofSnd Recursive1.cfst)
          (Recursive2.ofFst Recursive1.cfst)))
      (Recursive2.comp2 hSc (Recursive2.ofFst (Recursive1.comp Recursive1.csnd Recursive1.csnd))
        (Recursive2.comp2 Recursive2.cp (Recursive2.ofFst Recursive1.cfst)
          (Recursive2.ofSnd Recursive1.csnd))), ?_⟩
  intro a c
  show relComp R S a c ↔ ∃ z, tR (cfst (csnd z)) (cp (cfst (cp a c)) (cfst z))
      + tS (csnd (csnd z)) (cp (cfst z) (csnd (cp a c))) = 0
  simp only [cfst_cp, csnd_cp, add_eq_zero]
  rw [exists_split3 (P := fun b y1 y2 => tR y1 (cp a b) = 0 ∧ tS y2 (cp b c) = 0)]
  constructor
  · rintro ⟨b, hb⟩
    rw [hRs a b, hSs b c] at hb
    obtain ⟨⟨y1, h1⟩, ⟨y2, h2⟩⟩ := hb
    exact ⟨b, y1, y2, h1, h2⟩
  · rintro ⟨b, y1, y2, h1, h2⟩
    exact ⟨b, (hRs a b).mpr ⟨y1, h1⟩, (hSs b c).mpr ⟨y2, h2⟩⟩

/-- The empty relation is r.e. -/
public theorem isRE_zero : IsRE relZero := by
  refine ⟨fun _ _ => 1, Recursive2.ofFst (Recursive1.const 1), ?_⟩
  intro a b
  simp only [relZero]
  constructor
  · exact False.elim
  · rintro ⟨_, hy⟩; exact absurd hy (by omega)

/-- Union of two r.e. relations is r.e. -/
public theorem isRE_union {R S : Nat → Nat → Prop} (hR : IsRE R) (hS : IsRE S) :
    IsRE (relUnion R S) := by
  obtain ⟨tR, hRc, hRs⟩ := hR
  obtain ⟨tS, hSc, hSs⟩ := hS
  refine ⟨fun z n => tR (cfst z) n * tS (csnd z) n,
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 hRc (Recursive2.ofFst Recursive1.cfst) (show Recursive2 fun _ b => b from RecursiveV.proj 1))
      (Recursive2.comp2 hSc (Recursive2.ofFst Recursive1.csnd) (show Recursive2 fun _ b => b from RecursiveV.proj 1)), ?_⟩
  intro a b
  show relUnion R S a b ↔ ∃ z, tR (cfst z) (cp a b) * tS (csnd z) (cp a b) = 0
  simp only [relUnion, Nat.mul_eq_zero]
  rw [hRs a b, hSs a b]
  exact exists_split2_or.symm

/-! ## Layer 1b: the one-object allegory `A` of r.e. relations -/

/-- A morphism of `A`: an r.e. relation on ℕ. -/
@[expose] public def RERel : Type := {R : Nat → Nat → Prop // IsRE R}

/-- The single object `*` of the allegory. -/
public inductive REObj : Type where
  | star : REObj

/-- Extensionality for `RERel`: pointwise iff determines the morphism. -/
public theorem rerel_ext {R S : RERel} (h : ∀ a b, R.1 a b ↔ S.1 a b) : R = S :=
  Subtype.ext (funext fun a => funext fun b => propext (h a b))

/-- Bundled operations. -/
@[expose] public def reId : RERel := ⟨relId, isRE_id⟩
@[expose] public def reComp (R S : RERel) : RERel := ⟨relComp R.1 S.1, isRE_comp R.2 S.2⟩
@[expose] public def reConv (R : RERel) : RERel := ⟨relConv R.1, isRE_conv R.2⟩
@[expose] public def reInter (R S : RERel) : RERel := ⟨relInter R.1 S.1, isRE_inter R.2 S.2⟩

/-- The single object carries `RERel` as its endo-hom-set; composition is relational
    composition in diagram order, identity is the diagonal.  A genuine `Cat`. -/
@[expose] public instance instCat : Cat REObj where
  Hom _ _ := RERel
  id _ := reId
  comp R S := reComp R S
  id_comp R := rerel_ext fun a c => by
    simp only [reComp, reId, relComp, relId]
    exact ⟨fun ⟨b, hab, hbc⟩ => by subst hab; exact hbc, fun h => ⟨a, rfl, h⟩⟩
  comp_id R := rerel_ext fun a c => by
    simp only [reComp, reId, relComp, relId]
    exact ⟨fun ⟨b, hab, hbc⟩ => by subst hbc; exact hab, fun h => ⟨c, h, rfl⟩⟩
  assoc R S T := rerel_ext fun a d => by
    simp only [reComp, relComp]
    constructor
    · rintro ⟨c, ⟨b, hR, hS⟩, hT⟩; exact ⟨b, hR, c, hS, hT⟩
    · rintro ⟨b, hR, c, hS, hT⟩; exact ⟨c, ⟨b, hR, hS⟩, hT⟩

/-- The one-object `Allegory` of r.e. relations (§2.437).  Reciprocation is converse,
    intersection is relational meet; every axiom is a `Rel`-identity. -/
@[expose] public instance instAllegory : Allegory REObj where
  recip R := reConv R
  inter R S := reInter R S
  recip_recip R := rerel_ext fun a b => by simp only [reConv, relConv]
  recip_comp R S := rerel_ext fun a b =>
    ⟨fun ⟨c, hR, hS⟩ => ⟨c, hS, hR⟩, fun ⟨c, hS, hR⟩ => ⟨c, hR, hS⟩⟩
  recip_inter R S := rerel_ext fun a b => by simp only [reConv, reInter, relConv, relInter]
  inter_idem R := rerel_ext fun a b => by
    simp only [reInter, relInter]; exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  inter_comm R S := rerel_ext fun a b => by
    simp only [reInter, relInter]; exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  inter_assoc R S T := rerel_ext fun a b => by
    simp only [reInter, relInter]; exact and_assoc.symm
  semidistrib R S T := rerel_ext fun a c =>
    ⟨fun ⟨b, hR, hS, hT⟩ => ⟨⟨⟨b, hR, hS⟩, ⟨b, hR, hS, hT⟩⟩, ⟨b, hR, hT⟩⟩,
     fun ⟨⟨_, hmid⟩, _⟩ => hmid⟩
  modular R S T := rerel_ext fun a c =>
    ⟨fun ⟨⟨b, hR, hS⟩, hT⟩ => ⟨⟨⟨b, hR, hS⟩, hT⟩, b, ⟨hR, c, hT, hS⟩, hS⟩,
     fun ⟨h, _⟩ => h⟩

/-- The construction fires: `REObj` is a one-object allegory. -/
example : Allegory REObj := inferInstance

/-! ## Layer 2: the universal morphism `T`

  `universal_genuine` (`Freyd.S2_153b_RecursiveModulus`) gives a single unary code
  `cU` that, on the packed input `cp (Gödel# of c) r`, halts exactly with the values
  of `c` on `[r]`.  Its graph, sliced by a recipe number `n`, is Freyd's `T`. -/

/-- The fixed universal machine. -/
@[expose] public noncomputable def cU : RecCode 1 := Classical.choose universal_genuine

/-- The universal relation: `n T m` iff the universal machine halts on `cp n m`. -/
@[expose] public noncomputable def relT (n m : Nat) : Prop := ∃ w, Eval cU (fun _ => cp n m) w

/-- BRIDGE: a unary code halts on `[r]` iff the arithmetized checker accepts some
    witness — this converts the `Eval`-halting form of r.e. into the recursive-test
    form of `IsRE`.  (`acceptOn`, `acceptOn_sound/complete` from §2.153b.) -/
public theorem evalHalt_iff_acceptOn (c : RecCode 1) (r : Nat) :
    (∃ w, Eval c (fun _ => r) w) ↔ ∃ wit, acceptOn (cp (encCode c) r) wit = 1 := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨wit, hacc, _⟩ := acceptOn_complete (c := c) (r := r) (y := w) hw
    exact ⟨wit, hacc⟩
  · rintro ⟨wit, hwit⟩
    have hcf : cfst (cp (encCode c) r) = encCode c := cfst_cp _ _
    have hev := acceptOn_sound hwit (c := c) hcf
    rw [csnd_cp] at hev
    exact ⟨_, hev⟩

/-- `T` is a genuine r.e. relation. -/
public theorem isRE_relT : IsRE relT := by
  refine ⟨fun wit n => 1 - eqInd (acceptOn (cp (encCode cU) n) wit) 1,
    Recursive2.comp2 Recursive2.sub (Recursive2.ofFst (Recursive1.const 1))
      (Recursive2.comp2 Recursive2.eqInd
        (Recursive2.comp2 Recursive2_acceptOn
          (Recursive2.ofSnd (Recursive1.comp2 Recursive2.cp (Recursive1.const (encCode cU))
            (show Recursive1 fun n => n from RecursiveV.proj 0))) (show Recursive2 fun a _ => a from RecursiveV.proj 0))
        (Recursive2.ofFst (Recursive1.const 1))), ?_⟩
  intro a b
  show relT a b ↔ ∃ y, 1 - eqInd (acceptOn (cp (encCode cU) (cp a b)) y) 1 = 0
  have hbridge := evalHalt_iff_acceptOn cU (cp a b)
  refine (show relT a b ↔ ∃ wit, acceptOn (cp (encCode cU) (cp a b)) wit = 1 from hbridge).trans ?_
  refine exists_congr fun wit => ?_
  constructor
  · intro h; rw [h, eqInd_eq rfl]
  · intro h
    by_cases hx : acceptOn (cp (encCode cU) (cp a b)) wit = 1
    · exact hx
    · rw [eqInd_ne hx] at h; omega

/-- The universal morphism `T` of `A`. -/
@[expose] public noncomputable def reT : RERel := ⟨relT, isRE_relT⟩

/-! ### Universality of `T` on r.e. sets -/

/-- An r.e. SET: the domain (through a code) of a partial-recursive semi-decision. -/
def IsREset (S : Nat → Prop) : Prop :=
  ∃ c : RecCode 1, ∀ n, S n ↔ ∃ w, Eval c (fun _ => n) w

/-- A recursive SET: decided by a total-recursive 0/1 characteristic function. -/
def IsRecursiveSet (S : Nat → Prop) : Prop :=
  ∃ χ : Nat → Nat, Recursive1 χ ∧ ∀ n, S n ↔ χ n = 1

/-- **§2.437 universality of `T`**: every r.e. set `S` is a row `{ m | n T m }`.
    The recipe `n` is the Gödel number of any code enumerating `S`. -/
theorem re_set_is_row_of_reT {S : Nat → Prop} (hS : IsREset S) :
    ∃ n, ∀ m, S m ↔ relT n m := by
  obtain ⟨c, hc⟩ := hS
  refine ⟨encCode c, fun m => ?_⟩
  rw [hc m]
  show (∃ w, Eval c (fun _ => m) w) ↔ ∃ w, Eval cU (fun _ => cp (encCode c) m) w
  exact exists_congr fun w => (Classical.choose_spec universal_genuine c m w).symm

/-! ## Layer 4: an r.e. set that is not recursive (§2.437 corollary)

  If complements of r.e. sets were r.e. then `A` would be boolean, hence a division
  allegory (the §2.436 route).  Freyd's conclusion is that some r.e. set is not
  recursive.  We deliver it directly: the diagonal halting set `Kc` of §1.572b is
  r.e. (its accept predicate `acceptN` is a total-recursive semi-test) but not
  recursive (`K_not_recursive`). -/

/-- The domain of a total-recursive semi-test is an r.e. set: `μ`-search of the test
    gives a code halting exactly on the domain. -/
theorem muDomain {t : Nat → Nat → Nat} (ht : Recursive2 t) :
    ∃ c : RecCode 1, ∀ n, (∃ w, Eval c (fun _ => n) w) ↔ (∃ y, t y n = 0) := by
  obtain ⟨ct, hct⟩ := ht
  refine ⟨.mu ct, fun n => ?_⟩
  constructor
  · rintro ⟨w, hw⟩
    cases hw with
    | mu r hy _ =>
      refine ⟨w, ?_⟩
      have hval := hct (vcons w (fun _ => n))
      simp only [vcons_zero, vcons_one] at hval
      exact (Eval.det hy hval).symm
  · rintro ⟨y, hy⟩
    obtain ⟨y0, hmem, hmin⟩ : ∃ y0, t y0 n = 0 ∧ ∀ i, i < y0 → ¬ t i n = 0 :=
      ⟨theLeast (fun y => t y n = 0) ⟨y, hy⟩,
        theLeast_mem (fun y => t y n = 0) ⟨y, hy⟩, theLeast_min (fun y => t y n = 0) ⟨y, hy⟩⟩
    refine ⟨y0, Eval.mu (fun i => t i n - 1) ?_ (fun i hi => ?_)⟩
    · have hval := hct (vcons y0 (fun _ => n))
      simp only [vcons_zero, vcons_one] at hval
      rw [hmem] at hval; exact hval
    · show Eval ct (vcons i (fun _ => n)) (t i n - 1 + 1)
      have hval := hct (vcons i (fun _ => n))
      simp only [vcons_zero, vcons_one] at hval
      rw [show t i n - 1 + 1 = t i n from by have := hmin i hi; omega]
      exact hval

/-- The diagonal halting set `Kc` is r.e. -/
theorem isREset_Kc : IsREset Kc := by
  obtain ⟨c, hc⟩ := muDomain (t := fun wit e => 1 - eqInd (acceptN e wit) 1)
    (Recursive2.comp2 Recursive2.sub (Recursive2.ofFst (Recursive1.const 1))
      (Recursive2.comp2 Recursive2.eqInd (Recursive2.swap Recursive2.acceptN)
        (Recursive2.ofFst (Recursive1.const 1))))
  refine ⟨c, fun e => ?_⟩
  rw [hc e]
  show (∃ wit, acceptN e wit = 1) ↔ ∃ y, 1 - eqInd (acceptN e y) 1 = 0
  refine exists_congr fun wit => ?_
  constructor
  · intro h; rw [h, eqInd_eq rfl]
  · intro h
    by_cases hx : acceptN e wit = 1
    · exact hx
    · rw [eqInd_ne hx] at h; omega

/-- **§2.437 corollary**: there exists a recursively enumerable set that is not
    recursive. -/
theorem exists_re_not_recursive : ∃ S : Nat → Prop, IsREset S ∧ ¬ IsRecursiveSet S := by
  refine ⟨Kc, isREset_Kc, ?_⟩
  rintro ⟨χ, hχ, hspec⟩
  exact K_not_recursive ⟨χ, hχ, hspec⟩

end Freyd.REAlleg
