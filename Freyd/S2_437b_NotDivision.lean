/-
  Freyd & Scedrov, *Categories and Allegories* §2.437 — Layer 3.

  The one-object allegory `A` of recursively-enumerable relations on ℕ (built in
  `Freyd.S2_437_REAllegory`) is NOT a division allegory.

  Freyd's argument.  The universal morphism `T` (`reT`) has the s-m-n property:
  for any morphism `R` there is a MAP `R̂` (the "parametrization / recipe map")
  with
        (i)   `1 ⊑ R̂ R̂°`   (entire),
        (ii)  `R̂ T ⊑ R`,
        (iii) `R̂° R ⊑ T`.
  If `A` were a DIVISION allegory, take `R := 𝟘 / (1 ∩ T)` (the §2.436 diagonal).
  The four containments collapse `1 = 𝟘` (this is §2.438 `godel_collapse`).  But
  `A` is non-trivial (`id ≠ 𝟘`, the diagonal relation contains `(0,0)`, the empty
  relation does not).  Contradiction.

  ## What is new here (the genuine assembly)

  * **s-m-n** — the ONE piece not already in the repo.  From a recursive test `t`
    for `R` (with `R a c ↔ ∃ y, t y (cp a c) = 0`) and a code `ct` for `t`, we
    build a code `smnCode ct a : RecCode 1` that on input `c` searches for a
    witness `y` with `t y (cp a c) = 0`; it converges iff `R a c`.  Its Gödel
    number `smnNum ct a = encCode (smnCode ct a)` is TOTAL RECURSIVE in `a` (the
    only `a`-dependence is a `constCode 2 a` subterm, so `smnNum` is a primitive
    recursion over the encoding), giving `relT (smnNum ct a) c ↔ R a c`.

  * **`hatWitness_of_code`** — the MAP `R̂` is the graph of `smnNum ct`; the three
    §2.437 containments (i)–(iii) follow from the correctness `relT (f a) c ↔ R a c`
    and the fact that `f` is a total function.  This assembles §2.438's
    `HatWitness` for ANY r.e. `R`.

  * **`not_division`** — assuming a right-division operation on `A` (equivalently,
    that `A` is a division allegory), the §2.436 diagonal `𝟘/(1∩T)` supplies the
    §2.438 `GodelHyp`, and `godel_collapse` forces `id = 𝟘`, contradicting
    `reId_ne_zero`.

  MATHLIB-FREE.  Composition DIAGRAM ORDER.  Reuses `Freyd.S2_437_REAllegory`,
  `Freyd.S2_438_Godel` (`HatWitness`/`GodelHyp`/`godel_collapse`) and
  `Freyd.S2_43` (`diag`, `le_diag_iff`, `diag_comp_le_zero`).
-/
module

public import Freyd.S2_437_REAllegory
public import Freyd.S2_438_Godel
public import Freyd.S2_43

namespace Freyd.REAlleg

open Freyd.Rcat Freyd.Alg Freyd.Godel

/-! ## Layer 3a: the distributive-allegory structure on `A`

  `godel_collapse` runs in any `DistributiveAllegory`, so we equip the r.e.
  relations with zero and union (both `IsRE`, from §2.437). -/

/-- The empty relation as a morphism of `A`. -/
@[expose] public def reZero : RERel := ⟨relZero, isRE_zero⟩

/-- Union of two r.e. relations as a morphism of `A`. -/
@[expose] public def reUnion (R S : RERel) : RERel := ⟨relUnion R.1 S.1, isRE_union R.2 S.2⟩

/-- The allegory order on `A` is pointwise implication. -/
theorem reLe_iff {R S : REObj.star ⟶ REObj.star} : R ⊑ S ↔ ∀ a b, R.1 a b → S.1 a b := by
  constructor
  · intro h a b hR
    have hval := congrArg (fun r : REObj.star ⟶ REObj.star => r.1 a b) h
    have hand : R.1 a b ∧ S.1 a b := (iff_of_eq hval).mpr hR
    exact hand.2
  · intro h; apply rerel_ext; intro a b
    exact ⟨fun x => x.1, fun hR => ⟨hR, h a b hR⟩⟩

/-- `A` is non-trivial: the identity is not the empty relation (both contain,
    resp. omit, the pair `(0,0)`).  This is what the collapse `id = 𝟘` contradicts. -/
theorem reId_ne_zero : (reId : RERel) ≠ reZero := by
  intro h
  have hval : relId = relZero := congrArg Subtype.val h
  have h00 := congrFun (congrFun hval 0) 0
  exact (iff_of_eq h00).mp rfl

/-- The one-object DISTRIBUTIVE allegory of r.e. relations: zero and union added
    to `instAllegory`.  Every axiom is a `Rel`-identity, proved pointwise. -/
@[expose] public instance instDist : DistributiveAllegory REObj where
  toAllegory := instAllegory
  zero := reZero
  union R S := reUnion R S
  zero_comp R := rerel_ext fun a c =>
    ⟨fun ⟨_, h, _⟩ => h, fun h => h.elim⟩
  comp_zero R := rerel_ext fun a c =>
    ⟨fun ⟨_, _, h⟩ => h, fun h => h.elim⟩
  union_idem R := rerel_ext fun a b =>
    ⟨fun h => h.elim id id, Or.inl⟩
  union_comm R S := rerel_ext fun a b => ⟨Or.symm, Or.symm⟩
  union_assoc R S T := rerel_ext fun a b => or_assoc.symm
  union_inter_absorb R S := rerel_ext fun a b =>
    ⟨fun h => h.elim id (fun x => x.2), Or.inl⟩
  inter_union_absorb R S := rerel_ext fun a b =>
    ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
  comp_union_distrib R S T := rerel_ext fun a c => by
    constructor
    · rintro ⟨b, hR, hS | hT⟩
      · exact Or.inl ⟨b, hR, hS⟩
      · exact Or.inr ⟨b, hR, hT⟩
    · rintro (⟨b, hR, hS⟩ | ⟨b, hR, hT⟩)
      · exact ⟨b, hR, Or.inl hS⟩
      · exact ⟨b, hR, Or.inr hT⟩
  inter_union_distrib R S T := rerel_ext fun a b =>
    ⟨fun ⟨hR, hST⟩ => hST.elim (fun h => Or.inl ⟨hR, h⟩) (fun h => Or.inr ⟨hR, h⟩),
      fun h => h.elim (fun ⟨hR, hS⟩ => ⟨hR, Or.inl hS⟩) (fun ⟨hR, hT⟩ => ⟨hR, Or.inr hT⟩)⟩
  zero_union R := rerel_ext fun a b =>
    ⟨fun h => h.elim (fun x => x.elim) id, Or.inr⟩

/-! ## Layer 3b: the s-m-n parametrization (building `R̂`)

  The one genuinely new piece.  Given an r.e. relation `R` with recursive test
  `t` (so `R a c ↔ ∃ y, t y (cp a c) = 0`) and a code `ct` for `t`, we build a
  Kleene code `smnCode ct a : RecCode 1` that on input `c` searches for a witness
  `y` with `t y (cp a c) = 0`.  It halts iff `R a c`; its Gödel number
  `smnNum ct a` is total-recursive in `a`, and `relT (smnNum ct a) c ↔ R a c`. -/

/-- A fixed code for the Cantor pairing `cp`. -/
noncomputable def cpCode : RecCode 2 := Classical.choose Recursive2.cp

/-- A two-element family of subcodes, for `Eval.comp`. -/
def gs2 {k : Nat} (A B : RecCode k) : Fin 2 → RecCode k := fun i => if i.val = 0 then A else B

@[simp] theorem gs2_zero {k : Nat} (A B : RecCode k) : gs2 A B 0 = A := rfl
@[simp] theorem gs2_one {k : Nat} (A B : RecCode k) : gs2 A B 1 = B := rfl

/-- Evaluation of a binary composition `comp cf (gs2 A B)`. -/
theorem eval_comp2 {k : Nat} {cf : RecCode 2} {A B : RecCode k} {v : Vec k} {wa wb y : Nat}
    (hA : Eval A v wa) (hB : Eval B v wb) (hf : Eval cf (vcons wa (fun _ => wb)) y) :
    Eval (.comp cf (gs2 A B)) v y := by
  refine .comp (vcons wa (fun _ => wb)) (fun j => ?_) hf
  rcases j with ⟨jv, hj⟩
  match jv with
  | 0 => exact hA
  | 1 => exact hB
  | n + 2 => exact absurd hj (by omega)

/-- The inner code computing `(y, r) ↦ cp a r` (with `a` a hardwired constant). -/
noncomputable def smnCP (a : Nat) : RecCode 2 := .comp cpCode (gs2 (constCode 2 a) (.proj 1))

/-- The mu-body computing `(y, r) ↦ t y (cp a r)`. -/
noncomputable def smnBody (ct : RecCode 2) (a : Nat) : RecCode 2 :=
  .comp ct (gs2 (.proj 0) (smnCP a))

/-- The s-m-n code: on input `r`, searches for `y` with `t y (cp a r) = 0`. -/
noncomputable def smnCode (ct : RecCode 2) (a : Nat) : RecCode 1 := .mu (smnBody ct a)

theorem smnCP_eval (a : Nat) (v : Vec 2) : Eval (smnCP a) v (cp a (v 1)) := by
  refine eval_comp2 (A := constCode 2 a) (B := .proj 1) (wa := a) (wb := v 1)
    (evalConst 2 a v) (.proj 1) ?_
  have := Classical.choose_spec Recursive2.cp (vcons a (fun _ => v 1)); simpa using this

theorem smnBody_eval {t : Nat → Nat → Nat} {ct : RecCode 2}
    (hct : ∀ w, Eval ct w (t (w 0) (w 1))) (a : Nat) (v : Vec 2) :
    Eval (smnBody ct a) v (t (v 0) (cp a (v 1))) := by
  refine eval_comp2 (A := .proj 0) (B := smnCP a) (wa := v 0) (wb := cp a (v 1))
    (.proj 0) (smnCP_eval a v) ?_
  have := hct (vcons (v 0) (fun _ => cp a (v 1))); simpa using this

/-- Convergence of the s-m-n code: it halts on input `r` iff `∃ y, t y (cp a r) = 0`.
    (Same `μ`-search structure as §2.437 `muDomain`.) -/
theorem smnCode_conv {t : Nat → Nat → Nat} {ct : RecCode 2}
    (hct : ∀ w, Eval ct w (t (w 0) (w 1))) (a r : Nat) :
    (∃ w, Eval (smnCode ct a) (fun _ => r) w) ↔ ∃ y, t y (cp a r) = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    cases hw with
    | mu rr hy _ =>
      refine ⟨w, ?_⟩
      have hval := smnBody_eval hct a (vcons w (fun _ => r))
      simp only [vcons_zero, vcons_one] at hval
      exact (Eval.det hy hval).symm
  · rintro ⟨y, hy⟩
    obtain ⟨y0, hmem, hmin⟩ : ∃ y0, t y0 (cp a r) = 0 ∧ ∀ i, i < y0 → ¬ t i (cp a r) = 0 :=
      ⟨theLeast (fun y => t y (cp a r) = 0) ⟨y, hy⟩,
        theLeast_mem (fun y => t y (cp a r) = 0) ⟨y, hy⟩,
        theLeast_min (fun y => t y (cp a r) = 0) ⟨y, hy⟩⟩
    refine ⟨y0, Eval.mu (fun i => t i (cp a r) - 1) ?_ (fun i hi => ?_)⟩
    · have hval := smnBody_eval hct a (vcons y0 (fun _ => r))
      simp only [vcons_zero, vcons_one] at hval
      rw [hmem] at hval; exact hval
    · have hval := smnBody_eval hct a (vcons i (fun _ => r))
      simp only [vcons_zero, vcons_one] at hval
      rw [show t i (cp a r) - 1 + 1 = t i (cp a r) from by have := hmin i hi; omega]
      exact hval

/-- The Gödel number of the s-m-n code — the value `f_R a`. -/
noncomputable def smnNum (ct : RecCode 2) (a : Nat) : Nat := encCode (smnCode ct a)

/-- **s-m-n correctness.**  `f_R a = smnNum ct a` is a recipe for the row
    `{ c | R a c }`: `relT (smnNum ct a) c ↔ ∃ y, t y (cp a c) = 0`. -/
theorem relT_smnNum {t : Nat → Nat → Nat} {ct : RecCode 2}
    (hct : ∀ w, Eval ct w (t (w 0) (w 1))) (a c : Nat) :
    relT (smnNum ct a) c ↔ ∃ y, t y (cp a c) = 0 := by
  have hspec : (∃ w, Eval cU (fun _ => cp (smnNum ct a) c) w)
      ↔ ∃ w, Eval (smnCode ct a) (fun _ => c) w :=
    exists_congr fun w => Classical.choose_spec universal_genuine (smnCode ct a) c w
  exact hspec.trans (smnCode_conv hct a c)

/-! ### `smnNum ct` is total-recursive in `a`

  The only `a`-dependence of `smnCode ct a` is the constant subcode
  `constCode 2 a`, so its Gödel number is a fixed recursive context `Ψ` applied
  to `encCode (constCode 2 a)`, which is itself a primitive recursion in `a`. -/

-- `encVec_one` is `Freyd.Rcat.encVec_one` (opened above); only the two-element case is new here.
theorem encVec_two (f : Vec 2) : encVec f = consN (f 0) (consN (f 1) 0) := rfl

/-- The step function of the `encCode ∘ constCode 2` primitive recursion. -/
noncomputable def encConstH : Nat → Nat → Nat :=
  fun _ r => cp 3 (cp 1 (cp (cp 1 0) (consN r 0)))

/-- The Gödel number of a constant code is a primitive recursion in the constant. -/
theorem encConst2_eq (a : Nat) : encCode (constCode 2 a) = natIter (cp 0 0) encConstH a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    show encCode (RecCode.comp RecCode.succ (fun _ => constCode 2 a)) = _
    rw [encCode_comp, encCode_succ, encVec_one, ih]; rfl

theorem Recursive1_encConst2 : Recursive1 (fun a => encCode (constCode 2 a)) := by
  have hrec : Recursive1 (natIter (cp 0 0) encConstH) := by
    apply Recursive1.natIter; apply Recursive2.ofSnd
    exact Recursive1.comp2 Recursive2.cp (Recursive1.const 3)
      (Recursive1.comp2 Recursive2.cp (Recursive1.const 1)
        (Recursive1.comp2 Recursive2.cp (Recursive1.const (cp 1 0))
          (Recursive1.comp2 Recursive2.consN (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.const 0))))
  exact hrec.congr (fun a => (encConst2_eq a).symm)

/-- The fixed recursive context around `encCode (constCode 2 a)` in `smnNum ct a`. -/
noncomputable def encSmnCtx (ct : RecCode 2) (x : Nat) : Nat :=
  cp 5 (cp 3 (cp 2 (cp (encCode ct)
    (consN (cp 2 0)
      (consN (cp 3 (cp 2 (cp (encCode cpCode) (consN x (consN (cp 2 1) 0))))) 0)))))

theorem smnNum_eq (ct : RecCode 2) (a : Nat) :
    smnNum ct a = encSmnCtx ct (encCode (constCode 2 a)) := by
  show encCode (smnCode ct a) = _
  unfold smnCode smnBody smnCP
  rw [encCode_mu, encCode_comp, encVec_two]
  simp only [gs2_zero, gs2_one, encCode_proj]
  rw [encCode_comp, encVec_two]
  simp only [gs2_zero, gs2_one, encCode_proj]
  rfl

theorem Recursive1_encSmnCtx (ct : RecCode 2) : Recursive1 (encSmnCtx ct) := by
  unfold encSmnCtx
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const 5) ?_
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const 3) ?_
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const 2) ?_
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const (encCode ct)) ?_
  refine Recursive1.comp2 Recursive2.consN (Recursive1.const (cp 2 0)) ?_
  refine Recursive1.comp2 Recursive2.consN ?_ (Recursive1.const 0)
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const 3) ?_
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const 2) ?_
  refine Recursive1.comp2 Recursive2.cp (Recursive1.const (encCode cpCode)) ?_
  exact Recursive1.comp2 Recursive2.consN (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.const (consN (cp 2 1) 0))

/-- **The s-m-n map is recursive.**  `f_R = smnNum ct` is total-recursive. -/
theorem Recursive1_smnNum (ct : RecCode 2) : Recursive1 (smnNum ct) :=
  ((Recursive1_encConst2).comp (Recursive1_encSmnCtx ct)).congr
    (fun a => (smnNum_eq ct a).symm)

/-! ## Layer 3c: the §2.437 hat structure for any r.e. relation

  The MAP `R̂` is the graph of `f_R = smnNum ct`; the three §2.437 containments
  (i)–(iii) follow from the correctness `relT (f_R a) c ↔ R a c` and the fact
  that `f_R` is a total function.  This builds §2.438's `HatWitness` for ANY
  r.e. `R`. -/

/-- **§2.437 hat structure (data form).**  For any morphism `Rr` of `A` with a
    recursive test `t` (code `ct`), the s-m-n map `R̂` (graph of `f_R = smnNum ct`)
    is entire and satisfies `R̂ T ⊑ Rr`, `R̂° Rr ⊑ T` with `T = reT`. -/
noncomputable def hatWitness_of_data (Rr : RERel) (t : Nat → Nat → Nat) (ct : RecCode 2)
    (hct : ∀ w : Vec 2, Eval ct w (t (w 0) (w 1)))
    (hRs : ∀ a b, Rr.1 a b ↔ ∃ y, t y (cp a b) = 0) : HatWitness (REObj.star) := by
  have hcorrect : ∀ a c, relT (smnNum ct a) c ↔ Rr.1 a c :=
    fun a c => (relT_smnNum hct a c).trans (hRs a c).symm
  -- The map `R̂`: graph of the total recursive `f_R = smnNum ct`.
  have hatIsRE : IsRE (fun a n => n = smnNum ct a) := by
    refine ⟨fun _ m => (smnNum ct (cfst m) - csnd m) + (csnd m - smnNum ct (cfst m)),
      Recursive2.ofSnd (Recursive1.comp2 Recursive2.add
        (Recursive1.comp2 Recursive2.sub
          (Recursive1.comp Recursive1.cfst (Recursive1_smnNum ct)) Recursive1.csnd)
        (Recursive1.comp2 Recursive2.sub Recursive1.csnd
          (Recursive1.comp Recursive1.cfst (Recursive1_smnNum ct)))), ?_⟩
    intro a n
    simp only [cfst_cp, csnd_cp]
    exact ⟨fun h => ⟨0, by omega⟩, fun ⟨_, hy⟩ => by omega⟩
  refine
    { T := reT
      R := Rr
      hat := ⟨fun a n => n = smnNum ct a, hatIsRE⟩
      entire := ?_
      hatT_le := ?_
      hatR_le := ?_ }
  · refine reLe_iff.mpr fun x y hxy => ?_
    have hxy' : x = y := hxy
    exact ⟨smnNum ct x, rfl, congrArg (smnNum ct) hxy'⟩
  · refine reLe_iff.mpr fun x c => fun ⟨n, hn, hT⟩ => ?_
    have hn' : n = smnNum ct x := hn
    exact (hcorrect x c).mp (hn' ▸ hT)
  · refine reLe_iff.mpr fun n c => fun ⟨x, hn, hR⟩ => ?_
    have hn' : n = smnNum ct x := hn
    rw [hn']; exact (hcorrect x c).mpr hR

/-- **§2.437 hat structure.**  For any morphism `Rr` of `A`, the s-m-n map `R̂`
    is entire and satisfies `R̂ T ⊑ Rr`, `R̂° Rr ⊑ T` with `T = reT`.  Non-vacuously
    instantiates §2.438's `HatWitness` (the test/code come from `Rr`'s r.e. data). -/
noncomputable def hatWitness_of_code (Rr : RERel) : HatWitness (REObj.star) :=
  let hspec := Classical.choose_spec Rr.2
  hatWitness_of_data Rr (Classical.choose Rr.2) (Classical.choose hspec.1)
    (Classical.choose_spec hspec.1) hspec.2

/-! ## Layer 3d: `A` is not a division allegory (the headline)

  A right-division operation `div` on `A` with the adjointness
  `X ⊑ div R S ↔ X ≫ S ⊑ R` is exactly what a `DivisionAllegory` structure adds
  to the distributive allegory `instDist`.  We show no such operation exists:
  the §2.436 diagonal `div 𝟘 (1 ∩ T)` supplies the §2.438 `GodelHyp`, and
  `godel_collapse` (fed the s-m-n `HatWitness`) forces `id = 𝟘`, contradicting
  the non-triviality `reId_ne_zero`. -/

/-- **§2.437 Layer 3 — `A` is NOT a division allegory.**  There is no right-division
    operation on the r.e.-relations allegory (equivalently, its distributive-allegory
    structure `instDist` does not extend to a `DivisionAllegory`).  Freyd: "Hence `A`
    cannot be a division allegory." -/
theorem not_division :
    ¬ ∃ div : (REObj.star ⟶ REObj.star) → (REObj.star ⟶ REObj.star) →
        (REObj.star ⟶ REObj.star),
      ∀ X R S : REObj.star ⟶ REObj.star, X ⊑ div R S ↔ X ≫ S ⊑ R := by
  rintro ⟨div, hdiv⟩
  -- The §2.436 diagonal `dgn = 𝟘 / (1 ∩ T)` for `T = reT`.
  have H : GodelHyp reT (div 𝟘 (Cat.id REObj.star ∩ reT)) :=
    { divisor := fun S hS =>
        (hdiv S 𝟘 (Cat.id REObj.star ∩ reT)).mpr (by rw [hS]; exact le_refl _)
      consistency := le_antisymm
        ((hdiv (div 𝟘 (Cat.id REObj.star ∩ reT)) 𝟘 (Cat.id REObj.star ∩ reT)).mp
          (le_refl _)) (zero_le _) }
  -- The s-m-n hat structure for the diagonal, then §2.438's collapse.
  exact reId_ne_zero
    (godel_collapse (hatWitness_of_code (div 𝟘 (Cat.id REObj.star ∩ reT))) H)

end Freyd.REAlleg
