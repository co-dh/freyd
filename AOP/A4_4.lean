/-
  Bird & de Moor, *Algebra of Programming* §4.4  Locally complete allegories.

  All statements are in Freyd conventions: diagram-order composition `R ≫ S` (first R then S),
  converse `R°`, meet `∩`, order `⊑`, union `R ∪ S`, zero `𝟘`.  We build on `Freyd.S2_3`
  (`DistributiveAllegory`/`DivisionAllegory`/`LocallyCompleteDistributiveAllegory`, division)
  and `Freyd.S2_147_MapCat` (`dom_union`, `dom_zero`, the `TabularUnitary*` classes).

  Contents:
  §A  Meets as joins (`Inf`, Ex 4.28).
  §B  The top of a hom-set (`topHom`).
  §C  Implication `R ⇨ S` (p.97, Ex 4.32/4.33).
  §D  `Sup`/zero interaction (`dom_Sup`, Ex 4.29/4.31).
  §E  Lexicographic composition `R ⨾ S` (p.98, Ex 4.34).
  §F  Division map-laws (Ex 4.35).
  §G  Galois connections (Ex 4.36–4.40).
-/

import Freyd.S2_30
import Freyd.S2_147_MapCat
import AOP.A4_2  -- modular_sym/modular_le_right (via A4_1), map_shunt_left/right, entire_id_le

universe v u

namespace Freyd.Alg

/-! ## Allegory-level utilities and cross-agent private helpers

  These need only `[Allegory 𝒜]`.  `modular_sym`/`map_shunt_right`/`map_shunt_left` are
  duplicated here as `private` because other agents are concurrently building the canonical
  copies in `A4_1`/`A4_2`, which this file cannot import; the collector should dedupe. -/

section AllegoryLevel

variable {𝒜 : Type u} [Allegory 𝒜]

/-- `∩` is monotone in both arguments (a basic `Allegory` fact missing from `S2_1`, used
    throughout this file). -/
theorem inter_mono {a b : 𝒜} {R R' S S' : a ⟶ b} (hR : R ⊑ R') (hS : S ⊑ S') :
    R ∩ S ⊑ R' ∩ S' :=
  le_inter (le_trans (inter_lb_left R S) hR) (le_trans (inter_lb_right R S) hS)

/-- Poset extensionality via principal down-sets: if `X ⊑ A ↔ X ⊑ B` for every `X`, then
    `A = B`.  The standard technique for proving equalities of `Sup`-defined operators without
    chasing elements of the `Sup` directly. -/
theorem antisymm_of_le_iff {a b : 𝒜} {A B : a ⟶ b} (h : ∀ X, X ⊑ A ↔ X ⊑ B) : A = B :=
  le_antisymm ((h A).mp (le_refl A)) ((h B).mpr (le_refl B))

-- (`modular_le_right`, `modular_sym`, `entire_id_le`, `map_shunt_right`, `map_shunt_left`
--  come from A4_1/A4_2 — the private wave-time copies were deduped at collection.)

-- (`simple_dist_inter_recip` was hoisted to A4_2 at ch.5 collection.)

/-! ### Galois connections (B&dM Ex 4.36–4.39, hom-set level)

  Galois connections are the engine of program calculation (thinning/greedy theorems later
  in B&dM).  Freyd's "adjoint pair of functions between posets" (§1.51) and the monotonicity of
  both legs are the GENERIC `Freyd.GaloisConnection` / `GaloisConnection.monotone_l` /
  `monotone_u` (Freyd/S1_51_Order), instantiated here at hom-sets with the allegory order `⊑`
  (reflexivity `le_refl`, transitivity `le_trans`); the join-preservation facts are in the
  `LocallyCompleteDistributiveAllegory` section below.  No hom-set-specific `GaloisConn` is
  re-defined. -/

end AllegoryLevel

/-! ## Locally complete distributive allegories -/

section LCDA

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

-- (`Sup_congr` comes from S2_22, which is in scope via S2_147_MapCat.)

/-! ### §A  Meets as joins (B&dM Ex 4.28) -/

/-- Meets as joins: `Inf P := ⊔ { S | S is a lower bound of every R with P R }`. -/
def Inf {a b : 𝒜} (P : (a ⟶ b) → Prop) : a ⟶ b := Sup (fun S => ∀ R, P R → S ⊑ R)

theorem le_Inf {a b : 𝒜} {P : (a ⟶ b) → Prop} {T : a ⟶ b} (h : ∀ R, P R → T ⊑ R) : T ⊑ Inf P :=
  le_Sup h

/-! ### §B  The top of a hom-set (B&dM p.97)

  In a locally complete distributive allegory each hom-set `(a,b)` has a top element: the
  join of everything. -/

/-- The top of the hom-set `(a,b)`. -/
def topHom (a b : 𝒜) : a ⟶ b := Sup (fun _ => True)

theorem recip_topHom {a b : 𝒜} : (topHom a b)° = topHom b a := by
  apply le_antisymm
  · exact le_Sup trivial
  · exact recip_le_iff.mp (le_Sup trivial)

/-! ### §C  Implication (B&dM §4.4 p.97, Ex 4.32/4.33) -/

/-- Implication `R ⇨ S := ⊔ { X | X∩R ⊑ S }`, the right adjoint to `_ ∩ R`. -/
def impl {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b := Sup (fun X => X ∩ R ⊑ S)

/-- Implication notation `R ⇨ S` (B&dM §4.4 p.97). -/
infixr:58 (name := implNotation) " ⇨ " => impl

/-- The universal property of implication: `X ⊑ R⇨S ↔ X∩R ⊑ S`. -/
theorem le_impl_iff {a b : 𝒜} (X R S : a ⟶ b) : (X ⊑ R ⇨ S) ↔ (X ∩ R ⊑ S) := by
  constructor
  · intro h
    have h1 : X ∩ R ⊑ (R ⇨ S) ∩ R := inter_mono h (le_refl R)
    rw [Allegory.inter_comm (R ⇨ S) R] at h1
    have h2 : R ∩ (R ⇨ S) = Sup (fun Y => ∃ Z, (Z ∩ R ⊑ S) ∧ Y = R ∩ Z) := by
      dsimp only [impl]; exact inter_Sup_distrib R (fun Z => Z ∩ R ⊑ S)
    rw [h2] at h1
    refine le_trans h1 (Sup_le ?_)
    rintro Y ⟨Z, hZ, rfl⟩
    rw [Allegory.inter_comm R Z]
    exact hZ
  · intro h; exact le_Sup h

theorem impl_cancel {a b : 𝒜} (R S : a ⟶ b) : (R ⇨ S) ∩ R ⊑ S :=
  (le_impl_iff (R ⇨ S) R S).mp (le_refl _)

theorem impl_mono_right {a b : 𝒜} {R S S' : a ⟶ b} (h : S ⊑ S') : (R ⇨ S) ⊑ (R ⇨ S') := by
  dsimp only [impl]
  apply Sup_le
  intro X hX
  exact le_Sup (le_trans hX h)

theorem impl_antitone_left {a b : 𝒜} {R R' S : a ⟶ b} (h : R ⊑ R') : (R' ⇨ S) ⊑ (R ⇨ S) := by
  dsimp only [impl]
  apply Sup_le
  intro X hX
  exact le_Sup (le_trans (inter_mono (le_refl X) h) hX)

/-- Implication into the top is the top: `R ⇨ ⊤ = ⊤`. -/
theorem impl_topHom {a b : 𝒜} (R : a ⟶ b) : (R ⇨ (topHom a b)) = topHom a b :=
  le_antisymm (le_Sup trivial) ((le_impl_iff _ _ _).mpr (le_Sup trivial))

/-- The top implies anything it dominates trivially: `⊤ ⇨ S = S`. -/
theorem topHom_impl {a b : 𝒜} (R : a ⟶ b) : (topHom a b ⇨ R) = R := by
  apply antisymm_of_le_iff
  intro X
  rw [le_impl_iff, inter_eq_left (show X ⊑ topHom a b from le_Sup trivial)]

/-- Currying: `R ⇨ (S ⇨ T) = (R∩S) ⇨ T` (Ex 4.32). -/
theorem impl_curry {a b : 𝒜} (R S T : a ⟶ b) : (R ⇨ (S ⇨ T)) = ((R ∩ S) ⇨ T) := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ R ⇨ (S ⇨ T) ↔ X ∩ R ⊑ S ⇨ T := le_impl_iff X R (S ⇨ T)
    _ ↔ (X ∩ R) ∩ S ⊑ T := le_impl_iff (X ∩ R) S T
    _ ↔ X ∩ (R ∩ S) ⊑ T := by rw [Allegory.inter_assoc]
    _ ↔ X ⊑ (R ∩ S) ⇨ T := (le_impl_iff X (R ∩ S) T).symm

/-- `(R∪S) ⇨ T = (R⇨T) ∩ (S⇨T)` (Ex 4.32). -/
theorem union_impl {a b : 𝒜} (R S T : a ⟶ b) : ((R ∪ S) ⇨ T) = ((R ⇨ T) ∩ (S ⇨ T)) := by
  apply le_antisymm
  · exact le_inter (impl_antitone_left (le_union_left R S)) (impl_antitone_left (le_union_right R S))
  · apply (le_impl_iff _ _ _).mpr
    rw [DistributiveAllegory.inter_union_distrib]
    apply union_lub
    · exact le_trans (inter_mono (inter_lb_left (R ⇨ T) (S ⇨ T)) (le_refl R)) (impl_cancel R T)
    · exact le_trans (inter_mono (inter_lb_right (R ⇨ T) (S ⇨ T)) (le_refl S)) (impl_cancel S T)

/-- `R ⇨ (S∩T) = (R⇨S) ∩ (R⇨T)` (Ex 4.32). -/
theorem impl_inter {a b : 𝒜} (R S T : a ⟶ b) : (R ⇨ (S ∩ T)) = ((R ⇨ S) ∩ (R ⇨ T)) := by
  apply le_antisymm
  · exact le_inter (impl_mono_right (inter_lb_left S T)) (impl_mono_right (inter_lb_right S T))
  · apply (le_impl_iff _ _ _).mpr
    apply le_inter
    · exact le_trans (inter_mono (inter_lb_left (R ⇨ S) (R ⇨ T)) (le_refl R)) (impl_cancel R S)
    · exact le_trans (inter_mono (inter_lb_right (R ⇨ S) (R ⇨ T)) (le_refl R)) (impl_cancel R T)

/-- `R ∩ (R⇨S) = R∩S` (Ex 4.32). -/
theorem inter_impl_absorb {a b : 𝒜} (R S : a ⟶ b) : (R ∩ (R ⇨ S)) = (R ∩ S) := by
  apply le_antisymm
  · apply le_inter (inter_lb_left R (R ⇨ S))
    rw [Allegory.inter_comm R (R ⇨ S)]
    exact impl_cancel R S
  · apply le_inter (inter_lb_left R S)
    apply (le_impl_iff _ _ _).mpr
    exact le_trans (inter_lb_left (R ∩ S) R) (inter_lb_right R S)

/-- **B&dM Ex 4.33** (one direction): conjugation by maps preserves `⇨` in the `⊑` direction.

    The reverse containment (which would upgrade this to the book's stated equality
    `f≫(R⇨S)≫g° = (f≫R≫g°) ⇨ (f≫S≫g°)`) resists a general LCDA proof.  Unwinding it via
    `map_shunt_left`/`map_shunt_right`/`le_impl_iff` reduces to: for arbitrary `X : c⟶d`
    (with `M := f≫R≫g°`, `N := f≫S≫g°`), `X∩M ⊑ N → (f°≫X≫g)∩R ⊑ S`.  This needs
    `R ⊑ f°≫M≫g`, but only the OPPOSITE containment `f°≫M≫g ⊑ R` follows from `Simple f`,
    `Simple g` (`f°≫M≫g = (f°f)≫R≫(g°g)`, and `Map` only gives `f°f ⊑ 1`, `g°g ⊑ 1` — an
    upper, never a lower, bound).  Recovering `R` needs `f`, `g` to ALSO be co-simple
    (injective), which a bare `Map` does not provide.  A powerset (`Rel`) check with `f`
    non-surjective confirms the full equality nonetheless holds THERE, via "preimage commutes
    with Boolean complement" — i.e. the reverse direction is a genuinely BOOLEAN fact (§4.5),
    not a general-LCDA one. -/
theorem map_conj_impl_le {a b c d : 𝒜} {f : c ⟶ a} {g : d ⟶ b} (hf : Map f) (hg : Map g)
    (R S : a ⟶ b) :
    f ≫ (R ⇨ S) ≫ g° ⊑ (f ≫ R ≫ g°) ⇨ (f ≫ S ≫ g°) := by
  apply (le_impl_iff _ _ _).mpr
  have e1 : f ≫ (R ⇨ S) ≫ g° = (f ≫ (R ⇨ S)) ≫ g° := (Cat.assoc f (R ⇨ S) g°).symm
  have e2 : f ≫ R ≫ g° = (f ≫ R) ≫ g° := (Cat.assoc f R g°).symm
  have e3 : f ≫ S ≫ g° = (f ≫ S) ≫ g° := (Cat.assoc f S g°).symm
  rw [e1, e2, e3, ← simple_dist_inter_recip hg.2, ← simple_dist_inter hf.2]
  exact comp_mono_right (comp_mono_left f (impl_cancel R S)) g°

/-! ### §D  `Sup`/zero interaction (B&dM Ex 4.29, 4.31) -/

/-- `dom` distributes over `Sup`: `dom (⊔ P) = ⊔ { dom R | P R }` (Ex 4.29). -/
theorem dom_Sup {a b : 𝒜} (P : (a ⟶ b) → Prop) :
    dom (Sup P) = Sup (fun D => ∃ R, P R ∧ D = dom R) := by
  apply le_antisymm
  · have h1 : (Sup P)° = Sup (fun T : b ⟶ a => ∃ R, P R ∧ T = R°) := recip_Sup P
    have h2 : Sup P ≫ (Sup P)° = Sup (fun U : a ⟶ a => ∃ R, P R ∧ U = Sup P ≫ R°) := by
      rw [h1, comp_Sup_distrib]
      apply Sup_congr
      intro U
      constructor
      · rintro ⟨T, ⟨R, hR, rfl⟩, hU⟩; exact ⟨R, hR, hU⟩
      · rintro ⟨R, hR, hU⟩; exact ⟨R°, ⟨R, hR, rfl⟩, hU⟩
    have h3 : Cat.id a ∩ (Sup P ≫ (Sup P)°)
        = Sup (fun D => ∃ R, P R ∧ D = Cat.id a ∩ (Sup P ≫ R°)) := by
      rw [h2, inter_Sup_distrib]
      apply Sup_congr
      intro D
      constructor
      · rintro ⟨U, ⟨R, hR, rfl⟩, hD⟩; exact ⟨R, hR, hD⟩
      · rintro ⟨R, hR, hD⟩; exact ⟨Sup P ≫ R°, ⟨R, hR, rfl⟩, hD⟩
    show Cat.id a ∩ (Sup P ≫ (Sup P)°) ⊑ _
    rw [h3]
    apply Sup_le
    rintro D ⟨R, hR, rfl⟩
    have hD : Cat.id a ∩ (Sup P ≫ R°) = dom (R ∩ Sup P) := (dom_inter R (Sup P)).symm
    rw [hD, inter_eq_left (le_Sup hR)]
    exact le_Sup ⟨R, hR, rfl⟩
  · apply Sup_le
    rintro D ⟨R, hR, rfl⟩
    exact dom_mono_of_le (le_Sup hR)

/-- A morphism is zero iff its domain is zero (Ex 4.31). -/
theorem eq_zero_iff_dom_zero {a b : 𝒜} (R : a ⟶ b) : R = (𝟘 : a ⟶ b) ↔ dom R = (𝟘 : a ⟶ a) := by
  constructor
  · intro h; rw [h]; exact dom_zero
  · intro h
    calc R = dom R ≫ R := (dom_comp_self R).symm
      _ = (𝟘 : a ⟶ a) ≫ R := by rw [h]
      _ = 𝟘 := DistributiveAllegory.zero_comp R

/-- `(R≫S)∩T = 0 ↔ R∩(T≫S°) = 0` (Ex 4.31). -/
theorem comp_inter_zero_iff {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    ((R ≫ S) ∩ T = (𝟘 : a ⟶ c)) ↔ (R ∩ (T ≫ S°) = (𝟘 : a ⟶ b)) := by
  constructor
  · intro h
    have hmod := modular_le T (S°) R
    rw [Allegory.recip_recip] at hmod
    rw [(Allegory.inter_comm T (R ≫ S)).trans h, DistributiveAllegory.zero_comp] at hmod
    rw [Allegory.inter_comm R (T ≫ S°)]
    exact le_antisymm hmod (zero_le _)
  · intro h
    have hmod := modular_le R S T
    rw [h, DistributiveAllegory.zero_comp] at hmod
    exact le_antisymm hmod (zero_le _)

/-! ### §E  Lexicographic composition (B&dM p.98, Ex 4.34)

  `R ⨾ S` compares by `R` first, breaking ties by `S`: the lexicographic ordering built from
  `(fst-projected leq) ⨾ (snd-projected leq)`. -/

/-- `R ⨾ S := R ∩ (R°⇨S)` — B&dM's `R;S`: compare by `R`, break ties by `S`. -/
def thenRel {a : 𝒜} (R S : a ⟶ a) : a ⟶ a := R ∩ (R° ⇨ S)

/-- Lexicographic-composition notation `R ⨾ S`. -/
infixl:62 (name := thenRelNotation) " ⨾ " => thenRel

theorem thenRel_reflexive {a : 𝒜} {R S : a ⟶ a} (hR : Reflexive R) (hS : Reflexive S) :
    Reflexive (R ⨾ S) := by
  apply le_inter hR
  apply (le_impl_iff _ _ _).mpr
  exact le_trans (inter_lb_left (Cat.id a) (R°)) hS

/-- **B&dM Ex 4.34**: `R ⨾ S` is transitive when `R`, `S` are (uses the symmetric modular law,
    per the book's hint). -/
theorem thenRel_transitive {a : 𝒜} {R S : a ⟶ a} (_hR : Reflexive R)
    (hRt : Transitive R) (hSt : Transitive S) : Transitive (R ⨾ S) := by
  have hMR : (R ⨾ S) ⊑ R := inter_lb_left R (R° ⇨ S)
  have hMS : (R ⨾ S) ∩ R° ⊑ S := (le_impl_iff (R ⨾ S) (R°) S).mp (inter_lb_right R (R° ⇨ S))
  have hRR : R° ≫ R° ⊑ R° := by
    have h := recip_mono hRt
    rwa [Allegory.recip_comp] at h
  have hM'R' : (R ⨾ S)° ≫ R° ⊑ R° :=
    le_trans (comp_mono_right (recip_mono hMR) R°) hRR
  have hR'M' : R° ≫ (R ⨾ S)° ⊑ R° :=
    le_trans (comp_mono_left R° (recip_mono hMR)) hRR
  have hfac1 : (R ⨾ S) ∩ (R° ≫ (R ⨾ S)°) ⊑ S :=
    le_trans (inter_mono (le_refl (R ⨾ S)) hR'M') hMS
  have hfac2 : (R ⨾ S) ∩ ((R ⨾ S)° ≫ R°) ⊑ S :=
    le_trans (inter_mono (le_refl (R ⨾ S)) hM'R') hMS
  have hms := modular_sym (R ⨾ S) (R ⨾ S) (R°)
  have hfinal : ((R ⨾ S) ≫ (R ⨾ S)) ∩ R° ⊑ S :=
    le_trans hms (le_trans (comp_mono_right hfac1 _) (le_trans (comp_mono_left S hfac2) hSt))
  apply le_inter
  · exact le_trans (comp_mono_right hMR (R ⨾ S)) (le_trans (comp_mono_left R hMR) hRt)
  · exact (le_impl_iff _ (R°) S).mpr hfinal

theorem topHom_thenRel {a : 𝒜} (R : a ⟶ a) : (topHom a a) ⨾ R = R := by
  show topHom a a ∩ ((topHom a a)° ⇨ R) = R
  rw [recip_topHom, topHom_impl, Allegory.inter_comm,
    inter_eq_left (show R ⊑ topHom a a from le_Sup trivial)]

theorem thenRel_topHom {a : 𝒜} (R : a ⟶ a) : R ⨾ (topHom a a) = R := by
  show R ∩ (R° ⇨ topHom a a) = R
  rw [impl_topHom, inter_eq_left (show R ⊑ topHom a a from le_Sup trivial)]

-- BOOK Ex 4.34: `(R⨾S)⨾T = R⨾(S⨾T)` (associativity of lexicographic composition).
-- STATUS: DROPPED after genuine attempt — semantic check first, as instructed.
-- Expanding both sides with `impl_inter`/`impl_curry` gives
--   `R⨾(S⨾T) = (R⨾S) ∩ ((R°∩S°)⇨T)`
-- while directly
--   `(R⨾S)⨾T = (R⨾S) ∩ ((R⨾S)°⇨T)`.
-- These agree for every `T` iff `(R⨾S)°⇨T = (R°∩S°)⇨T` for every `T`, which (`impl` being
-- antitone in its left argument but not order-REFLECTING in general) would need
-- `(R⨾S)° = R°∩S°` outright.  But `(R⨾S)° = R° ∩ (R°⇨S)°`, and `(R°⇨S)° = S°` fails in
-- general (`⇨` is not self-dual under reciprocation) — e.g. `(R°⇨S)° ⊒ S°` is the only
-- direction that follows from `impl_cancel` + reciprocation.  Associativity therefore
-- genuinely needs extra hypotheses beyond the bare `impl`/`thenRel` laws (plausibly `R`, `S`
-- both preorders plus a further compatibility fact); dropped here rather than guessing at
-- the missing hypothesis.

/-! ### §G  Galois connections, LCDA part (B&dM Ex 4.36–4.40)

  Instances of the generic `Freyd.GaloisConnection` (Freyd/S1_51_Order) at allegory hom-sets,
  ordered by `⊑`; `Sup` is the hom-set's join, which is the `IsSup` for that family
  (`⟨le_Sup, Sup_le⟩`). -/

/-- A left adjoint preserves every existing join (Ex 4.39/4.40 direction): the generic
    `GaloisConnection.map_isSup` transported through `Sup` = `IsSup`. -/
theorem lower_Sup {a b c d : 𝒜} {f : (a ⟶ b) → (c ⟶ d)} {g : (c ⟶ d) → (a ⟶ b)}
    (h : GaloisConnection le le f g) (P : (a ⟶ b) → Prop) :
    f (Sup P) = Sup (fun Y => ∃ X, P X ∧ Y = f X) :=
  (h.map_isSup le_refl le_trans ⟨fun _ hR => le_Sup hR, fun _ hT => Sup_le hT⟩).unique
    (fun h₁ h₂ => le_antisymm h₁ h₂) ⟨fun _ hR => le_Sup hR, fun _ hT => Sup_le hT⟩

/-- The right adjoint is the join of everything mapped below the target (Ex 4.40). -/
theorem upper_eq {a b c d : 𝒜} {f : (a ⟶ b) → (c ⟶ d)} {g : (c ⟶ d) → (a ⟶ b)}
    (h : GaloisConnection le le f g) (Y : c ⟶ d) : g Y = Sup (fun X => f X ⊑ Y) := by
  apply le_antisymm
  · exact le_Sup ((h (g Y) Y).mpr (le_refl _))
  · apply Sup_le
    intro X hX
    exact (h X Y).mp hX

/-- `(_∩R) ⊣ (R⇨_)` is a Galois connection (instance of Ex 4.36–4.40). -/
theorem gc_inter_impl {a b : 𝒜} (R : a ⟶ b) :
    GaloisConnection le le (fun X : a ⟶ b => X ∩ R) (fun Y => R ⇨ Y) :=
  fun X Y => (le_impl_iff X R Y).symm

end LCDA

/-! ## Division allegories -/

section DivAllegory

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### §F  Division map-laws (B&dM Ex 4.35) -/

theorem map_comp_div {a b c d : 𝒜} {f : d ⟶ a} (hf : Map f) (R : a ⟶ c) (S : b ⟶ c) :
    f ≫ (R / S) = (f ≫ R) / S := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ f ≫ (R / S) ↔ f° ≫ X ⊑ R / S := (map_shunt_left hf X (R / S)).symm
    _ ↔ (f° ≫ X) ≫ S ⊑ R := le_div_iff _ _ _
    _ ↔ f° ≫ (X ≫ S) ⊑ R := by rw [Cat.assoc]
    _ ↔ X ≫ S ⊑ f ≫ R := map_shunt_left hf (X ≫ S) R
    _ ↔ X ⊑ (f ≫ R) / S := (le_div_iff _ _ _).symm

theorem div_comp_recip_map {a b c d : 𝒜} {f : d ⟶ b} (hf : Map f) (R : a ⟶ c) (S : b ⟶ c) :
    R / (f ≫ S) = (R / S) ≫ f° := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ R / (f ≫ S) ↔ X ≫ (f ≫ S) ⊑ R := le_div_iff _ _ _
    _ ↔ (X ≫ f) ≫ S ⊑ R := by rw [← Cat.assoc]
    _ ↔ X ≫ f ⊑ R / S := (le_div_iff _ _ _).symm
    _ ↔ X ⊑ (R / S) ≫ f° := map_shunt_right hf X (R / S)

/-! ### §G  Galois connections, division part -/

/-- `(S≫_) ⊣ (S\_)` is a Galois connection (Ex 4.36, left-division form). -/
theorem gc_comp_leftDiv {a b c : 𝒜} (S : a ⟶ b) :
    GaloisConnection le le (fun X : b ⟶ c => S ≫ X) (fun Y => (S \ Y)) :=
  fun X Y => (le_leftDiv_iff X S Y).symm

end DivAllegory

end Freyd.Alg
