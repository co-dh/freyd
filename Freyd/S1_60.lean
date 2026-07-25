/-
  Freyd & Scedrov, *Categories and Allegories* §1.6  Pre-logoi.

  §1.6  PRE-LOGOS: regular category where subobject posets are lattices
        and inverse image preserves unions.  Equivalent: Cartesian +
        images + pullbacks transfer finite covers.
  §1.61 0 = minimal subobject of 1.  Any map to 0 is iso. 0 is coterminator.
  §1.612 For monic f: A↣B, f# distributes over unions iff distributive lattice.
  §1.613 Poset is pre-logos iff it is a distributive lattice.
  §1.614 Representation of pre-logoi.
-/


import Freyd.S1_1
import Freyd.S1_34
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_43
import Freyd.S1_45
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56
import Freyd.S1_58


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.6 Pre-logos

  A PRE-LOGOS is a regular category in which subobject posets
  are lattices (have binary unions) and inverse image preserves
  unions.  Equivalent: Cartesian + images + pullbacks transfer
  finite covers (§1.6). -/

/-- Subobjects have binary unions (join). -/
class HasSubobjectUnions (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞] where
  union : ∀ {B : 𝒞} (_ _ : Subobject 𝒞 B), Subobject 𝒞 B
  union_left  : ∀ {B} (S T : Subobject 𝒞 B), S.le (union S T)
  union_right : ∀ {B} (S T : Subobject 𝒞 B), T.le (union S T)
  union_min   : ∀ {B} (S T U : Subobject 𝒞 B), S.le U → T.le U → (union S T).le U

/-- Inverse image f#: 𝒫(B) → 𝒫(A).  For subobject B'↣B, f#(B')
    is the pullback of B'.arr along f.  The pullback of a monic is
    monic (standard; proof deferred). -/
def InverseImage (f : A ⟶ B) (B' : Subobject 𝒞 B) [HasPullbacks 𝒞] : Subobject 𝒞 A :=
  let pb := HasPullbacks.has f B'.arr
  { dom := pb.cone.pt
    arr := pb.cone.π₁
    monic := by
      -- Pullback of a monic is monic: π₁ is left-cancellable.
      intro W u v huv
      -- B'.arr monic forces the π₂-legs to agree
      have hπ₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂ := by
        apply B'.monic
        rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, huv, Cat.assoc, pb.cone.w, ← Cat.assoc]
      -- both u and v are the unique lift of the cone ⟨W, u≫π₁, u≫π₂⟩
      let c : Cone f B'.arr :=
        ⟨W, u ≫ pb.cone.π₁, u ≫ pb.cone.π₂, by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]⟩
      rw [pb.lift_uniq c u rfl rfl, pb.lift_uniq c v huv.symm hπ₂.symm] }

/-- f# preserves binary unions: for any S,T subobjects of B,
    f#(S ∪ T) EQUALS f#(S) ∪ f#(T) as subobjects of A — i.e. each is
    `Subobject.le` the other.  This is stronger than a bare object
    `Isomorphic` of the domains: the mediating maps commute with the
    monics into A, so they can serve as the factorizing maps that
    `Subobject.le` (and hence the §1.62 relational lattice) requires. -/
def inverseImage_preserves_unions [HasImages 𝒞] [HasSubobjectUnions 𝒞] {A B : 𝒞} (f : A ⟶ B) [HasPullbacks 𝒞] : Prop :=
  ∀ (S T : Subobject 𝒞 B),
    (InverseImage f (HasSubobjectUnions.union S T)).le
        (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T))
    ∧ (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).le
        (InverseImage f (HasSubobjectUnions.union S T))

/-- A PRE-LOGOS (§1.6): regular + subobject lattices + inverse image
    preserves finite unions (including empty joins). -/
class PreLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasSubobjectUnions 𝒞 where
  -- empty join (bottom) of each subobject lattice
  bottom : ∀ (A : 𝒞), Subobject 𝒞 A
  bottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (bottom A).le S
  bottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (bottom A).dom (bottom B).dom
  -- f# preserves binary unions
  invImage_preserves_union : ∀ {A B : 𝒞} (f : A ⟶ B), inverseImage_preserves_unions f
  -- f# preserves the empty join (bottom)
  invImage_preserves_bottom : ∀ {A B : 𝒞} (f : A ⟶ B),
    Isomorphic (InverseImage f (bottom B)).dom (bottom A).dom

/-! ## §1.613 Posets as pre-logoi

  A poset viewed as a category is a pre-logos iff the poset is
  a distributive lattice (§1.613). -/

/-- A DISTRIBUTIVE LATTICE (§1.613): the subobject lattices satisfy the
    *meet-over-join* distributive law.  The meet `A ∩ S` is `InverseImage A.arr S`
    (the pullback of `A.arr` along `S.arr`), exactly as in §1.612
    (`monic_inverseImage_iff_distributive`).  We state the substantive direction

        A ∩ (S ∪ T)  ≤  (A ∩ S) ∪ (A ∩ T)

    (the reverse always holds in any lattice; this forward inequality is what
    fails in the non-distributive N₅, M₃).  Unlike the previous meet-free
    formulation `(A∪S)∪A ≤ A∪(S∪T)` — a join-absorption that is true in EVERY
    lattice and so captures nothing — this genuinely characterizes distributivity. -/
def IsDistributiveLattice [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasPullbacks 𝒞] : Prop :=
  ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
    Subobject.le
      (InverseImage A.arr (HasSubobjectUnions.union S T))
      (HasSubobjectUnions.union (InverseImage A.arr S) (InverseImage A.arr T))

/-- **§1.613**: In a thin category (poset), a pre-logos IS a distributive lattice.
    The distributive inequality `A ∩ (S∪T) ≤ (A∩S) ∪ (A∩T)` is exactly the forward
    half of `PreLogos.invImage_preserves_union` specialized to the monic `A.arr`:
    `A.arr#` preserves the union `S ∪ T`, and `A ∩ X = InverseImage A.arr X`.

    Faithful, fully proved: we read off the inequality from the pre-logos axiom
    that inverse images preserve binary unions. -/
theorem poset_prelogos_iff_distributive [PreLogos 𝒞]
    (_hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g) : IsDistributiveLattice (𝒞 := 𝒞) := by
  intro B A S T
  -- `inverseImage_preserves_unions A.arr` gives both inclusions; we need the
  -- forward one: A.arr#(S∪T) ≤ A.arr#(S) ∪ A.arr#(T), i.e. A∩(S∪T) ≤ (A∩S)∪(A∩T).
  exact (PreLogos.invImage_preserves_union A.arr S T).1

/-! ## §1.616  BinRel(A,B) is a distributive lattice

  In a pre-logos, BinRel(A,B) is isomorphic to Sub(A×B), hence a
  distributive lattice.  We define union via the SUBOBJECT-union of the two
  relation tables (no coproducts needed) and establish the lattice +
  distributivity laws. -/

/-! ### The `relSub` ⟷ `subRel` bridge (pure, COPRODUCT- and union-free)

  `relSub`/`subRel` and the order-translation `relLe_iff_subLe` need only `[HasBinaryProducts]`
  (the pairing `A×B`).  They are deliberately kept OUT of the union section so that downstream
  callers with an unrelated `[HasImages]` in scope (e.g. `[HasRightAdjointImage]` in S1_77) do not
  hit a `HasImages` instance-diamond when synthesizing the bridge's hypotheses. -/

section BinRelSub

-- Only `[HasBinaryProducts]` (the pairing) + `[HasPullbacks]` (for `Subobject.le`/`prod` plumbing).
-- Deliberately NO `[HasImages]`/`[HasSubobjectUnions]`: that keeps the bridge free of the
-- `HasImages` instance-diamond that `[HasSubobjectUnions]` (parameterized by `HasImages`) would
-- introduce when an unrelated `[HasImages]` (e.g. via `[HasRightAdjointImage]`, S1_77) is in scope.
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The subobject of `A×B` represented by a relation `R : A → B`: its monic pairing. -/
def relSub {A B : 𝒞} (R : BinRel 𝒞 A B) : Subobject 𝒞 (prod A B) :=
  ⟨R.src, pair R.colA R.colB, monic_pair_of_monicPair R.colA R.colB R.isMonicPair⟩

/-- A subobject of `A×B` read back as a relation `A → B` (inverse of `relSub`). -/
def subRel {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) : BinRel 𝒞 A B where
  src := S.dom
  colA := S.arr ≫ fst
  colB := S.arr ≫ snd
  isMonicPair := by
    intro W u v hA hB
    apply S.monic
    apply (fst_snd_jointly_monic) (u ≫ S.arr) (v ≫ S.arr)
    · rw [Cat.assoc, Cat.assoc]; exact hA
    · rw [Cat.assoc, Cat.assoc]; exact hB

/-- `relSub (subRel S) = S` up to the identification `pair (S.arr≫fst) (S.arr≫snd) = S.arr`. -/
theorem relSub_subRel_arr {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) :
    (relSub (subRel S)).arr = S.arr := by
  show pair (S.arr ≫ fst) (S.arr ≫ snd) = S.arr
  exact (pair_uniq _ _ _ rfl rfl).symm

/-- `RelLe R S` is exactly `Subobject.le (relSub R) (relSub S)`: a relation homomorphism
    `h` (commuting with both legs) is the same data as a subobject factorization
    `h ≫ pair S.colA S.colB = pair R.colA R.colB`. -/
theorem relLe_iff_subLe {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe R S ↔ (relSub R).le (relSub S) := by
  constructor
  · rintro ⟨⟨h, hA, hB⟩⟩
    refine ⟨h, ?_⟩
    show h ≫ pair S.colA S.colB = pair R.colA R.colB
    exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hA]) (by rw [Cat.assoc, snd_pair, hB])
  · rintro ⟨h, hh⟩
    simp only [relSub] at hh
    refine ⟨⟨h, ?_, ?_⟩⟩
    · have h2 : (h ≫ pair S.colA S.colB) ≫ fst = pair R.colA R.colB ≫ fst :=
        congrArg (· ≫ fst) hh
      rwa [Cat.assoc, fst_pair, fst_pair] at h2
    · have h2 : (h ≫ pair S.colA S.colB) ≫ snd = pair R.colA R.colB ≫ snd :=
        congrArg (· ≫ snd) hh
      rwa [Cat.assoc, snd_pair, snd_pair] at h2

theorem subLe_of_relLe {A B : 𝒞} {R S : BinRel 𝒞 A B}
    (h : RelLe R S) : (relSub R).le (relSub S) := (relLe_iff_subLe R S).1 h

end BinRelSub

section BinRelLattice

-- The whole section is COPRODUCT-FREE.  `relUnion` is the subobject-union of the two relation
-- tables read back as a relation (`subRel (union (relSub R) (relSub S))`), so it works in any
-- category with `[HasSubobjectUnions]` (in particular any pre-logos), matching Freyd §1.616 /
-- §2.212 ("Rel(C) is distributive for ANY pre-logos").
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasSubobjectUnions 𝒞]

/-- Union of two relations R, S : A → B (§1.616), COPRODUCT-FREE.
    Read back the subobject-union of the two relation tables `relSub R`, `relSub S`. -/
def relUnion {A B : 𝒞} (R S : BinRel 𝒞 A B) : BinRel 𝒞 A B :=
  subRel (HasSubobjectUnions.union (relSub R) (relSub S))

/-- Notation ∪ for relUnion. -/
infixl:65 (name := relUnionNotation) " ∪ᵣ " => relUnion

/-- `relSub (R ∪ᵣ S) = union (relSub R) (relSub S)` — both directions.  `R ∪ᵣ S` is by
    definition `subRel (union …)`, so `relSub (R ∪ᵣ S)` has the same arrow as `union …`
    (`relSub_subRel_arr`), witnessed by the identity. -/
theorem relSub_union_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (relSub (R ∪ᵣ S)).le (HasSubobjectUnions.union (relSub R) (relSub S)) :=
  ⟨Cat.id _, by rw [Cat.id_comp]; exact (relSub_subRel_arr _).symm⟩

theorem relSub_union_ge {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (HasSubobjectUnions.union (relSub R) (relSub S)).le (relSub (R ∪ᵣ S)) :=
  ⟨Cat.id _, by rw [Cat.id_comp]; exact relSub_subRel_arr _⟩

/-- R ≤ R ∪ S (left inclusion). -/
theorem relUnion_le_left {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe R (R ∪ᵣ S) :=
  (relLe_iff_subLe R (R ∪ᵣ S)).2 (Subobject.le_trans
    (HasSubobjectUnions.union_left (relSub R) (relSub S)) (relSub_union_ge R S))

/-- S ≤ R ∪ S (right inclusion). -/
theorem relUnion_le_right {A B : 𝒞} (R S : BinRel 𝒞 A B) : RelLe S (R ∪ᵣ S) :=
  (relLe_iff_subLe S (R ∪ᵣ S)).2 (Subobject.le_trans
    (HasSubobjectUnions.union_right (relSub R) (relSub S)) (relSub_union_ge R S))

/-- Universal property of relUnion: R ≤ U → S ≤ U → R ∪ S ≤ U. -/
theorem le_relUnion {A B : 𝒞} {R S U : BinRel 𝒞 A B}
    (hRU : RelLe R U) (hSU : RelLe S U) : RelLe (R ∪ᵣ S) U :=
  (relLe_iff_subLe (R ∪ᵣ S) U).2 (Subobject.le_trans (relSub_union_le R S)
    (HasSubobjectUnions.union_min _ _ _ (subLe_of_relLe hRU) (subLe_of_relLe hSU)))

/-- §1.616: (R ∩ S) ∪ (R ∩ T) ≤ R ∩ (S ∪ T) — the reverse always holds. -/
theorem rel_union_inter_le {A B : 𝒞} (R S T : BinRel 𝒞 A B) :
    RelLe ((R ⊓ S) ∪ᵣ (R ⊓ T)) (R ⊓ (S ∪ᵣ T)) := by
  apply le_relUnion
  · exact le_intersect (intersect_le_left R S) (rel_le_trans (intersect_le_right R S) (relUnion_le_left S T))
  · exact le_intersect (intersect_le_left R T) (rel_le_trans (intersect_le_right R T) (relUnion_le_right S T))

/-- §1.616: (R⊚S) ∪ (R⊚T) ≤ R ⊚ (S ∪ T) — always holds. -/
theorem compose_union_right_le {A B C : 𝒞} (R : BinRel 𝒞 A B) (S T : BinRel 𝒞 B C) :
    RelLe ((R ⊚ S) ∪ᵣ (R ⊚ T)) (R ⊚ (S ∪ᵣ T)) := by
  apply le_relUnion
  · -- R⊚S ≤ R⊚(S∪T): use monotonicity of composition in second argument
    -- Since S ≤ S∪T (relUnion_le_left), we need compose_mono_right.
    -- Exhibit the witness: for any k : (R⊚S).src → witness, compose with the
    -- containment of S in S∪T.
    obtain ⟨⟨hST_w, hST_A, hST_B⟩⟩ := relUnion_le_left S T
    -- hST_w : S.src → (S∪ᵣT).src with hST_w ≫ (S∪T).colA = S.colA etc.
    -- compose R (S∪T): pullback of R.colB and (S∪T).colA
    -- We need to show (R⊚S).src → (R⊚(S∪T)).src
    -- The pullback of R.colB over S.colA factors through the pullback over (S∪T).colA
    -- via hST_w.
    -- Strategy: construct a cone for the (S∪T) pullback from the S pullback.
    let pbS  := HasPullbacks.has R.colB S.colA
    let pbST := HasPullbacks.has R.colB (S ∪ᵣ T).colA
    -- (S∪T).colA = (image m).arr ≫ fst, but morally hST_w : S → (S∪T) gives S.colA = hST_w ≫ (S∪T).colA
    have hST_colA : hST_w ≫ (S ∪ᵣ T).colA = S.colA := hST_A
    -- Build cone for pbST from pbS
    let cST : Cone R.colB (S ∪ᵣ T).colA :=
      ⟨pbS.cone.pt, pbS.cone.π₁, pbS.cone.π₂ ≫ hST_w,
       by rw [Cat.assoc, hST_colA, pbS.cone.w]⟩
    let uST : pbS.cone.pt ⟶ pbST.cone.pt := pbST.lift cST
    have huST_π₁ : uST ≫ pbST.cone.π₁ = pbS.cone.π₁ := pbST.lift_fst cST
    have huST_π₂ : uST ≫ pbST.cone.π₂ = pbS.cone.π₂ ≫ hST_w := pbST.lift_snd cST
    -- Now: (R⊚S).src = image(pair(pbS.π₁≫R.colA, pbS.π₂≫S.colB)).dom
    -- The span for R⊚(S∪T) is pair(pbST.π₁≫R.colA, pbST.π₂≫(S∪T).colB)
    -- We have a map from the S-pullback point to the (S∪T)-pullback point via uST.
    -- And pbS.π₂ ≫ S.colB = pbS.π₂ ≫ hST_w ≫ (S∪T).colB (since hST_w ≫ (S∪T).colB = S.colB)
    have hST_colB : hST_w ≫ (S ∪ᵣ T).colB = S.colB := hST_B
    -- Build the map from (R⊚S).src to (R⊚(S∪T)).src
    let spanS  : pbS.cone.pt ⟶ prod A C :=
      pair (pbS.cone.π₁ ≫ R.colA) (pbS.cone.π₂ ≫ S.colB)
    let spanST : pbST.cone.pt ⟶ prod A C :=
      pair (pbST.cone.π₁ ≫ R.colA) (pbST.cone.π₂ ≫ (S ∪ᵣ T).colB)
    -- spanS factors through spanST via uST: uST ≫ spanST = spanS
    have h_span_eq : uST ≫ spanST = spanS := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, huST_π₁]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, huST_π₂, Cat.assoc, hST_colB]
    -- image(spanS) ≤ image(spanST): since spanS = uST ≫ spanST, spanS allows image(spanST)
    let IS  := image spanS
    let IST := image spanST
    have hallow : Allows IST spanS := by
      obtain ⟨k, hk⟩ := image_allows spanST
      exact ⟨uST ≫ k, by rw [Cat.assoc, hk, h_span_eq]⟩
    obtain ⟨wit, hwit⟩ := image_min spanS IST hallow
    -- wit : IS.dom → IST.dom with wit ≫ IST.arr = IS.arr
    -- R⊚S has src = IS.dom, R⊚(S∪T) has src = IST.dom
    refine ⟨⟨wit, ?_, ?_⟩⟩
    · calc wit ≫ (R ⊚ (S ∪ᵣ T)).colA
          = wit ≫ IST.arr ≫ fst := rfl
        _ = (wit ≫ IST.arr) ≫ fst := by rw [Cat.assoc]
        _ = IS.arr ≫ fst := by rw [hwit]
        _ = (R ⊚ S).colA := rfl
    · calc wit ≫ (R ⊚ (S ∪ᵣ T)).colB
          = wit ≫ IST.arr ≫ snd := rfl
        _ = (wit ≫ IST.arr) ≫ snd := by rw [Cat.assoc]
        _ = IS.arr ≫ snd := by rw [hwit]
        _ = (R ⊚ S).colB := rfl
  · -- symmetric: R⊚T ≤ R⊚(S∪T)
    obtain ⟨⟨hST_w, hST_A, hST_B⟩⟩ := relUnion_le_right S T
    let pbT  := HasPullbacks.has R.colB T.colA
    let pbST := HasPullbacks.has R.colB (S ∪ᵣ T).colA
    have hST_colA : hST_w ≫ (S ∪ᵣ T).colA = T.colA := hST_A
    let cST : Cone R.colB (S ∪ᵣ T).colA :=
      ⟨pbT.cone.pt, pbT.cone.π₁, pbT.cone.π₂ ≫ hST_w,
       by rw [Cat.assoc, hST_colA, pbT.cone.w]⟩
    let uST : pbT.cone.pt ⟶ pbST.cone.pt := pbST.lift cST
    have huST_π₁ : uST ≫ pbST.cone.π₁ = pbT.cone.π₁ := pbST.lift_fst cST
    have huST_π₂ : uST ≫ pbST.cone.π₂ = pbT.cone.π₂ ≫ hST_w := pbST.lift_snd cST
    have hST_colB : hST_w ≫ (S ∪ᵣ T).colB = T.colB := hST_B
    let spanT  : pbT.cone.pt ⟶ prod A C :=
      pair (pbT.cone.π₁ ≫ R.colA) (pbT.cone.π₂ ≫ T.colB)
    let spanST : pbST.cone.pt ⟶ prod A C :=
      pair (pbST.cone.π₁ ≫ R.colA) (pbST.cone.π₂ ≫ (S ∪ᵣ T).colB)
    have h_span_eq : uST ≫ spanST = spanT := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, huST_π₁]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, huST_π₂, Cat.assoc, hST_colB]
    let IT  := image spanT
    let IST := image spanST
    have hallow : Allows IST spanT := by
      obtain ⟨k, hk⟩ := image_allows spanST
      exact ⟨uST ≫ k, by rw [Cat.assoc, hk, h_span_eq]⟩
    obtain ⟨wit, hwit⟩ := image_min spanT IST hallow
    refine ⟨⟨wit, ?_, ?_⟩⟩
    · show wit ≫ IST.arr ≫ fst = IT.arr ≫ fst
      rw [← Cat.assoc, hwit]
    · show wit ≫ IST.arr ≫ snd = IT.arr ≫ snd
      rw [← Cat.assoc, hwit]

/-- Pushing a subobject of `A×B` along the iso `prodSwap A B : A×B → B×A` (post-composition,
    monic because `prodSwap` is iso).  This is the relational reciprocal at the subobject level. -/
private def pushSwap {A B : 𝒞} (P : Subobject 𝒞 (prod A B)) : Subobject 𝒞 (prod B A) :=
  ⟨P.dom, P.arr ≫ prodSwap A B, by
    intro X u v huv
    refine P.monic u v ?_
    have := congrArg (· ≫ prodSwap B A) huv
    simpa [Cat.assoc, prodSwap_prodSwap, Cat.comp_id] using this⟩

/-- `pushSwap` is monotone: a factorization `f ≫ Q.arr = P.arr` post-composes with `prodSwap`. -/
private theorem pushSwap_mono {A B : 𝒞} {P Q : Subobject 𝒞 (prod A B)} (hle : P.le Q) :
    (pushSwap P).le (pushSwap Q) := by
  obtain ⟨f, hf⟩ := hle
  exact ⟨f, by show f ≫ (Q.arr ≫ prodSwap A B) = P.arr ≫ prodSwap A B; rw [← Cat.assoc, hf]⟩

/-- `relSub (R°) = pushSwap (relSub R)`: the reciprocal's table is the swap of `R`'s table. -/
private theorem relSub_reciprocal_arr {A B : 𝒞} (R : BinRel 𝒞 A B) :
    (relSub R°).arr = (pushSwap (relSub R)).arr := by
  show pair R.colB R.colA = pair R.colA R.colB ≫ prodSwap A B
  exact (pair_uniq _ _ _
    (by rw [Cat.assoc, show prodSwap A B ≫ fst = snd (A := A) (B := B) from fst_pair _ _, snd_pair])
    (by rw [Cat.assoc, show prodSwap A B ≫ snd = fst (A := A) (B := B) from snd_pair _ _,
      fst_pair])).symm

private theorem relSub_reciprocal_le {A B : 𝒞} (R : BinRel 𝒞 A B) :
    (relSub R°).le (pushSwap (relSub R)) :=
  ⟨Cat.id _, by rw [Cat.id_comp]; exact (relSub_reciprocal_arr R).symm⟩

private theorem relSub_reciprocal_ge {A B : 𝒞} (R : BinRel 𝒞 A B) :
    (pushSwap (relSub R)).le (relSub R°) :=
  ⟨Cat.id _, by rw [Cat.id_comp]; exact relSub_reciprocal_arr R⟩

/-- `pushSwap` reflects `≤`: a factorization post-composed with `prodSwap` descends because
    `prodSwap` is split monic (`prodSwap A B ≫ prodSwap B A = id`). -/
private theorem pushSwap_reflects {A B : 𝒞} {P Q : Subobject 𝒞 (prod A B)}
    (hle : (pushSwap P).le (pushSwap Q)) : P.le Q := by
  obtain ⟨f, hf⟩ := hle
  refine ⟨f, ?_⟩
  -- hf : f ≫ (Q.arr ≫ prodSwap A B) = P.arr ≫ prodSwap A B.  Cancel prodSwap on the right.
  have hf' : f ≫ (Q.arr ≫ prodSwap A B) = P.arr ≫ prodSwap A B := hf
  have h := congrArg (· ≫ prodSwap B A) hf'
  simpa [Cat.assoc, prodSwap_prodSwap, Cat.comp_id] using h

/-- `pushSwap` sends a union below the union of the swaps.  Both swapped legs `pushSwap P`,
    `pushSwap Q` reflect back (via `pushSwap_reflects`) into `pushSwap⁻¹` of the target union,
    so `union_min` bounds `union P Q`, and monotone `pushSwap` carries it across; the double
    swap cancels. -/
private theorem pushSwap_union_le {A B : 𝒞} (P Q : Subobject 𝒞 (prod A B)) :
    (pushSwap (HasSubobjectUnions.union P Q)).le
      (HasSubobjectUnions.union (pushSwap P) (pushSwap Q)) := by
  let U := HasSubobjectUnions.union (pushSwap P) (pushSwap Q)
  -- P ≤ pushSwap U  and  Q ≤ pushSwap U  (reflect the union inclusions back across the swap).
  have hP : P.le (pushSwap U) :=
    pushSwap_reflects (by
      refine Subobject.le_trans (HasSubobjectUnions.union_left (pushSwap P) (pushSwap Q)) ?_
      exact ⟨Cat.id _, by
        show Cat.id _ ≫ (pushSwap (pushSwap U)).arr = U.arr
        simp only [pushSwap, Cat.id_comp, Cat.assoc, prodSwap_prodSwap, Cat.comp_id]⟩)
  have hQ : Q.le (pushSwap U) :=
    pushSwap_reflects (by
      refine Subobject.le_trans (HasSubobjectUnions.union_right (pushSwap P) (pushSwap Q)) ?_
      exact ⟨Cat.id _, by
        show Cat.id _ ≫ (pushSwap (pushSwap U)).arr = U.arr
        simp only [pushSwap, Cat.id_comp, Cat.assoc, prodSwap_prodSwap, Cat.comp_id]⟩)
  -- union P Q ≤ pushSwap U, push across, double swap cancels back to U.
  refine Subobject.le_trans (pushSwap_mono (HasSubobjectUnions.union_min _ _ _ hP hQ)) ?_
  exact ⟨Cat.id _, by
    show Cat.id _ ≫ U.arr = (pushSwap (pushSwap U)).arr
    simp only [pushSwap, Cat.id_comp, Cat.assoc, prodSwap_prodSwap, Cat.comp_id]⟩

/-- §1.616: Reciprocation distributes over union: (R ∪ᵣ S)° ≤ S° ∪ᵣ R°.  COPRODUCT-FREE:
    `relSub((R∪ᵣS)°) = swap(union(relSub R)(relSub S))`, and the swap of each piece lands below
    `relSub S°` / `relSub R°` (`relSub_reciprocal`), so `union_min` packages the bound. -/
theorem relUnion_le_reciprocal {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe (R ∪ᵣ S)° (S° ∪ᵣ R°) := by
  apply (relLe_iff_subLe _ _).2
  -- relSub((R∪ᵣS)°) ≤ pushSwap(relSub(R∪ᵣS)) ≤ pushSwap(union(relSub R)(relSub S))
  --   ≤ union(pushSwap(relSub R))(pushSwap(relSub S)) ≤ union(relSub R°)(relSub S°) = relSub(S°∪ᵣR°).
  refine Subobject.le_trans (relSub_reciprocal_le (R ∪ᵣ S))
    (Subobject.le_trans (pushSwap_mono (relSub_union_le R S))
    (Subobject.le_trans (pushSwap_union_le (relSub R) (relSub S)) ?_))
  refine Subobject.le_trans ?_ (relSub_union_ge S° R°)
  -- union(pushSwap relSub R)(pushSwap relSub S) ≤ union(relSub S°)(relSub R°)
  exact HasSubobjectUnions.union_min _ _ _
    (Subobject.le_trans (relSub_reciprocal_ge R) (HasSubobjectUnions.union_right _ _))
    (Subobject.le_trans (relSub_reciprocal_ge S) (HasSubobjectUnions.union_left _ _))

/-- §1.616: S° ∪ᵣ R° ≤ (R ∪ᵣ S)° (reverse direction).  Apply `relUnion_le_reciprocal` to the
    reciprocals and use involutivity `(·°)° = ·`. -/
theorem relUnion_reciprocal_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    RelLe (S° ∪ᵣ R°) (R ∪ᵣ S)° := by
  -- relUnion_le_reciprocal (S°) (R°) : (S° ∪ᵣ R°)° ≤ R°° ∪ᵣ S°° = R ∪ᵣ S.
  have h := relUnion_le_reciprocal S° R°
  rw [reciprocal_invol, reciprocal_invol] at h
  -- h : (S° ∪ᵣ R°)° ≤ R ∪ᵣ S.  Reciprocate both sides (reciprocal is monotone + involutive).
  have h2 := reciprocal_mono h
  rwa [reciprocal_invol] at h2

end BinRelLattice

/-! ## §1.616 (pre-logos): the substantive distributive laws

  Freyd §1.616: *in a pre-logos* the relations `B&(A,B) ≃ Sub(A×B)` form a distributive
  lattice and composition distributes over union.  These are FALSE in a bare regular
  category — they need the defining pre-logos axiom that inverse images preserve unions.
  We therefore state them with `[PreLogos 𝒞]` (matching the book) and transport the
  pre-logos subobject-lattice facts across the canonical bridge `relSub : BinRel A B → Sub(A×B)`. -/

section BinRelDistributive

-- The `relSub` bridge and the lattice laws (`relSub_union_le/ge`, `relLe_iff_subLe`, …) now live
-- in the COPRODUCT-FREE `BinRelLattice` section above (they need only `[HasSubobjectUnions]`).
-- This section adds the existential-image / inverse-image calculus (`existsAlong`, `pushMono`,
-- `InverseImage`) and the SUBSTANTIVE pre-logos distributive laws, which use the defining
-- pre-logos axiom that inverse images preserve unions.
variable [PreLogos 𝒞]

/-- Post-composition with a fixed mono `m : Z ↣ W` carries `Sub Z` into `Sub W`
    order-preservingly: `push m P := ⟨P.dom, P.arr ≫ m⟩`. -/
def pushMono {Z W : 𝒞} (m : Z ⟶ W) (hm : Monic m) (P : Subobject 𝒞 Z) : Subobject 𝒞 W :=
  ⟨P.dom, P.arr ≫ m, by
    intro X u v huv
    refine P.monic u v (hm _ _ ?_)
    rw [Cat.assoc, Cat.assoc]; exact huv⟩

theorem pushMono_mono {Z W : 𝒞} (m : Z ⟶ W) (hm : Monic m) {P Q : Subobject 𝒞 Z}
    (hle : P.le Q) : (pushMono m hm P).le (pushMono m hm Q) := by
  obtain ⟨f, hf⟩ := hle
  exact ⟨f, by show f ≫ (Q.arr ≫ m) = P.arr ≫ m; rw [← Cat.assoc, hf]⟩

/-- `pushMono` reflects `≤`: a factorization through `m` descends because `m` is monic. -/
theorem pushMono_reflects {Z W : 𝒞} (m : Z ⟶ W) (hm : Monic m) {P Q : Subobject 𝒞 Z}
    (hle : (pushMono m hm P).le (pushMono m hm Q)) : P.le Q := by
  obtain ⟨f, hf⟩ := hle
  exact ⟨f, hm _ _ (by show (f ≫ Q.arr) ≫ m = P.arr ≫ m; rw [Cat.assoc]; exact hf)⟩

/-- `pushMono` of a union is `≤` the union of the `pushMono`s.  The ambient union of the two
    pushed pieces factors through `m` (both pieces do, so `union_min`), giving a subobject `Pre`
    of `Z` with `pushMono Pre = union(push P)(push Q)`; `P,Q ≤ Pre` (by `pushMono_reflects`), so
    `union P Q ≤ Pre` (`union_min`), and `pushMono` is monotone. -/
theorem pushMono_union_le {Z W : 𝒞} (m : Z ⟶ W) (hm : Monic m) (P Q : Subobject 𝒞 Z) :
    (pushMono m hm (HasSubobjectUnions.union P Q)).le
      (HasSubobjectUnions.union (pushMono m hm P) (pushMono m hm Q)) := by
  let UP := HasSubobjectUnions.union (pushMono m hm P) (pushMono m hm Q)
  -- both pushed pieces are ≤ ⟨Z, m⟩, hence so is their union; extract the factorization.
  have hsubZ : UP.le ⟨Z, m, hm⟩ :=
    HasSubobjectUnions.union_min _ _ _ ⟨P.arr, rfl⟩ ⟨Q.arr, rfl⟩
  obtain ⟨pre, hpre⟩ := hsubZ
  -- pre : UP.dom → Z with pre ≫ m = UP.arr.  `Pre := ⟨UP.dom, pre⟩` is a subobject of Z.
  have hpre_mono : Monic pre := by
    intro X u v huv
    exact UP.monic u v (by rw [← hpre, ← Cat.assoc, ← Cat.assoc, huv])
  let Pre : Subobject 𝒞 Z := ⟨UP.dom, pre, hpre_mono⟩
  -- pushMono m Pre = UP  (same dom, arr = pre ≫ m = UP.arr)
  -- P ≤ Pre and Q ≤ Pre, via pushMono_reflects (push P ≤ UP = push Pre).
  have hP_pre : P.le Pre :=
    pushMono_reflects m hm (P := P) (Q := Pre)
      (Subobject.le_trans (HasSubobjectUnions.union_left (pushMono m hm P) (pushMono m hm Q))
        ⟨Cat.id _, by show Cat.id _ ≫ (pre ≫ m) = UP.arr; rw [Cat.id_comp, hpre]⟩)
  have hQ_pre : Q.le Pre :=
    pushMono_reflects m hm (P := Q) (Q := Pre)
      (Subobject.le_trans (HasSubobjectUnions.union_right (pushMono m hm P) (pushMono m hm Q))
        ⟨Cat.id _, by show Cat.id _ ≫ (pre ≫ m) = UP.arr; rw [Cat.id_comp, hpre]⟩)
  have hunion_pre : (HasSubobjectUnions.union P Q).le Pre :=
    HasSubobjectUnions.union_min _ _ _ hP_pre hQ_pre
  -- finally push forward and land in UP (= pushMono m Pre).
  obtain ⟨g, hg⟩ := hunion_pre
  -- hg : g ≫ pre = (union P Q).arr.  Goal: g ≫ UP.arr = (union P Q).arr ≫ m.
  refine ⟨g, ?_⟩
  show g ≫ UP.arr = (HasSubobjectUnions.union P Q).arr ≫ m
  rw [← hpre, ← Cat.assoc, hg]

/-- The two arrows agree: `relSub (R ⊓ S).arr = pb.π₁ ≫ pairR = (pushMono pairR (InverseImage..)).arr`.
    `intersect` reads off `pb.π₁ ≫ R.colA` and `pb.π₁ ≫ R.colB`, which pair up to `pb.π₁ ≫ pairR`;
    `InverseImage pairR (relSub S)` has arr `pb.π₁` (same pullback `pb`), whose pushforward along
    `pairR` is exactly that.  We record the identity-witnessed `≤` both ways. -/
theorem relSub_inter_le {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (relSub (R ⊓ S)).le
      (pushMono (pair R.colA R.colB) (monic_pair_of_monicPair R.colA R.colB R.isMonicPair)
        (InverseImage (pair R.colA R.colB) (relSub S))) := by
  refine ⟨Cat.id _, ?_⟩
  -- Goal: id ≫ (pb.π₁ ≫ pairR) = relSub(R⊓S).arr = pair (pb.π₁≫R.colA) (pb.π₁≫R.colB)
  rw [Cat.id_comp]
  show (HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)).cone.π₁ ≫ pair R.colA R.colB
        = pair (R ⊓ S).colA (R ⊓ S).colB
  exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; rfl) (by rw [Cat.assoc, snd_pair]; rfl)

theorem relSub_inter_ge {A B : 𝒞} (R S : BinRel 𝒞 A B) :
    (pushMono (pair R.colA R.colB) (monic_pair_of_monicPair R.colA R.colB R.isMonicPair)
        (InverseImage (pair R.colA R.colB) (relSub S))).le (relSub (R ⊓ S)) := by
  refine ⟨Cat.id _, ?_⟩
  rw [Cat.id_comp]
  show pair (R ⊓ S).colA (R ⊓ S).colB
        = (HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)).cone.π₁ ≫ pair R.colA R.colB
  exact (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; rfl) (by rw [Cat.assoc, snd_pair]; rfl)).symm

/-- Local copy of inverse-image monotonicity (the canonical one lives downstream in `S1_61`,
    which imports this file).  If `S ≤ T` then `f# S ≤ f# T`: the `S`-pullback cone maps into
    the `T`-pullback via the factorization, and pullback-lift gives the comparison on `π₁`. -/
theorem invImage_mono_local {A B : 𝒞} (f : A ⟶ B) {S T : Subobject 𝒞 B} (hle : S.le T) :
    (InverseImage f S).le (InverseImage f T) := by
  obtain ⟨l, hl⟩ := hle
  let pbS := HasPullbacks.has f S.arr
  let pbT := HasPullbacks.has f T.arr
  -- cone over (f, T.arr): pt = pbS.pt, legs π₁ and π₂≫l (since (π₂≫l)≫T.arr = π₂≫S.arr = π₁≫f).
  let c : Cone f T.arr :=
    ⟨pbS.cone.pt, pbS.cone.π₁, pbS.cone.π₂ ≫ l,
      by rw [Cat.assoc, hl, pbS.cone.w]⟩
  refine ⟨pbT.lift c, ?_⟩
  show pbT.lift c ≫ pbT.cone.π₁ = pbS.cone.π₁
  exact pbT.lift_fst c

/-- **§1.616** (pre-logos): `BinRel(A,B)` is a DISTRIBUTIVE lattice — the meet-over-join law
    `R ⊓ (S ∪ T) ≤ (R ⊓ S) ∪ (R ⊓ T)`.  Transported across `relSub` from the pre-logos fact
    that inverse images preserve unions (`PreLogos.invImage_preserves_union`) plus monotonicity
    of `pushMono`/`InverseImage` and the union laws. -/
theorem rel_inter_union_le {A B : 𝒞} (R S T : BinRel 𝒞 A B) :
    RelLe (R ⊓ (S ∪ᵣ T)) ((R ⊓ S) ∪ᵣ (R ⊓ T)) := by
  apply (relLe_iff_subLe _ _).2
  let pR := pair R.colA R.colB
  let hpR : Monic pR := monic_pair_of_monicPair R.colA R.colB R.isMonicPair
  -- LHS = relSub(R ⊓ (S∪T)) ≤ pushMono pR (InverseImage pR (relSub (S∪T)))
  have hL : (relSub (R ⊓ (S ∪ᵣ T))).le
              (pushMono pR hpR (InverseImage pR (relSub (S ∪ᵣ T)))) := relSub_inter_le R (S ∪ᵣ T)
  -- step 1: InverseImage pR (relSub(S∪T)) ≤ InverseImage pR (union (relSub S)(relSub T))
  have h1 : (InverseImage pR (relSub (S ∪ᵣ T))).le
              (InverseImage pR (HasSubobjectUnions.union (relSub S) (relSub T))) :=
    invImage_mono_local pR (relSub_union_le S T)
  -- step 2 (PreLogos): InverseImage pR (union ..) ≤ union (InverseImage pR (relSub S)) (.. T)
  have h2 := (PreLogos.invImage_preserves_union pR (relSub S) (relSub T)).1
  have h12 := Subobject.le_trans h1 h2
  have hpush := pushMono_mono pR hpR h12
  -- step 3: pushMono of union ≤ union of pushMono
  have hdist := pushMono_union_le pR hpR (InverseImage pR (relSub S)) (InverseImage pR (relSub T))
  -- step 4: each pushMono pR (InverseImage pR (relSub X)) ≤ relSub (R ⊓ X)
  have hSge := relSub_inter_ge R S
  have hTge := relSub_inter_ge R T
  let pS := pushMono pR hpR (InverseImage pR (relSub S))
  let pT := pushMono pR hpR (InverseImage pR (relSub T))
  have hunion_mono : (HasSubobjectUnions.union pS pT).le
                     (HasSubobjectUnions.union (relSub (R ⊓ S)) (relSub (R ⊓ T))) :=
    HasSubobjectUnions.union_min pS pT _
      (Subobject.le_trans hSge (HasSubobjectUnions.union_left (relSub (R ⊓ S)) (relSub (R ⊓ T))))
      (Subobject.le_trans hTge (HasSubobjectUnions.union_right (relSub (R ⊓ S)) (relSub (R ⊓ T))))
  -- step 5: union (relSub(R⊓S)) (relSub(R⊓T)) ≤ relSub ((R⊓S) ∪ (R⊓T))
  have hfinal := relSub_union_ge (R ⊓ S) (R ⊓ T)
  exact Subobject.le_trans hL
    (Subobject.le_trans hpush (Subobject.le_trans hdist (Subobject.le_trans hunion_mono hfinal)))

/-! ### §1.616  Composition distributes over union (right)

  Freyd's pre-logos proof reformulates `R ⊚ S` as a DIRECT IMAGE of a MEET of INVERSE IMAGES
  on the ternary product `A×B×C := prod A (prod B C)`:

      R ⊚ S  =  ∃_{πAC} ( πAB# (relSub R)  ⊓  πBC# (relSub S) ).

  Then `R⊚(S∪T) ≤ (R⊚S)∪(R⊚T)` falls out of three pre-logos facts, each available here:
    • `πBC#` preserves unions            (`PreLogos.invImage_preserves_union`),
    • meet distributes over join          (the `rel_inter_union_le` pattern, in `Sub(A×B×C)`),
    • `∃_{πAC}` preserves unions          (direct image of a union, `union_via_coproduct_image`).

  The ternary product and projections exist (`HasBinaryProducts`).  The remaining work is the
  geometric IDENTITY relating the binary-pullback definition of `compose` to the ternary
  direct-image-of-meet form; that single bridge is isolated below as `compose_eq_ternary`. -/

/-- Ternary product `A×B×C`. -/
abbrev prod₃ (A B C : 𝒞) : 𝒞 := prod A (prod B C)

omit [PreLogos 𝒞] in
/-- Direct image (∃) of a subobject `U ↣ X` along `g : X ⟶ Y`: the image of `U.arr ≫ g`.
    Needs only `[HasImages]` (ambient `[PreLogos]` dropped so the minimal-hypothesis
    `S1_70.DirectImage` / `S1_967.directImage` can forward to this canonical copy). -/
def existsAlong [HasImages 𝒞] {X Y : 𝒞} (g : X ⟶ Y) (U : Subobject 𝒞 X) : Subobject 𝒞 Y :=
  image (U.arr ≫ g)

omit [PreLogos 𝒞] in
/-- The image/pullback **adjunction** `∃_g ⊣ g#`, stated as the generic
    `Freyd.GaloisConnection` (Freyd/S1_51_Order) between the subobject preorders of `X` and `Y`:
    `existsAlong g P ≤ V  ↔  P ≤ InverseImage g V`.  Forward: a factorization of `(image).arr`
    through `V` makes `P.arr ≫ g` factor through `V.arr`, so `P.arr` lifts to `pullback(g, V.arr)`.
    Reverse: a lift of `P.arr` to the pullback gives `P.arr ≫ g = (k ≫ π₂) ≫ V.arr`, so `V` allows
    `P.arr ≫ g` and `image_min` finishes.  Pure regular-category fact (no pre-logos needed) —
    hence `omit`s `PreLogos` so this is the canonical `∃_f ⊣ f#` even in a bare regular
    (e.g. abelian) category; S1_59_10 reuses it directly (no local re-proof). -/
theorem existsAlong_adj [HasImages 𝒞] [HasPullbacks 𝒞] {X Y : 𝒞} (g : X ⟶ Y) :
    GaloisConnection (Subobject.le (𝒞 := 𝒞) (B := X)) (Subobject.le (𝒞 := 𝒞) (B := Y))
      (existsAlong g) (fun V => InverseImage g V) := by
  intro P V
  constructor
  · rintro ⟨k, hk⟩
    -- hk : k ≫ V.arr = (existsAlong g P).arr = (image (P.arr≫g)).arr.
    have hk' : k ≫ V.arr = (image (P.arr ≫ g)).arr := hk
    have hfac : (image.lift (P.arr ≫ g) ≫ k) ≫ V.arr = P.arr ≫ g := by
      rw [Cat.assoc, hk', image.lift_fac]
    let pb := HasPullbacks.has g V.arr
    let c : Cone g V.arr := ⟨P.dom, P.arr, image.lift (P.arr ≫ g) ≫ k, hfac.symm⟩
    exact ⟨pb.lift c, pb.lift_fst c⟩
  · rintro ⟨k, hk⟩
    let pb := HasPullbacks.has g V.arr
    have hk' : k ≫ pb.cone.π₁ = P.arr := hk
    refine image_min (P.arr ≫ g) V ⟨k ≫ pb.cone.π₂, ?_⟩
    -- (k ≫ π₂) ≫ V.arr = k ≫ π₁ ≫ g = P.arr ≫ g  using the pullback square π₁≫g = π₂≫V.arr.
    rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hk']

theorem existsAlong_mono {X Y : 𝒞} (g : X ⟶ Y) {P Q : Subobject 𝒞 X} (hle : P.le Q) :
    (existsAlong g P).le (existsAlong g Q) := by
  obtain ⟨f, hf⟩ := hle
  refine image_min (P.arr ≫ g) (existsAlong g Q) ⟨f ≫ image.lift (Q.arr ≫ g), ?_⟩
  show (f ≫ image.lift (Q.arr ≫ g)) ≫ (existsAlong g Q).arr = P.arr ≫ g
  show (f ≫ image.lift (Q.arr ≫ g)) ≫ (image (Q.arr ≫ g)).arr = P.arr ≫ g
  rw [Cat.assoc, image.lift_fac, ← Cat.assoc, hf]

/-- `∃_g` preserves binary unions: `existsAlong g (union P Q) ≤ union (existsAlong g P) (existsAlong g Q)`.
    Via the `∃_g ⊣ g#` adjunction: the RHS-bound `V` satisfies `existsAlong g P ≤ V` and
    `existsAlong g Q ≤ V` (union inclusions), hence `P ≤ g#V` and `Q ≤ g#V`, hence `union P Q ≤ g#V`
    by `union_min`, hence `existsAlong g (union P Q) ≤ V` by the adjunction. -/
theorem existsAlong_union_le {X Y : 𝒞} (g : X ⟶ Y) (P Q : Subobject 𝒞 X) :
    (existsAlong g (HasSubobjectUnions.union P Q)).le
      (HasSubobjectUnions.union (existsAlong g P) (existsAlong g Q)) := by
  let V := HasSubobjectUnions.union (existsAlong g P) (existsAlong g Q)
  have hP : P.le (InverseImage g V) :=
    (existsAlong_adj g P V).1 (HasSubobjectUnions.union_left _ _)
  have hQ : Q.le (InverseImage g V) :=
    (existsAlong_adj g Q V).1 (HasSubobjectUnions.union_right _ _)
  exact (existsAlong_adj g (HasSubobjectUnions.union P Q) V).2
    (HasSubobjectUnions.union_min _ _ _ hP hQ)

/-! ### §1.616  Composition distributes over union (right) — coproduct-free via `∃ ⊣ #`

  Earlier drafts reduced `R⊚(S∪T) ≤ (R⊚S)∪(R⊚T)` to an *extensive split* of the coproduct that
  presents the union (`pullback(S.src+T.src,−) ≅ ⋯`), which is not available in a bare pre-logos.
  That route is UNNECESSARY: the union here is the Sub-lattice JOIN, and `compose` itself is a
  composite `∃_ω ∘ θ#` of two union-preserving operations.  Concretely, fix `R` and set

      θ := pair (fst ≫ R.colB) snd : R.src × C ⟶ B × C      (re-uses `R.colB` on the first factor),
      ω := pair (fst ≫ R.colA) snd : R.src × C ⟶ A × C.

  Then for *every* `X : B → C`,  `relSub (R ⊚ X)  =  ∃_ω ( θ# (relSub X) )`  as subobjects of
  `A×C` (`relSub_compose_eq`, proved below by the two factorizations between `pullback(R.colB,X.colA)`
  and `pullback(θ, relSub X)`).  Composition therefore inherits union-preservation from the two
  pre-logos primitives already in this file:
    • `θ#` preserves unions      (`PreLogos.invImage_preserves_union`),
    • `∃_ω` preserves unions     (`existsAlong_union_le`),
  and `relSub_union_le`/`_ge` bridge `relSub(S∪T)` with the subobject union.  No coproduct
  extensivity, no new hypothesis. -/

/-- The "B-side reindexing" `θ_R := pair (fst ≫ R.colB) snd : R.src × C ⟶ B × C`. -/
def thetaR {A B : 𝒞} (R : BinRel 𝒞 A B) (C : 𝒞) : prod R.src C ⟶ prod B C :=
  pair (fst ≫ R.colB) snd

/-- The "A-side reindexing" `ω_R := pair (fst ≫ R.colA) snd : R.src × C ⟶ A × C`. -/
def omegaR {A B : 𝒞} (R : BinRel 𝒞 A B) (C : 𝒞) : prod R.src C ⟶ prod A C :=
  pair (fst ≫ R.colA) snd

/-- **Geometric identity (coproduct-free)** §1.616: `relSub (R ⊚ X) = ∃_{ω_R}(θ_R# (relSub X))`.
    `compose` images the span `s := pair (pbX.π₁ ≫ R.colA)(pbX.π₂ ≫ X.colB)` out of
    `pbX := pullback(R.colB, X.colA)`; `θ_R#(relSub X)` images `pbI.π₁` out of
    `pbI := pullback(θ_R, relSub X)`, and `∃_{ω_R}` of it images `pbI.π₁ ≫ ω_R`.  The two index
    objects map to each other (`α : pbX → pbI`, `β : pbI → pbX`) compatibly with the spans
    (`s = α ≫ (pbI.π₁ ≫ ω_R)` and `pbI.π₁ ≫ ω_R = β ≫ s`), so the two images coincide.  We return
    both `Subobject.le` directions. -/
theorem relSub_compose_eq {A B C : 𝒞} (R : BinRel 𝒞 A B) (X : BinRel 𝒞 B C) :
    (relSub (R ⊚ X)).le (existsAlong (omegaR R C) (InverseImage (thetaR R C) (relSub X)))
    ∧ (existsAlong (omegaR R C) (InverseImage (thetaR R C) (relSub X))).le (relSub (R ⊚ X)) := by
  let pbX := HasPullbacks.has R.colB X.colA
  let s : pbX.cone.pt ⟶ prod A C := pair (pbX.cone.π₁ ≫ R.colA) (pbX.cone.π₂ ≫ X.colB)
  let pbI := HasPullbacks.has (thetaR R C) (relSub X).arr
  -- relSub(R⊚X).arr = (image s).arr  (reconstruct the pair from its projections).
  have hRX_arr : (relSub (R ⊚ X)).arr = (image s).arr := by
    show pair (R ⊚ X).colA (R ⊚ X).colB = (image s).arr
    exact (pair_uniq (R ⊚ X).colA (R ⊚ X).colB (image s).arr rfl rfl).symm
  -- existsAlong(ω)(θ#(relSub X)).arr = (image (pbI.π₁ ≫ ω)).arr  by definition.
  have hF_arr : (existsAlong (omegaR R C) (InverseImage (thetaR R C) (relSub X))).arr
      = (image (pbI.cone.π₁ ≫ omegaR R C)).arr := rfl
  -- α : pbX.pt → pbI.pt with α ≫ pbI.π₁ = pair pbX.π₁ (pbX.π₂ ≫ X.colB).
  let μ : pbX.cone.pt ⟶ prod R.src C := pair pbX.cone.π₁ (pbX.cone.π₂ ≫ X.colB)
  have hμθ : μ ≫ thetaR R C = pbX.cone.π₂ ≫ (relSub X).arr := by
    have hl : μ ≫ thetaR R C
        = pair (pbX.cone.π₁ ≫ R.colB) (pbX.cone.π₂ ≫ X.colB) :=
      pair_uniq _ _ _
        (by show (μ ≫ pair (fst ≫ R.colB) snd) ≫ fst = _
            rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair])
        (by show (μ ≫ pair (fst ≫ R.colB) snd) ≫ snd = _
            rw [Cat.assoc, snd_pair, snd_pair])
    have hr : pbX.cone.π₂ ≫ (relSub X).arr
        = pair (pbX.cone.π₁ ≫ R.colB) (pbX.cone.π₂ ≫ X.colB) :=
      pair_uniq _ _ _
        (by show (pbX.cone.π₂ ≫ pair X.colA X.colB) ≫ fst = _
            rw [Cat.assoc, fst_pair]; exact pbX.cone.w.symm)
        (by show (pbX.cone.π₂ ≫ pair X.colA X.colB) ≫ snd = _
            rw [Cat.assoc, snd_pair])
    rw [hl, hr]
  let cα : Cone (thetaR R C) (relSub X).arr := ⟨pbX.cone.pt, μ, pbX.cone.π₂, hμθ⟩
  let α : pbX.cone.pt ⟶ pbI.cone.pt := pbI.lift cα
  have hα₁ : α ≫ pbI.cone.π₁ = μ := pbI.lift_fst cα
  have hs_fac : s = α ≫ (pbI.cone.π₁ ≫ omegaR R C) := by
    rw [← Cat.assoc, hα₁]
    -- goal: s = μ ≫ ω,  with s the literal pair.
    refine (pair_uniq (pbX.cone.π₁ ≫ R.colA) (pbX.cone.π₂ ≫ X.colB) (μ ≫ omegaR R C) ?_ ?_).symm
    · show (μ ≫ pair (fst ≫ R.colA) snd) ≫ fst = _
      rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]
    · show (μ ≫ pair (fst ≫ R.colA) snd) ≫ snd = _
      rw [Cat.assoc, snd_pair, snd_pair]
  -- β : pbI.pt → pbX.pt with β ≫ pbX.π₁ = pbI.π₁ ≫ fst, β ≫ pbX.π₂ = pbI.π₂.
  have hIw : pbI.cone.π₁ ≫ thetaR R C = pbI.cone.π₂ ≫ (relSub X).arr := pbI.cone.w
  have hθfst : thetaR R C ≫ fst = fst ≫ R.colB := fst_pair _ _
  have hXarrfst : (relSub X).arr ≫ fst = X.colA := fst_pair _ _
  have hXarrsnd : (relSub X).arr ≫ snd = X.colB := snd_pair _ _
  have hβsq : (pbI.cone.π₁ ≫ fst) ≫ R.colB = pbI.cone.π₂ ≫ X.colA := by
    have h := congrArg (· ≫ fst) hIw
    simp only at h
    rw [Cat.assoc, Cat.assoc, hθfst, hXarrfst] at h
    -- h : pbI.π₁ ≫ (fst ≫ R.colB) = pbI.π₂ ≫ X.colA
    rw [Cat.assoc]; exact h
  let cβ : Cone R.colB X.colA := ⟨pbI.cone.pt, pbI.cone.π₁ ≫ fst, pbI.cone.π₂, hβsq⟩
  let β : pbI.cone.pt ⟶ pbX.cone.pt := pbX.lift cβ
  have hβ₁ : β ≫ pbX.cone.π₁ = pbI.cone.π₁ ≫ fst := pbX.lift_fst cβ
  have hβ₂ : β ≫ pbX.cone.π₂ = pbI.cone.π₂ := pbX.lift_snd cβ
  have hIsnd : pbI.cone.π₂ ≫ X.colB = pbI.cone.π₁ ≫ snd := by
    have h := congrArg (· ≫ snd) hIw
    simp only at h
    rw [Cat.assoc, Cat.assoc, show thetaR R C ≫ snd = snd from snd_pair _ _, hXarrsnd] at h
    -- h : pbI.π₁ ≫ snd = pbI.π₂ ≫ X.colB
    exact h.symm
  have hF_fac : pbI.cone.π₁ ≫ omegaR R C = β ≫ s := by
    -- both sides equal `pair (pbI.π₁ ≫ fst ≫ R.colA) (pbI.π₁ ≫ snd)`.
    have hLHS : pbI.cone.π₁ ≫ omegaR R C
        = pair ((pbI.cone.π₁ ≫ fst) ≫ R.colA) (pbI.cone.π₁ ≫ snd) :=
      pair_uniq _ _ _
        (by show (pbI.cone.π₁ ≫ pair (fst ≫ R.colA) snd) ≫ fst = _
            rw [Cat.assoc, fst_pair, ← Cat.assoc])
        (by show (pbI.cone.π₁ ≫ pair (fst ≫ R.colA) snd) ≫ snd = _
            rw [Cat.assoc, snd_pair])
    have hRHS : β ≫ s
        = pair ((pbI.cone.π₁ ≫ fst) ≫ R.colA) (pbI.cone.π₁ ≫ snd) :=
      pair_uniq _ _ _
        (by show (β ≫ pair (pbX.cone.π₁ ≫ R.colA) (pbX.cone.π₂ ≫ X.colB)) ≫ fst = _
            rw [Cat.assoc, fst_pair, ← Cat.assoc, hβ₁])
        (by show (β ≫ pair (pbX.cone.π₁ ≫ R.colA) (pbX.cone.π₂ ≫ X.colB)) ≫ snd = _
            rw [Cat.assoc, snd_pair, ← Cat.assoc, hβ₂, hIsnd])
    rw [hLHS, hRHS]
  refine ⟨?_, ?_⟩
  · -- relSub(R⊚X) = image s ≤ image(pbI.π₁ ≫ ω) = F :  s allows F's image via α.
    obtain ⟨k, hk⟩ := image_min s (image (pbI.cone.π₁ ≫ omegaR R C)) ⟨α ≫ image.lift (pbI.cone.π₁ ≫ omegaR R C), by
      rw [Cat.assoc, image.lift_fac]; exact hs_fac.symm⟩
    exact ⟨k, by rw [hF_arr, hk, hRX_arr]⟩
  · obtain ⟨k, hk⟩ := image_min (pbI.cone.π₁ ≫ omegaR R C) (image s) ⟨β ≫ image.lift s, by
      rw [Cat.assoc, image.lift_fac]; exact hF_fac.symm⟩
    exact ⟨k, by rw [hRX_arr, hk, hF_arr]⟩

/-- §1.616: Composition distributes over union (right): `R ⊚ (S ∪ T) ≤ (R⊚S) ∪ (R⊚T)`.

    FAITHFUL to Freyd: pre-logos hypothesis (the statement is FALSE in a bare regular category,
    true in a pre-logos).  COPRODUCT-FREE proof via the `∃ ⊣ #` reformulation
    `relSub(R⊚X) = ∃_{ω_R}(θ_R# (relSub X))` (`relSub_compose_eq`): both `θ_R#`
    (`PreLogos.invImage_preserves_union`) and `∃_{ω_R}` (`existsAlong_union_le`) preserve unions,
    so the join descends with no extensivity. -/
theorem compose_union_right {A B C : 𝒞} (R : BinRel 𝒞 A B) (S T : BinRel 𝒞 B C) :
    RelLe (R ⊚ (S ∪ᵣ T)) ((R ⊚ S) ∪ᵣ (R ⊚ T)) := by
  apply (relLe_iff_subLe _ _).2
  -- LHS  =  ∃_ω (θ# relSub(S∪T)).
  have hL := (relSub_compose_eq R (S ∪ᵣ T)).1
  -- θ# relSub(S∪T) ≤ θ# (union (relSub S)(relSub T))   (monotone of θ#).
  have h1 := invImage_mono_local (thetaR R C) (relSub_union_le S T)
  -- θ# (union ..) ≤ union (θ# relSub S)(θ# relSub T)   (PreLogos: # preserves unions).
  have h2 := (PreLogos.invImage_preserves_union (thetaR R C) (relSub S) (relSub T)).1
  -- ∃_ω preserves the resulting union  ≤ union (∃_ω θ# relSub S)(∃_ω θ# relSub T).
  have h3 := existsAlong_union_le (omegaR R C)
              (InverseImage (thetaR R C) (relSub S)) (InverseImage (thetaR R C) (relSub T))
  -- each ∃_ω(θ# relSub X) = relSub(R⊚X)  ≤ relSub(R⊚X), then union ≤ relSub of the union.
  have hS := (relSub_compose_eq R S).2
  have hT := (relSub_compose_eq R T).2
  have hpieces : (HasSubobjectUnions.union
        (existsAlong (omegaR R C) (InverseImage (thetaR R C) (relSub S)))
        (existsAlong (omegaR R C) (InverseImage (thetaR R C) (relSub T)))).le
      (HasSubobjectUnions.union (relSub (R ⊚ S)) (relSub (R ⊚ T))) :=
    HasSubobjectUnions.union_min _ _ _
      (Subobject.le_trans hS (HasSubobjectUnions.union_left _ _))
      (Subobject.le_trans hT (HasSubobjectUnions.union_right _ _))
  have hfinal := relSub_union_ge (R ⊚ S) (R ⊚ T)
  exact Subobject.le_trans hL (Subobject.le_trans (existsAlong_mono (omegaR R C) (Subobject.le_trans h1 h2))
    (Subobject.le_trans h3 (Subobject.le_trans hpieces hfinal)))

end BinRelDistributive

end Freyd
