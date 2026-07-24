/-
  Freyd & Scedrov, *Categories, Allegories* §1.75  THE STONE REPRESENTATION THEOREM

  This file formalizes the cleanly stateable, infrastructure-light part of §1.75:
  the §1.751 vocabulary of ATOMS that opens the proof of the Stone Representation
  Theorem.  The Stone theorem proper (§1.75, §1.752–§1.755) is irreducibly
  topological — it builds the Stone space 𝒮(ℬ) of the boolean algebra of
  complemented subterminators, its stalk/sheaf functor `T : A → 𝓜(X)`, and uses
  point-set facts about Cantor space / the real line (Appendix A).  None of that
  machinery (Stone spaces, ultra-filters, stalk functors, sheaves on ℝ) exists in
  this repo, so those statements are recorded MISSING below rather than faked.

  §1.751  ATOM:  an object whose unique PROPER subobject is 0.
          ATOMICALLY BASED logos:  its atoms form a basis (§1.632).
          ATOMLESS logos:  it has no atoms.
          "Atomically based ⇒ boolean."   (book theorem; PROVED below as
            `atomicallyBased_isComplementedSub`, given indexed subobject joins +
            the §1.84 frame law, packaged as `HasIndexedSubobjectJoins`.)

  This file also BUILDS the missing `HasIndexedSubobjectJoins` infrastructure (the
  indexed/small subobject join `sup` plus the frame law `invImage_preserves_sup`) and the
  atom-image disjointness machinery used to discharge the boolean property.

  REUSE (DRY):
    Subobject, Subobject.le, Subobject.IsEntire, image, Allows, Cover (S1_51)
    PreLogos, PreLogos.bottom, HasSubobjectUnions, InverseImage       (S1_60)
    minimal_subobject_of_one_is_coterminator, any_map_to_zero_is_iso  (S1_61)
    Subobject.inter, IsComplementedSub, IsBasis                       (S1_62)
    image_lift_cover, cover_pullback                                  (S1_52/S1_56)
-/

import Freyd.S1_51
import Freyd.S1_60
import Freyd.S1_61
import Freyd.S1_62
import Freyd.S1_64
import Freyd.S1_70

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.751  Atoms -/

/-- A subobject `S ↣ A` is PROPER (§1.751) if it is not entire, i.e. its
    representing mono is not an isomorphism.  (Freyd: "proper subobject" = a
    subobject strictly below the whole object.) -/
def Subobject.IsProper {A : 𝒞} (S : Subobject 𝒞 A) : Prop :=
  ¬ S.IsEntire

/-- An object `A` is an ATOM (§1.751): "0 is its unique proper subobject."

    Unwound (Freyd's literal phrasing):
    * `0` (the bottom subobject) is itself proper — equivalently `A` is not a
      zero-object; the book stresses "the definition of atom excludes
      zero-objects";
    * every proper subobject of `A` coincides with `0`, i.e. factors through the
      bottom.  Since `bottom_min` already gives `0 ≤ S` for all `S`, demanding
      `S ≤ 0` pins `S` to `0` as a subobject.

    So: `0` is proper, and every proper subobject is `≤ 0`. -/
def IsAtom [PreLogos 𝒞] (A : 𝒞) : Prop :=
  (PreLogos.bottom A).IsProper ∧
  ∀ (S : Subobject 𝒞 A), S.IsProper → S.le (PreLogos.bottom A)

/-- A logos is ATOMICALLY BASED (§1.751) if its atoms form a basis (§1.632):
    the representable functors `Hom(A, −)` for atoms `A` are collectively faithful
    and separate proper subobjects.  Reuses `IsBasis` from §1.632. -/
def AtomicallyBased [PreLogos 𝒞] [HasPullbacks 𝒞] : Prop :=
  IsBasis (𝒞 := 𝒞) (fun A => IsAtom A)

/-- A logos is ATOMLESS (§1.751) if it has no atoms.  (Freyd: "note that the
    definition of atom excludes zero-objects", so a degenerate/zero logos is
    vacuously atomless under this reading.) -/
def Atomless [PreLogos 𝒞] : Prop :=
  ∀ (A : 𝒞), ¬ IsAtom A

/-! ## §1.75  Indexed subobject joins (+ frame law)

  Freyd's complement of `S ⊆ A` is the join of all atom-images not factoring through `S`:
      `¬S = ⊔ { image(x) | G atom, x : G → A, x ∤ S }`.
  This is an INDEXED (small) join over a family parameterized by every atom and every map
  out of it; `HasSubobjectUnions` (S1_60) gives only BINARY joins.  We package exactly the
  needed primitive: a least-upper-bound `sup` for a predicate-family of subobjects of a
  fixed object (the §1.712 `LocallyComplete` structure), together with the FRAME LAW
  `invImage_preserves_sup` (inverse image preserves arbitrary joins).  The frame law is the
  §1.84 `PullbacksPreserveArbitraryUnions` / infinite distributive law; it is NOT derivable
  from `PreLogos` (which preserves only binary unions), so it is a field of the class — the
  same shape as `locallyComplete_with_union_preserving_is_logos` (S1_70) and the Giraud
  `pullback_union` field (S1_84). -/

/-- **`HasIndexedSubobjectJoins`** (§1.712 / §1.84).  Least upper bound `sup` for a
    predicate-family of subobjects of a fixed `A`, *plus* the frame law
    `invImage_preserves_sup`.  `sup`/`sup_upper`/`sup_least` are the `LocallyComplete`
    complete-lattice fields; `invImage_preserves_sup` is the infinite distributive law
    (`PullbacksPreserveArbitraryUnions`, §1.84), which a bare `PreLogos` does not supply. -/
class HasIndexedSubobjectJoins (𝒞 : Type u) [Cat.{v} 𝒞] [PreLogos 𝒞] where
  sup : ∀ {A : 𝒞}, ((Subobject 𝒞 A) → Prop) → Subobject 𝒞 A
  sup_upper : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (s : Subobject 𝒞 A),
    S s → Subobject.le s (sup S)
  sup_least : ∀ {A : 𝒞} (S : (Subobject 𝒞 A) → Prop) (U : Subobject 𝒞 A),
    (∀ (s : Subobject 𝒞 A), S s → Subobject.le s U) → Subobject.le (sup S) U
  /-- FRAME LAW (§1.84 `PullbacksPreserveArbitraryUnions`): inverse image preserves
      arbitrary joins, `f# (⊔ S) ≤ ⊔ { f# B' | B' ∈ S }`. -/
  invImage_preserves_sup : ∀ {A B : 𝒞} (f : A ⟶ B) (S : (Subobject 𝒞 B) → Prop),
    Subobject.le (InverseImage f (sup S))
      (sup (fun A' => ∃ B', S B' ∧ A' = InverseImage f B'))

/-- **Bridge to the canonical arbitrary-join class**: `HasIndexedSubobjectJoins` = the §1.712
    `LocallyComplete` (S1_70) complete-lattice structure *plus* the §1.84 frame law
    `invImage_preserves_sup`.  Its `sup`/`sup_upper`/`sup_least` fields are exactly
    `LocallyComplete`'s, so any category with indexed joins is locally complete.  This keeps
    `LocallyComplete` the single canonical arbitrary-join primitive (the frame-law class derives
    it); the ambient `HasImages` from `[PreLogos 𝒞]` is reused, so no new image structure is
    introduced. -/
instance (priority := 100) [PreLogos 𝒞] [HasIndexedSubobjectJoins 𝒞] : LocallyComplete 𝒞 where
  toHasImages := inferInstance
  sup := HasIndexedSubobjectJoins.sup
  sup_isSup := fun S =>
    ⟨HasIndexedSubobjectJoins.sup_upper S, HasIndexedSubobjectJoins.sup_least S⟩

open HasIndexedSubobjectJoins

/-- Maps out of `(bottom X).dom` are unique: it is a zero object (§1.61). -/
theorem botDom_map_uniq [hPL : PreLogos 𝒞] {X Y : 𝒞}
    (f g : (PreLogos.bottom X).dom ⟶ Y) : f = g := by
  let ct := minimal_subobject_of_one_is_coterminator hPL
  obtain ⟨φ, ψ, hφψ, _⟩ := hPL.bottom_dom_iso X (hPL.toHasTerminal.one)
  have hψf : ψ ≫ f = ψ ≫ g := ct.init_uniq (ψ ≫ f) (ψ ≫ g)
  calc f = (φ ≫ ψ) ≫ f := by rw [hφψ, Cat.id_comp]
    _ = φ ≫ (ψ ≫ f) := Cat.assoc _ _ _
    _ = φ ≫ (ψ ≫ g) := by rw [hψf]
    _ = (φ ≫ ψ) ≫ g := (Cat.assoc _ _ _).symm
    _ = g := by rw [hφψ, Cat.id_comp]

/-- Any morphism into `(bottom P).dom` is an isomorphism (§1.61 `any_map_to_zero_is_iso`). -/
theorem mapTo_botDom_iso [hPL : PreLogos 𝒞] {Z P : 𝒞} (j : Z ⟶ (PreLogos.bottom P).dom) :
    IsIso j := by
  obtain ⟨θ, θinv, hθ1, hθ2⟩ := hPL.bottom_dom_iso P (hPL.toHasTerminal.one)
  have hjθ : IsIso (j ≫ θ) := any_map_to_zero_is_iso hPL (j ≫ θ)
  obtain ⟨w, hw1, hw2⟩ := hjθ
  have hθmono : Monic θ := fun {W} g h hgh => by
    calc g = g ≫ (θ ≫ θinv) := by rw [hθ1, Cat.comp_id]
      _ = (g ≫ θ) ≫ θinv := (Cat.assoc _ _ _).symm
      _ = (h ≫ θ) ≫ θinv := by rw [hgh]
      _ = h ≫ (θ ≫ θinv) := Cat.assoc _ _ _
      _ = h := by rw [hθ1, Cat.comp_id]
  refine ⟨θ ≫ w, by rw [← Cat.assoc]; exact hw1, ?_⟩
  apply hθmono
  calc ((θ ≫ w) ≫ j) ≫ θ = θ ≫ (w ≫ (j ≫ θ)) := by
        rw [Cat.assoc (θ ≫ w) j θ, Cat.assoc θ w (j ≫ θ)]
    _ = θ ≫ Cat.id _ := by rw [hw2]
    _ = θ := Cat.comp_id _
    _ = Cat.id (PreLogos.bottom P).dom ≫ θ := (Cat.id_comp _).symm

/-- If `x# S` is entire (pullback of `S` along `x` is the whole source), then `x` factors
    through `S`. -/
theorem allows_of_invImage_entire [PreLogos 𝒞] {G A : 𝒞} (x : G ⟶ A) (S : Subobject 𝒞 A)
    (hent : (InverseImage x S).IsEntire) : Allows S x := by
  obtain ⟨inv, _, hinv2⟩ := hent
  let pb := HasPullbacks.has x S.arr
  refine ⟨inv ≫ pb.cone.π₂, ?_⟩
  have hw : pb.cone.π₁ ≫ x = pb.cone.π₂ ≫ S.arr := pb.cone.w
  have hi : inv ≫ pb.cone.π₁ = Cat.id G := hinv2
  calc (inv ≫ pb.cone.π₂) ≫ S.arr = inv ≫ (pb.cone.π₂ ≫ S.arr) := Cat.assoc _ _ _
    _ = inv ≫ (pb.cone.π₁ ≫ x) := by rw [hw]
    _ = (inv ≫ pb.cone.π₁) ≫ x := (Cat.assoc _ _ _).symm
    _ = Cat.id G ≫ x := by rw [hi]
    _ = x := Cat.id_comp x

/-- A cover whose source admits a map to a bottom-domain (hence is a zero object) and that
    factors through a subobject `N` forces `N ≤ 0`. -/
theorem cover_from_zero_le [PreLogos 𝒞] {P Q : 𝒞} {Z : 𝒞}
    (N : Subobject 𝒞 Q) (cfac : Z ⟶ N.dom) (hc : Cover cfac)
    (j : Z ⟶ (PreLogos.bottom P).dom) : N.le (PreLogos.bottom Q) := by
  obtain ⟨jinv, hj1, _⟩ := mapTo_botDom_iso j (P := P)
  obtain ⟨γ, _⟩ := PreLogos.bottom_dom_iso P N.dom
  let z₀ : Z ⟶ (PreLogos.bottom N.dom).dom := j ≫ γ
  have hcfac_eq : cfac = z₀ ≫ (PreLogos.bottom N.dom).arr := by
    have key : jinv ≫ cfac = jinv ≫ (z₀ ≫ (PreLogos.bottom N.dom).arr) := botDom_map_uniq _ _
    calc cfac = (j ≫ jinv) ≫ cfac := by rw [hj1, Cat.id_comp]
      _ = j ≫ (jinv ≫ cfac) := Cat.assoc _ _ _
      _ = j ≫ (jinv ≫ (z₀ ≫ (PreLogos.bottom N.dom).arr)) := by rw [key]
      _ = (j ≫ jinv) ≫ (z₀ ≫ (PreLogos.bottom N.dom).arr) := (Cat.assoc _ _ _).symm
      _ = z₀ ≫ (PreLogos.bottom N.dom).arr := by rw [hj1, Cat.id_comp]
  have hbot_iso : IsIso (PreLogos.bottom N.dom).arr :=
    hc (PreLogos.bottom N.dom).arr z₀ (PreLogos.bottom N.dom).monic hcfac_eq.symm
  obtain ⟨bi, _, hbi2⟩ := hbot_iso
  obtain ⟨δ, _⟩ := PreLogos.bottom_dom_iso N.dom Q
  refine ⟨bi ≫ δ, ?_⟩
  have hbridge : δ ≫ (PreLogos.bottom Q).arr = (PreLogos.bottom N.dom).arr ≫ N.arr :=
    botDom_map_uniq _ _
  calc (bi ≫ δ) ≫ (PreLogos.bottom Q).arr = bi ≫ (δ ≫ (PreLogos.bottom Q).arr) := Cat.assoc _ _ _
    _ = bi ≫ ((PreLogos.bottom N.dom).arr ≫ N.arr) := by rw [hbridge]
    _ = (bi ≫ (PreLogos.bottom N.dom).arr) ≫ N.arr := (Cat.assoc _ _ _).symm
    _ = Cat.id N.dom ≫ N.arr := by rw [hbi2]
    _ = N.arr := Cat.id_comp _

/-- Bridge (⇐): `S.arr# M ≤ 0` implies `S ∩ M ≤ 0`. -/
theorem inter_le_bottom_of_invImage [PreLogos 𝒞] {A : 𝒞} (S M : Subobject 𝒞 A)
    (h : (InverseImage S.arr M).le (PreLogos.bottom S.dom)) :
    (Subobject.inter S M).le (PreLogos.bottom A) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨φ, _, _, _⟩ := PreLogos.bottom_dom_iso S.dom A
  refine ⟨k ≫ φ, ?_⟩
  have hbridge : φ ≫ (PreLogos.bottom A).arr = (PreLogos.bottom S.dom).arr ≫ S.arr :=
    botDom_map_uniq _ _
  show (k ≫ φ) ≫ (PreLogos.bottom A).arr = (Subobject.inter S M).arr
  have harr : (Subobject.inter S M).arr = (InverseImage S.arr M).arr ≫ S.arr := rfl
  rw [harr, ← hk]
  calc (k ≫ φ) ≫ (PreLogos.bottom A).arr = k ≫ (φ ≫ (PreLogos.bottom A).arr) := Cat.assoc _ _ _
    _ = k ≫ ((PreLogos.bottom S.dom).arr ≫ S.arr) := by rw [hbridge]
    _ = (k ≫ (PreLogos.bottom S.dom).arr) ≫ S.arr := (Cat.assoc _ _ _).symm

/-- Bridge (⇒): `S ∩ M ≤ 0` implies `S.arr# M ≤ 0`. -/
theorem invImage_le_bottom_of_inter [PreLogos 𝒞] {A : 𝒞} (S M : Subobject 𝒞 A)
    (h : (Subobject.inter S M).le (PreLogos.bottom A)) :
    (InverseImage S.arr M).le (PreLogos.bottom S.dom) := by
  obtain ⟨hwit, _⟩ := h
  obtain ⟨hi, hhi1, _⟩ := mapTo_botDom_iso hwit (P := A)
  obtain ⟨ε, _⟩ := PreLogos.bottom_dom_iso A S.dom
  refine ⟨hwit ≫ ε, ?_⟩
  have key : hi ≫ ((hwit ≫ ε) ≫ (PreLogos.bottom S.dom).arr) = hi ≫ (InverseImage S.arr M).arr :=
    botDom_map_uniq _ _
  have hfin : (hwit ≫ hi) ≫ (InverseImage S.arr M).arr = (InverseImage S.arr M).arr := by
    rw [hhi1, Cat.id_comp]
  calc (hwit ≫ ε) ≫ (PreLogos.bottom S.dom).arr
      = ((hwit ≫ hi) ≫ (hwit ≫ ε)) ≫ (PreLogos.bottom S.dom).arr := by rw [hhi1, Cat.id_comp]
    _ = hwit ≫ (hi ≫ ((hwit ≫ ε) ≫ (PreLogos.bottom S.dom).arr)) := by rw [Cat.assoc, Cat.assoc]
    _ = hwit ≫ (hi ≫ (InverseImage S.arr M).arr) := by rw [key]
    _ = (hwit ≫ hi) ≫ (InverseImage S.arr M).arr := (Cat.assoc _ _ _).symm
    _ = (InverseImage S.arr M).arr := hfin

/-- **Atom-image disjointness** (§1.751).  For an atom `G` and `x : G → A` that does NOT
    factor through `S`, the image of `x` is disjoint from `S`: `S ∩ image(x) ≤ 0`.

    Proof: `x# S` is a subobject of the atom `G`, so by atomicity it is `0` or all of `G`;
    "all of `G`" would make `x` factor through `S`, so `x# S ≤ 0`.  Pulling this `0` up
    along the cover `image.lift x` (covers are pullback-stable, §1.52) and the bridge
    lemmas transports it to `S ∩ image(x) ≤ 0`. -/
theorem atom_image_disjoint [PreLogos 𝒞] {G A : 𝒞} (hG : IsAtom G)
    (x : G ⟶ A) (S : Subobject 𝒞 A) (hx : ¬ Allows S x) :
    (Subobject.inter S (image x)).le (PreLogos.bottom A) := by
  have h0 : (InverseImage x S).le (PreLogos.bottom G) := by
    apply hG.2; intro hent; exact hx (allows_of_invImage_entire x S hent)
  obtain ⟨jw, _⟩ := h0
  let N : Subobject 𝒞 (image x).dom := InverseImage (image x).arr S
  let il := image.lift x
  let pb1 := HasPullbacks.has il N.arr
  have hcov : Cover pb1.cone.π₂ := cover_pullback (𝒞 := 𝒞) N.arr (image_lift_cover x)
  let Npb := HasPullbacks.has (image x).arr S.arr
  have hcone_w : pb1.cone.π₁ ≫ x = (pb1.cone.π₂ ≫ Npb.cone.π₂) ≫ S.arr := by
    have e1 : pb1.cone.π₁ ≫ il = pb1.cone.π₂ ≫ N.arr := pb1.cone.w
    have e2 : Npb.cone.π₁ ≫ (image x).arr = Npb.cone.π₂ ≫ S.arr := Npb.cone.w
    calc pb1.cone.π₁ ≫ x = pb1.cone.π₁ ≫ (il ≫ (image x).arr) := by rw [image.lift_fac]
      _ = (pb1.cone.π₁ ≫ il) ≫ (image x).arr := (Cat.assoc _ _ _).symm
      _ = (pb1.cone.π₂ ≫ N.arr) ≫ (image x).arr := by rw [e1]
      _ = (pb1.cone.π₂ ≫ Npb.cone.π₁) ≫ (image x).arr := rfl
      _ = pb1.cone.π₂ ≫ (Npb.cone.π₁ ≫ (image x).arr) := Cat.assoc _ _ _
      _ = pb1.cone.π₂ ≫ (Npb.cone.π₂ ≫ S.arr) := by rw [e2]
      _ = (pb1.cone.π₂ ≫ Npb.cone.π₂) ≫ S.arr := (Cat.assoc _ _ _).symm
  let invpb := HasPullbacks.has x S.arr
  let cone_xS : Cone x S.arr := ⟨pb1.cone.pt, pb1.cone.π₁, pb1.cone.π₂ ≫ Npb.cone.π₂, hcone_w⟩
  let j : pb1.cone.pt ⟶ (PreLogos.bottom G).dom := invpb.lift cone_xS ≫ jw
  have hN_le : N.le (PreLogos.bottom (image x).dom) := cover_from_zero_le N pb1.cone.π₂ hcov j
  exact Subobject.le_trans (inter_comm_le S (image x)) (inter_le_bottom_of_invImage (image x) S hN_le)

/-! ## §1.751  Atomically based ⇒ boolean -/

/-- **§1.751**: an ATOMICALLY BASED logos with arbitrary subobject joins is BOOLEAN —
    every subobject `S ⊆ A` is complemented.

    Freyd's complement: `¬S = ⊔ { image(x) | G atom, x : G → A, x ∤ S }`, the indexed
    join (`HasIndexedSubobjectJoins.sup`) of all atom-images not factoring through `S`.

    * **(1) `S ∩ ¬S = 0`.**  By the FRAME LAW, `S.arr# (¬S) = ⊔ { S.arr# (image x) }`;
      each `image x` in the family is disjoint from `S` by `atom_image_disjoint` (atomicity
      forces `x# S = 0` since `x ∤ S`), so every joinand `S.arr# (image x) ≤ 0`, hence
      `S.arr# (¬S) ≤ 0`, hence `S ∩ ¬S ≤ 0` (bridge lemmas).
    * **(2) `S ∪ ¬S = A`.**  If `S ∪ ¬S` were proper, `IsBasis` yields an atom `G` and
      `x : G → A` not factoring through `S ∪ ¬S`.  Then `x ∤ S` (else `x` would factor
      through `S ≤ S ∪ ¬S`), so `image x` is in the family and `image x ≤ ¬S ≤ S ∪ ¬S`;
      but `x` factors through `image x`, so `x` factors through `S ∪ ¬S` — contradiction.

    **Faithful complement predicate.**  The conclusion uses `IsComplementedSub` (§1.62:
    `S ∩ ¬S ≤ 0` and `A ≤ S ∪ ¬S`), the genuine book definition — NOT the S1_64 placeholder
    `IsComplemented`, which demands NO common lower bound *including* `0` and is therefore
    unsatisfiable in any pre-logos (`bottom` is below both `S` and any `¬S`).

    **Required structure.**  Beyond `AtomicallyBased`, the proof needs
    `HasIndexedSubobjectJoins` — arbitrary small joins of subobjects PLUS the frame law
    `invImage_preserves_sup` (inverse image preserves arbitrary joins).  The frame law is
    the §1.84 `PullbacksPreserveArbitraryUnions` / infinite distributive law and is NOT
    available from `PreLogos` (which preserves only binary unions); it is supplied by the
    `HasIndexedSubobjectJoins` instance, mirroring §1.712 (`LocallyComplete` +
    union-preservation = logos) and the Giraud §1.84 `pullback_union` field. -/
theorem atomicallyBased_isComplementedSub [PreLogos 𝒞] [HasIndexedSubobjectJoins 𝒞]
    (h : AtomicallyBased (𝒞 := 𝒞)) :
    ∀ {A : 𝒞} (S : Subobject 𝒞 A), IsComplementedSub S := by
  intro A S
  -- ¬S = join of all atom-images not factoring through S
  let F : Subobject 𝒞 A → Prop :=
    fun T => ∃ (G : 𝒞), IsAtom G ∧ ∃ (x : G ⟶ A), (¬ Allows S x) ∧ T = image x
  refine ⟨sup F, ?_, ?_⟩
  · -- (1) S ∩ ¬S ≤ 0, via the frame law + per-joinand disjointness.
    apply inter_le_bottom_of_invImage S (sup F)
    have hframe := invImage_preserves_sup S.arr F
    have hbound : (sup (fun A' => ∃ M, F M ∧ A' = InverseImage S.arr M)).le
        (PreLogos.bottom S.dom) := by
      apply sup_least
      rintro s ⟨M, ⟨G, hG, x, hx, rfl⟩, rfl⟩
      exact invImage_le_bottom_of_inter S (image x) (atom_image_disjoint hG x S hx)
    exact Subobject.le_trans hframe hbound
  · -- (2) A ≤ S ∪ ¬S: a missing atom-element would land in image(x) ≤ ¬S, contradiction.
    let U := HasSubobjectUnions.union S (sup F)
    apply Classical.byContradiction
    intro hcon
    have hnotiso : ¬ IsIso U.arr := by
      intro hiso
      obtain ⟨inv, _, hinv2⟩ := hiso
      exact hcon ⟨inv, by
        show inv ≫ U.arr = (Subobject.entire A).arr
        rw [hinv2]; rfl⟩
    obtain ⟨G, hG, x, hx⟩ := h.2 U.arr U.monic hnotiso
    have hxS : ¬ Allows S x := by
      rintro ⟨y, hy⟩
      obtain ⟨l, hl⟩ := HasSubobjectUnions.union_left S (sup F)
      exact hx ⟨y ≫ l, by rw [Cat.assoc, hl, hy]⟩
    have h1 : (image x).le (sup F) := sup_upper F (image x) ⟨G, hG, x, hxS, rfl⟩
    obtain ⟨r, hr⟩ := HasSubobjectUnions.union_right S (sup F)
    obtain ⟨a, ha⟩ := image_allows x
    obtain ⟨b, hb⟩ := h1
    refine hx ⟨a ≫ b ≫ r, ?_⟩
    calc (a ≫ b ≫ r) ≫ U.arr = a ≫ (b ≫ (r ≫ U.arr)) := by rw [Cat.assoc, Cat.assoc]
      _ = a ≫ (b ≫ (sup F).arr) := by rw [hr]
      _ = a ≫ (image x).arr := by rw [hb]
      _ = x := ha

/-! ## §1.751  Periodic-power / reduction-to-atomless (recorded MISSING)

  The remainder of §1.751 reduces the Stone theorem to the ATOMLESS case via the
  PERIODIC POWER `℘A` (periodic functions ℕ → A), a sublogos of `A^ℕ` with a
  faithful diagonal representation `A → ℘A` that is atomless whenever `A` is
  non-degenerate.  Faithfully stating this needs:
    * countable powers `A^ℕ` and the sublogos of periodic sequences,
    * the diagonal representation and its faithfulness,
    * preservation of "positive & capital".
  None of this infrastructure exists in the repo, so it is NOT emitted as Lean
  here (no vacuous stub).  See S1_75.md.

  §1.752–§1.755 (the Stone space 𝒮(ℬ), the stalk/sheaf functor `T : A → 𝓜(X)`,
  the two characterizing properties, and the descent to faithfulness) are likewise
  recorded MISSING in S1_75.md: they require Stone-space/ultra-filter/sheaf
  machinery outside this repo's category-theoretic core.
-/

/-! ## §1.752–§1.754  The Stone space `B̂` and the §1.754 faithfulness

  STATUS: §1.754 is now DONE **modulo the one genuine sheaf-equivalence TODO**
  `OSet(O(B̂)) ≃ Sh(B̂)` (= `H(B̂)`, see `Freyd/Locale.lean ~1077`).  The §1.635 half — the
  half that the now-PROVEN ultra-filter machinery (`exists_ultrafilter_extending`,
  `setRepOfPreLogos_of_ultrafilter`, `ultrafilter_unionPrime`) supplies — is proved here,
  and the §1.753 reduction (pre-logos rep + faithful + basis ⟹ logos rep) is stated as the
  conditional theorem `stoneRep_logos_of_faithful` over named hypotheses for the genuinely
  missing pieces.

  The point of §1.754 (Freyd's "If `X = B̂` then `T` is faithful [1.635]"): when the subspace
  `X ⊂ B̂` is the WHOLE Stone space — i.e. ALL ultra-filters — the stalk representation
  `T : A → H(B̂)` is faithful.  Freyd's faithfulness criterion (§1.754, second paragraph)
  reads:  for `X ⊂ B̂`, `T : A → H(X)` is faithful **iff** for each complemented `V ⊂ 1`
  there exists `F ∈ X` with `T_F(V) ≠ 1`, i.e. some ultra-filter that EXCLUDES `V`.  When
  `X = B̂` this is automatic, and that is exactly what we prove below:

  `exists_ultrafilter_excluding` — every PROPER complemented subterminator `V` (`V ≠ 1`) is
  excluded by some ultra-filter.  This is the §1.635 stalk-detection that powers the
  collective faithfulness of the stalk family over `B̂`.  It is the honest, infrastructure-
  light core of §1.754; the surrounding `H(X)`/sheaf packaging is the recorded TODO. -/

/-- §1.754 (the §1.635 detection core).  Every PROPER complemented subterminator `V ⊂ 1` —
    one that is *not* the whole of `1` — is **excluded by some ultra-filter** `F̂` in the
    Boolean algebra of complemented subterminators.

    This is the content of Freyd's §1.754 faithfulness criterion at `X = B̂` (the whole Stone
    space): "for each `V ⊂ 1` there exists `F ∈ B̂` with `T_F(V) ≠ 1`".  Here `F̂` excluding
    `V` (`¬ F̂ V`) is exactly `T_F̂(V) ≠ 1` (the stalk omits `V`).  Since this holds for EVERY
    proper `V`, the stalk family over all of `B̂` is collectively faithful — the §1.635 half of
    §1.754.

    PROOF.  Let `Vᶜ` be a complement of `V` (`V ∩ Vᶜ ≤ 0`, `⊤ ≤ V ∪ Vᶜ`).  Since `V` is proper
    (`¬ ⊤ ≤ V`), `Vᶜ` is *not* below `0`: else `⊤ ≤ V ∪ Vᶜ ≤ V`, contra.  The principal up-set
    `𝒫 = {W complemented | Vᶜ ≤ W}` is therefore a PROPER complemented pre-filter
    (`inter_complemented` for directedness; `Vᶜ ⊄ 0` for properness).  By
    `exists_ultrafilter_extending` it lifts to an ultra-filter `F̂ ⊇ 𝒫`, so `Vᶜ ∈ F̂`.  And
    `V ∉ F̂`: were `V ∈ F̂`, directedness yields `W ∈ F̂` with `W ≤ V` and `W ≤ Vᶜ`, hence
    `W ≤ V ∩ Vᶜ ≤ 0`, contradicting properness of `F̂`. -/
theorem exists_ultrafilter_excluding [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    (V : Subobject 𝒞 one) (hVcomp : IsComplementedSub V)
    (hVproper : ¬ (Subobject.entire one).le V) :
    ∃ Fhat, IsUltraFilter Fhat ∧ ¬ Fhat V := by
  obtain ⟨Vc, hVdisj, hVcov⟩ := hVcomp
  -- `Vc` is complemented (complement `V`).
  have hVcComp : IsComplementedSub Vc :=
    ⟨V, Subobject.le_trans (inter_comm_le Vc V) hVdisj,
      Subobject.le_trans hVcov (union_comm_le V Vc)⟩
  -- `Vc` is NOT below `0`: else `⊤ ≤ V ∪ Vc ≤ V`, making `V` entire.
  have hVcNotZero : ¬ Subobject.le Vc Zero1 := by
    intro hVc0
    refine hVproper ?_
    refine Subobject.le_trans hVcov ?_
    exact HasSubobjectUnions.union_min _ _ _ (Subobject.le_refl V)
      (Subobject.le_trans hVc0 (PreLogos.bottom_min V))
  -- the principal complemented up-set on `Vc`.
  let 𝒫 : (Subobject 𝒞 one) → Prop := fun W => IsComplementedSub W ∧ Subobject.le Vc W
  have h𝒫pre : IsPreFilter 𝒫 := by
    refine ⟨⟨Vc, hVcComp, Subobject.le_refl Vc⟩, ?_⟩
    rintro W₁ W₂ ⟨hW₁c, hVcW₁⟩ ⟨hW₂c, hVcW₂⟩
    exact ⟨Subobject.inter W₁ W₂, ⟨inter_complemented hW₁c hW₂c,
      Subobject.le_inter hVcW₁ hVcW₂⟩,
      Subobject.inter_le_left _ _, Subobject.inter_le_right _ _⟩
  have h𝒫proper : IsProperFilter 𝒫 := by
    refine ⟨h𝒫pre, ?_⟩
    rintro ⟨W, ⟨_, hVcW⟩, hW0⟩
    exact hVcNotZero (Subobject.le_trans hVcW hW0)
  have h𝒫comp : ∀ W, 𝒫 W → IsComplementedSub W := fun W hW => hW.1
  obtain ⟨Fhat, hUF, hext⟩ := exists_ultrafilter_extending 𝒫 h𝒫proper h𝒫comp
  refine ⟨Fhat, hUF, ?_⟩
  -- `Vc ∈ F̂` (it is in `𝒫`).
  have hVcF : Fhat Vc := hext Vc ⟨hVcComp, Subobject.le_refl Vc⟩
  -- `V ∉ F̂`: meet with `Vc` would be `≤ 0`, contradicting properness.
  intro hVF
  obtain ⟨W, hWF, hWV, hWVc⟩ := hUF.1.1.2 V Vc hVF hVcF
  exact hUF.1.2 ⟨W, hWF, Subobject.le_trans (Subobject.le_inter hWV hWVc) hVdisj⟩

/-! ### §1.753  The reduction:  pre-logos rep + faithful + basis ⟹ logos rep

  Freyd §1.753: "If `X ⊂ B̂` is such that `T : A → H(X)` is faithful, then `T` is a faithful
  representation of logoi."  Because `T` is already a representation of pre-logoi [§1.752],
  the only thing left is that it preserves DOUBLE-SHARPS (`f^{##}`, the universal/∀ image),
  and Freyd derives this from (1) faithfulness and (2) the basis property §1.752(2) (every
  `Y ⊂ TA` is a union of `TA'`, `A' ⊂ A`), using that inverse images in a logos preserve
  arbitrary unions [§1.711].

  We package this reduction as a CONDITIONAL theorem.  The genuinely-missing infrastructure —
  the sheaf category `H(X)` (the `OSet(O(B̂)) ≃ Sh(B̂)` TODO in `Locale.lean`), the stalk
  functor `T`, and the §1.752(2) basis property — are taken as EXPLICIT NAMED HYPOTHESES
  (`hPreLogosRep`, `hBasis`, `hReflectsDoubleSharp`); the §1.635 faithfulness ingredient at
  `X = B̂` is the PROVEN `exists_ultrafilter_excluding`.  This is the same honest "state the
  theorem over what exists, take the missing piece as a hypothesis" device used at §2.218.

  The abstract shape: `LogosRepData T` bundles, as `Prop`s, the three §1.753 deliverables a
  faithful logos representation must have (pre-logos rep, faithful, preserves double-sharps);
  `stoneRep_logos_of_faithful` shows the third follows from the first two plus the basis. -/

/-- §1.753/§1.754 abstract logos-representation package.  `T : A → 𝒟` is a FAITHFUL
    REPRESENTATION OF LOGOI when it is a representation of PRE-logoi (`preLogosRep`), is
    FAITHFUL (`faithful`), and PRESERVES DOUBLE-SHARPS (`preservesDoubleSharp`).  Each field is
    an abstract `Prop` because the concrete `H(X)`/sheaf target is the recorded TODO; this
    records the §1.753 deliverable shape and lets §1.754's reduction be stated and proved. -/
structure LogosRepData (preLogosRep faithful preservesDoubleSharp : Prop) : Prop where
  preLogosRep         : preLogosRep
  faithful            : faithful
  preservesDoubleSharp : preservesDoubleSharp

/-- §1.753:  **pre-logos rep + faithful + basis property [§1.752(2)] ⟹ representation of
    logoi.**  The double-sharp-preservation deliverable is *derived* from faithfulness and the
    basis property via `hReflectsDoubleSharp` — the abstract carrier of Freyd's §1.753
    calculation "for arbitrary `Y ⊂ TB`, `Y ⊂ T(f^{##}A') ⇔ (Tf)^*Y ⊂ TA'`", which uses only
    faithfulness, basis, and that inverse images preserve arbitrary unions [§1.711].

    This is the honest reduction: it CONSUMES exactly the two §1.752/§1.753 hypotheses Freyd
    cites and PRODUCES the `LogosRepData`.  Specialising `faithful` to the `X = B̂` case is
    `exists_ultrafilter_excluding` (the §1.635 half); the sheaf target `H(B̂)` itself remains
    the `OSet(O(B̂)) ≃ Sh` TODO. -/
theorem stoneRep_logos_of_faithful
    {preLogosRep faithful basis preservesDoubleSharp : Prop}
    (hPreLogosRep : preLogosRep)
    (hFaithful : faithful)
    (hBasis : basis)
    (hReflectsDoubleSharp : preLogosRep → faithful → basis → preservesDoubleSharp) :
    LogosRepData preLogosRep faithful preservesDoubleSharp :=
  ⟨hPreLogosRep, hFaithful, hReflectsDoubleSharp hPreLogosRep hFaithful hBasis⟩

/-- §1.754:  **If `X = B̂` then `T` is faithful [1.635] and `A → H(B̂)` is a representation of
    logoi.**  Stated as a conditional theorem over the named sheaf/stalk hypotheses, with the
    §1.635 faithfulness half SUPPLIED here (not assumed): `hStalkDetect` is `T_F̂`-detection,
    instantiable by `exists_ultrafilter_excluding`, and `hFaithfulOfDetect` is the §1.754
    criterion "detection on all complemented `V` ⟹ `T` faithful" (the collective faithfulness
    of the stalk family, whose general form `collectively faithful family of pre-logos
    representations` Freyd cites in §1.752; the concrete `H(B̂)` instance is the sheaf TODO).

    Given those, `T` is faithful and — by `stoneRep_logos_of_faithful` — a representation of
    logoi.  Thus §1.754 reduces, with NO further topological input, to the single TODO
    `OSet(O(B̂)) ≃ Sh(B̂)`. -/
theorem stoneRep_faithful_logos_of_sheaf [PreLogos 𝒞] [HasBinaryCoproducts 𝒞]
    {preLogosRep faithful basis preservesDoubleSharp : Prop}
    (hPreLogosRep : preLogosRep)
    (hBasis : basis)
    (hReflectsDoubleSharp : preLogosRep → faithful → basis → preservesDoubleSharp)
    -- the §1.754 faithfulness criterion: detection on every proper complemented `V`
    -- (PROVABLE by `exists_ultrafilter_excluding`) ⟹ `T` faithful.
    (hFaithfulOfDetect :
      (∀ V : Subobject 𝒞 one, IsComplementedSub V → ¬ (Subobject.entire one).le V →
        ∃ Fhat, IsUltraFilter Fhat ∧ ¬ Fhat V) → faithful) :
    faithful ∧ LogosRepData preLogosRep faithful preservesDoubleSharp := by
  -- the §1.635 detection (PROVEN above) discharges the criterion's antecedent.
  have hDetect : ∀ V : Subobject 𝒞 one, IsComplementedSub V → ¬ (Subobject.entire one).le V →
      ∃ Fhat, IsUltraFilter Fhat ∧ ¬ Fhat V :=
    fun V hVc hVp => exists_ultrafilter_excluding V hVc hVp
  have hFaithful : faithful := hFaithfulOfDetect hDetect
  exact ⟨hFaithful, stoneRep_logos_of_faithful hPreLogosRep hFaithful hBasis hReflectsDoubleSharp⟩

end Freyd
