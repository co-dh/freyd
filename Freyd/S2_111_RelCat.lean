/-
  Freyd & Scedrov, *Categories and Allegories* §2.111 / §2.142 / §2.214
  The bridge Rel(C): relations in a (pre-)regular category form an ALLEGORY.

  This is the Ch1→Ch2 dual of `Freyd/MapCat.lean` (which built `Map(𝒜)` of an
  allegory).  Here we build `Rel(C)` of a category C: its objects are those of C,
  its morphisms `a ⟶ b` are binary relations `BinRel C a b` (§1.56) — taken up to
  mutual containment so the allegory's *equational* laws hold on the nose — with
  composition `⊚`, reciprocal `°`, intersection `⊓`, union `relUnionSub`, all from
  Chapter 1.

  **The quotient.**  `BinRel C a b` is only a PREORDER under `RelLe` (`⊂`): two
  isomorphic tables are mutually contained but not Lean-equal.  The `Allegory` class
  (S2_1) states its laws as *equalities* (`inter_idem`, `recip_comp`, `modular`, …),
  so we quotient `BinRel C a b` by the equivalence "mutual `RelLe`".  Every Ch1
  operation is monotone (`compose_le`, `reciprocal_mono`, `intersect`-UMP, …), hence
  descends to the quotient, and every Ch1 containment lemma becomes the corresponding
  allegory equation via `le_antisymm`.

  **Built (Sorry-free):**
    • `Cat (RelObj C)`            for `[RegularCategory C]`        — §2.111
    • `Allegory (RelObj C)`        for `[RegularCategory C]`        — §2.111 (modular = §2.142)
    • `DistributiveAllegory (RelObj C)` for `[PositivePreLogos C]`  — §2.21
    • §2.214 (positive ⇒ Rel(C) has finite coproducts), forward direction over
      `[DisjointBinaryCoproduct C]`: the full five-equation `Coproduct (RelObj C)` record
      (`relCoproduct`).  Eqs (1),(4) [monic injections], (2),(3) [disjointness], and
      (5) [joint cover, `relGraph_recip_union_eq_id`] are all PROVED.

  This is a BRIDGE file: it imports BOTH Ch1 (BinRel) and Ch2 (Allegory class).  Ch1
  facts are NEVER proved from allegory axioms — only the reverse.
-/

import Freyd.S1_56
import Freyd.S1_59
import Freyd.S1_60
import Freyd.S1_61
import Freyd.S1_62
import Freyd.S2_10
import Freyd.S2_20
import Freyd.S2_147_MapCat
import Freyd.S2_216_MatrixAllegory
import Freyd.S2_165_Spl

open Freyd
open Freyd.Alg

universe v u

namespace Freyd

/-! ## The object type of `Rel(C)`

  A wrapper structure (like `MapObj` is an alias, but we use a `structure` to FORCE a
  distinct `Cat` instance that does not clash with C's own `Cat`/`RegularCategory`). -/

/-- Objects of `Rel(C)`: a wrapper around objects of `C`. -/
structure RelObj (𝒞 : Type u) where
  /-- The underlying object of `C`. -/
  carrier : 𝒞

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## Mutual-containment equivalence on `BinRel`

  `RelLe` (`⊂`) is reflexive (`rel_le_refl`) and transitive (`rel_le_trans`); mutual
  containment is therefore an equivalence.  We quotient by it. -/

section Equiv
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The setoid on `BinRel C a b`: `R ≈ S` iff `R ⊂ S` and `S ⊂ R`. -/
def relSetoid (a b : 𝒞) : Setoid (BinRel 𝒞 a b) where
  r R S := RelLe R S ∧ RelLe S R
  iseqv :=
    { refl  := fun R => ⟨rel_le_refl R, rel_le_refl R⟩
      symm  := fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
      trans := fun ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ =>
        ⟨rel_le_trans h₁ h₂, rel_le_trans h₂' h₁'⟩ }

end Equiv

/-! ## The hom-type and its order

  `BinRelQuot C a b := Quotient (relSetoid a b)`.  Containment descends to a genuine
  partial order on the quotient (antisymmetric by construction). -/

section Quot
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- A morphism `a ⟶ b` in `Rel(C)`: an `RelLe`-equivalence class of relations. -/
def BinRelQuot (a b : 𝒞) : Type _ := Quotient (relSetoid (𝒞 := 𝒞) a b)

/-- The canonical class of a relation. -/
def relClass {a b : 𝒞} (R : BinRel 𝒞 a b) : BinRelQuot a b := Quotient.mk _ R

/-- Containment descends to the quotient (well-defined: monotone in both slots). -/
def quotLe {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) : Prop :=
  Quotient.liftOn₂ x y (fun R S => RelLe R S)
    (fun _ _ _ _ hR hS => propext
      ⟨fun h => rel_le_trans (rel_le_trans hR.2 h) hS.1,
       fun h => rel_le_trans (rel_le_trans hR.1 h) hS.2⟩)

/-- `relClass` is monotone: `R ⊂ S → relClass R ≤ relClass S`. -/
theorem relClass_mono {a b : 𝒞} {R S : BinRel 𝒞 a b} (h : RelLe R S) :
    quotLe (relClass R) (relClass S) := h

end Quot

/-! ## §2.111  `Rel(C)` is a category

  Composition is relation composition `⊚` (diagram order: `relClass R ≫ relClass S`
  is "first R then S"); identity is the graph of `id`.  All three category laws come
  from the Ch1 identity/associativity containments (`graph_id_comp`, `comp_graph_id`,
  `compose_assoc_of_regular`) collapsed to a Lean equality by `Quotient.sound`. -/

section RelCat
variable [RegularCategory 𝒞]

/-- Composition on the quotient: `[R] ⊚ [S] = [R ⊚ S]`, well-defined by `compose_le`. -/
def qComp {a b c : 𝒞} (x : BinRelQuot (𝒞 := 𝒞) a b) (y : BinRelQuot (𝒞 := 𝒞) b c) :
    BinRelQuot (𝒞 := 𝒞) a c :=
  Quotient.liftOn₂ x y (fun R S => relClass (R ⊚ S))
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨compose_le hR.1 hS.1, compose_le hR.2 hS.2⟩)

@[simp] theorem qComp_mk {a b c : 𝒞} (R : BinRel 𝒞 a b) (S : BinRel 𝒞 b c) :
    qComp (relClass R) (relClass S) = relClass (R ⊚ S) := rfl

/-- The identity relation `[graph id]`. -/
def relId (a : 𝒞) : BinRelQuot (𝒞 := 𝒞) a a := relClass (graph (Cat.id a))

/-- **§2.111**: `Rel(C)` is a category.  Objects `RelObj C`; homs the `RelLe`-classes. -/
instance (priority := 0) relCat : Cat.{max u v} (RelObj 𝒞) where
  Hom A B := BinRelQuot (𝒞 := 𝒞) A.carrier B.carrier
  id  A   := relId A.carrier
  comp x y := qComp x y
  id_comp {A B} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    exact Quotient.sound ⟨graph_id_comp R, comp_graph_id_left R⟩
  comp_id {A B} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    exact Quotient.sound ⟨comp_graph_id R, comp_graph_id_right R⟩
  assoc {A B C D} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    exact Quotient.sound ⟨(compose_assoc_of_regular R S T).1,
      (compose_assoc_of_regular R S T).2⟩

end RelCat

/-! ## §2.111 / §2.142  `Rel(C)` is an allegory

  `°` = `reciprocal`, `∩` = `intersect`.  The semi-lattice laws come from the
  intersection UMP (`intersect_le_*`, `le_intersect`); reciprocation laws from
  `reciprocal_invol`/`reciprocal_comp`/`reciprocal_intersect`; semi-distributivity
  from monotonicity of `⊚`; and the MODULAR law is exactly Freyd's `modular_identity`
  (§1.563 / §2.142 — the crux, holding in any regular C). -/

section RelAllegory
variable [RegularCategory 𝒞]

/-- Reciprocal on the quotient: `[R]° = [R°]`, well-defined by `reciprocal_mono`. -/
def qRecip {a b : 𝒞} (x : BinRelQuot (𝒞 := 𝒞) a b) : BinRelQuot (𝒞 := 𝒞) b a :=
  Quotient.liftOn x (fun R => relClass R°)
    (fun _ _ h => Quotient.sound ⟨reciprocal_mono h.1, reciprocal_mono h.2⟩)

@[simp] theorem qRecip_mk {a b : 𝒞} (R : BinRel 𝒞 a b) :
    qRecip (relClass R) = relClass R° := rfl

/-- Intersection on the quotient: `[R] ∩ [S] = [R ⊓ S]`, well-defined by the meet UMP. -/
def qInter {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) : BinRelQuot (𝒞 := 𝒞) a b :=
  Quotient.liftOn₂ x y (fun R S => relClass (R ⊓ S))
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨le_intersect (rel_le_trans (intersect_le_left _ _) hR.1)
          (rel_le_trans (intersect_le_right _ _) hS.1),
       le_intersect (rel_le_trans (intersect_le_left _ _) hR.2)
          (rel_le_trans (intersect_le_right _ _) hS.2)⟩)

@[simp] theorem qInter_mk {a b : 𝒞} (R S : BinRel 𝒞 a b) :
    qInter (relClass R) (relClass S) = relClass (R ⊓ S) := rfl

/-- **§2.111**: `Rel(C)` is an allegory. -/
instance (priority := 0) relAllegory : Allegory.{max u v} (RelObj 𝒞) where
  recip {a b} x := qRecip x
  inter {a b} x y := qInter x y
  -- (R°)° = R  —  a genuine equality from `reciprocal_invol`.
  recip_recip {a b} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    show relClass R°° = relClass R
    rw [reciprocal_invol]
  -- (R ⊚ S)° = S° ⊚ R°
  recip_comp {a b c} x y := by
    refine Quotient.inductionOn₂ x y (fun R S => ?_)
    exact Quotient.sound ⟨reciprocal_comp_le R S, comp_reciprocal_le R S⟩
  -- (R ⊓ S)° = R° ⊓ S°  (note: book's recip_inter has same-order R°∩S°;
  --  Ch1 gives S°⊓R°, equal by inter_comm — we route via antisymmetry to R°⊓S°).
  recip_inter {a b} x y := by
    refine Quotient.inductionOn₂ x y (fun R S => ?_)
    refine Quotient.sound ⟨?_, ?_⟩
    · exact le_intersect
        (reciprocal_mono (intersect_le_left R S)) (reciprocal_mono (intersect_le_right R S))
    · -- R°⊓S° ⊆ (R⊓S)°: factor through S°⊓R° (inter_comm) then intersect_reciprocal_le.
      have w  : RelLe (S° ⊓ R°) ((R ⊓ S)°) := intersect_reciprocal_le R S
      have w' : RelLe (R° ⊓ S°) (S° ⊓ R°) :=
        le_intersect (intersect_le_right (R°) (S°)) (intersect_le_left (R°) (S°))
      exact rel_le_trans w' w
  inter_idem {a b} x := by
    refine Quotient.inductionOn x (fun R => ?_)
    exact Quotient.sound ⟨intersect_le_left R R, le_intersect (rel_le_refl R) (rel_le_refl R)⟩
  inter_comm {a b} x y := by
    refine Quotient.inductionOn₂ x y (fun R S => ?_)
    exact Quotient.sound
      ⟨le_intersect (intersect_le_right R S) (intersect_le_left R S),
       le_intersect (intersect_le_right S R) (intersect_le_left S R)⟩
  inter_assoc {a b} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    refine Quotient.sound ⟨?_, ?_⟩
    · exact le_intersect
        (le_intersect (intersect_le_left R _) (rel_le_trans (intersect_le_right R _) (intersect_le_left S T)))
        (rel_le_trans (intersect_le_right R _) (intersect_le_right S T))
    · exact le_intersect
        (rel_le_trans (intersect_le_left _ T) (intersect_le_left R S))
        (le_intersect (rel_le_trans (intersect_le_left _ T) (intersect_le_right R S)) (intersect_le_right _ T))
  -- semi-distributivity: R⊚(S⊓T) = (R⊚S) ⊓ (R⊚(S⊓T)) ⊓ (R⊚T).
  semidistrib {a b c} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    -- LHS = R⊚(S⊓T); RHS = ((R⊚S) ⊓ (R⊚(S⊓T))) ⊓ (R⊚T).
    refine Quotient.sound ⟨?_, ?_⟩
    · -- R⊚(S⊓T) ⊆ RHS: below each conjunct by monotonicity.
      exact le_intersect
        (le_intersect (compose_le (rel_le_refl R) (intersect_le_left S T))
          (rel_le_refl _))
        (compose_le (rel_le_refl R) (intersect_le_right S T))
    · -- RHS ⊆ R⊚(S⊓T): the middle conjunct already IS R⊚(S⊓T).
      exact rel_le_trans (intersect_le_left _ _) (intersect_le_right _ _)
  -- modular law: (R⊚S)⊓T = ((R⊚S)⊓T) ⊓ ((R ⊓ (T⊚S°)) ⊚ S).
  modular {a b c} x y z := by
    refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
    refine Quotient.sound ⟨?_, ?_⟩
    · -- LHS ⊆ RHS: LHS ⊆ LHS (refl) and LHS ⊆ (R⊓(T⊚S°))⊚S by modular_identity.
      exact le_intersect (rel_le_refl _) (modular_identity R S T)
    · -- RHS ⊆ LHS = (R⊚S)⊓T: the first conjunct.
      exact intersect_le_left _ _

/-- The lattice order `⊑` on `Rel(C)` is exactly the relation containment `quotLe`
    (`= RelLe` on representatives).  `x ⊑ y` unfolds to `x ∩ y = x`, i.e. `[R⊓S] = [R]`,
    i.e. `R⊓S ≈ R`; the nontrivial half is `R ⊑ R⊓S ↔ R ⊑ S` (meet UMP). -/
theorem quotLe_iff_algLe {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) :
    quotLe x y ↔ Freyd.Alg.le (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) x y := by
  refine Quotient.inductionOn₂ x y (fun R S => ?_)
  show RelLe R S ↔ qInter (relClass R) (relClass S) = relClass R
  rw [qInter_mk]
  constructor
  · intro h
    exact Quotient.sound ⟨intersect_le_left R S, le_intersect (rel_le_refl R) h⟩
  · intro h
    -- [R⊓S] = [R] gives R ⊑ R⊓S, hence R ⊑ S via intersect_le_right.
    have hRRS : quotLe (relClass R) (relClass (R ⊓ S)) := by
      rw [h]; exact rel_le_refl R   -- quotLe on relClass values defeq-reduces to rel_le
    exact rel_le_trans hRRS (intersect_le_right R S)

end RelAllegory

/-! ## §2.21  `Rel(C)` is a distributive allegory

  For `[PreLogos C]` we add `0` = the empty relation (`subRel` of the bottom subobject
  of `A×B`) and `∪` = `relUnionSub` (the coproduct-free relational union of §1.61).
  The lattice + distributivity laws come from the Ch1 union UMP (`le_relUnionSub`,
  `relUnionSub_le_*`) and the §1.616 distributivity (`compose_union_right`, the
  pre-logos `invImage`-preservation).  The zero laws use that the empty relation is the
  global minimum (`bottom_min`) and that composing with it stays empty
  (`invImage_preserves_bottom` + `existsAlong`/`invImage` adjunction). -/

namespace DisjointGluing

open Freyd.DisjointGluing

section RelDistributive
-- A BARE pre-logos (§1.6) now suffices.  The §1.616 `∪ᵣ` (`relUnion`) distributivity lemmas
-- (compose-over-union, meet-over-union, reciprocal-over-union, in S1_60) were re-based on the
-- SUBOBJECT-union, so they need only `[HasSubobjectUnions]` (supplied by any pre-logos) — no
-- finite coproducts.  This matches Freyd §2.212: "Rel(C) is distributive for ANY pre-logos."
variable [PreLogos 𝒞]

/-- The coterminator `0` (initial object) of a pre-logos (§1.61). -/
private noncomputable def zeroObj : 𝒞 := (minimal_subobject_of_one_is_coterminator (inferInstance)).zero

/-- The EMPTY relation `a → b`: the bottom subobject of `a × b` read as a relation. -/
def emptyRel (a b : 𝒞) : BinRel 𝒞 a b := subRel (PreLogos.bottom (prod a b))

/-- **Strict-initial key**: a subobject `S` whose domain admits a map into the
    coterminator `0` is `≤` every subobject.  (Such an `S.dom` is iso to `0`, hence
    initial, so any two maps out of it — in particular `h ≫ T.arr` and `S.arr` — agree.) -/
theorem subobject_le_of_dom_to_zero {B : 𝒞} {S : Subobject 𝒞 B}
    (m : S.dom ⟶ zeroObj (𝒞 := 𝒞)) (T : Subobject 𝒞 B) : S.le T := by
  -- m is iso (strict initial, §1.61); let minv be its inverse.
  obtain ⟨minv, _hmm, _hmm'⟩ := any_map_to_zero_is_iso (inferInstance) m
  -- S.dom is initial (iso to 0): any two maps S.dom → X agree.
  have hinit : ∀ {X : 𝒞} (f g : S.dom ⟶ X), f = g := by
    intro X f g
    have key : m ≫ (minv ≫ f) = m ≫ (minv ≫ g) :=
      congrArg (m ≫ ·)
        ((minimal_subobject_of_one_is_coterminator (inferInstance)).init_uniq (minv ≫ f) (minv ≫ g))
    calc f = (m ≫ minv) ≫ f := by rw [_hmm, Cat.id_comp]
      _ = m ≫ (minv ≫ f) := Cat.assoc _ _ _
      _ = m ≫ (minv ≫ g) := key
      _ = (m ≫ minv) ≫ g := (Cat.assoc _ _ _).symm
      _ = g := by rw [_hmm, Cat.id_comp]
  -- any map S.dom → T.dom works; the factorization holds automatically by initiality.
  exact ⟨m ≫ (minimal_subobject_of_one_is_coterminator (inferInstance)).init T.dom, hinit _ _⟩

/-- `bottom B`'s domain maps to the coterminator `0` (it is iso to it, §1.61).
    `0 = (bottom one).dom` definitionally, so `bottom_dom_iso B one` provides the map. -/
private noncomputable def bottomToZero (B : 𝒞) : (PreLogos.bottom B).dom ⟶ zeroObj (𝒞 := 𝒞) :=
  (PreLogos.bottom_dom_iso (𝒞 := 𝒞) B (Freyd.one)).choose

/-- The empty relation is the global minimum: `emptyRel a b ⊂ R` for every `R`. -/
theorem emptyRel_le {a b : 𝒞} (R : BinRel 𝒞 a b) : RelLe (emptyRel a b) R := by
  apply (relLe_iff_subLe _ _).2
  -- relSub(emptyRel) ≤ relSub R via subobject_le_of_dom_to_zero (its dom maps to 0).
  have hm : (relSub (emptyRel a b)).dom ⟶ zeroObj (𝒞 := 𝒞) := by
    -- (relSub (subRel (bottom))).dom = (bottom).dom
    exact bottomToZero (prod a b)
  exact subobject_le_of_dom_to_zero hm (relSub R)

/-- A map out of an object that maps to the coterminator `0` is determined by `0`: any two
    such maps agree (the source is iso to initial `0`). -/
private theorem hom_uniq_of_to_zero {X Y : 𝒞} (m : X ⟶ zeroObj (𝒞 := 𝒞)) (f g : X ⟶ Y) :
    f = g := by
  obtain ⟨minv, hmm, _⟩ := any_map_to_zero_is_iso (inferInstance) m
  have key : m ≫ (minv ≫ f) = m ≫ (minv ≫ g) :=
    congrArg (m ≫ ·)
      ((minimal_subobject_of_one_is_coterminator (inferInstance)).init_uniq (minv ≫ f) (minv ≫ g))
  calc f = (m ≫ minv) ≫ f := by rw [hmm, Cat.id_comp]
    _ = m ≫ (minv ≫ f) := Cat.assoc _ _ _
    _ = m ≫ (minv ≫ g) := key
    _ = (m ≫ minv) ≫ g := (Cat.assoc _ _ _).symm
    _ = g := by rw [hmm, Cat.id_comp]

/-- **§2.21 absorbing (right)**: `R ⊚ emptyRel ⊂ emptyRel`.  The composition span sits over
    the pullback whose `π₂`-leg lands in `emptyRel.src ≅ 0`; so the span's source is initial.
    Then `bottom (a×c)` allows the span (any two maps out of an initial object agree), and
    image-minimality gives `relSub(R⊚emptyRel) = image span ≤ bottom = relSub(emptyRel)`.
    (`emptyRel` minimal gives the reverse, so this is the equation `R ⊚ 0 = 0`.) -/
theorem comp_emptyRel_le {a b c : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe (R ⊚ emptyRel b c) (emptyRel a c) := by
  apply (relLe_iff_subLe _ _).2
  let pb := HasPullbacks.has R.colB (emptyRel b c).colA
  let s : pb.cone.pt ⟶ prod a c :=
    pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ (emptyRel b c).colB)
  -- pb.pt is initial: π₂ → emptyRel.src = (bottom (b×c)).dom → 0.
  let m0 : pb.cone.pt ⟶ zeroObj (𝒞 := 𝒞) := pb.cone.π₂ ≫ bottomToZero (prod b c)
  -- relSub(R⊚emptyRel) = image s as a subobject of a×c.
  have hRX_arr : (relSub (R ⊚ emptyRel b c)).arr = (image s).arr := by
    show pair (R ⊚ emptyRel b c).colA (R ⊚ emptyRel b c).colB = (image s).arr
    exact (pair_uniq (R ⊚ emptyRel b c).colA (R ⊚ emptyRel b c).colB (image s).arr rfl rfl).symm
  -- bottom (a×c) allows s: pick any q : pb.pt → bottom.dom; q ≫ bottom.arr = s by initiality.
  have hallow : Allows (PreLogos.bottom (prod a c)) s := by
    obtain ⟨q, _hq⟩ := PreLogos.bottom_min (A := prod a c) (image s)  -- bottom.dom ← ... ; need pb.pt → bottom.dom
    refine ⟨pb.cone.π₂ ≫ bottomToZero (prod b c) ≫
      (minimal_subobject_of_one_is_coterminator (inferInstance)).init (PreLogos.bottom (prod a c)).dom, ?_⟩
    exact hom_uniq_of_to_zero m0 _ s
  -- image s ≤ bottom (a×c).
  have himg_le : (image s).le (PreLogos.bottom (prod a c)) := image_min s _ hallow
  -- transport to relSub(emptyRel a c) (= subRel bottom, same arr as bottom).
  obtain ⟨k, hk⟩ := himg_le   -- k ≫ bottom.arr = (image s).arr
  refine ⟨k, ?_⟩
  -- goal: k ≫ (relSub (emptyRel a c)).arr = (relSub (R⊚emptyRel)).arr
  show k ≫ pair (emptyRel a c).colA (emptyRel a c).colB = (relSub (R ⊚ emptyRel b c)).arr
  rw [hRX_arr]
  -- (emptyRel a c) = subRel (bottom): pair colA colB = bottom.arr (relSub_subRel_arr).
  have hbarr : pair (emptyRel a c).colA (emptyRel a c).colB = (PreLogos.bottom (prod a c)).arr := by
    have := relSub_subRel_arr (𝒞 := 𝒞) (PreLogos.bottom (prod a c))
    -- (relSub (subRel bottom)).arr = bottom.arr; LHS arr is pair of subRel's legs = emptyRel legs.
    simpa [emptyRel, relSub] using this
  rw [hbarr, hk]

/-- **§2.21 absorbing (left)**: `emptyRel ⊚ R ⊂ emptyRel`.  Symmetric to `comp_emptyRel_le`:
    now the pullback's `π₁`-leg lands in `emptyRel.src ≅ 0`. -/
theorem emptyRel_comp_le {a b c : 𝒞} (R : BinRel 𝒞 b c) :
    RelLe (emptyRel a b ⊚ R) (emptyRel a c) := by
  apply (relLe_iff_subLe _ _).2
  let pb := HasPullbacks.has (emptyRel a b).colB R.colA
  let s : pb.cone.pt ⟶ prod a c :=
    pair (pb.cone.π₁ ≫ (emptyRel a b).colA) (pb.cone.π₂ ≫ R.colB)
  let m0 : pb.cone.pt ⟶ zeroObj (𝒞 := 𝒞) := pb.cone.π₁ ≫ bottomToZero (prod a b)
  have hRX_arr : (relSub (emptyRel a b ⊚ R)).arr = (image s).arr := by
    show pair (emptyRel a b ⊚ R).colA (emptyRel a b ⊚ R).colB = (image s).arr
    exact (pair_uniq (emptyRel a b ⊚ R).colA (emptyRel a b ⊚ R).colB (image s).arr rfl rfl).symm
  have hallow : Allows (PreLogos.bottom (prod a c)) s := by
    refine ⟨pb.cone.π₁ ≫ bottomToZero (prod a b) ≫
      (minimal_subobject_of_one_is_coterminator (inferInstance)).init (PreLogos.bottom (prod a c)).dom, ?_⟩
    exact hom_uniq_of_to_zero m0 _ s
  have himg_le : (image s).le (PreLogos.bottom (prod a c)) := image_min s _ hallow
  obtain ⟨k, hk⟩ := himg_le
  refine ⟨k, ?_⟩
  show k ≫ pair (emptyRel a c).colA (emptyRel a c).colB = (relSub (emptyRel a b ⊚ R)).arr
  rw [hRX_arr]
  have hbarr : pair (emptyRel a c).colA (emptyRel a c).colB = (PreLogos.bottom (prod a c)).arr := by
    have := relSub_subRel_arr (𝒞 := 𝒞) (PreLogos.bottom (prod a c))
    simpa [emptyRel, relSub] using this
  rw [hbarr, hk]

/-! ### Union on the quotient and the distributive-allegory instance

  Union on `Rel(C)` is the §1.616 relational union `∪ᵣ` (`relUnion`, the image of the
  coproduct-of-tables).  All distributivity laws are reused from S1_60. -/

/-- Union on the quotient: `[R] ∪ [S] = [R ∪ᵣ S]`, well-defined by the union UMP. -/
def qUnion {a b : 𝒞} (x y : BinRelQuot (𝒞 := 𝒞) a b) : BinRelQuot (𝒞 := 𝒞) a b :=
  Quotient.liftOn₂ x y (fun R S => relClass (R ∪ᵣ S))
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨le_relUnion (rel_le_trans hR.1 (relUnion_le_left _ _))
          (rel_le_trans hS.1 (relUnion_le_right _ _)),
       le_relUnion (rel_le_trans hR.2 (relUnion_le_left _ _))
          (rel_le_trans hS.2 (relUnion_le_right _ _))⟩)

@[simp] theorem qUnion_mk {a b : 𝒞} (R S : BinRel 𝒞 a b) :
    qUnion (relClass R) (relClass S) = relClass (R ∪ᵣ S) := rfl

/-- **§2.21**: `Rel(C)` is a distributive allegory (for a positive pre-logos C).
    `0` = the empty relation, `∪` = the §1.616 relational union `∪ᵣ`. -/
instance (priority := 0) relDistributiveAllegory : DistributiveAllegory (RelObj 𝒞) :=
  { relAllegory with
    zero  := fun {A B} => relClass (emptyRel A.carrier B.carrier)
    union := fun x y => qUnion x y
    -- 0 ⊚ R = 0  and  R ⊚ 0 = 0  (antisymmetry: emptyRel minimal + absorbing).
    zero_comp := fun {A B C} R => by
      refine Quotient.inductionOn R (fun S => ?_)
      exact Quotient.sound ⟨emptyRel_comp_le S, emptyRel_le _⟩
    comp_zero := fun {A B C} R => by
      refine Quotient.inductionOn R (fun S => ?_)
      exact Quotient.sound ⟨comp_emptyRel_le S, emptyRel_le _⟩
    -- union semi-lattice laws (UMP of ∪ᵣ).
    union_idem := fun {A B} x => by
      refine Quotient.inductionOn x (fun R => ?_)
      exact Quotient.sound ⟨le_relUnion (rel_le_refl R) (rel_le_refl R), relUnion_le_left R R⟩
    union_comm := fun {A B} x y => by
      refine Quotient.inductionOn₂ x y (fun R S => ?_)
      exact Quotient.sound
        ⟨le_relUnion (relUnion_le_right S R) (relUnion_le_left S R),
         le_relUnion (relUnion_le_right R S) (relUnion_le_left R S)⟩
    union_assoc := fun {A B} x y z => by
      refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
      refine Quotient.sound ⟨?_, ?_⟩
      · -- R∪(S∪T) ⊆ (R∪S)∪T
        refine le_relUnion ?_ ?_
        · exact rel_le_trans (relUnion_le_left R S) (relUnion_le_left _ T)
        · refine le_relUnion ?_ ?_
          · exact rel_le_trans (relUnion_le_right R S) (relUnion_le_left _ T)
          · exact relUnion_le_right _ T
      · -- (R∪S)∪T ⊆ R∪(S∪T)
        refine le_relUnion ?_ ?_
        · refine le_relUnion ?_ ?_
          · exact relUnion_le_left R _
          · exact rel_le_trans (relUnion_le_left S T) (relUnion_le_right R _)
        · exact rel_le_trans (relUnion_le_right S T) (relUnion_le_right R _)
    -- absorption laws.
    union_inter_absorb := fun {A B} x y => by
      refine Quotient.inductionOn₂ x y (fun R S => ?_)
      exact Quotient.sound
        ⟨le_relUnion (rel_le_refl R) (intersect_le_right S R), relUnion_le_left R _⟩
    inter_union_absorb := fun {A B} x y => by
      refine Quotient.inductionOn₂ x y (fun R S => ?_)
      exact Quotient.sound ⟨intersect_le_right (R ∪ᵣ S) R,
        le_intersect (relUnion_le_left R S) (rel_le_refl R)⟩
    -- composition distributes over union (§1.616, both directions).
    comp_union_distrib := fun {A B C} x y z => by
      refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
      exact Quotient.sound ⟨compose_union_right R S T,
        le_relUnion (compose_le (rel_le_refl R) (relUnion_le_left S T))
          (compose_le (rel_le_refl R) (relUnion_le_right S T))⟩
    -- intersection distributes over union (§1.616, both directions).
    inter_union_distrib := fun {A B} x y z => by
      refine Quotient.inductionOn₃ x y z (fun R S T => ?_)
      exact Quotient.sound ⟨rel_inter_union_le R S T, rel_union_inter_le R S T⟩
    -- 0 ∪ R = R.
    zero_union := fun {A B} x => by
      refine Quotient.inductionOn x (fun R => ?_)
      exact Quotient.sound
        ⟨le_relUnion (emptyRel_le R) (rel_le_refl R), relUnion_le_right _ R⟩ }

end RelDistributive

/-! ## §2.214  Coproducts in `Rel(C)` from a positive coproduct of `C`

  Freyd §2.214: *a pre-logos `C` is POSITIVE iff `Rel(C)` has finite coproducts.*  The
  reachable (forward) direction builds the allegory `Coproduct` (the §2.214 five-equation
  diagram, S2_2) of `Rel(C)` from a disjoint binary coproduct of `C`: the injections are the
  graphs `[graph inl], [graph inr]`, and the five equations are the relational forms of

    (1,4)  `inl`, `inr` MONIC          ⟹  `[inl]⊚[inl]° = 1`,  `[inr]⊚[inr]° = 1`
    (2,3)  `inl ∩ inr = 0` (§1.621)    ⟹  `[inl]⊚[inr]° = 0`,  `[inr]⊚[inl]° = 0`
    (5)    `inl ∪ inr = A+B` (§1.621)  ⟹  `[inl]°⊚[inl] ∪ [inr]°⊚[inr] = 1`.

  Equations (1) and (4) are fully reachable from Ch1 (`graph_comp_recip_le_one_of_mono`
  for `⊆`; `graph` ENTIRE for `⊇`) and are proved below.  Equations (2,3,5) require a
  bridge translating the SUBOBJECT-level §1.621 facts (`inl_inter_inr_le_bottom`,
  `inl_union_inr_entire`, both about subobjects of `A+B`) into the RELATION-composite
  forms `[inl]⊚[inr]° = 0` and `[inl]°⊚[inl] ∪ [inr]°⊚[inr] = 1` — i.e. identifying the
  pullback `pullback(inl, inr)` (a subobject of `A+B`) with the composite relation
  `graph inl ⊚ graph inr°` (a relation `A → B`).  That `compose`-vs-`pullback` dictionary
  for graphs of monics is not yet in the Ch1 layer, so (2,3,5) and the full `Coproduct`
  assembly are left as a precise BOOK TODO (see below). -/

section Coproduct214
-- The §2.214 forward direction lives over a positive (disjoint) coproduct of `C`.
variable [DisjointBinaryCoproduct 𝒞]

/-- The graph injection `[graph f]` as a `Rel(C)`-morphism (an element of `BinRelQuot a b`). -/
def relGraph {a b : 𝒞} (f : a ⟶ b) : BinRelQuot (𝒞 := 𝒞) a b := relClass (graph f)

/-- **§2.214 eq (1)/(4) — the monic injection equation.**  For a MONIC `f : a → b`, the
    graph satisfies `[graph f] ≫ [graph f]° = 1` in `Rel(C)`.  (`⊆` from
    `graph_comp_recip_le_one_of_mono`; `⊇` from `graph` ENTIRE.)  This is the §2.214
    `u₁u₁° = 1` / `u₂u₂° = 1` equation. -/
theorem relGraph_comp_recip_of_monic {a b : 𝒞} (f : a ⟶ b) (hf : Monic f) :
    qComp (relGraph f) (qRecip (relGraph f)) = relId a := by
  show relClass (graph f ⊚ (graph f)°) = relClass (graph (Cat.id a))
  exact Quotient.sound ⟨graph_comp_recip_le_one_of_mono f hf, (graph_is_map f).1⟩

/-- **§2.214 (graph injections are maps).**  Every graph `[graph f]` is entire + simple
    (a MAP) in `Rel(C)`; in particular the would-be coproduct injections are maps. -/
theorem relGraph_simple {a b : 𝒞} (f : a ⟶ b) :
    quotLe (qComp (qRecip (relGraph f)) (relGraph f)) (relId b) :=
  (graph_is_map f).2

/-- A composite `R ⊚ S` whose composition-pullback apex maps to the coterminator `0` is
    the empty relation.  (The composite's source is the image of a span out of that apex;
    since the apex is initial the span factors through `bottom`, so `image ⊂ bottom`.)
    The two §2.214 disjointness equations are instances with `R, S` the injection graphs:
    `pullback(inl, inr)` is initial by §1.621 disjointness. -/
theorem comp_le_empty_of_pullback_to_zero {a b c : 𝒞} (R : BinRel 𝒞 a b) (S : BinRel 𝒞 b c)
    (m : (HasPullbacks.has R.colB S.colA).cone.pt ⟶ zeroObj (𝒞 := 𝒞)) :
    RelLe (R ⊚ S) (emptyRel a c) := by
  apply (relLe_iff_subLe _ _).2
  let pb := HasPullbacks.has R.colB S.colA
  let s : pb.cone.pt ⟶ prod a c := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  have hRX_arr : (relSub (R ⊚ S)).arr = (image s).arr := by
    show pair (R ⊚ S).colA (R ⊚ S).colB = (image s).arr
    exact (pair_uniq (R ⊚ S).colA (R ⊚ S).colB (image s).arr rfl rfl).symm
  have hallow : Allows (PreLogos.bottom (prod a c)) s := by
    refine ⟨m ≫ (minimal_subobject_of_one_is_coterminator (inferInstance)).init
      (PreLogos.bottom (prod a c)).dom, ?_⟩
    exact hom_uniq_of_to_zero m _ s
  obtain ⟨k, hk⟩ := image_min s _ hallow
  refine ⟨k, ?_⟩
  show k ≫ pair (emptyRel a c).colA (emptyRel a c).colB = (relSub (R ⊚ S)).arr
  rw [hRX_arr]
  have hbarr : pair (emptyRel a c).colA (emptyRel a c).colB = (PreLogos.bottom (prod a c)).arr := by
    have := relSub_subRel_arr (𝒞 := 𝒞) (PreLogos.bottom (prod a c)); simpa [emptyRel, relSub] using this
  rw [hbarr, hk]

/-- The pullback apex of the injections `inl, inr` maps to the coterminator `0`: it is the
    domain of `inl ∩ inr`, which §1.621 disjointness places `≤ bottom ≅ 0`. -/
private noncomputable def inlInrPullbackToZero (A B : 𝒞) :
    (HasPullbacks.has (HasBinaryCoproducts.inl (A := A) (B := B)) HasBinaryCoproducts.inr).cone.pt
      ⟶ zeroObj (𝒞 := 𝒞) :=
  (inl_inter_inr_le_bottom (𝒟 := 𝒞) (A := A) (B := B)).choose ≫ bottomToZero _

/-- **§2.214 eq (2) — left/right disjointness.**  `[graph inl] ⊚ [graph inr]° = 0` in
    `Rel(C)`: the composition pullback is `pullback(inl, inr) ≅ 0` (§1.621 disjointness),
    so the composite is empty. -/
theorem relGraph_inl_comp_recip_inr {A B : 𝒞} :
    qComp (relGraph (HasBinaryCoproducts.inl (A := A) (B := B)))
          (qRecip (relGraph (HasBinaryCoproducts.inr (A := A) (B := B))))
      = (relClass (emptyRel A B)) := by
  show relClass (graph HasBinaryCoproducts.inl ⊚ (graph HasBinaryCoproducts.inr)°)
      = relClass (emptyRel A B)
  exact Quotient.sound
    ⟨comp_le_empty_of_pullback_to_zero (graph HasBinaryCoproducts.inl)
      ((graph HasBinaryCoproducts.inr)°) (inlInrPullbackToZero A B),
    emptyRel_le _⟩

/-- **§2.214 eq (3) — right/left disjointness** (symmetric). -/
theorem relGraph_inr_comp_recip_inl {A B : 𝒞} :
    qComp (relGraph (HasBinaryCoproducts.inr (A := A) (B := B)))
          (qRecip (relGraph (HasBinaryCoproducts.inl (A := A) (B := B))))
      = (relClass (emptyRel B A)) := by
  show relClass (graph HasBinaryCoproducts.inr ⊚ (graph HasBinaryCoproducts.inl)°)
      = relClass (emptyRel B A)
  refine Quotient.sound
    ⟨comp_le_empty_of_pullback_to_zero (graph HasBinaryCoproducts.inr)
      ((graph HasBinaryCoproducts.inl)°) ?_, emptyRel_le _⟩
  -- pullback(inr, inl).pt → pullback(inl, inr).pt (swap legs) → 0.
  let pbRL := HasPullbacks.has (HasBinaryCoproducts.inr (A := A) (B := B)) HasBinaryCoproducts.inl
  let pbLR := HasPullbacks.has (HasBinaryCoproducts.inl (A := A) (B := B)) HasBinaryCoproducts.inr
  -- pbRL square: π₁≫inr = π₂≫inl, so (π₂, π₁) is a cone over (inl, inr).
  let cswap : Cone (HasBinaryCoproducts.inl (A := A) (B := B)) HasBinaryCoproducts.inr :=
    ⟨pbRL.cone.pt, pbRL.cone.π₂, pbRL.cone.π₁, pbRL.cone.w.symm⟩
  exact pbLR.lift cswap ≫ inlInrPullbackToZero A B

/-! ### §2.214 eq (5) and the full `Coproduct (RelObj C)` record.

  `u₁_self_comp_recip`, `u₂_self_comp_recip` : `relGraph_comp_recip_of_monic`.
  `u₁_u₂_recip`, `u₂_u₁_recip`               : `relGraph_inl_comp_recip_inr` /
                                               `relGraph_inr_comp_recip_inl`.
  `recip_union_eq_id : [inl]°⊚[inl] ∪ [inr]°⊚[inr] = 1` : proved below
  (`relGraph_recip_union_eq_id`).  Strategy: the union inclusions `x : A → U.dom`,
  `y : B → U.dom` (`U := inlSub ∪ inrSub`) jointly cover `U.dom` (`union_joint_cover`),
  and the union arrow `e := U.arr : U.dom → A+B` is an ISO (`inl_union_inr_entire` makes
  `U = entire`).  Conjugating `1_{U.dom} ⊑ x°x ∪ y°y` by the iso graph `[e]` and using
  `[inl] = [x]⊚[e]`, `[inr] = [y]⊚[e]` (graph respects composition) lands the unit at
  `A+B`. -/

/-- **`graph` respects composition on the quotient** (§1.564): `[graph (f ≫ g)] =
    [graph f] ⊚ [graph g]`.  Both containments are Ch1 (`graph_comp` / `comp_graph`). -/
theorem relGraph_comp {a b c : 𝒞} (f : a ⟶ b) (g : b ⟶ c) :
    relGraph (f ≫ g) = qComp (relGraph f) (relGraph g) :=
  Quotient.sound ⟨graph_comp f g, comp_graph f g⟩

/-- **`[graph e]° ≫ [graph e] = 1` for a cover `e`** (in particular an iso): a cover's
    reciprocal-then-graph composite is the unit (`cover_iff_reciprocal_comp_self_eq_one`).
    Stated with the `Rel(C)` allegory operations on `RelObj C`. -/
theorem relGraph_recip_comp_self_of_cover {a b : 𝒞} (e : a ⟶ b) (he : Cover e) :
    (relGraph e)° ≫ (relGraph e) = @Cat.id (RelObj 𝒞) _ ⟨b⟩ := by
  show relClass ((graph e)° ⊚ graph e) = relClass (graph (Cat.id b))
  obtain ⟨hle, hge⟩ := (cover_iff_reciprocal_comp_self_eq_one e).mp he
  exact Quotient.sound ⟨hle, hge⟩

open Freyd.Alg in
/-- **§2.214 eq (5)** — the joint-cover equation.  `[inl]° ≫ [inl] ∪ [inr]° ≫ [inr] = 1`
    on `A+B` in `Rel(C)` (allegory operations).  The union inclusions jointly cover
    `U := inlSub ∪ inrSub` (`union_joint_cover`), and the union arrow is an iso
    (`inl_union_inr_entire`), so conjugating the `U`-unit by the iso graph transports it
    to `A+B`. -/
theorem relGraph_recip_union_eq_id {A B : 𝒞} :
    ((relGraph (HasBinaryCoproducts.inl (A := A) (B := B)))°
        ≫ relGraph (HasBinaryCoproducts.inl (A := A) (B := B)))
      ∪ ((relGraph (HasBinaryCoproducts.inr (A := A) (B := B)))°
        ≫ relGraph (HasBinaryCoproducts.inr (A := A) (B := B)))
      = @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ := by
  -- The union subobject and its inclusions.
  let U := HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
                                    (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)
  obtain ⟨x, hx⟩ := HasSubobjectUnions.union_left
    (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono) (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)
  obtain ⟨y, hy⟩ := HasSubobjectUnions.union_right
    (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono) (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono)
  -- hx : x ≫ U.arr = inlSub.arr = inl ;  hy : y ≫ U.arr = inrSub.arr = inr.
  change x ≫ U.arr = HasBinaryCoproducts.inl at hx
  change y ≫ U.arr = HasBinaryCoproducts.inr at hy
  -- U.arr is an ISO: entire ≤ U (inl_union_inr_entire) gives a section, so U.arr is a
  -- split-epi monic, hence a cover.
  obtain ⟨e, he⟩ := inl_union_inr_entire (𝒟 := 𝒞) (A := A) (B := B)  -- e ≫ U.arr = (entire).arr = id
  have heU : e ≫ U.arr = Cat.id (HasBinaryCoproducts.coprod A B) := he
  have hcov : Cover U.arr := cover_of_section U.arr e heU
  -- Allegory-level abbreviations (morphisms of `RelObj C`).  `let` keeps them defeq to
  -- the underlying graphs so the bridge lemmas apply on the nose.
  let inlR : (⟨A⟩ : RelObj 𝒞) ⟶ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    relGraph (HasBinaryCoproducts.inl (A := A) (B := B))
  let inrR : (⟨B⟩ : RelObj 𝒞) ⟶ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    relGraph (HasBinaryCoproducts.inr (A := A) (B := B))
  let eR : (⟨U.dom⟩ : RelObj 𝒞) ⟶ ⟨HasBinaryCoproducts.coprod A B⟩ := relGraph U.arr
  let xR : (⟨A⟩ : RelObj 𝒞) ⟶ ⟨U.dom⟩ := relGraph x
  let yR : (⟨B⟩ : RelObj 𝒞) ⟶ ⟨U.dom⟩ := relGraph y
  -- rewrite the goal in terms of the abbreviations.
  show (inlR° ≫ inlR) ∪ (inrR° ≫ inrR) = @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩
  -- [inl] = [x] ≫ [e],  [inr] = [y] ≫ [e]  (graph respects composition).
  have hinl_fac : inlR = xR ≫ eR := by
    show relGraph (HasBinaryCoproducts.inl (A := A) (B := B)) = qComp (relGraph x) (relGraph U.arr)
    rw [← hx]; exact relGraph_comp x U.arr
  have hinr_fac : inrR = yR ≫ eR := by
    show relGraph (HasBinaryCoproducts.inr (A := A) (B := B)) = qComp (relGraph y) (relGraph U.arr)
    rw [← hy]; exact relGraph_comp y U.arr
  -- [e]° ≫ [e] = 1_{A+B}.
  have heRe : eR° ≫ eR = @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    relGraph_recip_comp_self_of_cover U.arr hcov
  -- The joint cover at U: 1_{U.dom} ⊑ x°x ∪ y°y (bridge `quotLe → ⊑`).
  have hjoint : (@Cat.id (RelObj 𝒞) _ ⟨U.dom⟩) ⊑ (xR° ≫ xR) ∪ (yR° ≫ yR) :=
    (quotLe_iff_algLe _ _).mp
      (union_joint_cover (𝒞 := 𝒞) (inlSub (𝒞 := 𝒞) (A := A) (B := B) inl_mono)
        (inrSub (𝒞 := 𝒞) (A := A) (B := B) inr_mono) hx hy)
  -- `relGraph_simple` summands ⊑ 1 (bridge).
  have hsimp_l : inlR° ≫ inlR ⊑ @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    (quotLe_iff_algLe _ _).mp (relGraph_simple (HasBinaryCoproducts.inl (A := A) (B := B)))
  have hsimp_r : inrR° ≫ inrR ⊑ @Cat.id (RelObj 𝒞) _ ⟨HasBinaryCoproducts.coprod A B⟩ :=
    (quotLe_iff_algLe _ _).mp (relGraph_simple (HasBinaryCoproducts.inr (A := A) (B := B)))
  apply Freyd.Alg.le_antisymm
  · -- (u₁°u₁ ∪ u₂°u₂) ⊑ 1 : each summand is simple.
    exact union_lub hsimp_l hsimp_r
  · -- 1 = e°≫e = e°≫1_U≫e ⊑ e°≫(x°x∪y°y)≫e = u₁°u₁∪u₂°u₂.
    have hconj : (eR° ≫ ((@Cat.id (RelObj 𝒞) _ ⟨U.dom⟩)) ≫ eR)
        ⊑ (eR° ≫ ((xR° ≫ xR) ∪ (yR° ≫ yR)) ≫ eR) :=
      comp_mono_left _ (comp_mono_right hjoint _)
    -- LHS = e°≫e = 1.
    rw [Cat.id_comp, heRe] at hconj
    -- RHS = u₁°u₁ ∪ u₂°u₂.
    have hRHS : eR° ≫ ((xR° ≫ xR) ∪ (yR° ≫ yR)) ≫ eR
        = (inlR° ≫ inlR) ∪ (inrR° ≫ inrR) := by
      rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib, hinl_fac, hinr_fac]
      -- both summands: e°≫(z°≫z)≫e = (z≫e)°≫(z≫e)  via assoc + recip_comp.
      congr 1 <;>
        · rw [Allegory.recip_comp]
          simp only [Cat.assoc]
    rw [hRHS] at hconj
    exact hconj

/-- **§2.214 (forward direction).**  A disjoint/positive binary coproduct of `C` gives a
    coproduct in `Rel(C)`: the §2.214 five-equation `Coproduct` record over `RelObj C`,
    with injections the graphs `[inl], [inr]`. -/
noncomputable def relCoproduct (A B : 𝒞) :
    Coproduct (𝒜 := RelObj 𝒞) ⟨HasBinaryCoproducts.coprod A B⟩ ⟨A⟩ ⟨B⟩ where
  u₁ := relGraph (HasBinaryCoproducts.inl (A := A) (B := B))
  u₂ := relGraph (HasBinaryCoproducts.inr (A := A) (B := B))
  u₁_self_comp_recip := relGraph_comp_recip_of_monic _ inl_mono
  u₂_self_comp_recip := relGraph_comp_recip_of_monic _ inr_mono
  u₁_u₂_recip := relGraph_inl_comp_recip_inr
  u₂_u₁_recip := relGraph_inr_comp_recip_inl
  recip_union_eq_id := relGraph_recip_union_eq_id

end Coproduct214

end DisjointGluing

/-! ## §2.14 / §2.15  `Rel(C)` is a tabular, unitary allegory

  The two structural facts of `Rel(C)` that, with `Map(Rel C)`, make it a pre-logos
  (the §2.217 faithful-representation route):

    • **Tabular** (§2.14): every relation tabulates.  A relation `R : a → b`, picked as
      a `BinRel` table `⟨src; colA, colB⟩`, is tabulated by its own legs read as graphs:
      `f = [graph colA] : ⟨src⟩ → ⟨a⟩`, `g = [graph colB] : ⟨src⟩ → ⟨b⟩`.  These are
      maps (`graph_is_map`), `R = f° ≫ g` (span reconstitution), and `ff° ∩ gg° = 1`
      (joint monicity of the tabulating pair).

    • **Unitary** (§2.15): the unit object is `C`'s terminator `1`.  Every relation
      `T → T` (T := ⟨1⟩) is `⊑ 1` because both legs of any table over `1` are the unique
      map to the terminator; and every object has an entire relation to `1` (the graph of
      the terminal map). -/

section TabularUnitary
variable [RegularCategory 𝒞]

/-! ### BinRel-level reconstitution and joint monicity -/

/-- **Span reconstitution (⊆)**: `(graph R.colA)° ⊚ graph R.colB ⊂ R`.  The composite's
    pullback is `pullback(id, id)` over `R.src`, on which `π₁ = π₂`, so its span is
    `π₁ ≫ pair R.colA R.colB`, which `Allows` the subobject `⟨R.src; pair colA colB⟩`;
    image-minimality gives the `RelHom`. -/
theorem reconstitute_le {a b : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe ((graph R.colA)° ⊚ graph R.colB) R := by
  let pb := HasPullbacks.has ((graph R.colA)°).colB (graph R.colB).colA
  -- both pullback maps are id_{R.src}, so π₁ = π₂.
  have h_pb_w : pb.cone.π₁ = pb.cone.π₂ := by
    have := pb.cone.w; simpa [graph, reciprocal, Cat.comp_id] using this
  let span := pair (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₂ ≫ (graph R.colB).colB)
  have h_monic : Monic (pair R.colA R.colB) := monic_pair_of_monicPair R.colA R.colB R.isMonicPair
  let S : Subobject 𝒞 (prod a b) := ⟨R.src, pair R.colA R.colB, h_monic⟩
  -- span = π₁ ≫ pair R.colA R.colB.
  have h_span_eq : pb.cone.π₁ ≫ pair R.colA R.colB = span := by
    show pb.cone.π₁ ≫ pair R.colA R.colB
       = pair (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₂ ≫ (graph R.colB).colB)
    rw [← h_pb_w]
    apply pair_uniq (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₁ ≫ (graph R.colB).colB) _
      (by rw [Cat.assoc, fst_pair]; rfl)
      (by rw [Cat.assoc, snd_pair]; rfl)
  have hallows : Allows S span := ⟨pb.cone.π₁, h_span_eq⟩
  let I := image span
  rcases image_min span S hallows with ⟨k, hk⟩
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ R.colA = (I.arr ≫ fst)
    calc k ≫ R.colA = (k ≫ pair R.colA R.colB) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = I.arr ≫ fst := by rw [hk]
  · show k ≫ R.colB = (I.arr ≫ snd)
    calc k ≫ R.colB = (k ≫ pair R.colA R.colB) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = I.arr ≫ snd := by rw [hk]

/-- **Span reconstitution (⊇)**: `R ⊂ (graph R.colA)° ⊚ graph R.colB`.  Lift `R.src` into
    the trivial pullback via the cone `⟨id, id⟩`, then `R.src → I.dom` through the image
    lift; its legs are `R.colA`, `R.colB`. -/
theorem le_reconstitute {a b : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe R ((graph R.colA)° ⊚ graph R.colB) := by
  let pb := HasPullbacks.has ((graph R.colA)°).colB (graph R.colB).colA
  -- cone ⟨R.src; id, id⟩ over (id, id).
  have h_cone_w : (Cat.id R.src) ≫ ((graph R.colA)°).colB
      = (Cat.id R.src) ≫ (graph R.colB).colA := by
    show (Cat.id R.src) ≫ (Cat.id R.src) = (Cat.id R.src) ≫ (Cat.id R.src); rfl
  let c : Cone ((graph R.colA)°).colB (graph R.colB).colA :=
    ⟨R.src, Cat.id R.src, Cat.id R.src, h_cone_w⟩
  let u := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id R.src := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = Cat.id R.src := pb.lift_snd c
  let span := pair (pb.cone.π₁ ≫ ((graph R.colA)°).colA) (pb.cone.π₂ ≫ (graph R.colB).colB)
  let I := image span
  let h : R.src ⟶ I.dom := u ≫ image.lift span
  refine ⟨⟨h, ?_, ?_⟩⟩
  · show h ≫ (I.arr ≫ fst) = R.colA
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac, fst_pair,
        ← Cat.assoc u pb.cone.π₁, hu₁, Cat.id_comp]
    rfl
  · show h ≫ (I.arr ≫ snd) = R.colB
    rw [Cat.assoc, ← Cat.assoc (image.lift span), image.lift_fac, snd_pair,
        ← Cat.assoc u pb.cone.π₂, hu₂, Cat.id_comp]
    rfl

/-- **Joint monicity (⊆)**: the legs of the meet `P ⊓ Q`, where `P = graph colA ⊚
    (graph colA)°` and `Q = graph colB ⊚ (graph colB)°` are the levels of the two
    columns, are equal.  `(P⊓Q).colA = π₁ ≫ P.colA`, `(P⊓Q).colB = π₁ ≫ P.colB`; the two
    agree under `colA` (`level_legs_comp` for colA, since `P.colA, P.colB` are `P`'s legs)
    and under `colB` (the pullback identifies `π₁≫P.legs` with `π₂≫Q.legs`, then
    `level_legs_comp` for colB), so `R.isMonicPair` collapses them — giving
    `graph colA ⊚ (graph colA)° ∩ graph colB ⊚ (graph colB)° ⊂ graph (id R.src)`. -/
private theorem jointMonic_le {a b : 𝒞} (R : BinRel 𝒞 a b) :
    RelLe ((graph R.colA ⊚ (graph R.colA)°) ⊓ (graph R.colB ⊚ (graph R.colB)°))
          (graph (Cat.id R.src)) := by
  let P := graph R.colA ⊚ (graph R.colA)°
  let Q := graph R.colB ⊚ (graph R.colB)°
  -- the meet is the pullback of eP, eQ into R.src × R.src.
  let eP := pair P.colA P.colB
  let eQ := pair Q.colA Q.colB
  let pb := HasPullbacks.has eP eQ
  -- `level_legs_comp` for each column (defeq to P, Q).
  have hlevP : P.colA ≫ R.colA = P.colB ≫ R.colA := level_legs_comp R.colA
  have hlevQ : Q.colA ≫ R.colB = Q.colB ≫ R.colB := level_legs_comp R.colB
  -- (P⊓Q).colA = π₁ ≫ P.colA, (P⊓Q).colB = π₁ ≫ P.colB.
  -- pullback identification: π₁ ≫ eP = π₂ ≫ eQ, projecting to:
  have hidA : pb.cone.π₁ ≫ P.colA = pb.cone.π₂ ≫ Q.colA := by
    have hsq := pb.cone.w
    calc pb.cone.π₁ ≫ P.colA = pb.cone.π₁ ≫ (eP ≫ fst) := by rw [fst_pair]
      _ = (pb.cone.π₁ ≫ eP) ≫ fst := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₂ ≫ eQ) ≫ fst := by rw [hsq]
      _ = pb.cone.π₂ ≫ (eQ ≫ fst) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ Q.colA := by rw [fst_pair]
  have hidB : pb.cone.π₁ ≫ P.colB = pb.cone.π₂ ≫ Q.colB := by
    have hsq := pb.cone.w
    calc pb.cone.π₁ ≫ P.colB = pb.cone.π₁ ≫ (eP ≫ snd) := by rw [snd_pair]
      _ = (pb.cone.π₁ ≫ eP) ≫ snd := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₂ ≫ eQ) ≫ snd := by rw [hsq]
      _ = pb.cone.π₂ ≫ (eQ ≫ snd) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ Q.colB := by rw [snd_pair]
  -- legs equal under colA : (π₁≫P.colA)≫colA = (π₁≫P.colB)≫colA  [level of colA].
  have hcolA : (pb.cone.π₁ ≫ P.colA) ≫ R.colA = (pb.cone.π₁ ≫ P.colB) ≫ R.colA := by
    calc (pb.cone.π₁ ≫ P.colA) ≫ R.colA = pb.cone.π₁ ≫ (P.colA ≫ R.colA) := Cat.assoc _ _ _
      _ = pb.cone.π₁ ≫ (P.colB ≫ R.colA) := by rw [hlevP]
      _ = (pb.cone.π₁ ≫ P.colB) ≫ R.colA := (Cat.assoc _ _ _).symm
  -- legs equal under colB : (π₁≫P.colA)≫colB = (π₁≫P.colB)≫colB  [via Q, level of colB].
  have hcolB : (pb.cone.π₁ ≫ P.colA) ≫ R.colB = (pb.cone.π₁ ≫ P.colB) ≫ R.colB := by
    calc (pb.cone.π₁ ≫ P.colA) ≫ R.colB = (pb.cone.π₂ ≫ Q.colA) ≫ R.colB := by rw [hidA]
      _ = pb.cone.π₂ ≫ (Q.colA ≫ R.colB) := Cat.assoc _ _ _
      _ = pb.cone.π₂ ≫ (Q.colB ≫ R.colB) := by rw [hlevQ]
      _ = (pb.cone.π₂ ≫ Q.colB) ≫ R.colB := (Cat.assoc _ _ _).symm
      _ = (pb.cone.π₁ ≫ P.colB) ≫ R.colB := by rw [hidB]
  -- joint monicity collapses the two legs.
  have hlegs : pb.cone.π₁ ≫ P.colA = pb.cone.π₁ ≫ P.colB :=
    R.isMonicPair _ _ hcolA hcolB
  -- the RelHom into graph(id): witness = (P⊓Q).colA; `graph(id).colA = graph(id).colB = id`,
  -- so both legs reduce to `(P⊓Q).colA` (using `hlegs : (P⊓Q).colA = (P⊓Q).colB`).
  refine ⟨⟨(P ⊓ Q).colA, ?_, ?_⟩⟩
  · show (P ⊓ Q).colA ≫ Cat.id R.src = (P ⊓ Q).colA; rw [Cat.comp_id]
  · show (P ⊓ Q).colA ≫ Cat.id R.src = (P ⊓ Q).colB
    rw [Cat.comp_id]; exact hlegs

/-! ### Allegory-level bridges: `Map`, `Entire`, `Simple` of a `relClass` -/

/-- The allegory domain `dom` of a `relClass` is the class of `graph id ⊓ R⊚R°`. -/
private theorem dom_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.dom (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R)
      = relClass (graph (Cat.id a) ⊓ (R ⊚ R°)) := by
  show qInter (relId a) (qComp (relClass R) (qRecip (relClass R))) = _
  rw [qRecip_mk, qComp_mk]; rfl

/-- **Entire bridge**: `Alg.Entire (relClass R) ↔ Entire R` (BinRel).  Both say
    `graph id ⊂ R⊚R°`. -/
private theorem entire_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.Entire (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R) ↔ Freyd.Entire R := by
  show Freyd.Alg.dom (𝒜 := RelObj 𝒞) (relClass R) = relId a ↔ _
  rw [dom_relClass]
  constructor
  · intro h
    -- relClass (graph id ⊓ R⊚R°) = relClass (graph id) gives graph id ⊂ R⊚R°.
    have hqe : quotLe (relClass (graph (Cat.id a))) (relClass (graph (Cat.id a) ⊓ (R ⊚ R°))) := by
      rw [h]; exact rel_le_refl _   -- quotLe on relClass values defeq-reduces to rel_le
    exact rel_le_trans hqe (intersect_le_right _ _)
  · intro h
    -- graph id ⊂ R⊚R° gives graph id ⊓ R⊚R° ≈ graph id.
    exact Quotient.sound ⟨intersect_le_left _ _, le_intersect (rel_le_refl _) h⟩

/-- **Simple bridge**: `Alg.Simple (relClass R) ↔ Simple R` (BinRel).  Both say
    `R°⊚R ⊂ graph id`. -/
private theorem simple_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.Simple (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R) ↔ Freyd.Simple R := by
  -- `Alg.Simple (relClass R)` is `Alg.le (relClass (R°⊚R)) (relId b)`; `Simple R` is the
  -- corresponding `quotLe`, which `quotLe_iff_algLe` identifies.
  change Freyd.Alg.le (𝒜 := RelObj 𝒞) (relClass (R° ⊚ R)) (relId b) ↔ _
  exact (quotLe_iff_algLe (relClass (R° ⊚ R)) (relId b)).symm

/-- **Map bridge**: `Alg.Map (relClass R) ↔ Map R`. -/
private theorem map_relClass {a b : 𝒞} (R : BinRel 𝒞 a b) :
    Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R) ↔ Freyd.Map R :=
  and_congr (entire_relClass R) (simple_relClass R)

/-- A graph's class is a `Map` in `Rel(C)` (from `graph_is_map`). -/
theorem relClass_graph_map {a b : 𝒞} (f : a ⟶ b) :
    Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass (graph f)) :=
  (map_relClass (graph f)).mpr (graph_is_map f)

/-! ### §2.14  `Rel(C)` is a tabular allegory -/

/-- **§2.14**: `Rel(C)` is a TABULAR allegory.  A relation `[R]` is tabulated by the
    graphs of its own legs: apex `⟨R.src⟩`, `f = [graph R.colA]`, `g = [graph R.colB]`.
    The four conjuncts are: both graphs are maps (`relClass_graph_map`); `[R] = f° ≫ g`
    (`reconstitute_le`/`le_reconstitute`); `f f° ∩ g g° = 1` (`jointMonic_le` for `⊆`,
    `relGraph_entire`-style entirety for `⊇`). -/
instance (priority := 0) relTabularAllegory : TabularAllegory (RelObj 𝒞) :=
  { relAllegory with
    tabular := fun {A B} x => by
      refine Quotient.inductionOn x (fun R => ?_)
      refine ⟨⟨R.src⟩, relClass (graph R.colA), relClass (graph R.colB),
        relClass_graph_map R.colA, relClass_graph_map R.colB, ?_, ?_⟩
      · -- [R] = [graph R.colA]° ≫ [graph R.colB]
        show relClass R = relClass ((graph R.colA)° ⊚ graph R.colB)
        exact Quotient.sound ⟨le_reconstitute R, reconstitute_le R⟩
      · -- f f° ∩ g g° = 1_{R.src}
        show qInter (relClass (graph R.colA ⊚ (graph R.colA)°))
              (relClass (graph R.colB ⊚ (graph R.colB)°)) = relId R.src
        rw [qInter_mk]
        -- relClass (graph colA ⊚ (graph colA)° ⊓ graph colB ⊚ (graph colB)°) = relId R.src
        refine Quotient.sound ⟨jointMonic_le R, ?_⟩
        -- 1 ⊂ ff° ∩ gg° : both columns are entire (graphs are maps).
        exact le_intersect (graph_is_map R.colA).1 (graph_is_map R.colB).1 }

/-! ### §2.15  `Rel(C)` is a unitary allegory: the unit is `C`'s terminator `1` -/

/-- Every relation over the terminator `T → T` (`T = ⟨1⟩`) is `⊑ 1`: both legs of any
    table over `1` are the unique map to `1`, so the table is `⊂ graph (id 1)`. -/
private theorem partialUnit_one : PartialUnit (𝒜 := RelObj 𝒞) ⟨Freyd.one (𝒞 := 𝒞)⟩ := by
  intro x
  refine Quotient.inductionOn x (fun R => ?_)
  rw [← quotLe_iff_algLe]
  -- RelHom R (graph (id 1)) : witness R.colA; both legs land on the terminator.
  refine ⟨⟨R.colA, ?_, ?_⟩⟩
  · show R.colA ≫ Cat.id Freyd.one = R.colA; rw [Cat.comp_id]
  · -- R.colA ≫ id = R.colB : both R.colA, R.colB : R.src → 1 are the unique terminal map.
    show R.colA ≫ Cat.id Freyd.one = R.colB
    rw [Cat.comp_id]; exact Freyd.term_uniq R.colA R.colB

/-- The graph of the terminal map `a → 1` is an entire relation `⟨a⟩ → ⟨1⟩`. -/
private theorem entire_to_one (a : 𝒞) :
    Freyd.Alg.Entire (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨Freyd.one (𝒞 := 𝒞)⟩)
      (relClass (graph (Freyd.term a))) :=
  (entire_relClass (graph (Freyd.term a))).mpr (graph_is_map (Freyd.term a)).1

/-- **§2.15**: `Rel(C)` is a UNITARY allegory with unit object `⟨1⟩` (`C`'s terminator).
    Partial-unit: `partialUnit_one`.  Entirety: each object `⟨a⟩` has the entire relation
    `[graph (a → 1)]` (`entire_to_one`). -/
instance (priority := 0) relUnitaryAllegory : UnitaryAllegory (RelObj 𝒞) :=
  { relAllegory with
    unit_obj := ⟨Freyd.one (𝒞 := 𝒞)⟩
    unit_prop := ⟨partialUnit_one,
      fun a => ⟨relClass (graph (Freyd.term a.carrier)), entire_to_one a.carrier⟩⟩ }

end TabularUnitary

/-! ## §1.784 / §2.32 (forward)  `Rel(C)` is a DIVISION ALLEGORY when `C` is a logos

  Freyd §1.784: "in a logos, `R/S` exists for every pair of relations with a common target."
  §1.78 (`RelQuot`) already gives the universal property `T ⊑ R/S ↔ T⊚S ⊑ R`, and §1.782/§1.784
  (S1_77) supply two SPECIAL quotients: by a graph (`relQuotByMap`) and by the reciprocal of a
  graph (`relQuotByMapRecip`, the `f##` right-adjoint image, needs `HasRightAdjointImage`).

  Every relation factors through its own legs: `S ≈ (graph S.colA)° ⊚ graph S.colB`
  (`reconstitute_le`/`le_reconstitute`).  By §1.783 associativity, the GENERAL quotient is the
  two special ones composed:

      R / S  =  (R / graph S.colB) / (graph S.colA)°.

  The inner `R/graph(S.colB)` lives because `C` is regular (`PullbacksTransferCovers`); the outer
  `_/(graph S.colA)°` because `C` is a logos (`HasRightAdjointImage`).  We package the result as
  `DivisionAllegory (RelObj C)` — the LAST gap for §2.343 (every logos embeds in a positive
  effective logos). -/

section RelDivision

variable [Logos 𝒞]

-- A logos is in particular a pre-logos (§1.711); make it available so the `BinRel`/subobject
-- bridge (`relSub`, `relLe_iff_subLe`) and the `relQuotByMapRecip` (`f##`) construction resolve.
attribute [local instance] logos_implies_preLogos

/-- **§1.784 general relational quotient.**  For `R : a → c` and `S : b → c` in a logos, the
    quotient `R/S : a → b` (maximal `T` with `T⊚S ⊑ R`), built as `(R/graph(S.colB))/(graph S.colA)°`
    via the span factorisation `S ≈ (graph S.colA)° ⊚ graph S.colB`. -/
noncomputable def relQuotGen {a b c : 𝒞} (R : BinRel 𝒞 a c) (S : BinRel 𝒞 b c) :
    RelQuot R S where
  quot := (relQuotByMapRecip (relQuotByMap R S.colB).quot S.colA).quot
  le := by
    -- quot ⊚ S ≈ quot ⊚ ((graph S.colA)° ⊚ graph S.colB) ≈ (quot ⊚ (graph S.colA)°) ⊚ graph S.colB
    -- and (quot ⊚ (graph S.colA)°) ⊑ (R/graph S.colB), so the whole ⊑ R.
    let q₁ := relQuotByMap R S.colB                                   -- R / graph(S.colB)
    let q₂ := relQuotByMapRecip q₁.quot S.colA                        -- q₁.quot / (graph S.colA)°
    -- q₂.quot ⊚ (graph S.colA)° ⊑ q₁.quot   (q₂.le)
    have hstep : RelLe (q₂.quot ⊚ (graph S.colA)°) q₁.quot := q₂.le
    -- q₂.quot ⊚ S ⊑ q₂.quot ⊚ ((graph S.colA)° ⊚ graph S.colB)        [S ⊑ recon]
    have hS : RelLe (q₂.quot ⊚ S) (q₂.quot ⊚ ((graph S.colA)° ⊚ graph S.colB)) :=
      compose_le (rel_le_refl _) (le_reconstitute S)
    -- reassociate to ((q₂.quot ⊚ (graph S.colA)°) ⊚ graph S.colB)
    have hass : RelLe (q₂.quot ⊚ ((graph S.colA)° ⊚ graph S.colB))
        ((q₂.quot ⊚ (graph S.colA)°) ⊚ graph S.colB) :=
      compose_assoc' q₂.quot ((graph S.colA)°) (graph S.colB)
    -- (q₂.quot ⊚ (graph S.colA)°) ⊚ graph S.colB ⊑ q₁.quot ⊚ graph S.colB ⊑ R
    have h3 : RelLe ((q₂.quot ⊚ (graph S.colA)°) ⊚ graph S.colB) (q₁.quot ⊚ graph S.colB) :=
      compose_le_left hstep (graph S.colB)
    exact rel_le_trans hS (rel_le_trans hass (rel_le_trans h3 q₁.le))
  maximal := by
    intro T hT
    -- hT : T ⊚ S ⊑ R.   Want T ⊑ q₂.quot, i.e. T ⊚ (graph S.colA)° ⊑ q₁.quot,
    -- i.e. (T ⊚ (graph S.colA)°) ⊚ graph S.colB ⊑ R.
    let q₁ := relQuotByMap R S.colB
    let q₂ := relQuotByMapRecip q₁.quot S.colA
    apply (relQuot_iff q₂ T).mpr        -- reduce to T ⊚ (graph S.colA)° ⊑ q₁.quot
    apply (relQuot_iff q₁ _).mpr        -- reduce to (T ⊚ (graph S.colA)°) ⊚ graph S.colB ⊑ R
    -- (T ⊚ (graph S.colA)°) ⊚ graph S.colB ≈ T ⊚ ((graph S.colA)° ⊚ graph S.colB) ⊑ T ⊚ S ⊑ R
    have hass : RelLe ((T ⊚ (graph S.colA)°) ⊚ graph S.colB)
        (T ⊚ ((graph S.colA)° ⊚ graph S.colB)) :=
      compose_assoc T ((graph S.colA)°) (graph S.colB)
    have hrec : RelLe (T ⊚ ((graph S.colA)° ⊚ graph S.colB)) (T ⊚ S) :=
      compose_le (rel_le_refl T) (reconstitute_le S)
    exact rel_le_trans hass (rel_le_trans hrec hT)

/-- The quotient `R/S` is MONOTONE in `R` and ANTITONE in `S`: from `R ⊂ R'` and `S' ⊂ S`,
    `relQuotGen R S ⊂ relQuotGen R' S'`.  (Pure consequence of the universal property
    `relQuot_iff`; used to descend `R/S` to the `RelLe`-quotient.) -/
private theorem relQuotGen_mono {a b c : 𝒞}
    {R R' : BinRel 𝒞 a c} {S S' : BinRel 𝒞 b c}
    (hR : RelLe R R') (hS : RelLe S' S) :
    RelLe (relQuotGen R S).quot (relQuotGen R' S').quot := by
  apply (relQuot_iff (relQuotGen R' S') _).mpr
  -- (R/S) ⊚ S' ⊑ (R/S) ⊚ S ⊑ R ⊑ R'
  refine rel_le_trans (compose_le (rel_le_refl _) hS) ?_
  exact rel_le_trans (relQuotGen R S).le hR

/-- Division on the `RelLe`-quotient: `[R] / [S] = [relQuotGen R S]`, well-defined by
    `relQuotGen_mono` (antisymmetry of the two monotonicity directions). -/
noncomputable def qDiv {a b c : 𝒞}
    (x : BinRelQuot (𝒞 := 𝒞) a c) (y : BinRelQuot (𝒞 := 𝒞) b c) :
    BinRelQuot (𝒞 := 𝒞) a b :=
  Quotient.liftOn₂ x y (fun R S => relClass (relQuotGen R S).quot)
    (fun _ _ _ _ hR hS => Quotient.sound
      ⟨relQuotGen_mono hR.1 hS.2, relQuotGen_mono hR.2 hS.1⟩)

@[simp] theorem qDiv_mk {a b c : 𝒞} (R : BinRel 𝒞 a c) (S : BinRel 𝒞 b c) :
    qDiv (relClass R) (relClass S) = relClass (relQuotGen R S).quot := rfl

/-- **§1.784 / §2.32 (forward)**: `Rel(C)` is a DIVISION ALLEGORY for a logos `C`.
    `div = qDiv` (the §1.784 general quotient); the two adjunction laws are exactly the
    `le`/`maximal` of `relQuotGen`, transported across the `quotLe ↔ ⊑` bridge
    (`quotLe_iff_algLe`).  This is the last brick for §2.343. -/
noncomputable instance relDivisionAllegory : DivisionAllegory (RelObj 𝒞) :=
  { DisjointGluing.relDistributiveAllegory with
    div := fun {a b c} R S => qDiv R S
    div_comp_le := fun {a b c} R S => by
      -- (R/S) ≫ S ⊑ R  ⟺  RelLe ((relQuotGen R S).quot ⊚ S') R  =  (relQuotGen R S).le
      refine Quotient.inductionOn₂ R S (fun R S => ?_)
      rw [← quotLe_iff_algLe]
      show quotLe (qComp (qDiv (relClass R) (relClass S)) (relClass S)) (relClass R)
      rw [qDiv_mk, qComp_mk]
      exact (relQuotGen R S).le
    le_div := fun {a b c} T R S h => by
      -- T ≫ S ⊑ R → T ⊑ R/S, by `relQuotGen.maximal` (= `relQuot_iff`).
      refine Quotient.inductionOn₃ T R S (fun T R S h => ?_) h
      rw [← quotLe_iff_algLe]
      show quotLe (relClass T) (qDiv (relClass R) (relClass S))
      rw [qDiv_mk]
      apply (relQuotGen R S).maximal
      -- h : T ≫ S ⊑ R  ⟹  RelLe (T ⊚ S) R
      have h' : quotLe (qComp (relClass T) (relClass S)) (relClass R) :=
        (quotLe_iff_algLe _ _).mpr h
      rwa [qComp_mk] at h' }

end RelDivision

/-! ### §2.217  `Rel(C)` is a tabular-unitary-distributive allegory; `Map(Rel C)` is a pre-logos;
    and `C ↪ Map(Rel C)` is a faithful embedding.

  Assembling `relTabularAllegory`, `relUnitaryAllegory` (§2.14/§2.15) and the positive-pre-logos
  `relDistributiveAllegory` (§2.21) onto the SINGLE diamond-merged class
  `TabularUnitaryDistributiveAllegory` lets `MapCat`'s `mapPreLogos` fire, giving a pre-logos
  `Map(Rel C)`.  The graph functor `C → Map(Rel C)` is faithful because graphs of distinct maps
  are distinct relations (`relClass_graph_inj`). -/

section MapRel

variable [PreLogos 𝒞]

/-- **§2.217**: for a pre-logos `C`, `Rel(C)` is a tabular-unitary-distributive allegory.
    All three parents (`relTabularAllegory`, `relUnitaryAllegory`,
    `DisjointGluing.relDistributiveAllegory`) are built `{ relAllegory with … }`, so their shared
    `toAllegory` grandparent is the SAME `relAllegory` — the diamond merges cleanly. -/
instance (priority := 0) relTabularUnitaryDistributiveAllegory :
    TabularUnitaryDistributiveAllegory (RelObj 𝒞) :=
  { relTabularAllegory, relUnitaryAllegory, DisjointGluing.relDistributiveAllegory with }

/-- **§2.217**: `Map(Rel C)` is a pre-logos for a positive pre-logos `C` — immediate from
    `MapCat.mapPreLogos` applied to `relTabularUnitaryDistributiveAllegory`.  Stated explicitly so
    typeclass resolution finds it (the `MapObj (RelObj C)` instance head). -/
noncomputable instance relMapPreLogos :
    @PreLogos (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
  Freyd.Alg.mapPreLogos (A := RelObj 𝒞)

end MapRel

/-! ### §2.217  Faithful graph embedding `C ↪ Map(Rel C)`.

  The crux is `relClass_graph_inj`: graphs of distinct morphisms are distinct relations, so the
  object-and-graph assignment `f ↦ [graph f]` is injective on hom-sets.  This needs only
  `[RegularCategory C]` (it is pure §1.413 table algebra), NOT positivity. -/

section GraphEmbedding

variable [RegularCategory 𝒞]

/-- **§2.217 core**: `graph` is injective up to relational equality.  If `[graph f] = [graph g]`
    as morphisms of `Rel(C)` then `f = g`.  Proof: equality of classes gives `graph f ⊂ graph g`,
    i.e. a `RelHom` — a map `h : A ⟶ A` with `h ≫ (graph g).colA = (graph f).colA` and
    `h ≫ (graph g).colB = (graph f).colB`.  Since `(graph _).colA = id A` and `(graph _).colB = _`,
    the first equation forces `h = id A` and the second then reads `g = id ≫ g = h ≫ g = f`. -/
theorem relClass_graph_inj {a b : 𝒞} {f g : a ⟶ b}
    (h : relClass (graph f) = relClass (graph g)) : f = g := by
  -- [graph f] = [graph g] ⇒ graph f ≈ graph g (mutual RelLe); take the ⊂ direction.
  have hle : RelLe (graph f) (graph g) := (Quotient.exact h).1
  obtain ⟨w, hA, hB⟩ := hle
  -- w : A ⟶ A.  (graph _).colA = id A (defeq), (graph _).colB = f resp g (defeq).
  -- hA : w ≫ id a = id a  ⇒  w = id a.
  have hw : w = Cat.id a := by
    have hA' : w ≫ Cat.id a = Cat.id a := hA
    exact (Cat.comp_id w).symm.trans hA'
  -- hB : w ≫ g = f  ⇒  f = id a ≫ g = g.
  have hB' : w ≫ g = f := hB
  rw [hw] at hB'
  exact ((Cat.id_comp g).symm.trans hB').symm

/-- **§2.217**: the graph of `f` is a `Map` in `Rel(C)`, packaged as a `Map(Rel C)` morphism
    `⟨a⟩ ⟶ ⟨b⟩` (a `mapCat` hom = subtype `{ R // Map R }`).  This is the morphism part of the
    embedding `C → Map(Rel C)`. -/
noncomputable def embedRel {a b : 𝒞} (f : a ⟶ b) :
    @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩ :=
  ⟨relClass (graph f), relClass_graph_map f⟩

/-- **§2.217**: the graph embedding `C → Map(Rel C)` is FAITHFUL — distinct morphisms have
    distinct graph-maps.  Reduces (via `Subtype.ext_iff`) to `relClass_graph_inj`. -/
theorem embedRel_faithful {a b : 𝒞} {f g : a ⟶ b} (h : embedRel f = embedRel g) : f = g :=
  relClass_graph_inj (a := a) (b := b) (Subtype.ext_iff.mp h)

/-- **§2.148-dual (fullness)**: every `Map` in `Rel(C)` is the graph of a unique `C`-morphism.
    Given `R : BinRel C a b` whose class is a map (`Alg.Map (relClass R)`), there is `f : a ⟶ b`
    with `relClass R = relClass (graph f)` — i.e. `f` realises `R` via `embedRel f`.

    Proof: `map_relClass` lowers `Alg.Map (relClass R)` to `Map R` (entire+simple at the BinRel
    level).  `tabulated_is_map_iff_left_iso` (§1.564) turns that into `IsIso R.colA` — its left
    leg is a cover (entire) and monic (simple), and a regular category is balanced, so cover+mono
    ⟹ iso (`monic_cover_iso`).  With the inverse `i := R.colA⁻¹`, set `f := i ≫ R.colB`;
    `tabulated_left_iso_eq_graph` (§1.564) gives `R ≈ graph f` (mutual `⊂`), collapsed to a Lean
    equality by `Quotient.sound`.  (`R` and `BinRel.mk R.src R.colA R.colB R.isMonicPair` are
    defeq by η.) -/
theorem embedRel_full {a b : 𝒞} (R : BinRel 𝒞 a b)
    (M : Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨a⟩) (b := ⟨b⟩) (relClass R)) :
    ∃ f : a ⟶ b, relClass R = relClass (graph f) := by
  have hmapR : Map R := (map_relClass R).mp M
  -- left leg is an iso (cover ∧ monic, then balance)
  have hiso : IsIso R.colA :=
    (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp hmapR
  obtain ⟨i, hi₁, hi₂⟩ := hiso  -- i = R.colA⁻¹ : a ⟶ R.src
  refine ⟨i ≫ R.colB, ?_⟩
  obtain ⟨hle, hge⟩ :=
    tabulated_left_iso_eq_graph R.colA R.colB R.isMonicPair i hi₁ hi₂
  exact Quotient.sound ⟨relClass_mono hle, relClass_mono hge⟩

/-! ### The functor `embedRel : C → Map(Rel C)` and the category iso `C ≅ Map(Rel C)`.

  `embedRel` is identity-on-objects (`⟨a⟩ = RelObj.mk a`), functorial (`embedRel_id`,
  `embedRel_comp`), faithful (`embedRel_faithful`) and full (`embedRel_full` — every Map is a
  graph).  These four facts ARE the iso of categories `C ≅ Map(Rel C)` (§2.148 dual / §2.214). -/

/-- `embedRel` preserves identities: `embedRel (id a) = id ⟨a⟩` in `Map(Rel C)`.  Both sides have
    `val = relClass (graph (id a)) = relId a` (the `relCat` identity), and `Map`-witnesses are
    proof-irrelevant, so `Subtype.ext` closes it. -/
theorem embedRel_id (a : 𝒞) :
    embedRel (Cat.id a) = @Cat.id (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ :=
  Subtype.ext rfl

/-- `embedRel` preserves composition: `embedRel (f ≫ g) = embedRel f ≫ embedRel g`.  On `val`
    this is `relClass (graph (f ≫ g)) = qComp (relClass (graph f)) (relClass (graph g))`, the
    mutual-`⊂` graph-composition law (`graph_comp` / `comp_graph`) collapsed to a Lean equality
    by `Quotient.sound`. -/
theorem embedRel_comp {a b c : 𝒞} (f : a ⟶ b) (g : b ⟶ c) :
    embedRel (f ≫ g)
      = @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩ ⟨c⟩
          (embedRel f) (embedRel g) :=
  Subtype.ext (Quotient.sound ⟨graph_comp f g, comp_graph f g⟩)

/-- **§2.148 dual / §2.214 core — `C ≅ Map(Rel C)`.**  The graph embedding is an isomorphism of
    categories: identity-on-objects (`⟨·⟩`), functorial (`embedRel_id`/`embedRel_comp`), FAITHFUL
    (`embedRel_faithful`) and FULL (`embedRel_full`: every Map of `Rel C` is a unique graph).
    Packaged as the conjunction of the bijection-on-homs facts; downstream transport of structure
    (limits, coproducts) along this iso uses fullness to lift a `Map`-morphism back to a
    `C`-morphism. -/
theorem embedRel_cat_iso :
    (∀ {a b : 𝒞} {f g : a ⟶ b}, embedRel f = embedRel g → f = g) ∧
    (∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
        ∃ f : a ⟶ b, m = embedRel f) :=
  ⟨fun h => embedRel_faithful h,
   fun {a b} m => by
     -- `m.val : BinRelQuot a b` is a quotient class; pick a representative `R` with `[R] = m.val`.
     refine Quotient.inductionOn (motive := fun q => (hq : Freyd.Alg.Map (𝒜 := RelObj 𝒞) q) →
        ∃ f : a ⟶ b, (⟨q, hq⟩ : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩)
          = embedRel f) m.val ?_ m.property
     intro R hq
     obtain ⟨f, hf⟩ := embedRel_full (a := a) (b := b) R hq
     exact ⟨f, Subtype.ext hf⟩⟩

/-- **A full + faithful identity-on-objects functor reflects monos.**  If `embedRel f` is monic in
    `Map(Rel C)` then `f` is monic in `C`.  Given `g h : W ⟶ a` with `g ≫ f = h ≫ f`, lift the
    Map-arrows `embedRel g`, `embedRel h : ⟨W⟩ ⟶ ⟨a⟩` (already in the image of `embedRel`);
    functoriality (`embedRel_comp`) sends `g ≫ f = h ≫ f` to `embedRel g ≫ embedRel f =
    embedRel h ≫ embedRel f`, monicity of `embedRel f` gives `embedRel g = embedRel h`, and
    faithfulness (`embedRel_faithful`) returns `g = h`. -/
theorem embedRel_reflects_monic {a b : 𝒞} {f : a ⟶ b}
    (hm : @Monic (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩ (embedRel f)) :
    Monic f := by
  intro W g h hgh
  apply embedRel_faithful
  -- map both sides through `embedRel` (functorial), then cancel `embedRel f` (monic).
  refine hm (embedRel g) (embedRel h) ?_
  rw [← embedRel_comp, ← embedRel_comp, hgh]

end GraphEmbedding

/-! ### §2.217(1)  A positive pre-logos embeds faithfully in a POSITIVE pre-logos.

  `relMapPreLogos` above gives only a *pre-logos* `Map(Rel C)`; §2.217(1) wants the target
  to be *positive* as well.  The positive reflection is Freyd's matrix construction `Mat(-)`:
  `Map(Mat(Rel C))` is a positive pre-logos, and `C` embeds into it as 1×1 matrices of graphs.

  Assembly:
    1. `Rel(C)` is a `TabularDistributiveAllegory` and a `UnitaryDistributiveAllegory`
       (the two local §2.342 hypothesis classes of `MatrixAllegory`).  Both diamonds merge
       because every parent is built `{ relAllegory with … }`.
    2. Hence `Mat(Rel C)` is tabular + unitary + distributive + positive
       (`instTabularAllegoryMat`, `instUnitaryAllegoryMat`, `instDistributiveAllegoryMat`,
       `instPositiveAllegoryMat`), i.e. a `TabularUnitaryPositiveAllegory`.
    3. So `Map(Mat(Rel C))` is a POSITIVE pre-logos (`MapCat.mapPositivePreLogos`).
    4. `C ↪ Map(Mat(Rel C))`, `f ↦ embed1 (embedRel f)` (1×1 matrix of the graph of `f`),
       is faithful (peel the 1×1 matrix, then `relClass_graph_inj`). -/

section Positivize

open Freyd.DisjointGluing Freyd.Alg.Mat

variable [PreLogos 𝒞]

/-- **§2.217(1) step 1**: `Rel(C)` is a tabular *distributive* allegory — the §2.342 hypothesis
    class of the matrix construction.  Parents share the SAME `relAllegory` grandparent, so the
    diamond merges. -/
instance relTabularDistributiveAllegory :
    Freyd.Alg.Mat.TabularDistributiveAllegory (RelObj 𝒞) :=
  { relTabularAllegory, DisjointGluing.relDistributiveAllegory with }

/-- **§2.217(1) step 1**: `Rel(C)` is a unitary *distributive* allegory — the other §2.342
    matrix hypothesis class. -/
instance relUnitaryDistributiveAllegory :
    Freyd.Alg.Mat.UnitaryDistributiveAllegory (RelObj 𝒞) :=
  { relUnitaryAllegory, DisjointGluing.relDistributiveAllegory with }

/-- **§2.217(1) step 2**: `Mat(Rel C)` is a tabular-unitary-POSITIVE allegory.  Combines the four
    matrix instances (`instTabularAllegoryMat`, `instUnitaryAllegoryMat`,
    `instDistributiveAllegoryMat`, `instPositiveAllegoryMat`), all now resolvable from step 1. -/
noncomputable instance matRelTabularUnitaryPositiveAllegory :
    Freyd.Alg.TabularUnitaryPositiveAllegory (MatObj (RelObj 𝒞)) :=
  { (instTabularAllegoryMat : TabularAllegory (MatObj (RelObj 𝒞))),
    (instUnitaryAllegoryMat  : UnitaryAllegory  (MatObj (RelObj 𝒞))),
    (instPositiveAllegoryMat : PositiveAllegory (MatObj (RelObj 𝒞))) with }

/-- **§2.217(1) step 3**: `Map(Mat(Rel C))` is a POSITIVE pre-logos — the target object of the
    embedding.  Immediate from `MapCat.mapPositivePreLogos` over the
    `TabularUnitaryPositiveAllegory (MatObj (RelObj C))` of step 2.  Stated explicitly so
    typeclass resolution finds the `MapObj (MatObj (RelObj C))` instance head. -/
noncomputable instance s217PreLogos :
    @PositivePreLogos (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞))) :=
  Freyd.Alg.mapPositivePreLogos (A := MatObj (RelObj 𝒞))

end Positivize

/-! ### §2.217(1)  Faithful embedding `C ↪ Map(Mat(Rel C))`.

  `embed1 : 𝒜 → MatObj 𝒜` (§H) wraps a base morphism as a 1×1 matrix and is a faithful allegory
  homomorphism (preserves `≫`, `°`, `∩`, `id`).  We show it carries `Map`s to `Map`s, so the
  graph-map `embedRel f : ⟨a⟩ ⟶ ⟨b⟩` in `Map(Rel C)` lifts to a Map in `Mat(Rel C)`, giving the
  morphism part of `C → Map(Mat(Rel C))`.  Faithfulness peels the 1×1 matrix back to
  `embedRel`, then `embedRel_faithful`. -/

section MatEmbedding

open Freyd.Alg.Mat

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- `embed1` sends the identity to the matrix identity (1×1 case: `matId` of `unitObj a`). -/
theorem embed1_id {a : 𝒜} : embed1 (Cat.id a) = matId (unitObj a) := by
  funext i j
  have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero i
  have hj : j = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero j
  subst hi; subst hj
  simp only [embed1, matId, unitObj, ↓reduceDIte]

/-- `embed1 R`, retyped as a category morphism `unitObj a ⟶ unitObj b` (defeq to its `MatHom`
    type, but `⟶`-headed so the allegory operations `⊑`/`°`/`≫`/`dom` elaborate). -/
def embed1' {a b : 𝒜} (R : a ⟶ b) : (unitObj a) ⟶ (unitObj b) := embed1 R

/-- `embed1` reflects/preserves the allegory order (1×1 entrywise). -/
theorem embed1_le_iff {a b : 𝒜} {R S : a ⟶ b} :
    (embed1' R ⊑ embed1' S) ↔ (R ⊑ S) := by
  -- `X ⊑ Y` unfolds to `X ∩ Y = X`; `embed1` preserves `∩` and is injective, so the two
  -- equations `embed1 (R∩S) = embed1 R` and `R∩S = R` are interchangeable.
  show (Allegory.inter (embed1' R) (embed1' S) = embed1' R) ↔ (R ∩ S = R)
  rw [show Allegory.inter (embed1' R) (embed1' S) = embed1' (R ∩ S) from (embed1_inter R S).symm]
  exact ⟨fun h => embed1_injective h, fun h => congrArg embed1' h⟩

/-- `embed1` commutes with `dom` (`dom = id ∩ R ≫ R°`; all preserved by `embed1`). -/
theorem embed1_dom {a b : 𝒜} (R : a ⟶ b) : dom (embed1' R) = embed1' (dom R) := by
  show Allegory.inter (Cat.id (unitObj a)) (matComp (embed1 R) (matRecip (embed1 R)))
      = embed1 (Cat.id a ∩ R ≫ R°)
  -- Expand the RHS through `embed1`'s homomorphism laws to match the LHS (all `mat*` primitives).
  rw [embed1_inter, embed1_comp, embed1_recip, embed1_id]
  rfl

/-- **§2.217(1) step 4 (preservation)**: `embed1` carries a `Map` of `𝒜` to a `Map` of
    `Mat 𝒜`.  `Entire`: `dom (embed1 R) = embed1 (dom R) = embed1 id = matId`.
    `Simple`: `(embed1 R)° ≫ embed1 R = embed1 (R° ≫ R) ⊑ embed1 id = matId`. -/
theorem embed1_map {a b : 𝒜} {R : a ⟶ b} (hR : Freyd.Alg.Map R) :
    Freyd.Alg.Map (𝒜 := MatObj 𝒜) (embed1' R) := by
  obtain ⟨hEnt, hSim⟩ := hR
  refine ⟨?_, ?_⟩
  · -- Entire
    show dom (embed1' R) = Cat.id (unitObj a)
    rw [embed1_dom, show dom R = Cat.id a from hEnt]
    show embed1 (Cat.id a) = matId (unitObj a)
    rw [embed1_id]
  · -- Simple: `(embed1 R)° ≫ embed1 R = embed1 (R° ≫ R) ⊑ embed1 (id) = id`.
    have hkey : embed1' (R° ≫ R) ⊑ embed1' (Cat.id b) := embed1_le_iff.mpr hSim
    show ((embed1' R)° ≫ embed1' R) ⊑ Cat.id (unitObj b)
    have hlhs : ((embed1' R)° ≫ embed1' R) = embed1' (R° ≫ R) := by
      show matComp (matRecip (embed1 R)) (embed1 R) = embed1 (R° ≫ R)
      rw [embed1_comp, embed1_recip]
    have hrhs : Cat.id (unitObj b) = embed1' (Cat.id b) := by
      show matId (unitObj b) = embed1 (Cat.id b); rw [embed1_id]
    rw [hlhs, hrhs]; exact hkey

end MatEmbedding

section GraphMatEmbedding

open Freyd.Alg.Mat

variable [PreLogos 𝒞]

/-- **§2.217(1)**: the object part `C → Map(Mat(Rel C))`: `a ↦ unitObj ⟨a⟩` (the 1×1 matrix on
    the relation-object `⟨a⟩`). -/
def embed217Obj (a : 𝒞) : MapObj (MatObj (RelObj 𝒞)) := unitObj (⟨a⟩ : RelObj 𝒞)

/-- **§2.217(1)**: the morphism part `f ↦ embed1 (embedRel f)` — the 1×1 matrix whose single
    entry is the graph-map `[graph f]` of `Rel(C)`, packaged as a Map of `Mat(Rel C)`. -/
noncomputable def embed217 {a b : 𝒞} (f : a ⟶ b) :
    @Cat.Hom (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞)))
      (embed217Obj a) (embed217Obj b) :=
  ⟨embed1' (embedRel f).val, embed1_map (embedRel f).property⟩

/-- **§2.217(1)**: the embedding `C ↪ Map(Mat(Rel C))` is FAITHFUL.  Peel the 1×1 matrix
    (`embed1_injective`) to recover `embedRel f = embedRel g`, then `embedRel_faithful`. -/
theorem embed217_faithful {a b : 𝒞} {f g : a ⟶ b} (h : embed217 f = embed217 g) : f = g := by
  have hval : embed1' (embedRel f).val = embed1' (embedRel g).val := congrArg Subtype.val h
  exact embedRel_faithful (Subtype.ext (embed1_injective hval))

end GraphMatEmbedding

/-! ### §2.217(1)  Headline. -/

section S217

open Freyd.Alg.Mat

variable [PreLogos 𝒞]

/-- **§2.217(1)** (GENERAL — Freyd's headline): *every pre-logos `C` embeds faithfully in a
    positive pre-logos.*  Hypothesis is a BARE `[PreLogos 𝒞]` — `C` need NOT be positive.
    Take `D := Map(Mat(Rel C))`; it is a positive pre-logos (`s217PreLogos`) and `embed217` is a
    faithful functor `C ↪ D` (`embed217_faithful`).  Packaged as: there exist a positive-pre-logos
    structure on `D` and a per-hom injection of `C` into `D`.

    This is now fully general because `DisjointGluing.relDistributiveAllegory` holds over any
    `[PreLogos 𝒞]` (the §1.616/§2.212 `relUnion`-via-subobject-union refactor): `Rel(C)` is
    distributive without `C` having disjoint coproducts, and the TARGET's positivity is supplied
    entirely by `Mat`, not by `C`. -/
theorem s217_faithful_embed_into_positive :
    Nonempty (@PositivePreLogos (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞)))) ∧
    ∀ {a b : 𝒞} {f g : a ⟶ b}, embed217 f = embed217 g → f = g :=
  ⟨⟨s217PreLogos⟩, fun {_ _ _ _} h => embed217_faithful h⟩

end S217

/-! ### §2.217(2)  Every pre-logos embeds faithfully in a PRE-TOPOS.

  Freyd §2.217(2): a pre-logos `C` embeds faithfully in a pre-topos.  The §2.217(1) target
  `Map(Mat(Rel C))` is a positive pre-logos but need NOT be EFFECTIVE.  To make it effective we
  split the equivalence relations: the pre-topos target is

      D := Map(SplObj(Mat(Rel C)))                                                    (§2.169)

  `SplObj(𝒜)` splits every symmetric idempotent of `𝒜`, so over the tabular-unitary-positive
  allegory `𝒜 = Mat(Rel C)`:
    • `SplObj 𝒜` is again TABULAR/UNITARY/DISTRIBUTIVE/POSITIVE (`splObj_tabular_of_semiSimple`,
      `instUnitarySpl`, `instDistributiveSpl`, `instPositiveSpl`), hence `Map(SplObj 𝒜)` is a
      POSITIVE PRE-LOGOS (`mapPositivePreLogos`);
    • `SplObj 𝒜` is EFFECTIVE (`instEffectiveSpl`): every equivalence relation splits as a map.

  WHAT LANDS HERE (sorry-free):
    (i)  `s217_2_target_positivePreLogos`  — `D` is a positive pre-logos;
    (ii) `s217_2_effectiveAllegory`        — `SplObj(Mat(Rel C))` is an EFFECTIVE allegory;
    (iii)`s217_2_effectiveSplit_isCover`   — the allegory-side core: the effective splitting of
         an equivalence relation `R` of `SplObj(Mat(Rel C))` is a COVER of `D` (via
         `MapCat.mapEffectivenessSplit`), with `x≫x° = R`, `x°≫x = id`.

  THE DICTIONARY (now built, sorry-free, in `MapCat`, `[propext]` only).  `relOf E := E.colA°≫E.colB`
  is the underlying allegory endo of a category-level `E : BinRel (Map A) A A`, and (over a bare
  `[TabularAllegory A]`):
    • `MapCat.relOf_le_of_relLe` : `E ⊂ F` (Map(A))  ⟹  `relOf E ⊑ relOf F`  (allegory);
    • `MapCat.relOf_reciprocal`  : `relOf (E°) = (relOf E)°`;
    • `MapCat.relOf_graph`       : `relOf (graph x) = x.val`;
    • `MapCat.relOf_reflexive`   : `E`'s diagonal ⟹ `Reflexive (relOf E)`;
    • `MapCat.relOf_symmetric`   : `E ⊂ E°`        ⟹ `Symmetric (relOf E)`.
  (The instance-pinning accessors `MapCat.relColA`/`relColB`/`relColA_map`/`relColB_map` package the
  `mapCat`-explicit field projections that the `MapObj A := A` abbrev otherwise mis-synthesizes.)

  -- BOOK §2.217(2): the two RelLe bridges are now BOTH CLOSED in `MapCat` (the §2.14 `Rel(Map A) ≅ A`
  -- equivalence at the CATEGORY level), and the full assembly lands below.
  --   (C)  COMPOSITION  `relOf (R ⊚ S) = relOf R ≫ relOf S`  =  `MapCat.relOf_compose`.  `compose`
  --        (S1_56) is the pullback-then-IMAGE of a span; the pullback CROSS-term collapses by
  --        `MapCat.mapPullback_cross` (`π₁°≫π₂ = R.colB≫S.colA°`) and the image-cover `e` by
  --        `e°≫e = id` (cover-map), giving the equality OUTRIGHT (no cover⊥mono descent needed).
  --   (D)  REVERSE containment  `relOf E ⊑ relOf F ⟹ E ⊂ F`  =  `MapCat.relLe_of_relOf_le`, via
  --        `MapCat.relOf_tabulates`: EVERY `BinRel(Map A)` tabulates its `relOf` — the tabulation
  --        identity `colA≫colA° ∩ colB≫colB° = id` follows from the categorical joint-monicity
  --        (`isMonicPair`) by `MapCat.monicPair_tab_identity` (the §2.141 converse).  Then §2.143
  --        `tabulation_UP_forward` factors `E`'s columns through `F`'s = a `RelHom E F`.
  -- ASSEMBLY (below): `MapCat.relOf_idempotent` (C + transitivity + reflexivity) ⟹ idempotent
  -- `relOf E`; `MapCat.mapIsEffective_of_split` packages every equivalence relation as the level of a
  -- cover (`relOf E = x≫x° = relOf (graph x ⊚ graph x°)` via `relOf_graph`/`relOf_reciprocal`, both
  -- containments by (D)); `MapCat.mapEffectiveRegular` ⟹ `EffectiveRegular D`; hence `s217_2_preTopos`
  -- (`PreTopos D`) and `s217_2_faithful_embed_into_preTopos` (the §2.217(2) headline). -/

section S217_2

open Freyd.Alg.Mat

variable [PreLogos 𝒞]

/-- **§2.217(2) ingredient**: `SplObj(Mat(Rel C))` is a TABULAR-UNITARY-POSITIVE allegory.
    Bundles the splitting-completion instances over the tabular-unitary-positive `Mat(Rel C)`
    (`splObj_tabular_of_semiSimple` via `semiSimpleAllegory_of_tabular`, `instUnitarySpl`,
    `instPositiveSpl` — which also yields `instDistributiveSpl`). -/
noncomputable instance splMatRelTUP :
    Freyd.Alg.TabularUnitaryPositiveAllegory (SplObj (MatObj (RelObj 𝒞))) :=
  letI : SemiSimpleAllegory (MatObj (RelObj 𝒞)) :=
    Freyd.Alg.semiSimpleAllegory_of_tabular (ℬ := MatObj (RelObj 𝒞))
  { (Freyd.Alg.splObj_tabular_of_semiSimple : TabularAllegory (SplObj (MatObj (RelObj 𝒞)))),
    (Freyd.Alg.instUnitarySpl  : UnitaryAllegory  (SplObj (MatObj (RelObj 𝒞)))),
    (Freyd.Alg.instPositiveSpl : PositiveAllegory (SplObj (MatObj (RelObj 𝒞)))) with }

/-- **§2.217(2) ingredient (i)**: `D = Map(SplObj(Mat(Rel C)))` is a POSITIVE PRE-LOGOS.
    Immediate from `mapPositivePreLogos` over `splMatRelTUP`. -/
noncomputable instance s217_2_target_positivePreLogos :
    @PositivePreLogos (MapObj (SplObj (MatObj (RelObj 𝒞))))
      (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) :=
  Freyd.Alg.mapPositivePreLogos (A := SplObj (MatObj (RelObj 𝒞)))

/-- **§2.217(2) ingredient (ii)**: `SplObj(Mat(Rel C))` is an EFFECTIVE allegory — every
    equivalence relation splits as a map (`instEffectiveSpl`, since `Mat(Rel C)` is tabular
    hence semi-simple). -/
noncomputable def s217_2_effectiveAllegory :
    Freyd.Alg.EffectiveAllegory (SplObj (MatObj (RelObj 𝒞))) :=
  Freyd.Alg.splObj_effective_of_tabular (𝒜 := MatObj (RelObj 𝒞))

/-- **§2.217(2) ingredient (iii) — allegory-side effectiveness core**: in
    `D = Map(SplObj(Mat(Rel C)))`, the effective splitting of a reflexive symmetric idempotent
    `R` of `SplObj(Mat(Rel C))` (an allegory-level equivalence relation) IS a COVER of `D`,
    with `x≫x° = R` and `x°≫x = id`.  Combines `splObj_split_equivalence` (the split as a map)
    with `MapCat.mapEffectivenessSplit` (the split leg is a cover).  This is exactly the
    cover/quotient datum the category-level `IsEffective` needs; what remains is the BinRel↔
    allegory translation flagged in the `-- BOOK §2.217(2)` marker above. -/
theorem s217_2_effectiveSplit_isCover
    {a : SplObj (MatObj (RelObj 𝒞))} (R : a ⟶ a)
    (hrefl : Freyd.Alg.Reflexive R) (hsym : Freyd.Alg.Symmetric R) (hidem : R ≫ R = R) :
    ∃ (Q : SplObj (MatObj (RelObj 𝒞)))
      (x : @Cat.Hom (MapObj (SplObj (MatObj (RelObj 𝒞))))
            (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) a Q),
      x.val ≫ x.val° = R ∧ x.val° ≫ x.val = Cat.id Q ∧
      @Cover (MapObj (SplObj (MatObj (RelObj 𝒞))))
        (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) a Q x := by
  obtain ⟨Q, x, hxMap, hxx, hxxId⟩ :=
    Freyd.Alg.splObj_split_equivalence (𝒜 := MatObj (RelObj 𝒞)) R hrefl hsym hidem
  -- Bundle the bare allegory map `x` with its `Map` proof into a `Map(𝒜)`-morphism.
  refine ⟨Q, ⟨x, hxMap⟩, hxx, hxxId,
    Freyd.Alg.mapEffectivenessSplit (A := SplObj (MatObj (RelObj 𝒞))) ⟨x, hxMap⟩ hxxId⟩

/-- The splitting-completion embedding `embObj/embHom : 𝒜 ↪ SplObj 𝒜` preserves MAPS: from
    `Map R` follows `Map (embHom R)`.  `embHom` is an allegory functor (`embHom_id/comp/recip/
    inter`) and is injective, so it commutes with `dom` and reflects/preserves `⊑`:
    `dom (embHom R) = embHom (dom R) = embHom 1 = 1` (Entire), and similarly Simple. -/
theorem embHom_preserves_map {𝒜 : Type u} [Freyd.Alg.Allegory 𝒜] {a b : 𝒜} {R : a ⟶ b}
    (hR : Freyd.Alg.Map R) :
    Freyd.Alg.Map (a := Freyd.Alg.embObj a) (b := Freyd.Alg.embObj b) (Freyd.Alg.embHom R) := by
  obtain ⟨hEnt, hSim⟩ := hR
  let eR : Freyd.Alg.embObj a ⟶ Freyd.Alg.embObj b := Freyd.Alg.embHom R
  -- embHom commutes with `dom` (functoriality of `∩`, `≫`, `°`, `id`).
  have hdom : Freyd.Alg.dom eR = Freyd.Alg.embHom (Freyd.Alg.dom R) := by
    show Cat.id _ ∩ eR ≫ eR° = Freyd.Alg.embHom (Cat.id a ∩ R ≫ R°)
    rw [Freyd.Alg.embHom_inter, Freyd.Alg.embHom_id, Freyd.Alg.embHom_comp,
        Freyd.Alg.embHom_recip]
    rfl
  constructor
  · -- Entire: dom (embHom R) = embHom (dom R) = embHom 1 = 1.
    show Freyd.Alg.dom eR = Cat.id _
    rw [hdom, hEnt, Freyd.Alg.embHom_id]
  · -- Simple: eR°≫eR ⊑ 1.  R°≫R ⊑ 1 (`hSim`) ⟹ embHom monotone via dom-commuting:
    -- dom(eR°) = embHom(dom R°); R° simple-ish unused — use injectivity of `∩`-eqn instead.
    show eR° ≫ eR ∩ Cat.id _ = eR° ≫ eR
    have : Freyd.Alg.embHom (R° ≫ R ∩ Cat.id b) = Freyd.Alg.embHom (R° ≫ R) :=
      congrArg Freyd.Alg.embHom hSim
    rw [Freyd.Alg.embHom_inter, Freyd.Alg.embHom_comp, Freyd.Alg.embHom_recip,
        Freyd.Alg.embHom_id] at this
    exact this

/-- **§2.217(2) — the effectiveness field** of `D = Map(SplObj(Mat(Rel C)))`: every category-level
    equivalence relation is the level of a cover.  `MapCat.mapIsEffective_of_split` fed the splitting
    datum of the EFFECTIVE allegory `SplObj(Mat(Rel C))`
    (`s217_2_effectiveAllegory.split_symmetric_idempotent`) — closed by the bridges (C)/(D). -/
theorem s217_2_effective {a : MapObj (SplObj (MatObj (RelObj 𝒞)))}
    (E : @BinRel (MapObj (SplObj (MatObj (RelObj 𝒞))))
          (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) a a)
    (hE : @EquivalenceRelation (MapObj (SplObj (MatObj (RelObj 𝒞))))
            (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) _ _ _ a E) :
    @IsEffective (MapObj (SplObj (MatObj (RelObj 𝒞))))
      (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) a E _ _ _ :=
  Freyd.Alg.mapIsEffective_of_split (A := SplObj (MatObj (RelObj 𝒞)))
    (s217_2_effectiveAllegory (𝒞 := 𝒞)).split_symmetric_idempotent hE

/-- **§2.217(2) — `D = Map(SplObj(Mat(Rel C)))` is a PRE-TOPOS.**  The positive-pre-logos structure
    is `s217_2_target_positivePreLogos`; the `effective` field is `s217_2_effective`.  Supplying
    `toPositivePreLogos` (not a separate `EffectiveRegular`) keeps a SINGLE `mapRegularCategory`
    grandparent — the repo's standard diamond dodge for `PreTopos`. -/
noncomputable def s217_2_preTopos :
    @Freyd.PreTopos (MapObj (SplObj (MatObj (RelObj 𝒞))))
      (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) :=
  letI er : @Freyd.EffectiveRegular (MapObj (SplObj (MatObj (RelObj 𝒞))))
      (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) :=
    Freyd.Alg.mapEffectiveRegular (A := SplObj (MatObj (RelObj 𝒞)))
      (s217_2_effectiveAllegory (𝒞 := 𝒞)).split_symmetric_idempotent
  letI pl : @Freyd.PreLogos (MapObj (SplObj (MatObj (RelObj 𝒞))))
      (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) :=
    (s217_2_target_positivePreLogos (𝒞 := 𝒞)).toPreLogos
  @Freyd.PreTopos.mk (MapObj (SplObj (MatObj (RelObj 𝒞))))
    (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) er
    pl.toHasSubobjectUnions pl.bottom (fun {_A} S => pl.bottom_min S)
    pl.bottom_dom_iso (fun {_A _B} f => pl.invImage_preserves_union f)
    (fun {_A _B} f => pl.invImage_preserves_bottom f)
    (s217_2_target_positivePreLogos (𝒞 := 𝒞)).toHasBinaryCoproducts

/-! ### §2.217(2)  The faithful embedding `C ↪ D = Map(SplObj(Mat(Rel C)))` and the headline. -/

/-- **§2.217(2)**: object part `C → Map(SplObj(Mat(Rel C)))`, `a ↦ embObj (embed217Obj a)` — the
    §2.217(1) embedding `a ↦ unitObj ⟨a⟩` followed by the splitting-completion embedding. -/
def embed217_2Obj (a : 𝒞) : MapObj (SplObj (MatObj (RelObj 𝒞))) :=
  Freyd.Alg.embObj (embed217Obj a)

/-- **§2.217(2)**: morphism part `f ↦ embHom (embed217 f)` — `embed217 f` (a Map of `Mat(Rel C)`)
    pushed through the splitting-completion embedding, a Map of `SplObj(Mat(Rel C))` by
    `embHom_preserves_map`. -/
noncomputable def embed217_2 {a b : 𝒞} (f : a ⟶ b) :
    @Cat.Hom (MapObj (SplObj (MatObj (RelObj 𝒞))))
      (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) (embed217_2Obj a) (embed217_2Obj b) :=
  ⟨Freyd.Alg.embHom (embed217 f).val, embHom_preserves_map (embed217 f).property⟩

/-- **§2.217(2)**: the embedding `C ↪ D` is FAITHFUL.  Peel the splitting-completion embedding
    (`embHom_injective`) to recover `embed217 f = embed217 g`, then `embed217_faithful`. -/
theorem embed217_2_faithful {a b : 𝒞} {f g : a ⟶ b} (h : embed217_2 f = embed217_2 g) : f = g := by
  have hval : Freyd.Alg.embHom (embed217 f).val = Freyd.Alg.embHom (embed217 g).val :=
    congrArg Subtype.val h
  exact embed217_faithful (Subtype.ext (Freyd.Alg.embHom_injective hval))

/-- **§2.217(2)** (Freyd's headline): *every pre-logos `C` embeds faithfully in a PRE-TOPOS.*
    The target is `D := Map(SplObj(Mat(Rel C)))`, a pre-topos (`s217_2_preTopos`), and `embed217_2`
    is a faithful per-hom injection `C ↪ D` (`embed217_2_faithful`).  Bare `[PreLogos C]` — `C`
    need NOT be positive or effective; positivity is supplied by `Mat`, effectiveness by `SplObj`. -/
theorem s217_2_faithful_embed_into_preTopos :
    Nonempty (@Freyd.PreTopos (MapObj (SplObj (MatObj (RelObj 𝒞))))
                (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞))))) ∧
    ∀ {a b : 𝒞} {f g : a ⟶ b}, embed217_2 f = embed217_2 g → f = g :=
  ⟨⟨s217_2_preTopos⟩, fun {_ _ _ _} h => embed217_2_faithful h⟩

end S217_2

/-! ### §2.343  Every LOGOS embeds faithfully AND FULLY in a positive effective LOGOS.

  Freyd §2.343 upgrades §2.217(2) from *pre-logos ↪ pre-topos* to *logos ↪ positive effective
  logos*, AND makes the embedding FULL (not merely faithful).  The target is the SAME tower
  carrier

      D := Map(SplObj(Mat(Rel C)))                                                    (§2.169)

  but now over a `[Logos C]` (so `Rel(C)` is a DIVISION allegory, `relDivisionAllegory`).

  PART A (structure).  Over `[Logos C]`:
    • `RelObj C`               — DIVISION allegory (`relDivisionAllegory`, §1.784/§2.32 forward);
    • `MatObj (RelObj C)`      — DIVISION (`instDivisionAllegoryMat`, §2.342) + tabular + unitary;
    • `SplObj (MatObj (RelObj C))` — DIVISION (`instDivisionSpl`, §2.31) + tabular + unitary
      (`splMatRelTUP`), i.e. a `TabularUnitaryDivisionAllegory` (`splMatRelTUDiv` below);
    • hence `Map(SplObj(Mat(Rel C)))` is a `Logos` (`mapLogos`, §2.32 backward) — `s343_logos`;
    • it is also POSITIVE (`s217_2_target_positivePreLogos.toHasBinaryCoproducts`) and EFFECTIVE
      (`mapEffectiveRegular` over the `s217_2_effectiveAllegory` split) — `s343_effectiveRegular`.
    So `D` is a POSITIVE EFFECTIVE LOGOS (`s343_positive_effective_logos`).

  PART B (fullness).  The composite `embed217_2 : C → D` is FULL: every `D`-morphism
  `embed217_2Obj a ⟶ embed217_2Obj b` collapses through the 1×1 Spl/Mat structure to a
  `Map(Rel C)`-morphism `⟨a⟩ → ⟨b⟩`, which by `embedRel_full` is the graph of a unique
  `C`-morphism (`embed217_2_full`). -/

/-! #### §2.343 PART B helpers — the splitting/matrix embeddings are FULL and reflect `Map`.

  These two reflection lemmas are the layer-by-layer inverses of `embHom_preserves_map` /
  `embed1_map`.  Both `embHom : 𝒜 → SplObj 𝒜` and `embed1 : 𝒜 → MatObj 𝒜` are INJECTIVE allegory
  homomorphisms that commute with `dom` and `id` (so they REFLECT `Entire`/`Simple`, hence `Map`),
  and they are FULL onto the embedded objects (`embHom_full`; the 1×1 `Fin 1` collapse). -/

section EmbReflectMap

open Freyd.Alg Freyd.Alg.Mat

/-- `embHom : 𝒜 → SplObj 𝒜` REFLECTS `Map`: if the split-hom `embHom R` is a map (over the
    canonical `instAllegorySpl`) then `R` is a map in `𝒜`.  `embObj` carries the IDENTITY
    idempotent, so `Entire`/`Simple` of `embHom R` descend to `R` via `splLe_iff` and the
    `dom`/`id`-commutation of `embHom` (`embHom_inter`/`embHom_comp`/`embHom_recip`/`embHom_id`,
    plus `embHom_injective`). -/
theorem embHom_reflects_map {𝒜 : Type u} [Freyd.Alg.Allegory 𝒜] {a b : 𝒜} {R : a ⟶ b}
    (h : Freyd.Alg.Map (𝒜 := SplObj 𝒜) (a := Freyd.Alg.embObj a) (b := Freyd.Alg.embObj b)
          (Freyd.Alg.embHom R)) :
    Freyd.Alg.Map R := by
  obtain ⟨hEnt, hSim⟩ := h
  let eR : embObj a ⟶ embObj b := embHom R
  -- embHom commutes with `dom` (functoriality of `∩`, `≫`, `°`, `id`) — same as `embHom_preserves_map`.
  have hdom : dom eR = embHom (dom R) := by
    show Cat.id _ ∩ eR ≫ eR° = embHom (Cat.id a ∩ R ≫ R°)
    rw [embHom_inter, embHom_id, embHom_comp, embHom_recip]; rfl
  constructor
  · -- Entire: `dom (embHom R) = id` is `embHom (dom R) = embHom (id a)`; injective.
    show dom R = Cat.id a
    have : embHom (dom R) = embHom (Cat.id a) := by
      rw [← hdom, embHom_id]; exact hEnt
    exact embHom_injective this
  · -- Simple: `(embHom R)° ≫ embHom R ⊑ id_{embObj b}` descends via `splLe_iff`.
    show R° ≫ R ⊑ Cat.id b
    have hle : eR° ≫ eR ⊑ Cat.id (embObj b) := hSim
    -- `eR° ≫ eR` and `embHom (R° ≫ R)` agree on `.R` (`= R° ≫ R`), so are equal (`SplHom.ext`).
    have heq : eR° ≫ eR = embHom (R° ≫ R) := SplHom.ext rfl
    rw [heq, ← embHom_id] at hle
    exact (splLe_iff _ _).mp hle

/-- The 1×1 matrix `embed1 r : unitObj a ⟶ unitObj b` reflects `Map`: if `embed1 r` is a map of
    `Mat 𝒜` then `r` is a map of `𝒜`.  `embed1` is an injective allegory hom commuting with `dom`
    (`embed1_dom`) and `id` (`embed1_id`) and reflects order (`embed1_le_iff`). -/
theorem embed1_reflects_map {𝒜 : Type u} [Freyd.Alg.DistributiveAllegory 𝒜] {a b : 𝒜}
    {r : a ⟶ b}
    (h : Freyd.Alg.Map (𝒜 := MatObj 𝒜) (a := unitObj a) (b := unitObj b) (embed1' r)) :
    Freyd.Alg.Map r := by
  obtain ⟨hEnt, hSim⟩ := h
  constructor
  · -- Entire: `dom (embed1 r) = id` is `embed1 (dom r) = embed1 (id a)`; injective.
    show dom r = Cat.id a
    have hent' : dom (embed1' r) = Cat.id (unitObj a) := hEnt
    have hdom : dom (embed1' r) = embed1' (dom r) := embed1_dom r
    have hid : Cat.id (unitObj a) = embed1' (Cat.id a) := by
      show matId (unitObj a) = embed1 (Cat.id a); rw [embed1_id]
    rw [hdom, hid] at hent'
    exact embed1_injective hent'
  · -- Simple: `(embed1 r)° ≫ embed1 r ⊑ id` descends via `embed1_le_iff`.
    show r° ≫ r ⊑ Cat.id b
    have hsim' : (embed1' r)° ≫ embed1' r ⊑ Cat.id (unitObj b) := hSim
    have heq : (embed1' r)° ≫ embed1' r = embed1' (r° ≫ r) := by
      show matComp (matRecip (embed1 r)) (embed1 r) = embed1 (r° ≫ r)
      rw [embed1_comp, embed1_recip]
    have hid : Cat.id (unitObj b) = embed1' (Cat.id b) := by
      show matId (unitObj b) = embed1 (Cat.id b); rw [embed1_id]
    rw [heq, hid] at hsim'
    exact embed1_le_iff.mp hsim'

end EmbReflectMap

section S343

open Freyd.Alg.Mat

variable [Logos 𝒞]

-- A logos is a pre-logos (§1.711); needed for the §2.217(2) pieces (`s217_2_effectiveAllegory`,
-- `s217_2_target_positivePreLogos`) which are stated over `[PreLogos 𝒞]`.
attribute [local instance] logos_implies_preLogos

/-! #### PART A — `D = Map(SplObj(Mat(Rel C)))` is a positive effective LOGOS. -/

/-- **§2.343 PART A — division up the tower**: `SplObj(Mat(Rel C))` is a
    `TabularUnitaryDivisionAllegory`.  Over `[Logos C]`, `RelObj C` is a division allegory
    (`relDivisionAllegory`), so `Mat(Rel C)` is (`instDivisionAllegoryMat`), so `SplObj` of it
    is (`instDivisionSpl`); tabular+unitary are the same legs that build `splMatRelTUP`.  All
    parents share the ONE `Allegory (SplObj (Mat (Rel C)))` — the diamond merges. -/
noncomputable instance splMatRelTUDiv :
    TabularUnitaryDivisionAllegory (SplObj (MatObj (RelObj 𝒞))) :=
  letI : SemiSimpleAllegory (MatObj (RelObj 𝒞)) :=
    Freyd.Alg.semiSimpleAllegory_of_tabular (ℬ := MatObj (RelObj 𝒞))
  { (Freyd.Alg.splObj_tabular_of_semiSimple : TabularAllegory (SplObj (MatObj (RelObj 𝒞)))),
    (Freyd.Alg.instUnitarySpl  : UnitaryAllegory  (SplObj (MatObj (RelObj 𝒞)))),
    (Freyd.Alg.instDivisionSpl : DivisionAllegory (SplObj (MatObj (RelObj 𝒞)))) with }

/-- **§2.343 PART A (i)**: `D = Map(SplObj(Mat(Rel C)))` is a `Logos` (§2.32 backward).  Immediate
    from `mapLogos` over `splMatRelTUDiv`.  This is the one structure beyond the §2.217(2)
    pre-topos: the right adjoint `f##` to inverse-image, which needs the DIVISION allegory. -/
noncomputable def s343_logos :=
  Freyd.Alg.mapLogos (A := SplObj (MatObj (RelObj 𝒞)))

/-- **§2.343 PART A (ii)**: `D` is EFFECTIVE-regular — `mapEffectiveRegular` over the effective
    splitting of the EFFECTIVE allegory `SplObj(Mat(Rel C))` (`s217_2_effectiveAllegory`). -/
noncomputable def s343_effectiveRegular :=
  Freyd.Alg.mapEffectiveRegular (A := SplObj (MatObj (RelObj 𝒞)))
    (s217_2_effectiveAllegory (𝒞 := 𝒞)).split_symmetric_idempotent

/-- **§2.343 PART A — packaged**: `D = Map(SplObj(Mat(Rel C)))` is a POSITIVE EFFECTIVE LOGOS:
    a `Logos` (`s343_logos`), with finite coproducts (positive,
    `s217_2_target_positivePreLogos.toHasBinaryCoproducts`) and effective quotients
    (`s343_effectiveRegular`).  Bundled as the conjunction of the three structures, all over the
    single `mapCat` of `D`. -/
noncomputable def s343_positive_effective_logos :
    @Logos (MapObj (SplObj (MatObj (RelObj 𝒞))))
        (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) ×
    @HasBinaryCoproducts (MapObj (SplObj (MatObj (RelObj 𝒞))))
        (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) ×'
    @Freyd.EffectiveRegular (MapObj (SplObj (MatObj (RelObj 𝒞))))
        (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) :=
  ⟨s343_logos,
   (s217_2_target_positivePreLogos (𝒞 := 𝒞)).toHasBinaryCoproducts,
   s343_effectiveRegular⟩

/-! #### PART B — the embedding `C ↪ D = Map(SplObj(Mat(Rel C)))` is FULL. -/

/-- **§2.343 PART B (fullness)**: every `D`-morphism `embed217_2Obj a ⟶ embed217_2Obj b` is
    `embed217_2 f` for a unique `f : a ⟶ b`.  The collapse runs DOWN the tower:

      `D`-hom `m`                       — a `Map(SplObj(Mat(Rel C)))`-morphism `embObj⟨a⟩₁ → embObj⟨b⟩₁`
        ⟶ `m.val = embHom m.val.R`       (`embHom_full`; `embObj` has the identity idempotent)
        ⟶ `Map m.val.R`                  (`embHom_reflects_map`)            [Spl layer peeled]
        ⟶ `m.val.R = embed1' r`          (`Fin 1` collapse, `r` = the single entry)
        ⟶ `Map r`                        (`embed1_reflects_map`)            [Mat layer peeled]
        ⟶ `r = relClass (graph f)`       (`embedRel_full`, §2.148 dual)     [Rel layer = a graph]

    and BACK UP: `embed217_2 f` rebuilds `embHom (embed1' (relClass (graph f))) = embHom (embed1' r)
    = embHom m.val.R = m.val`, so `m = embed217_2 f` (`Subtype.ext`). -/
theorem embed217_2_full {a b : 𝒞}
    (m : @Cat.Hom (MapObj (SplObj (MatObj (RelObj 𝒞))))
          (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) (embed217_2Obj a) (embed217_2Obj b)) :
    ∃ f : a ⟶ b, m = embed217_2 f := by
  -- (1) Spl layer: `m.val = embHom m.val.R`, and `Map m.val.R` in `Mat(Rel C)`.
  have hsplmap : Freyd.Alg.Map (𝒜 := SplObj (MatObj (RelObj 𝒞)))
      (a := Freyd.Alg.embObj (embed217Obj a)) (b := Freyd.Alg.embObj (embed217Obj b))
      (Freyd.Alg.embHom m.val.R) := by
    rw [Freyd.Alg.embHom_full]; exact m.property
  have hmatmap : Freyd.Alg.Map (𝒜 := MatObj (RelObj 𝒞)) m.val.R := embHom_reflects_map hsplmap
  -- (2) Mat layer: 1×1 collapse `m.val.R = embed1' r` for the single entry `r`.
  let r : (⟨a⟩ : RelObj 𝒞) ⟶ (⟨b⟩ : RelObj 𝒞) :=
    m.val.R ⟨0, Nat.zero_lt_one⟩ ⟨0, Nat.zero_lt_one⟩
  have hcollapse : m.val.R = embed1' (𝒜 := RelObj 𝒞) r := by
    funext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; rfl
  have hrelmap : Freyd.Alg.Map (𝒜 := RelObj 𝒞) r :=
    embed1_reflects_map (by rw [← hcollapse]; exact hmatmap)
  -- (3) Rel layer: `r` is a Map of `Rel C`, hence (representative `R₀`) the graph of some `f`.
  obtain ⟨f, hf⟩ := Quotient.inductionOn (motive := fun q =>
      Freyd.Alg.Map (𝒜 := RelObj 𝒞) q → ∃ f : a ⟶ b, q = relClass (graph f))
    r (fun R₀ hR₀ => embedRel_full (a := a) (b := b) R₀ hR₀) hrelmap
  -- (4) Back up the tower: `m.val.R = embed1' r = embed1' (relClass (graph f)) = (embed217_2 f).val.R`.
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply Freyd.Alg.SplHom.ext
  -- `(embed217_2 f).val.R = (embHom (embed217 f).val).R = (embed217 f).val = embed1' (embedRel f).val`.
  show m.val.R = (Freyd.Alg.embHom (embed217 f).val).R
  rw [Freyd.Alg.embHom_R]
  -- `(embed217 f).val = embed1' (embedRel f).val` and `(embedRel f).val = relClass (graph f) = r`.
  show m.val.R = embed1' (𝒜 := RelObj 𝒞) (embedRel f).val
  show m.val.R = embed1' (𝒜 := RelObj 𝒞) (relClass (graph f))
  rw [hcollapse, hf]

/-- **§2.343** (Freyd's headline): *every LOGOS `C` embeds faithfully AND FULLY in a POSITIVE
    EFFECTIVE LOGOS.*  The target is `D := Map(SplObj(Mat(Rel C)))`, a positive effective logos
    (`s343_positive_effective_logos`), and `embed217_2 : C → D` is a per-hom BIJECTION:
    FAITHFUL (`embed217_2_faithful`) and FULL (`embed217_2_full`).  Bundled as: there is a positive
    effective logos structure on `D` together with a full+faithful embedding. -/
theorem s343_full_faithful_embed_into_positive_effective_logos :
    (Nonempty (@Logos (MapObj (SplObj (MatObj (RelObj 𝒞))))
                (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))))) ∧
    (Nonempty (@HasBinaryCoproducts (MapObj (SplObj (MatObj (RelObj 𝒞))))
                (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))))) ∧
    (Nonempty (@Freyd.EffectiveRegular (MapObj (SplObj (MatObj (RelObj 𝒞))))
                (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))))) ∧
    -- faithful
    (∀ {a b : 𝒞} {f g : a ⟶ b}, embed217_2 f = embed217_2 g → f = g) ∧
    -- full
    (∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (SplObj (MatObj (RelObj 𝒞))))
          (mapCat (𝒜 := SplObj (MatObj (RelObj 𝒞)))) (embed217_2Obj a) (embed217_2Obj b)),
        ∃ f : a ⟶ b, m = embed217_2 f) :=
  ⟨⟨s343_logos⟩,
   ⟨(s217_2_target_positivePreLogos (𝒞 := 𝒞)).toHasBinaryCoproducts⟩,
   ⟨s343_effectiveRegular⟩,
   fun {_ _ _ _} h => embed217_2_faithful h,
   fun {_ _} m => embed217_2_full m⟩

end S343

/-! ### §2.214 REVERSE — `Rel(C)` has finite coproducts ⟹ `C` is positive.

  Freyd §2.214: a pre-logos `C` is positive **iff** `Rel(C)` has finite coproducts.  The forward
  direction (`positive ⟹ coproducts`) is `DisjointGluing.relCoproduct` above.  This is the REVERSE.

  THE DIAMOND DODGE (marker option (b)).  We do NOT take an opaque `[PositiveAllegory (RelObj C)]`
  hypothesis: that instance would carry its OWN `Allegory (RelObj C)`/`Cat (RelObj C)` not defeq to
  `relAllegory`, so it could not be merged with `relTabularUnitaryDistributiveAllegory` to feed the
  `Map`-coproduct machinery.  Instead we hypothesize the positive part as raw coproduct DATA over the
  EXISTING `relAllegory`: a coterminal `zero`, a binary `coprodObj`, and a §2.2 `Coproduct` record
  for each pair.  Assembling `{ relTabularUnitaryDistributiveAllegory with … }` keeps the single
  `relAllegory` grandparent, so `MapCat.mapHasBinaryCoproducts` fires with no diamond.

  TRANSPORT across `C ≅ Map(Rel C)` (`embedRel_cat_iso`, identity-on-objects).  The Map(Rel C)
  coproduct of `⟨a⟩,⟨b⟩` lives over a `RelObj C` whose `carrier` IS the C-coproduct object; the
  injections / copairing are Maps of `Rel C`, pulled back to unique `C`-morphisms by fullness
  (`embedRel_full`), with the universal property transferred by faithfulness + `embedRel_comp/_id`.

  What lands here SORRY-FREE: `relReverseHasBinaryCoproducts` (full `HasBinaryCoproducts C`) and
  `relReverse_inl_monic`/`relReverse_inr_monic` (injections monic in `C`).  The remaining content of
  the FULL `DisjointBinaryCoproduct C` is the two §1.621 disjointness inequalities `inl∩inr ≤ 0` and
  `entire ≤ inl∪inr`, which live in the PRE-LOGOS subobject structure (intersection / union / bottom)
  and would need `embedRel` to PRESERVE/REFLECT that structure — see the sharpened marker in S2_21. -/

section ReverseCoproduct

-- A BARE pre-logos suffices for the REVERSE direction: we CONSTRUCT `C`'s (disjoint) coproducts
-- from the supplied `Rel(C)`-coproduct DATA (`hcop`), so no ambient positivity is assumed.  This
-- matches Freyd §2.214 ("`C` positive ⟺ `Rel(C)` has finite coproducts"): the ⟸ direction holds
-- over any pre-logos.  Everything below uses only `[PreLogos]` (the relaxed `relUnion`,
-- `relTUPositiveAllegory`, `relMapPreLogos`, and the `PreLogos.bottom` coterminator).
variable [PreLogos 𝒞]

/-- Assemble a `TabularUnitaryPositiveAllegory (RelObj C)` from the existing tabular/unitary/
    distributive structure on `relAllegory` plus supplied positive coproduct DATA.  Because
    `relTabularUnitaryDistributiveAllegory` is itself `{ relAllegory with … }`, the resulting
    `toAllegory` grandparent is `relAllegory` — no competing `Allegory (RelObj C)` instance, so the
    `Map`-coproduct lemmas of `MapCat` apply directly.  This is the marker's option (b). -/
def relTUPositiveAllegory (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    Freyd.Alg.TabularUnitaryPositiveAllegory (RelObj 𝒞) :=
  { relTabularUnitaryDistributiveAllegory with
    coterm := zero, coprod := coprodObj, has_coproduct := hcop }

/-- **§2.214 REVERSE (coproduct object + UMP).**  Given finite coproducts of `Rel(C)` (as positive
    coproduct data over `relAllegory`), `C` has binary coproducts.

    Construction.  The assembled `TabularUnitaryPositiveAllegory (RelObj C)` makes
    `Map(Rel C) = MapObj (RelObj C)` a category with binary coproducts (`mapHasBinaryCoproducts`),
    call it `H`.  Since `embedRel` is identity-on-objects, `H.coprod ⟨a⟩ ⟨b⟩ : RelObj C` is `⟨q⟩`
    with `q := (H.coprod ⟨a⟩ ⟨b⟩).carrier` the C-coproduct.  By fullness (`embedRel_cat_iso.2`)
    each Map-injection `H.inl`/`H.inr` and each copairing `H.case (embedRel f) (embedRel g)` is the
    graph of a UNIQUE C-morphism; faithfulness + `embedRel_comp`/`embedRel_id` transport the
    case-equations and uniqueness back to `C`. -/
noncomputable def relReverseHasBinaryCoproducts (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    HasBinaryCoproducts 𝒞 := by
  letI tup := relTUPositiveAllegory zero coprodObj hcop
  letI H : @HasBinaryCoproducts (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    Freyd.Alg.mapHasBinaryCoproducts (A := RelObj 𝒞)
  -- Faithfulness, and the fullness lift: every Map(Rel C) morphism between `⟨·⟩` objects is the
  -- graph of a UNIQUE C-morphism.  `lift m` is that C-morphism; `lift_spec` is `embedRel (lift m) = m`.
  have hfaithful : ∀ {a b : 𝒞} {f g : a ⟶ b}, embedRel f = embedRel g → f = g :=
    fun {a b f g} h => (embedRel_cat_iso (𝒞 := 𝒞)).1 h
  let lift : ∀ {a b : 𝒞}, (@Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩) → (a ⟶ b) :=
    fun {a b} m => ((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose
  have lift_spec : ∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
      embedRel (lift m) = m :=
    fun {a b} m => (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose_spec).symm
  refine
    { coprod := fun a b => (H.coprod ⟨a⟩ ⟨b⟩).carrier
      inl := fun {a b} => lift (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inl
      inr := fun {a b} => lift (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inr
      case := fun {x a b} f g =>
        lift (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g))
      case_inl := ?_
      case_inr := ?_
      case_uniq := ?_ }
  all_goals intro x a b f g
  · -- inl ≫ case f g = f
    apply hfaithful
    rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inl,
        lift_spec (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g)), H.case_inl]
  · -- inr ≫ case f g = g
    apply hfaithful
    rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inr,
        lift_spec (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g)), H.case_inr]
  · -- uniqueness
    intro h hl hr
    -- Push each C-hypothesis through `embedRel` (functorial) to Map(Rel C), using `embedRel_comp`
    -- forward (so the Map-composition instance is exactly `mapCat`, matching `H.case_uniq`).
    have hl' : @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _
        H.inl (embedRel h) = embedRel f := by
      have := congrArg embedRel hl
      rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inl] at this
      exact this
    have hr' : @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _
        H.inr (embedRel h) = embedRel g := by
      have := congrArg embedRel hr
      rw [embedRel_comp, lift_spec (b := (H.coprod ⟨a⟩ ⟨b⟩).carrier) H.inr] at this
      exact this
    have huniq : embedRel h = H.case (embedRel f) (embedRel g) := H.case_uniq _ _ _ hl' hr'
    -- Goal: `case f g = h`, i.e. `lift (H.case …) = h`.  Apply faithfulness then collapse.
    apply hfaithful
    rw [lift_spec (a := (H.coprod ⟨a⟩ ⟨b⟩).carrier) (H.case (embedRel f) (embedRel g)), huniq]

/-- **§2.214 REVERSE (left injection monic).**  Under the coproduct structure of
    `relReverseHasBinaryCoproducts`, the left injection `inl : a ⟶ a+b` is monic in `C`.  Its
    `embedRel`-image is `Map(Rel C)`'s `inl`, which is monic there (`DisjointBinaryCoproduct`),
    and `embedRel_reflects_monic` pulls monicity back to `C`. -/
theorem relReverse_inl_monic (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    @Monic 𝒞 _ a _
      (@HasBinaryCoproducts.inl 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b) := by
  letI tup := relTUPositiveAllegory zero coprodObj hcop
  letI H : @HasBinaryCoproducts (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    Freyd.Alg.mapHasBinaryCoproducts (A := RelObj 𝒞)
  -- `inl` of the C-structure is `lift H.inl`; its `embedRel`-image is `H.inl`, monic in Map(Rel C).
  apply embedRel_reflects_monic
  -- typed `have` so the leading `{a b}` implicits are not eagerly synthesized.
  have lift_spec : ∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
      embedRel (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose) = m :=
    fun {a b} m => (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose_spec).symm
  have hsp : embedRel (@HasBinaryCoproducts.inl 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b)
      = @HasBinaryCoproducts.inl (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩ :=
    lift_spec (@HasBinaryCoproducts.inl (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩)
  rw [hsp]
  exact @DisjointBinaryCoproduct.inl_monic (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    Freyd.Alg.mapDisjointBinaryCoproduct ⟨a⟩ ⟨b⟩

/-- **§2.214 REVERSE (right injection monic).**  Dual of `relReverse_inl_monic`. -/
theorem relReverse_inr_monic (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    @Monic 𝒞 _ b _
      (@HasBinaryCoproducts.inr 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b) := by
  letI tup := relTUPositiveAllegory zero coprodObj hcop
  letI H : @HasBinaryCoproducts (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    Freyd.Alg.mapHasBinaryCoproducts (A := RelObj 𝒞)
  apply embedRel_reflects_monic
  have lift_spec : ∀ {a b : 𝒞} (m : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩ ⟨b⟩),
      embedRel (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose) = m :=
    fun {a b} m => (((embedRel_cat_iso (𝒞 := 𝒞)).2 m).choose_spec).symm
  have hsp : embedRel (@HasBinaryCoproducts.inr 𝒞 _ (relReverseHasBinaryCoproducts zero coprodObj hcop) a b)
      = @HasBinaryCoproducts.inr (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩ :=
    lift_spec (@HasBinaryCoproducts.inr (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) H ⟨a⟩ ⟨b⟩)
  rw [hsp]
  exact @DisjointBinaryCoproduct.inr_monic (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    Freyd.Alg.mapDisjointBinaryCoproduct ⟨a⟩ ⟨b⟩

/-- **§2.214 REVERSE — union inequality `entire ≤ inl ∪ inr` (PURELY in C).**  The union
    `inlSub ∪ inrSub` is the image of `case inl inr` (`union_is_image`); by the coproduct UMP
    `case inl inr = id` (uniqueness against the identity), so the union is the image of the identity,
    which the entire subobject allows.  No transport across `embedRel` is needed for this half. -/
theorem relReverse_inl_union_inr (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    letI _H := relReverseHasBinaryCoproducts zero coprodObj hcop
    Subobject.le
      (Subobject.entire (HasBinaryCoproducts.coprod a b))
      (HasSubobjectUnions.union
        (inlSub (𝒞 := 𝒞) (A := a) (B := b)
          (relReverse_inl_monic zero coprodObj hcop))
        (inrSub (𝒞 := 𝒞) (A := a) (B := b)
          (relReverse_inr_monic zero coprodObj hcop))) := by
  letI H := relReverseHasBinaryCoproducts zero coprodObj hcop
  let Il := inlSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inl_monic zero coprodObj hcop)
  let Ir := inrSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inr_monic zero coprodObj hcop)
  -- `case Il.arr Ir.arr = case inl inr = id` by the coproduct uniqueness UMP.
  have hcase : HasBinaryCoproducts.case Il.arr Ir.arr
      = Cat.id (HasBinaryCoproducts.coprod a b) :=
    (HasBinaryCoproducts.case_uniq Il.arr Ir.arr (Cat.id _)
      (Cat.comp_id _) (Cat.comp_id _)).symm
  -- The union is an image of `case Il.arr Ir.arr`, hence allows it; rewriting by `hcase`
  -- it allows the identity, which is exactly `entire ≤ union`.
  obtain ⟨l, hl⟩ := (union_is_image Il Ir).1
  exact ⟨l, by rw [hl, hcase]; rfl⟩

-- `le_bottom_of_map_to_bottom` is now the canonical `Freyd.le_bottom_of_map_to_bottom` in `S1_62`
-- (DRY — this file's private copy was byte-identical and is now reused from the import).

/-- **§2.214 REVERSE — disjointness inequality `inl ∩ inr ≤ 0` (TRANSPORTED through `embedRel`).**
    The intersection's domain `P` is the C-pullback of `(inl, inr)`.  Pushing the pullback square
    through `embedRel` (functorial, sending `inl ↦ inl_Map`, `inr ↦ inr_Map`) makes `⟨P⟩` a cone over
    `Map(Rel C)`'s `(inl_Map, inr_Map)`; `Map`'s own disjointness (`coprod_inl_inr_disjoint_elt` via
    `mapDisjointBinaryCoproduct`) provides a `Map`-map `⟨P⟩ → bottom_Map.dom`, so `⟨P⟩` is initial in
    `Map(Rel C)` (`dom_initial_of_map_to_bottom`).  Routed through the `Map`-coterminator and lifted
    back by fullness, that yields a C-map `P → (⊥ _).dom`; `le_bottom_of_map_to_bottom` closes it. -/
theorem relReverse_inl_inter_inr (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) {a b : 𝒞} :
    letI _H := relReverseHasBinaryCoproducts zero coprodObj hcop
    Subobject.le
      (Subobject.inter
        (inlSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inl_monic zero coprodObj hcop))
        (inrSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inr_monic zero coprodObj hcop)))
      (PreLogos.bottom (HasBinaryCoproducts.coprod a b)) := by
  letI H := relReverseHasBinaryCoproducts zero coprodObj hcop
  let Il := inlSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inl_monic zero coprodObj hcop)
  let Ir := inrSub (𝒞 := 𝒞) (A := a) (B := b) (relReverse_inr_monic zero coprodObj hcop)
  -- the C-pullback defining the intersection.
  let pb := HasPullbacks.has Il.arr Ir.arr
  -- `Map(Rel C)`'s DisjointBinaryCoproduct instance.  The positive-allegory witness `tup` is passed
  -- EXPLICITLY (not as a `letI` instance) so it does NOT shadow the global `Allegory (RelObj C)`
  -- (`relAllegory`): `mapCat`/`relMapPreLogos` then resolve along the SAME global chain, and
  -- `DM.toPreLogos` is defeq `relMapPreLogos`, dissolving the diamond the marker warned about.
  let DM : @DisjointBinaryCoproduct (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) :=
    @Freyd.Alg.mapDisjointBinaryCoproduct (RelObj 𝒞) (relTUPositiveAllegory zero coprodObj hcop)
  -- `Map(Rel C)`'s injections, projected from `DM`'s coproduct.
  let il := @HasBinaryCoproducts.inl (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    DM.toPositivePreLogos.toHasBinaryCoproducts ⟨a⟩ ⟨b⟩
  let ir := @HasBinaryCoproducts.inr (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
    DM.toPositivePreLogos.toHasBinaryCoproducts ⟨a⟩ ⟨b⟩
  -- `embedRel`-images of the two injections are `Map(Rel C)`'s injections.
  have hinl : embedRel (Il.arr) = il :=
    (((embedRel_cat_iso (𝒞 := 𝒞)).2 il).choose_spec).symm
  have hinr : embedRel (Ir.arr) = ir :=
    (((embedRel_cat_iso (𝒞 := 𝒞)).2 ir).choose_spec).symm
  -- the pullback square in C, pushed through `embedRel` to a cone over `(inl_Map, inr_Map)`.
  have hsq : @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _ (embedRel pb.cone.π₁) il
      = @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _ (embedRel pb.cone.π₂) ir := by
    rw [← hinl, ← hinr, ← embedRel_comp, ← embedRel_comp]
    exact congrArg embedRel pb.cone.w
  -- `Map`'s disjointness: `⟨P⟩` admits a map into `Map`'s bottom domain (over `DM.toPreLogos`).
  obtain ⟨e, _he⟩ := @coprod_inl_inr_disjoint_elt (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) DM
    ⟨a⟩ ⟨b⟩ ⟨pb.cone.pt⟩ (embedRel pb.cone.π₁) (embedRel pb.cone.π₂) hsq
  -- `⟨P⟩` is initial in `Map(Rel C)`; route through the coterminator on `DM`'s own PreLogos
  -- (= `relMapPreLogos` definitionally, avoids the Cat-instance diamond) and lift back to C.
  let PLM := DM.toPositivePreLogos.toPreLogos
  letI ct := @minimal_subobject_of_one_is_coterminator (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) PLM
  have hbotiso := @PreLogos.bottom_dom_iso (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) PLM
    (@HasBinaryCoproducts.coprod (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞))
      DM.toPositivePreLogos.toHasBinaryCoproducts ⟨a⟩ ⟨b⟩)
    PLM.toHasTerminal.one
  obtain ⟨ι, _⟩ := hbotiso
  -- the `Map`-morphism `⟨P⟩ → ⟨(⊥ A+B in C).dom⟩`.
  let m₀ : @Cat.Hom (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨pb.cone.pt⟩
      ⟨(PreLogos.bottom (HasBinaryCoproducts.coprod a b)).dom⟩ :=
    @Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _
      (@Cat.comp (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) _ _ _ e ι)
      (ct.init ⟨(PreLogos.bottom (HasBinaryCoproducts.coprod a b)).dom⟩)
  -- lift `m₀` through fullness to a C-morphism `P → (⊥ A+B).dom`.
  obtain ⟨h, _hh⟩ := (embedRel_cat_iso (𝒞 := 𝒞)).2 m₀
  -- `inter.dom = pb.cone.pt = P`, so `h : inter.dom → (⊥ A+B).dom`; close by the helper.
  exact le_bottom_of_map_to_bottom _ h

/-- **§2.214 REVERSE — full assembly.**  From finite coproducts of `Rel(C)` (the
    positive-allegory coproduct DATA `zero`/`coprodObj`/`hcop`), `C` has disjoint binary
    coproducts.  The four §1.621 fields are `relReverse_inl_monic`, `relReverse_inr_monic`,
    `relReverse_inl_inter_inr`, `relReverse_inl_union_inr`.

    Instance plumbing: build `PPL := { inst✝.toPreLogos, HBC with }` where
    `HBC = relReverseHasBinaryCoproducts[inst✝]`, then pass `PPL` explicitly to all four
    field lemmas via `@`.  Lean accepts `hcop` at `PPL`-type because
    `relTabularUnitaryDistributiveAllegory[PPL] = relTabularUnitaryDistributiveAllegory[inst✝]`
    definitionally (the allegory only uses `PreLogos`, not `HasBinaryCoproducts`). -/
noncomputable def relReverseDisjointBinaryCoproduct (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    DisjointBinaryCoproduct 𝒞 :=
  -- `PPL` stores the ambient `PreLogos` LITERALLY (`mk ‹PreLogos 𝒞›`, not a `{…with}` rebuild) and
  -- pins the coproduct to `relReverseHasBinaryCoproducts` over the AMBIENT instance.  The four field
  -- lemmas are therefore applied at the AMBIENT `[PreLogos 𝒞]` (plain calls): their
  -- `relReverseHasBinaryCoproducts`/`bottom`/`inter`/`union` then match `PPL`'s projections
  -- definitionally, so no `relAllegory`/`hcop` re-elaboration diamond arises.
  @DisjointBinaryCoproduct.mk 𝒞 _
    (@PositivePreLogos.mk 𝒞 _ (‹PreLogos 𝒞›)
      (relReverseHasBinaryCoproducts zero coprodObj hcop))
    (fun {a b} => relReverse_inl_monic zero coprodObj hcop)
    (fun {a b} => relReverse_inr_monic zero coprodObj hcop)
    (fun {a b} => relReverse_inl_inter_inr zero coprodObj hcop)
    (fun {a b} => relReverse_inl_union_inr zero coprodObj hcop)

/-- **§2.214 (the iff).**  A pre-logos `C` is positive (has disjoint binary coproducts) iff
    `Rel(C)` has finite coproducts.  Forward: `DisjointGluing.relCoproduct`.
    Reverse: `relReverseDisjointBinaryCoproduct`. -/
theorem relReverse_positive_of_relCoproducts (zero : RelObj 𝒞)
    (coprodObj : RelObj 𝒞 → RelObj 𝒞 → RelObj 𝒞)
    (hcop : ∀ a b : RelObj 𝒞, Freyd.Alg.Coproduct (𝒜 := RelObj 𝒞) (coprodObj a b) a b) :
    Nonempty (DisjointBinaryCoproduct 𝒞) :=
  ⟨relReverseDisjointBinaryCoproduct zero coprodObj hcop⟩

end ReverseCoproduct

/-! ## §2.218 BRICK 2 — Rel-2-functoriality (`Rel(F)` for a regular functor `F`)

  A REGULAR FUNCTOR `F : C → D` between regular categories preserves finite limits
  (terminal/products/equalizers, hence pullbacks via §1.437), monos, images, and covers.
  Such an `F` induces an ALLEGORY FUNCTOR `Rel(F) : Rel(C) → Rel(D)`:
    • on objects:  `Rel(F)(A) := F A`  (lifted along `RelObj`);
    • on a relation `R ⊆ A×B` (a jointly-monic span `R.colA, R.colB`): apply `F` to the span,
      land in `F A × F B` via `pair (F R.colA) (F R.colB)`, and take the IMAGE.

  This file LANDS (all of BRICK 2, axioms [propext, Classical.choice, Quot.sound]):
    • `RegularFunctor` — the structure (products + pullbacks + covers + monos + images preservation).
    • `relImageObj` — the `BinRel D (F A) (F B)` built from `F`'s action on a span (the image of
      `⟨F colA, F colB⟩`), with the joint-monic proof; `relImageObj_cover` presents it via a cover.
    • `RegularFunctor.relMap` — the hom action on `BinRelQuot` (well-defined on `RelLe`-classes).
    • `RegularFunctor.relMap_id` / `relMap_recip` / `relMap_comp` / `relMap_inter` — the four
      allegory laws.  `relMap_comp`/`relMap_inter` are the Beck–Chevalley core: `F` preserving
      pullbacks + covers makes the §1.56 compose/meet image-spans commute with `F` (proven by
      `relLe_of_cover_factor` in both directions, via `relImageObj_cover` + `cover_pullback` +
      `pres_pullback`).
    • `RegularFunctor.relAllegoryHom : AllegoryFunctor (RelObj C) (RelObj D)` — the packaged morphism.
    • `RegularFunctor.relMap_faithful` — `Rel(F)` is faithful when `F` is full+faithful and covers
      in `D` split (`relImageObj_reflect_le`).  -/

section SubobjectPostIso
variable {D : Type u} [Cat.{v} D]

/-- Post-compose a subobject's arrow by an isomorphism `e`, giving a subobject of the target.
    (`m ≫ e` is monic because `e` is iso.) -/
noncomputable def Subobject.postIso {X Y : D} (S : Subobject D X) {e : X ⟶ Y} (he : IsIso e) :
    Subobject D Y where
  dom := S.dom
  arr := S.arr ≫ e
  monic := by
    obtain ⟨e', he1, _⟩ := he
    intro W g h hgh
    apply S.monic
    have : (g ≫ S.arr) ≫ e = (h ≫ S.arr) ≫ e := by rw [Cat.assoc, Cat.assoc]; exact hgh
    calc g ≫ S.arr = (g ≫ S.arr) ≫ e ≫ e' := by rw [he1, Cat.comp_id]
      _ = ((g ≫ S.arr) ≫ e) ≫ e' := (Cat.assoc _ _ _).symm
      _ = ((h ≫ S.arr) ≫ e) ≫ e' := by rw [this]
      _ = h ≫ S.arr := by rw [Cat.assoc, Cat.assoc, he1, Cat.comp_id]

/-- An iso post-composition preserves `IsImage`: if `I` is the image of `m`, then `I.postIso e`
    is the image of `m ≫ e`.  (Allowing/minimality both transport across the iso `e`.) -/
theorem isImage_postIso {W' X Y : D} {m : W' ⟶ X} {I : Subobject D X} (hI : IsImage m I)
    {e : X ⟶ Y} (he : IsIso e) : IsImage (m ≫ e) (I.postIso he) := by
  obtain ⟨e', he1, he2⟩ := he
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl⟩ := hI.1
    exact ⟨l, by show l ≫ (I.arr ≫ e) = m ≫ e; rw [← Cat.assoc, hl]⟩
  · rintro T ⟨t, ht⟩
    -- `T.postIso e'` allows `m`, so `I ≤ T.postIso e'`; transport the comparison back.
    have hTallows : Allows (T.postIso (⟨e, he2, he1⟩ : IsIso e')) m :=
      ⟨t, by
        show t ≫ (T.arr ≫ e') = m
        rw [← Cat.assoc, ht, Cat.assoc, he1, Cat.comp_id]⟩
    obtain ⟨k, hk⟩ := hI.2 _ hTallows
    refine ⟨k, ?_⟩
    show k ≫ T.arr = I.arr ≫ e
    have hk' : k ≫ (T.arr ≫ e') = I.arr := hk
    have hcollapse : (T.arr ≫ e') ≫ e = T.arr := by
      rw [Cat.assoc, he2, Cat.comp_id]
    have step : (k ≫ (T.arr ≫ e')) ≫ e = k ≫ T.arr := by
      rw [Cat.assoc, hcollapse]
    calc k ≫ T.arr = (k ≫ (T.arr ≫ e')) ≫ e := step.symm
      _ = I.arr ≫ e := by rw [hk']

end SubobjectPostIso

namespace RelFunctor

open Freyd

variable {C : Type u₁} {D : Type u₂} [Cat.{v} C] [Cat.{v} D]

/-- A **regular functor** `F : C → D` between regular categories: preserves binary products
    (`pres_prod`), covers (`pres_covers`), monos (`pres_mono`), and images (`pres_image`).
    These are exactly the data needed to transport relations: `pair` lands in `F A × F B`
    (products), `image` of the span exists & is preserved (images/monos), and `°`/`∩`/`≫` of
    relations are preserved (covers handle composition's image step).  We phrase everything
    over `[RegularCategory]` only (which already supplies products/pullbacks/images), avoiding the
    `exactPullbacks`/`RegularCategory.toHasPullbacks` instance diamond that `CartesianCategory`
    would introduce.  (Equalizer-preservation, needed only for the unused finite-limit packaging,
    is recovered from `pres_prod` + pullbacks where required.) -/
structure RegularFunctor (F : Functor C D)
    [RegularCategory C] [RegularCategory D] : Prop where
  /-- preserves binary products: the canonical `F(A×B) → FA×FB` is iso. -/
  pres_prod  : PreservesBinaryProducts F
  /-- preserves pullbacks (a finite limit; needed for the §1.56 compose-span). -/
  pres_pullback : PreservesPullbacks F
  /-- preserves covers (§1.52). -/
  pres_covers : PreservesCovers F
  /-- preserves monos. -/
  pres_mono  : PreservesMono F
  /-- preserves images (§1.51). -/
  pres_image : PreservesImages F pres_mono

variable {F : Functor C D}
  [RegularCategory C] [RegularCategory D]

/-- The image-relation of a span through `F`: take `F` of the columns, pair them into
    `F.obj A × F.obj B`, and form the `BinRel` from the image subobject (its arrow is monic, hence
    a jointly-monic pair via `monicPair_of_monic_pair`). -/
noncomputable def relImageObj (_hreg : RegularFunctor F) {A B : C}
    (R : BinRel C A B) : BinRel D (F.obj A) (F.obj B) :=
  let I := image (pair (F.map R.colA) (F.map R.colB))
  { src  := I.dom
    colA := I.arr ≫ fst
    colB := I.arr ≫ snd
    isMonicPair := by
      -- `I.arr` is monic, so the pair `(I.arr ≫ fst, I.arr ≫ snd)` is jointly monic.
      refine fun {W} f g hA hB => ?_
      have hfst : (f ≫ I.arr) ≫ fst = (g ≫ I.arr) ≫ fst := by
        simpa [Cat.assoc] using hA
      have hsnd : (f ≫ I.arr) ≫ snd = (g ≫ I.arr) ≫ snd := by
        simpa [Cat.assoc] using hB
      have hprod : f ≫ I.arr = g ≫ I.arr := by
        have hf : f ≫ I.arr = pair ((f ≫ I.arr) ≫ fst) ((f ≫ I.arr) ≫ snd) :=
          (pair_uniq _ _ (f ≫ I.arr) rfl rfl)
        have hg : g ≫ I.arr = pair ((f ≫ I.arr) ≫ fst) ((f ≫ I.arr) ≫ snd) :=
          (pair_uniq _ _ (g ≫ I.arr) hfst.symm hsnd.symm)
        rw [hf, hg]
      exact I.monic f g hprod }

/-- The image-cover of `relImageObj`: `image.lift (pair (F colA) (F colB))` is a cover from
    `F.obj R.src` onto `(relImageObj hreg R).src`, and its legs are exactly the `F`-images of `R`'s
    legs.  This is the key bridge: it presents `relImageObj hreg R` as the relation "generated by
    the span `(F.obj R.colA, F.obj R.colB)`", so `relLe_of_cover_factor` applies directly. -/
theorem relImageObj_cover (hreg : RegularFunctor F) {A B : C} (R : BinRel C A B) :
    ∃ e : F.obj R.src ⟶ (relImageObj hreg R).src,
      Cover e ∧ e ≫ (relImageObj hreg R).colA = F.map R.colA
        ∧ e ≫ (relImageObj hreg R).colB = F.map R.colB := by
  refine ⟨image.lift (pair (F.map R.colA) (F.map R.colB)), image_lift_cover _, ?_, ?_⟩
  · show image.lift _ ≫ ((image _).arr ≫ fst) = F.map R.colA
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  · show image.lift _ ≫ ((image _).arr ≫ snd) = F.map R.colB
    rw [← Cat.assoc, image.lift_fac, snd_pair]

/-- `relImageObj` is monotone for `RelLe`: a containment of spans upstairs gives a containment
    of their `F`-images downstairs (images are monotone, and `F` preserves the witnessing
    factorization).  This is what makes the hom action descend to `RelLe`-classes. -/
theorem relImageObj_mono (hreg : RegularFunctor F) {A B : C}
    {R S : BinRel C A B} (h : RelLe R S) :
    RelLe (relImageObj hreg R) (relImageObj hreg S) := by
  -- From `R ⊂ S` get the witness `z : R.src → S.src` with `z ≫ S.colA = R.colA` etc.
  obtain ⟨⟨z, hzA, hzB⟩⟩ := h
  -- `F z` sends the `R`-span to the `S`-span: `F z ≫ F.obj S.colA = F.obj R.colA`.
  have hFzA : F.map z ≫ F.map S.colA = F.map R.colA := by
    rw [← F.map_comp, hzA]
  have hFzB : F.map z ≫ F.map S.colB = F.map R.colB := by
    rw [← F.map_comp, hzB]
  -- The paired span `pR = pair (F.obj R.colA) (F.obj R.colB)` factors through `pS = pair (F.obj S.colA) (F.obj S.colB)`
  -- via `F z`.  Abbreviations `pR`, `pS`, `IR`, `IS` introduced with `let` (mathlib-free `set` is N/A).
  let pR := pair (F.map R.colA) (F.map R.colB)
  let pS := pair (F.map S.colA) (F.map S.colB)
  have hfst : (F.map z ≫ pS) ≫ fst = F.map R.colA := by
    rw [Cat.assoc]; show F.map z ≫ (pS ≫ fst) = F.map R.colA
    rw [fst_pair, hFzA]
  have hsnd : (F.map z ≫ pS) ≫ snd = F.map R.colB := by
    rw [Cat.assoc]; show F.map z ≫ (pS ≫ snd) = F.map R.colB
    rw [snd_pair, hFzB]
  have hfac : F.map z ≫ pS = pR :=
    pair_uniq (F.map R.colA) (F.map R.colB) (F.map z ≫ pS) hfst hsnd
  have hIS_allows_pR : Allows (image pS) pR := by
    obtain ⟨lS, hlS⟩ := (image_allows pS)
    refine ⟨F.map z ≫ lS, ?_⟩
    show (F.map z ≫ lS) ≫ (image pS).arr = pR
    rw [Cat.assoc, hlS, hfac]
  obtain ⟨k, hk⟩ := image_min pR (image pS) hIS_allows_pR
  -- `k : (image pR).dom → (image pS).dom` with `k ≫ (image pS).arr = (image pR).arr`.
  refine ⟨⟨k, ?_, ?_⟩⟩
  · show k ≫ ((image pS).arr ≫ fst) = (image pR).arr ≫ fst
    rw [← Cat.assoc, hk]
  · show k ≫ ((image pS).arr ≫ snd) = (image pR).arr ≫ snd
    rw [← Cat.assoc, hk]

/-- The hom action of `Rel(F)` on a single representative span, as a `RelLe`-class. -/
noncomputable def relMapRep (hreg : RegularFunctor F) {A B : C}
    (R : BinRel C A B) : BinRelQuot (𝒞 := D) (F.obj A) (F.obj B) :=
  relClass (relImageObj hreg R)

/-- The hom action `Rel(F) : BinRelQuot C A B → BinRelQuot D (F.obj A) (F.obj B)`, descended to
    `RelLe`-classes via `relImageObj_mono`. -/
noncomputable def RegularFunctor.relMap (hreg : RegularFunctor F) {A B : C}
    (x : BinRelQuot (𝒞 := C) A B) : BinRelQuot (𝒞 := D) (F.obj A) (F.obj B) :=
  Quotient.liftOn x (relMapRep hreg) (by
    intro R S ⟨hRS, hSR⟩
    exact Quotient.sound ⟨relImageObj_mono hreg hRS, relImageObj_mono hreg hSR⟩)

@[simp] theorem RegularFunctor.relMap_mk (hreg : RegularFunctor F) {A B : C}
    (R : BinRel C A B) :
    hreg.relMap (relClass R) = relClass (relImageObj hreg R) := rfl

/-- The swapped span `pair (F.obj R.colB) (F.obj R.colA)` equals `pair (F.obj R.colA) (F.obj R.colB) ≫ σ`. -/
theorem pair_swap_eq {A B : C} (R : BinRel C A B) :
    pair (F.map R.colB) (F.map R.colA)
      = pair (F.map R.colA) (F.map R.colB) ≫ prodSwap (F.obj A) (F.obj B) := by
  refine (pair_uniq (F.map R.colB) (F.map R.colA)
    (pair (F.map R.colA) (F.map R.colB) ≫ prodSwap (F.obj A) (F.obj B)) ?_ ?_).symm
  · rw [Cat.assoc, show prodSwap (F.obj A) (F.obj B) ≫ fst = snd (A := F.obj A) (B := F.obj B) from fst_pair _ _, snd_pair]
  · rw [Cat.assoc, show prodSwap (F.obj A) (F.obj B) ≫ snd = fst (A := F.obj A) (B := F.obj B) from snd_pair _ _, fst_pair]

/-- The swapped image subobject of `pair (F.obj R.colA) (F.obj R.colB)` is an image of the column-swapped
    span `pair (F.obj R.colB) (F.obj R.colA)`.  Technical heart of reciprocation-preservation. -/
theorem swapImage_isImage {A B : C} (R : BinRel C A B) :
    IsImage (pair (F.map R.colB) (F.map R.colA))
      ((image (pair (F.map R.colA) (F.map R.colB))).postIso
        (prod_comm_iso (A := F.obj A) (B := F.obj B))) := by
  rw [pair_swap_eq]
  exact isImage_postIso (HasImages.isImage _) (prod_comm_iso (A := F.obj A) (B := F.obj B))

/-- **`Rel(F)` preserves reciprocation.**  `relImageObj (R°)` is the image of the swapped span,
    which equals the reciprocal (column-swap) of `relImageObj R` up to the image-uniqueness iso. -/
theorem RegularFunctor.relMap_recip (hreg : RegularFunctor F) {A B : C}
    (x : BinRelQuot (𝒞 := C) A B) :
    hreg.relMap (qRecip x) = qRecip (hreg.relMap x) := by
  refine Quotient.inductionOn x (fun R => ?_)
  show relClass (relImageObj hreg (reciprocal R)) = qRecip (relClass (relImageObj hreg R))
  rw [qRecip_mk]
  -- The two images of `pair (F.obj R.colB) (F.obj R.colA)` give an iso comparison, hence equal classes.
  have hQimg := swapImage_isImage (F := F) R
  have hPimg : IsImage (pair (F.map R.colB) (F.map R.colA))
      (image (pair (F.map R.colB) (F.map R.colA))) := HasImages.isImage _
  -- Abbreviations (mathlib-free `set` is N/A): σ = swap iso, Ip/Iq the two images.
  let σ := prodSwap (F.obj A) (F.obj B)
  let Ip := image (pair (F.map R.colA) (F.map R.colB))
  let Iq := image (pair (F.map R.colB) (F.map R.colA))
  refine Quotient.sound ⟨?_, ?_⟩
  · -- `c : Iq.dom → Ip.dom`, `c ≫ (Ip.arr ≫ σ) = Iq.arr`.
    obtain ⟨c, hc⟩ := hPimg.2 _ hQimg.1
    have hc' : c ≫ (Ip.arr ≫ σ) = Iq.arr := hc
    refine ⟨c, ?_, ?_⟩
    · -- target colA of `(relImageObj R)°` is `Ip.arr ≫ snd`; source colA of `relImageObj (R°)` is `Iq.arr ≫ fst`.
      show c ≫ (Ip.arr ≫ snd) = Iq.arr ≫ fst
      have hexp : (c ≫ (Ip.arr ≫ σ)) ≫ fst = c ≫ (Ip.arr ≫ snd) := by
        rw [Cat.assoc, Cat.assoc, show prodSwap (F.obj A) (F.obj B) ≫ fst = snd (A := F.obj A) (B := F.obj B) from fst_pair _ _]
      rw [← hexp, hc']
    · show c ≫ (Ip.arr ≫ fst) = Iq.arr ≫ snd
      have hexp : (c ≫ (Ip.arr ≫ σ)) ≫ snd = c ≫ (Ip.arr ≫ fst) := by
        rw [Cat.assoc, Cat.assoc, show prodSwap (F.obj A) (F.obj B) ≫ snd = fst (A := F.obj A) (B := F.obj B) from snd_pair _ _]
      rw [← hexp, hc']
  · obtain ⟨c, hc⟩ := hQimg.2 _ hPimg.1
    have hc' : c ≫ Iq.arr = Ip.arr ≫ σ := hc
    refine ⟨c, ?_, ?_⟩
    · show c ≫ (Iq.arr ≫ fst) = Ip.arr ≫ snd
      have hlhs : c ≫ (Iq.arr ≫ fst) = (c ≫ Iq.arr) ≫ fst := (Cat.assoc _ _ _).symm
      have hrhs : Ip.arr ≫ snd = (Ip.arr ≫ σ) ≫ fst := by
        rw [Cat.assoc, show prodSwap (F.obj A) (F.obj B) ≫ fst = snd (A := F.obj A) (B := F.obj B) from fst_pair _ _]
      rw [hlhs, hc', hrhs]
    · show c ≫ (Iq.arr ≫ snd) = Ip.arr ≫ fst
      have hlhs : c ≫ (Iq.arr ≫ snd) = (c ≫ Iq.arr) ≫ snd := (Cat.assoc _ _ _).symm
      have hrhs : Ip.arr ≫ fst = (Ip.arr ≫ σ) ≫ snd := by
        rw [Cat.assoc, show prodSwap (F.obj A) (F.obj B) ≫ snd = fst (A := F.obj A) (B := F.obj B) from snd_pair _ _]
      rw [hlhs, hc', hrhs]

/-! ### §2.218 (2a) — `Rel(F)` preserves composition (Beck–Chevalley)

  `relImageObj hreg (R ⊚ S) ≡ relImageObj hreg R ⊚ relImageObj hreg S`.  The proof is a
  `relLe_of_cover_factor` chase in both directions: `relImageObj` of a span is, up to a cover
  (`relImageObj_cover`), the relation "generated by the `F`-image span", and `F` preserves the
  pullback square underlying `⊚` (it preserves products + covers, so it preserves the §1.56
  pullback-then-image construction up to RelLe).  -/

variable {Cobj : C}

/-- **(2a) — forward**: `relImageObj (R ⊚ S) ⊂ relImageObj R ⊚ relImageObj S`.  Pull the §1.56
    pullback `pbRS` of `R.colB, S.colA` through `F`; `F.obj pbRS.π₁/π₂` give a cone over the downstairs
    pullback `qb` (its square is the `F`-image of `pbRS.cone.w`), lift to `qb.pt`, then the image
    of the composite span supplies `φ`.  The cover is `F.obj (image.lift spanRS) ≫ (image-cover of R⊚S)`. -/
theorem relImageObj_compose_le (hreg : RegularFunctor F) {A B : C}
    (R : BinRel C A B) (S : BinRel C B Cobj) :
    RelLe (relImageObj hreg (R ⊚ S)) (relImageObj hreg R ⊚ relImageObj hreg S) := by
  -- image-covers of R and S downstairs
  obtain ⟨eR, heRcov, heRA, heRB⟩ := relImageObj_cover hreg R
  obtain ⟨eS, heScov, heSA, heSB⟩ := relImageObj_cover hreg S
  -- the §1.56 pullback for R ⊚ S, and its image-cover eRS
  let pbRS := HasPullbacks.has R.colB S.colA
  let spanRS := pair (pbRS.cone.π₁ ≫ R.colA) (pbRS.cone.π₂ ≫ S.colB)
  let eRS : pbRS.cone.pt ⟶ (R ⊚ S).src := image.lift spanRS
  have heRS_A : eRS ≫ (R ⊚ S).colA = pbRS.cone.π₁ ≫ R.colA := by
    show image.lift spanRS ≫ ((image spanRS).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have heRS_B : eRS ≫ (R ⊚ S).colB = pbRS.cone.π₂ ≫ S.colB := by
    show image.lift spanRS ≫ ((image spanRS).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- image-cover of (R ⊚ S) downstairs
  obtain ⟨eRSd, heRSdcov, heRSdA, heRSdB⟩ := relImageObj_cover hreg (R ⊚ S)
  -- the downstairs pullback qb for relImageObj R ⊚ relImageObj S
  let qb := HasPullbacks.has (relImageObj hreg R).colB (relImageObj hreg S).colA
  -- F of the upstairs pullback square, transported to the downstairs span legs
  have hcone_w :
      (F.map pbRS.cone.π₁ ≫ eR) ≫ (relImageObj hreg R).colB
        = (F.map pbRS.cone.π₂ ≫ eS) ≫ (relImageObj hreg S).colA := by
    rw [Cat.assoc, heRB, Cat.assoc, heSA, ← F.map_comp, ← F.map_comp, pbRS.cone.w]
  let cone : Cone (relImageObj hreg R).colB (relImageObj hreg S).colA :=
    { pt := F.obj pbRS.cone.pt
      π₁ := F.map pbRS.cone.π₁ ≫ eR
      π₂ := F.map pbRS.cone.π₂ ≫ eS
      w := hcone_w }
  let u : F.obj pbRS.cone.pt ⟶ qb.cone.pt := qb.lift cone
  have hu₁ : u ≫ qb.cone.π₁ = F.map pbRS.cone.π₁ ≫ eR := qb.lift_fst cone
  have hu₂ : u ≫ qb.cone.π₂ = F.map pbRS.cone.π₂ ≫ eS := qb.lift_snd cone
  -- the composite span downstairs, and its image-lift `eQ`
  let spanQ := pair (qb.cone.π₁ ≫ (relImageObj hreg R).colA)
                    (qb.cone.π₂ ≫ (relImageObj hreg S).colB)
  let eQ : qb.cone.pt ⟶ (relImageObj hreg R ⊚ relImageObj hreg S).src := image.lift spanQ
  have heQ_A : eQ ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colA
      = qb.cone.π₁ ≫ (relImageObj hreg R).colA := by
    show image.lift spanQ ≫ ((image spanQ).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have heQ_B : eQ ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colB
      = qb.cone.π₂ ≫ (relImageObj hreg S).colB := by
    show image.lift spanQ ≫ ((image spanQ).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- The cover onto relImageObj(R⊚S).src : `F eRS ≫ eRSd`.
  refine relLe_of_cover_factor (P := F.obj pbRS.cone.pt)
    (F.map eRS ≫ eRSd) (cover_comp (hreg.pres_covers _ (image_lift_cover spanRS)) heRSdcov)
    (u ≫ eQ) ?_ ?_
  · -- φ ≫ (compose).colA = c ≫ (relImageObj (R⊚S)).colA
    rw [Cat.assoc, heQ_A, ← Cat.assoc, hu₁, Cat.assoc, heRA, ← F.map_comp,
        Cat.assoc, heRSdA, ← F.map_comp, heRS_A, F.map_comp]
  · rw [Cat.assoc, heQ_B, ← Cat.assoc, hu₂, Cat.assoc, heSB, ← F.map_comp,
        Cat.assoc, heRSdB, ← F.map_comp, heRS_B, F.map_comp]

/-- **(2a) — reverse**: `relImageObj R ⊚ relImageObj S ⊂ relImageObj (R ⊚ S)`.  The downstairs
    composite is covered by `eQ : qb.pt ↠ src`.  Pull the image-covers `eR`/`eS` back along the
    `qb`-projections (`cover_pullback`) to a common stage `P2 ↠ qb.pt` carrying honest maps into
    `F.obj R.src`, `F.obj S.src` that agree on `F.obj B`; since `F` preserves the §1.56 pullback `pbRS`
    (`pres_pullback`), lift to `F.obj pbRS.pt`, then push through `F eRS ≫ eRSd` into `relImageObj (R⊚S)`. -/
theorem relImageObj_le_compose (hreg : RegularFunctor F) {A B : C}
    (R : BinRel C A B) (S : BinRel C B Cobj) :
    RelLe (relImageObj hreg R ⊚ relImageObj hreg S) (relImageObj hreg (R ⊚ S)) := by
  obtain ⟨eR, heRcov, heRA, heRB⟩ := relImageObj_cover hreg R
  obtain ⟨eS, heScov, heSA, heSB⟩ := relImageObj_cover hreg S
  -- §1.56 upstairs pullback & its image-cover, plus the downstairs (R⊚S) image-cover
  let pbRS := HasPullbacks.has R.colB S.colA
  let spanRS := pair (pbRS.cone.π₁ ≫ R.colA) (pbRS.cone.π₂ ≫ S.colB)
  let eRS : pbRS.cone.pt ⟶ (R ⊚ S).src := image.lift spanRS
  have heRS_A : eRS ≫ (R ⊚ S).colA = pbRS.cone.π₁ ≫ R.colA := by
    show image.lift spanRS ≫ ((image spanRS).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have heRS_B : eRS ≫ (R ⊚ S).colB = pbRS.cone.π₂ ≫ S.colB := by
    show image.lift spanRS ≫ ((image spanRS).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  obtain ⟨eRSd, heRSdcov, heRSdA, heRSdB⟩ := relImageObj_cover hreg (R ⊚ S)
  -- downstairs pullback qb and its composite image-cover eQ
  let qb := HasPullbacks.has (relImageObj hreg R).colB (relImageObj hreg S).colA
  let spanQ := pair (qb.cone.π₁ ≫ (relImageObj hreg R).colA)
                    (qb.cone.π₂ ≫ (relImageObj hreg S).colB)
  let eQ : qb.cone.pt ⟶ (relImageObj hreg R ⊚ relImageObj hreg S).src := image.lift spanQ
  have heQ_A : eQ ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colA
      = qb.cone.π₁ ≫ (relImageObj hreg R).colA := by
    show image.lift spanQ ≫ ((image spanQ).arr ≫ fst) = _
    rw [← Cat.assoc, image.lift_fac, fst_pair]
  have heQ_B : eQ ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colB
      = qb.cone.π₂ ≫ (relImageObj hreg S).colB := by
    show image.lift spanQ ≫ ((image spanQ).arr ≫ snd) = _
    rw [← Cat.assoc, image.lift_fac, snd_pair]
  -- Pull eR back along qb.π₁ : a cover c1 : P1 ↠ qb.pt and a lift pR1 : P1 → F.obj R.src.
  let pb1 := HasPullbacks.has eR qb.cone.π₁
  let c1 : pb1.cone.pt ⟶ qb.cone.pt := pb1.cone.π₂
  have hc1cov : Cover c1 := cover_pullback qb.cone.π₁ heRcov
  let pR1 : pb1.cone.pt ⟶ F.obj R.src := pb1.cone.π₁
  have hpb1w : pR1 ≫ eR = c1 ≫ qb.cone.π₁ := pb1.cone.w
  -- Pull eS back along (c1 ≫ qb.π₂) : a cover c2 : P2 ↠ P1 and a lift pS2 : P2 → F.obj S.src.
  let pb2 := HasPullbacks.has eS (c1 ≫ qb.cone.π₂)
  let c2 : pb2.cone.pt ⟶ pb1.cone.pt := pb2.cone.π₂
  have hc2cov : Cover c2 := cover_pullback (c1 ≫ qb.cone.π₂) heScov
  let pS2 : pb2.cone.pt ⟶ F.obj S.src := pb2.cone.π₁
  have hpb2w : pS2 ≫ eS = c2 ≫ (c1 ≫ qb.cone.π₂) := pb2.cone.w
  -- on P2: legs into F.obj R.src and F.obj S.src
  let p : pb2.cone.pt ⟶ F.obj R.src := c2 ≫ pR1
  let q : pb2.cone.pt ⟶ F.obj S.src := pS2
  -- they agree on F.obj B: p ≫ F.obj R.colB = q ≫ F.obj S.colA
  have hmid : p ≫ F.map R.colB = q ≫ F.map S.colA := by
    have e1 : p ≫ F.map R.colB = c2 ≫ (c1 ≫ qb.cone.π₁) ≫ (relImageObj hreg R).colB :=
      calc (c2 ≫ pR1) ≫ F.map R.colB
          = c2 ≫ pR1 ≫ (eR ≫ (relImageObj hreg R).colB) := by rw [Cat.assoc, heRB]
        _ = c2 ≫ (pR1 ≫ eR) ≫ (relImageObj hreg R).colB := by rw [Cat.assoc]
        _ = c2 ≫ (c1 ≫ qb.cone.π₁) ≫ (relImageObj hreg R).colB := by rw [hpb1w]
    have e2 : q ≫ F.map S.colA = c2 ≫ (c1 ≫ qb.cone.π₂) ≫ (relImageObj hreg S).colA :=
      calc pS2 ≫ F.map S.colA
          = (pS2 ≫ eS) ≫ (relImageObj hreg S).colA := by rw [Cat.assoc, heSA]
        _ = (c2 ≫ c1 ≫ qb.cone.π₂) ≫ (relImageObj hreg S).colA := by rw [hpb2w]
        _ = c2 ≫ (c1 ≫ qb.cone.π₂) ≫ (relImageObj hreg S).colA := by rw [Cat.assoc]
    rw [e1, e2]
    rw [Cat.assoc, Cat.assoc, qb.cone.w, ← Cat.assoc, ← Cat.assoc]
  -- F preserves pbRS, so (F.obj pbRS.cone) is a pullback of (F.obj R.colB, F.obj S.colA); lift (p,q).
  have hFpb : (Cone.mk (F.obj pbRS.cone.pt) (F.map pbRS.cone.π₁) (F.map pbRS.cone.π₂)
      (by rw [← F.map_comp, ← F.map_comp, pbRS.cone.w])).IsPullback :=
    hreg.pres_pullback R.colB S.colA pbRS.cone pbRS.cone_isPullback
  obtain ⟨w, ⟨hw₁, hw₂⟩, _⟩ := hFpb (Cone.mk pb2.cone.pt p q hmid)
  -- φ : P2 → relImageObj(R⊚S).src via w ≫ F eRS ≫ eRSd
  refine relLe_of_cover_factor (P := pb2.cone.pt)
    (c2 ≫ c1 ≫ eQ) (cover_comp hc2cov (cover_comp hc1cov (image_lift_cover spanQ)))
    (w ≫ F.map eRS ≫ eRSd) ?_ ?_
  · -- φ ≫ relImageObj(R⊚S).colA = c ≫ (compose).colA ; reduce both sides to `p ≫ F.obj R.colA`.
    have hfeRSA : F.map eRS ≫ F.map (R ⊚ S).colA = F.map (pbRS.cone.π₁ ≫ R.colA) := by
      rw [← F.map_comp, heRS_A]
    have hlhs : (w ≫ F.map eRS ≫ eRSd) ≫ (relImageObj hreg (R ⊚ S)).colA = p ≫ F.map R.colA :=
      calc (w ≫ F.map eRS ≫ eRSd) ≫ (relImageObj hreg (R ⊚ S)).colA
          = w ≫ F.map eRS ≫ (eRSd ≫ (relImageObj hreg (R ⊚ S)).colA) := by
              rw [Cat.assoc, Cat.assoc]
        _ = w ≫ F.map eRS ≫ F.map (R ⊚ S).colA := by rw [heRSdA]
        _ = w ≫ F.map (pbRS.cone.π₁ ≫ R.colA) := by rw [hfeRSA]
        _ = w ≫ F.map pbRS.cone.π₁ ≫ F.map R.colA := by rw [F.map_comp pbRS.cone.π₁ R.colA]
        _ = (w ≫ F.map pbRS.cone.π₁) ≫ F.map R.colA := by rw [Cat.assoc]
        _ = p ≫ F.map R.colA := by rw [hw₁]
    have hrhs : (c2 ≫ c1 ≫ eQ) ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colA
        = p ≫ F.map R.colA :=
      calc (c2 ≫ c1 ≫ eQ) ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colA
          = c2 ≫ c1 ≫ (eQ ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colA) := by
              rw [Cat.assoc, Cat.assoc]
        _ = c2 ≫ c1 ≫ (qb.cone.π₁ ≫ (relImageObj hreg R).colA) := by rw [heQ_A]
        _ = c2 ≫ (c1 ≫ qb.cone.π₁) ≫ (relImageObj hreg R).colA := by rw [Cat.assoc]
        _ = c2 ≫ (pR1 ≫ eR) ≫ (relImageObj hreg R).colA := by rw [hpb1w]
        _ = c2 ≫ pR1 ≫ (eR ≫ (relImageObj hreg R).colA) := by rw [Cat.assoc]
        _ = (c2 ≫ pR1) ≫ F.map R.colA := by rw [heRA, Cat.assoc]
    rw [hlhs, hrhs]
  · have hfeRSB : F.map eRS ≫ F.map (R ⊚ S).colB = F.map (pbRS.cone.π₂ ≫ S.colB) := by
      rw [← F.map_comp, heRS_B]
    have hlhs : (w ≫ F.map eRS ≫ eRSd) ≫ (relImageObj hreg (R ⊚ S)).colB = q ≫ F.map S.colB :=
      calc (w ≫ F.map eRS ≫ eRSd) ≫ (relImageObj hreg (R ⊚ S)).colB
          = w ≫ F.map eRS ≫ (eRSd ≫ (relImageObj hreg (R ⊚ S)).colB) := by
              rw [Cat.assoc, Cat.assoc]
        _ = w ≫ F.map eRS ≫ F.map (R ⊚ S).colB := by rw [heRSdB]
        _ = w ≫ F.map (pbRS.cone.π₂ ≫ S.colB) := by rw [hfeRSB]
        _ = w ≫ F.map pbRS.cone.π₂ ≫ F.map S.colB := by rw [F.map_comp pbRS.cone.π₂ S.colB]
        _ = (w ≫ F.map pbRS.cone.π₂) ≫ F.map S.colB := by rw [Cat.assoc]
        _ = q ≫ F.map S.colB := by rw [hw₂]
    have hrhs : (c2 ≫ c1 ≫ eQ) ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colB
        = q ≫ F.map S.colB :=
      calc (c2 ≫ c1 ≫ eQ) ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colB
          = c2 ≫ c1 ≫ (eQ ≫ (relImageObj hreg R ⊚ relImageObj hreg S).colB) := by
              rw [Cat.assoc, Cat.assoc]
        _ = c2 ≫ c1 ≫ (qb.cone.π₂ ≫ (relImageObj hreg S).colB) := by rw [heQ_B]
        _ = (c2 ≫ c1 ≫ qb.cone.π₂) ≫ (relImageObj hreg S).colB := by
              rw [Cat.assoc, Cat.assoc]
        _ = (pS2 ≫ eS) ≫ (relImageObj hreg S).colB := by rw [hpb2w]
        _ = q ≫ F.map S.colB := by rw [Cat.assoc, heSB]
    rw [hlhs, hrhs]

/-- **(2a) — `Rel(F)` preserves composition** on the quotient: `Rel(F)(x ⊚ y) = Rel(F)(x) ⊚ Rel(F)(y)`. -/
theorem RegularFunctor.relMap_comp (hreg : RegularFunctor F) {A B : C}
    (x : BinRelQuot (𝒞 := C) A B) (y : BinRelQuot (𝒞 := C) B Cobj) :
    hreg.relMap (qComp x y) = qComp (hreg.relMap x) (hreg.relMap y) := by
  refine Quotient.inductionOn₂ x y (fun R S => ?_)
  show relClass (relImageObj hreg (R ⊚ S)) = qComp (relClass _) (relClass _)
  rw [qComp_mk]
  exact Quotient.sound ⟨relImageObj_compose_le hreg R S, relImageObj_le_compose hreg R S⟩

/-! ### §2.218 (2a) — `Rel(F)` preserves intersection

  `relImageObj hreg (R ⊓ S) ≡ relImageObj hreg R ⊓ relImageObj hreg S`.  Same `relLe_of_cover_factor`
  pattern: `⊓` is a single pullback of the two paired spans (no image step), and `F` preserves that
  pullback (`pres_pullback`); the image-covers `eR`/`eS` bridge to the `relImageObj` legs. -/

/-- `F` preserving binary products makes `(F fst, F snd) : F(prod A B) ⇉ FA, FB` jointly monic:
    two maps into `F(prod A B)` agreeing after `F fst` and `F snd` are equal. -/
theorem map_prod_jointly_monic (hreg : RegularFunctor F) {A B : C} {P : D}
    {u v : P ⟶ F.obj (prod A B)}
    (hfst : u ≫ F.map fst = v ≫ F.map fst) (hsnd : u ≫ F.map snd = v ≫ F.map snd) :
    u = v := by
  obtain ⟨inv, hiv, _⟩ := hreg.pres_prod (A := A) (B := B)
  have hmono : Monic (pair (F.map (fst (A := A) (B := B))) (F.map (snd (A := A) (B := B)))) :=
    mono_of_retraction _ inv hiv
  apply hmono
  have h1 : u ≫ pair (F.map (fst (A:=A) (B:=B))) (F.map (snd (A:=A) (B:=B)))
      = pair (u ≫ F.map fst) (u ≫ F.map snd) :=
    pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
  have h2 : v ≫ pair (F.map (fst (A:=A) (B:=B))) (F.map (snd (A:=A) (B:=B)))
      = pair (u ≫ F.map fst) (u ≫ F.map snd) :=
    pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hfst]) (by rw [Cat.assoc, snd_pair, hsnd])
  rw [h1, h2]

/-- Cone-condition builder for the downstairs meet pullback `pq`: a stage `P` with `colA/colB`
    legs that match assembles into the pair-square `pq` needs.  Splits columns to avoid `F(pair …)`. -/
theorem inter_cone_w (hreg : RegularFunctor F) {A B : C} (R S : BinRel C A B)
    {P : D} {g₁ : P ⟶ (relImageObj hreg R).src} {g₂ : P ⟶ (relImageObj hreg S).src}
    (hA : g₁ ≫ (relImageObj hreg R).colA = g₂ ≫ (relImageObj hreg S).colA)
    (hB : g₁ ≫ (relImageObj hreg R).colB = g₂ ≫ (relImageObj hreg S).colB) :
    g₁ ≫ pair (relImageObj hreg R).colA (relImageObj hreg R).colB
      = g₂ ≫ pair (relImageObj hreg S).colA (relImageObj hreg S).colB := by
  have h1 : g₁ ≫ pair (relImageObj hreg R).colA (relImageObj hreg R).colB
      = pair (g₁ ≫ (relImageObj hreg R).colA) (g₁ ≫ (relImageObj hreg R).colB) :=
    pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
  have h2 : g₂ ≫ pair (relImageObj hreg S).colA (relImageObj hreg S).colB
      = pair (g₁ ≫ (relImageObj hreg R).colA) (g₁ ≫ (relImageObj hreg R).colB) :=
    pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hA]) (by rw [Cat.assoc, snd_pair, hB])
  rw [h1, h2]

/-- **(2a)∩ — forward**: `relImageObj (R ⊓ S) ⊂ relImageObj R ⊓ relImageObj S`. -/
theorem relImageObj_inter_le (hreg : RegularFunctor F) {A B : C}
    (R S : BinRel C A B) :
    RelLe (relImageObj hreg (R ⊓ S)) (relImageObj hreg R ⊓ relImageObj hreg S) := by
  obtain ⟨eR, _, heRA, heRB⟩ := relImageObj_cover hreg R
  obtain ⟨eS, _, heSA, heSB⟩ := relImageObj_cover hreg S
  obtain ⟨e, hecov, heA, heB⟩ := relImageObj_cover hreg (R ⊓ S)
  let pb := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  let pq := HasPullbacks.has (pair (relImageObj hreg R).colA (relImageObj hreg R).colB)
                             (pair (relImageObj hreg S).colA (relImageObj hreg S).colB)
  -- the upstairs meet square, split into columns
  have hpb_fst : pb.cone.π₁ ≫ R.colA = pb.cone.π₂ ≫ S.colA :=
    calc pb.cone.π₁ ≫ R.colA = (pb.cone.π₁ ≫ pair R.colA R.colB) ≫ fst := by
            rw [Cat.assoc, fst_pair]
      _ = (pb.cone.π₂ ≫ pair S.colA S.colB) ≫ fst := by rw [pb.cone.w]
      _ = pb.cone.π₂ ≫ S.colA := by rw [Cat.assoc, fst_pair]
  have hpb_snd : pb.cone.π₁ ≫ R.colB = pb.cone.π₂ ≫ S.colB :=
    calc pb.cone.π₁ ≫ R.colB = (pb.cone.π₁ ≫ pair R.colA R.colB) ≫ snd := by
            rw [Cat.assoc, snd_pair]
      _ = (pb.cone.π₂ ≫ pair S.colA S.colB) ≫ snd := by rw [pb.cone.w]
      _ = pb.cone.π₂ ≫ S.colB := by rw [Cat.assoc, snd_pair]
  have hcw := inter_cone_w hreg R S (P := F.obj pb.cone.pt)
    (g₁ := F.map pb.cone.π₁ ≫ eR) (g₂ := F.map pb.cone.π₂ ≫ eS)
    (by rw [Cat.assoc, heRA, Cat.assoc, heSA, ← F.map_comp, ← F.map_comp, hpb_fst])
    (by rw [Cat.assoc, heRB, Cat.assoc, heSB, ← F.map_comp, ← F.map_comp, hpb_snd])
  let cone : Cone (pair (relImageObj hreg R).colA (relImageObj hreg R).colB)
                  (pair (relImageObj hreg S).colA (relImageObj hreg S).colB) :=
    { pt := F.obj pb.cone.pt, π₁ := F.map pb.cone.π₁ ≫ eR, π₂ := F.map pb.cone.π₂ ≫ eS, w := hcw }
  let φ : F.obj pb.cone.pt ⟶ pq.cone.pt := pq.lift cone
  have hφ₁ : φ ≫ pq.cone.π₁ = F.map pb.cone.π₁ ≫ eR := pq.lift_fst cone
  refine relLe_of_cover_factor (P := F.obj pb.cone.pt) e hecov φ ?_ ?_
  · show φ ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colA) = e ≫ (relImageObj hreg (R ⊓ S)).colA
    rw [← Cat.assoc, hφ₁, Cat.assoc, heRA, ← F.map_comp, heA]
    rfl
  · show φ ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colB) = e ≫ (relImageObj hreg (R ⊓ S)).colB
    rw [← Cat.assoc, hφ₁, Cat.assoc, heRB, ← F.map_comp, heB]
    rfl

/-- **(2a)∩ — reverse**: `relImageObj R ⊓ relImageObj S ⊂ relImageObj (R ⊓ S)`. -/
theorem relImageObj_le_inter (hreg : RegularFunctor F) {A B : C}
    (R S : BinRel C A B) :
    RelLe (relImageObj hreg R ⊓ relImageObj hreg S) (relImageObj hreg (R ⊓ S)) := by
  obtain ⟨eR, heRcov, heRA, heRB⟩ := relImageObj_cover hreg R
  obtain ⟨eS, heScov, heSA, heSB⟩ := relImageObj_cover hreg S
  obtain ⟨e, hecov, heA, heB⟩ := relImageObj_cover hreg (R ⊓ S)
  let pb := HasPullbacks.has (pair R.colA R.colB) (pair S.colA S.colB)
  let pq := HasPullbacks.has (pair (relImageObj hreg R).colA (relImageObj hreg R).colB)
                             (pair (relImageObj hreg S).colA (relImageObj hreg S).colB)
  -- pull eR back along pq.π₁, then eS along (c1 ≫ pq.π₂)
  let pb1 := HasPullbacks.has eR pq.cone.π₁
  let c1 : pb1.cone.pt ⟶ pq.cone.pt := pb1.cone.π₂
  have hc1cov : Cover c1 := cover_pullback pq.cone.π₁ heRcov
  let pR1 : pb1.cone.pt ⟶ F.obj R.src := pb1.cone.π₁
  have hpb1w : pR1 ≫ eR = c1 ≫ pq.cone.π₁ := pb1.cone.w
  let pb2 := HasPullbacks.has eS (c1 ≫ pq.cone.π₂)
  let c2 : pb2.cone.pt ⟶ pb1.cone.pt := pb2.cone.π₂
  have hc2cov : Cover c2 := cover_pullback (c1 ≫ pq.cone.π₂) heScov
  let pS2 : pb2.cone.pt ⟶ F.obj S.src := pb2.cone.π₁
  have hpb2w : pS2 ≫ eS = c2 ≫ (c1 ≫ pq.cone.π₂) := pb2.cone.w
  let p : pb2.cone.pt ⟶ F.obj R.src := c2 ≫ pR1
  let q : pb2.cone.pt ⟶ F.obj S.src := pS2
  -- p and q agree on both columns (via the pq pullback square)
  have hpq_fst : pq.cone.π₁ ≫ (relImageObj hreg R).colA
      = pq.cone.π₂ ≫ (relImageObj hreg S).colA :=
    calc pq.cone.π₁ ≫ (relImageObj hreg R).colA
        = (pq.cone.π₁ ≫ pair (relImageObj hreg R).colA (relImageObj hreg R).colB) ≫ fst := by
          rw [Cat.assoc, fst_pair]
      _ = (pq.cone.π₂ ≫ pair (relImageObj hreg S).colA (relImageObj hreg S).colB) ≫ fst := by
          rw [pq.cone.w]
      _ = pq.cone.π₂ ≫ (relImageObj hreg S).colA := by rw [Cat.assoc, fst_pair]
  have hpq_snd : pq.cone.π₁ ≫ (relImageObj hreg R).colB
      = pq.cone.π₂ ≫ (relImageObj hreg S).colB :=
    calc pq.cone.π₁ ≫ (relImageObj hreg R).colB
        = (pq.cone.π₁ ≫ pair (relImageObj hreg R).colA (relImageObj hreg R).colB) ≫ snd := by
          rw [Cat.assoc, snd_pair]
      _ = (pq.cone.π₂ ≫ pair (relImageObj hreg S).colA (relImageObj hreg S).colB) ≫ snd := by
          rw [pq.cone.w]
      _ = pq.cone.π₂ ≫ (relImageObj hreg S).colB := by rw [Cat.assoc, snd_pair]
  have hpA : p ≫ F.map R.colA = q ≫ F.map S.colA :=
    calc p ≫ F.map R.colA = c2 ≫ pR1 ≫ (eR ≫ (relImageObj hreg R).colA) := by
            rw [heRA, Cat.assoc]
      _ = c2 ≫ (c1 ≫ pq.cone.π₁) ≫ (relImageObj hreg R).colA := by rw [← Cat.assoc pR1, hpb1w]
      _ = c2 ≫ c1 ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colA) := by rw [Cat.assoc]
      _ = c2 ≫ c1 ≫ (pq.cone.π₂ ≫ (relImageObj hreg S).colA) := by rw [hpq_fst]
      _ = (c2 ≫ c1 ≫ pq.cone.π₂) ≫ (relImageObj hreg S).colA := by rw [Cat.assoc, Cat.assoc]
      _ = (pS2 ≫ eS) ≫ (relImageObj hreg S).colA := by rw [hpb2w]
      _ = q ≫ F.map S.colA := by rw [Cat.assoc, heSA]
  have hpB : p ≫ F.map R.colB = q ≫ F.map S.colB :=
    calc p ≫ F.map R.colB = c2 ≫ pR1 ≫ (eR ≫ (relImageObj hreg R).colB) := by
            rw [heRB, Cat.assoc]
      _ = c2 ≫ (c1 ≫ pq.cone.π₁) ≫ (relImageObj hreg R).colB := by rw [← Cat.assoc pR1, hpb1w]
      _ = c2 ≫ c1 ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colB) := by rw [Cat.assoc]
      _ = c2 ≫ c1 ≫ (pq.cone.π₂ ≫ (relImageObj hreg S).colB) := by rw [hpq_snd]
      _ = (c2 ≫ c1 ≫ pq.cone.π₂) ≫ (relImageObj hreg S).colB := by rw [Cat.assoc, Cat.assoc]
      _ = (pS2 ≫ eS) ≫ (relImageObj hreg S).colB := by rw [hpb2w]
      _ = q ≫ F.map S.colB := by rw [Cat.assoc, heSB]
  -- cone condition into F(prod A B), via joint monicity of (F fst, F snd)
  have hcone_w : p ≫ F.map (pair R.colA R.colB) = q ≫ F.map (pair S.colA S.colB) := by
    apply map_prod_jointly_monic hreg
    · calc (p ≫ F.map (pair R.colA R.colB)) ≫ F.map fst
            = p ≫ F.map (pair R.colA R.colB ≫ fst) := by rw [Cat.assoc, ← F.map_comp]
        _ = p ≫ F.map R.colA := by rw [fst_pair]
        _ = q ≫ F.map S.colA := hpA
        _ = q ≫ F.map (pair S.colA S.colB ≫ fst) := by rw [fst_pair]
        _ = (q ≫ F.map (pair S.colA S.colB)) ≫ F.map fst := by rw [F.map_comp, Cat.assoc]
    · calc (p ≫ F.map (pair R.colA R.colB)) ≫ F.map snd
            = p ≫ F.map (pair R.colA R.colB ≫ snd) := by rw [Cat.assoc, ← F.map_comp]
        _ = p ≫ F.map R.colB := by rw [snd_pair]
        _ = q ≫ F.map S.colB := hpB
        _ = q ≫ F.map (pair S.colA S.colB ≫ snd) := by rw [snd_pair]
        _ = (q ≫ F.map (pair S.colA S.colB)) ≫ F.map snd := by rw [F.map_comp, Cat.assoc]
  have hFpb : (Cone.mk (F.obj pb.cone.pt) (F.map pb.cone.π₁) (F.map pb.cone.π₂)
      (by rw [← F.map_comp, ← F.map_comp, pb.cone.w])).IsPullback :=
    hreg.pres_pullback _ _ pb.cone pb.cone_isPullback
  obtain ⟨w, ⟨hw₁, hw₂⟩, _⟩ := hFpb (Cone.mk pb2.cone.pt p q hcone_w)
  refine relLe_of_cover_factor (P := pb2.cone.pt)
    (c2 ≫ c1) (cover_comp hc2cov hc1cov) (w ≫ e) ?_ ?_
  · show (w ≫ e) ≫ (relImageObj hreg (R ⊓ S)).colA
      = (c2 ≫ c1) ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colA)
    have lhs : (w ≫ e) ≫ (relImageObj hreg (R ⊓ S)).colA = p ≫ F.map R.colA :=
      calc (w ≫ e) ≫ (relImageObj hreg (R ⊓ S)).colA
          = w ≫ (e ≫ (relImageObj hreg (R ⊓ S)).colA) := by rw [Cat.assoc]
        _ = w ≫ F.map (R ⊓ S).colA := by rw [heA]
        _ = w ≫ F.map (pb.cone.π₁ ≫ R.colA) := rfl
        _ = (w ≫ F.map pb.cone.π₁) ≫ F.map R.colA := by rw [F.map_comp pb.cone.π₁ R.colA, Cat.assoc]
        _ = p ≫ F.map R.colA := by rw [hw₁]
    have rhs : (c2 ≫ c1) ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colA) = p ≫ F.map R.colA :=
      calc (c2 ≫ c1) ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colA)
          = c2 ≫ (c1 ≫ pq.cone.π₁) ≫ (relImageObj hreg R).colA := by rw [Cat.assoc, Cat.assoc]
        _ = c2 ≫ (pR1 ≫ eR) ≫ (relImageObj hreg R).colA := by rw [hpb1w]
        _ = (c2 ≫ pR1) ≫ F.map R.colA := by rw [Cat.assoc, Cat.assoc, heRA]
    rw [lhs, rhs]
  · show (w ≫ e) ≫ (relImageObj hreg (R ⊓ S)).colB
      = (c2 ≫ c1) ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colB)
    have lhs : (w ≫ e) ≫ (relImageObj hreg (R ⊓ S)).colB = p ≫ F.map R.colB :=
      calc (w ≫ e) ≫ (relImageObj hreg (R ⊓ S)).colB
          = w ≫ (e ≫ (relImageObj hreg (R ⊓ S)).colB) := by rw [Cat.assoc]
        _ = w ≫ F.map (R ⊓ S).colB := by rw [heB]
        _ = w ≫ F.map (pb.cone.π₁ ≫ R.colB) := rfl
        _ = (w ≫ F.map pb.cone.π₁) ≫ F.map R.colB := by rw [F.map_comp pb.cone.π₁ R.colB, Cat.assoc]
        _ = p ≫ F.map R.colB := by rw [hw₁]
    have rhs : (c2 ≫ c1) ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colB) = p ≫ F.map R.colB :=
      calc (c2 ≫ c1) ≫ (pq.cone.π₁ ≫ (relImageObj hreg R).colB)
          = c2 ≫ (c1 ≫ pq.cone.π₁) ≫ (relImageObj hreg R).colB := by rw [Cat.assoc, Cat.assoc]
        _ = c2 ≫ (pR1 ≫ eR) ≫ (relImageObj hreg R).colB := by rw [hpb1w]
        _ = (c2 ≫ pR1) ≫ F.map R.colB := by rw [Cat.assoc, Cat.assoc, heRB]
    rw [lhs, rhs]

/-- **(2a) — `Rel(F)` preserves intersection** on the quotient. -/
theorem RegularFunctor.relMap_inter (hreg : RegularFunctor F) {A B : C}
    (x y : BinRelQuot (𝒞 := C) A B) :
    hreg.relMap (qInter x y) = qInter (hreg.relMap x) (hreg.relMap y) := by
  refine Quotient.inductionOn₂ x y (fun R S => ?_)
  show relClass (relImageObj hreg (R ⊓ S)) = qInter (relClass _) (relClass _)
  rw [qInter_mk]
  exact Quotient.sound ⟨relImageObj_inter_le hreg R S, relImageObj_le_inter hreg R S⟩

/-- **(2a) — `Rel(F)` preserves the identity**: `Rel(F)(relId A) = relId (F.obj A)`.  `relImageObj` of
    `graph (id)` is the image of the diagonal, RelLe-equivalent to `graph (id (F.obj A))`. -/
theorem RegularFunctor.relMap_id (hreg : RegularFunctor F) (A : C) :
    hreg.relMap (relId A) = relId (F.obj A) := by
  show relClass (relImageObj hreg (graph (Cat.id A))) = relClass (graph (Cat.id (F.obj A)))
  obtain ⟨e, hecov, heA, heB⟩ := relImageObj_cover hreg (graph (Cat.id A))
  -- legs of graph (id A) are both `id`, so F-images are `id (F.obj A)`.
  have heA' : e ≫ (relImageObj hreg (graph (Cat.id A))).colA = Cat.id (F.obj A) := by
    rw [heA]; exact F.map_id A
  have heB' : e ≫ (relImageObj hreg (graph (Cat.id A))).colB = Cat.id (F.obj A) := by
    rw [heB]; exact F.map_id A
  refine Quotient.sound ⟨?_, ?_⟩
  · -- relImageObj ⊂ graph(id): cover e, φ = id
    refine relLe_of_cover_factor (P := F.obj A) e hecov (Cat.id (F.obj A)) ?_ ?_
    · show Cat.id (F.obj A) ≫ Cat.id (F.obj A) = e ≫ (relImageObj hreg (graph (Cat.id A))).colA
      rw [Cat.id_comp, heA']
    · show Cat.id (F.obj A) ≫ Cat.id (F.obj A) = e ≫ (relImageObj hreg (graph (Cat.id A))).colB
      rw [Cat.id_comp, heB']
  · -- graph(id) ⊂ relImageObj: cover id, φ = e
    have hcid : Cover (Cat.id (F.obj A)) := by
      intro Cc m g hm hgm
      -- g ≫ m = id, m monic ⟹ m ≫ g = id (monic + section), hence m iso
      refine ⟨g, ?_, hgm⟩
      apply hm
      rw [Cat.assoc, hgm, Cat.comp_id, Cat.id_comp]
    refine relLe_of_cover_factor (P := F.obj A) (Cat.id (F.obj A)) hcid e ?_ ?_
    · show e ≫ (relImageObj hreg (graph (Cat.id A))).colA = Cat.id (F.obj A) ≫ Cat.id (F.obj A)
      rw [Cat.id_comp, heA']
    · show e ≫ (relImageObj hreg (graph (Cat.id A))).colB = Cat.id (F.obj A) ≫ Cat.id (F.obj A)
      rw [Cat.id_comp, heB']

/-- **§2.218 (2a) — `Rel(F)` as an allegory functor `Rel(C) → Rel(D)`.**  Objects: `A ↦ F.obj A`;
    homs: `hreg.relMap`.  The four `AllegoryFunctor` laws are `relMap_id`/`relMap_comp`/
    `relMap_recip`/`relMap_inter`. -/
noncomputable def RegularFunctor.relAllegoryHom (hreg : RegularFunctor F) :
    AllegoryFunctor (RelObj C) (RelObj D) where
  obj A := ⟨F.obj A.carrier⟩
  map {_a _b} x := hreg.relMap x
  map_id A := hreg.relMap_id A.carrier
  map_comp R S := hreg.relMap_comp R S
  map_recip R := hreg.relMap_recip R
  map_inter R S := hreg.relMap_inter R S

/-! ### §2.218 (2b) — Faithfulness of `Rel(F)`

  If `F` is FULL and FAITHFUL and every cover in `D` splits (e.g. `D` capital / all objects
  projective — the case in the §2.218 assembly, where `F` is the capital hom-representation into
  `Set^I`), then `Rel(F)` is FAITHFUL on `RelLe`-classes: `relImageObj R ≡ relImageObj S ⟹ R ≡ S`.

  Mechanism: `relImageObj R` carries the cover `eR : F.obj R.src ↠ IR.src` with legs `F.obj R.colA/colB`
  (`relImageObj_cover`).  A `RelLe` between the images gives `k : IR.src → IS.src`; splitting the
  cover `eS` (`hsplit`) yields a section `sS`, so `g := eR ≫ k ≫ sS : F.obj R.src → F.obj S.src` carries
  the legs `F.obj R.colA → F.obj S.colA`.  Fullness lifts `g` to `F h`; faithfulness turns the leg equations
  `F(h ≫ S.colA) = F.obj R.colA` into `h ≫ S.colA = R.colA`, i.e. a `RelHom R S`.  -/

section SameUniverseFaithful
-- The full+faithful faithfulness route uses `Faithful F`, which is stated for a single object
-- universe; re-fix `D` at `C`'s universe `u₁` here.  (The §2.218 assembly uses instead the
-- cross-universe image-reflection variant `relMap_faithful_of_reflects` below.)
variable {D : Type u₁} [Cat.{v} D] [RegularCategory C] [RegularCategory D]
  {F : Functor C D}

/-- One direction of faithfulness: a `RelLe` between the `F`-image relations descends to a `RelLe`
    upstairs, given `F` full+faithful and split covers in `D`. -/
theorem relImageObj_reflect_le (hreg : RegularFunctor F)
    (hfull : Full F) (hfaith : Faithful F)
    (hsplit : ∀ {X Y : D} (e : X ⟶ Y), Cover e → ∃ s : Y ⟶ X, s ≫ e = Cat.id Y)
    {A B : C} {R S : BinRel C A B}
    (h : RelLe (relImageObj hreg R) (relImageObj hreg S)) : RelLe R S := by
  obtain ⟨eR, _, heRA, heRB⟩ := relImageObj_cover hreg R
  obtain ⟨eS, heScov, heSA, heSB⟩ := relImageObj_cover hreg S
  obtain ⟨⟨k, hkA, hkB⟩⟩ := h
  obtain ⟨sS, hsS⟩ := hsplit eS heScov
  -- g : F.obj R.src → F.obj S.src with the F-image leg equations
  let g : F.obj R.src ⟶ F.obj S.src := eR ≫ k ≫ sS
  have hgA : g ≫ F.map S.colA = F.map R.colA := by
    show (eR ≫ k ≫ sS) ≫ F.map S.colA = F.map R.colA
    have hsSA : sS ≫ F.map S.colA = (relImageObj hreg S).colA := by
      rw [← heSA, ← Cat.assoc, hsS, Cat.id_comp]
    rw [Cat.assoc, Cat.assoc, hsSA, hkA, heRA]
  have hgB : g ≫ F.map S.colB = F.map R.colB := by
    show (eR ≫ k ≫ sS) ≫ F.map S.colB = F.map R.colB
    have hsSB : sS ≫ F.map S.colB = (relImageObj hreg S).colB := by
      rw [← heSB, ← Cat.assoc, hsS, Cat.id_comp]
    rw [Cat.assoc, Cat.assoc, hsSB, hkB, heRB]
  -- fullness lifts g to `F h`
  obtain ⟨h, hh⟩ := hfull g
  refine ⟨⟨h, ?_, ?_⟩⟩
  · -- h ≫ S.colA = R.colA, by faithfulness from F(h ≫ S.colA) = F.obj R.colA
    apply hfaith.1
    rw [F.map_comp, hh, hgA]
  · apply hfaith.1
    rw [F.map_comp, hh, hgB]

/-- **§2.218 (2b) — `Rel(F)` is faithful** (full+faithful `F`, split covers in `D`):
    `hreg.relMap x = hreg.relMap y ⟹ x = y`. -/
theorem RegularFunctor.relMap_faithful (hreg : RegularFunctor F)
    (hfull : Full F) (hfaith : Faithful F)
    (hsplit : ∀ {X Y : D} (e : X ⟶ Y), Cover e → ∃ s : Y ⟶ X, s ≫ e = Cat.id Y)
    {A B : C} (x y : BinRelQuot (𝒞 := C) A B)
    (hxy : hreg.relMap x = hreg.relMap y) : x = y := by
  refine Quotient.inductionOn₂ x y (fun R S hRS => ?_) hxy
  have heq : relClass (relImageObj hreg R) = relClass (relImageObj hreg S) := hRS
  obtain ⟨hle, hge⟩ := Quotient.exact heq
  exact Quotient.sound
    ⟨relImageObj_reflect_le hreg hfull hfaith hsplit hle,
     relImageObj_reflect_le hreg hfull hfaith hsplit hge⟩

end SameUniverseFaithful

/-! ### §2.218 (2b′) — Cross-universe faithfulness of `Rel(F)` via image-reflection

  The §2.218 assembly's `F = homRep ‾Map A : ‾Map A → Set^|‾Map A|` is faithful and reflects
  monos, but is NOT full, and crosses universes (`Type u → Type (u+1)`).  The fullness-based
  `relMap_faithful` does not apply.  Instead we use that a `BinRel` span is already JOINTLY MONIC
  (its own image), so a `RelHom R S` is a *factorization of monos* `pair R.colA R.colB` through
  `pair S.colA S.colB` in `A × B`.  A pullback-preserving, iso-reflecting `F` reflects such a
  factorization: pull `pair R` back along the mono `pair S`; `F` carries the §1.56 product-pair to
  the downstairs one (`pres_prod`'s comparison iso), so the downstairs factorization `g` makes
  `F(π₁)` (the pullback projection, monic) a retraction, hence iso; `F` reflecting isos pulls that
  back upstairs to give `π₁` iso and the required leg-map `h := π₁⁻¹ ≫ π₂`. -/

/-- **Mono-factorization reflection** (the engine of `relImageObj_reflect_le_of_reflects`).
    For monos `m : M → X`, `n : N → X` in `C`, if `F` preserves pullbacks + monos and reflects isos,
    then a *downstairs* factorization `g : F.obj M → F.obj N` with `g ≫ F n = F m` reflects to an *upstairs*
    factorization `h : M → N` with `h ≫ n = m`.  Pullback of `m` along the mono `n` gives a monic
    projection `π₁ : P → M`; the downstairs cone `(F.obj M, id, g)` factors through `F.obj P`, exhibiting a
    section of `F π₁`, so `F π₁` (monic) is iso; reflecting the iso makes `π₁` iso upstairs. -/
theorem monoFactor_reflect (hreg : RegularFunctor F)
    (hreflIso : ∀ {X Y : C} (f : X ⟶ Y), IsIso (F.map f) → IsIso f)
    {M N X : C} {m : M ⟶ X} {n : N ⟶ X} (hn : Monic n)
    (g : F.obj M ⟶ F.obj N) (hg : g ≫ F.map n = F.map m) :
    ∃ h : M ⟶ N, h ≫ n = m := by
  -- pullback of `m` along the mono `n`
  let pb := HasPullbacks.has m n
  have hπ₁mono : Monic pb.cone.π₁ := mono_pullback m n hn pb
  -- downstairs cone `(F.obj M, id, g)` over the cospan `(F m, F n)`
  have hdw : Cat.id (F.obj M) ≫ F.map m = g ≫ F.map n := by rw [Cat.id_comp, hg]
  let dcone : Cone (F.map m) (F.map n) := ⟨F.obj M, Cat.id (F.obj M), g, hdw⟩
  have hFpb := hreg.pres_pullback m n pb.cone pb.cone_isPullback
  obtain ⟨u, ⟨hu₁, _hu₂⟩, _⟩ := hFpb dcone
  -- `u ≫ F π₁ = id_{F.obj M}`, so `u` is a section of `F π₁`
  have hFπ₁mono : Monic (F.map pb.cone.π₁) := hreg.pres_mono hπ₁mono
  -- a monic with a section is an iso
  have hFπ₁iso : IsIso (F.map pb.cone.π₁) := by
    refine ⟨u, ?_, hu₁⟩
    apply hFπ₁mono (F.map pb.cone.π₁ ≫ u) (Cat.id _)
    rw [Cat.assoc, hu₁, Cat.comp_id, Cat.id_comp]
  obtain ⟨π₁inv, _hpi1, hpi2⟩ := hreflIso pb.cone.π₁ hFπ₁iso
  refine ⟨π₁inv ≫ pb.cone.π₂, ?_⟩
  -- `(π₁⁻¹ ≫ π₂) ≫ n = π₁⁻¹ ≫ (π₁ ≫ m) = m`  (using the pullback square `π₂ ≫ n = π₁ ≫ m`)
  rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hpi2, Cat.id_comp]

/-- The §1.56 product-pair `pair (F a) (F b)` factors the `F`-image of the upstairs pair through
    the product-comparison iso: `F.obj (pair a b) ≫ φ = pair (F a) (F b)`, where
    `φ = pair (F fst) (F snd) : F.obj (A×B) → F.obj A × F.obj B`. -/
theorem map_pair_comp_comparison {A B Z : C} (a : Z ⟶ A) (b : Z ⟶ B) :
    F.map (pair a b) ≫ pair (F.map (fst (A := A) (B := B))) (F.map (snd (A := A) (B := B)))
      = pair (F.map a) (F.map b) := by
  refine pair_uniq (F.map a) (F.map b)
    (F.map (pair a b) ≫ pair (F.map (fst (A := A) (B := B))) (F.map (snd (A := A) (B := B))))
    ?_ ?_
  · rw [Cat.assoc, fst_pair, ← F.map_comp, fst_pair]
  · rw [Cat.assoc, snd_pair, ← F.map_comp, snd_pair]

/-- **§2.218 (2b′) reflection step.**  A `RelLe` between the `F`-image relations descends to a
    `RelLe` upstairs, using only that `F` preserves pullbacks/monos/products and reflects isos — no
    fullness.  The leg-map produced by the cover-split chase is converted (via `monoFactor_reflect`
    on the jointly-monic span `pair S.colA S.colB`) into the required `RelHom R S`. -/
theorem relImageObj_reflect_le_of_reflects (hreg : RegularFunctor F)
    (hreflIso : ∀ {X Y : C} (f : X ⟶ Y), IsIso (F.map f) → IsIso f)
    (hsplit : ∀ {X Y : D} (e : X ⟶ Y), Cover e → ∃ s : Y ⟶ X, s ≫ e = Cat.id Y)
    {A B : C} {R S : BinRel C A B}
    (h : RelLe (relImageObj hreg R) (relImageObj hreg S)) : RelLe R S := by
  obtain ⟨eR, _, heRA, heRB⟩ := relImageObj_cover hreg R
  obtain ⟨eS, heScov, heSA, heSB⟩ := relImageObj_cover hreg S
  obtain ⟨⟨k, hkA, hkB⟩⟩ := h
  obtain ⟨sS, hsS⟩ := hsplit eS heScov
  -- the leg-map `g : F.obj R.src → F.obj S.src` carrying `F.obj R.colA/colB` (fullness-FREE)
  let g : F.obj R.src ⟶ F.obj S.src := eR ≫ k ≫ sS
  have hsSA : sS ≫ F.map S.colA = (relImageObj hreg S).colA := by
    rw [← heSA, ← Cat.assoc, hsS, Cat.id_comp]
  have hsSB : sS ≫ F.map S.colB = (relImageObj hreg S).colB := by
    rw [← heSB, ← Cat.assoc, hsS, Cat.id_comp]
  have hgA : g ≫ F.map S.colA = F.map R.colA := by
    show (eR ≫ k ≫ sS) ≫ F.map S.colA = F.map R.colA
    rw [Cat.assoc, Cat.assoc, hsSA, hkA, heRA]
  have hgB : g ≫ F.map S.colB = F.map R.colB := by
    show (eR ≫ k ≫ sS) ≫ F.map S.colB = F.map R.colB
    rw [Cat.assoc, Cat.assoc, hsSB, hkB, heRB]
  -- convert leg equations into the single product-pair factorization `g ≫ F(pair S) = F(pair R)`
  let φ := pair (F.map (fst (A := A) (B := B))) (F.map (snd (A := A) (B := B)))
  have hφiso : IsIso φ := hreg.pres_prod
  obtain ⟨φinv, hφ1, _hφ2⟩ := hφiso
  -- `g ≫ pair (F.obj S.colA) (F.obj S.colB) = pair (F.obj R.colA) (F.obj R.colB)`
  have hgpair : g ≫ pair (F.map S.colA) (F.map S.colB)
      = pair (F.map R.colA) (F.map R.colB) := by
    refine pair_uniq (F.map R.colA) (F.map R.colB)
      (g ≫ pair (F.map S.colA) (F.map S.colB)) ?_ ?_
    · rw [Cat.assoc, fst_pair, hgA]
    · rw [Cat.assoc, snd_pair, hgB]
  -- substitute `pair (F·) (F·) = F(pair ·) ≫ φ` and cancel the iso `φ`
  have hgFpair : g ≫ F.map (pair S.colA S.colB) = F.map (pair R.colA R.colB) := by
    have hSφ := map_pair_comp_comparison (F := F) S.colA S.colB
    have hRφ := map_pair_comp_comparison (F := F) R.colA R.colB
    have : (g ≫ F.map (pair S.colA S.colB)) ≫ φ = F.map (pair R.colA R.colB) ≫ φ := by
      rw [Cat.assoc, hSφ, hgpair, ← hRφ]
    -- cancel `φ` on the right (`φ` iso)
    have hcancel := congrArg (· ≫ φinv) this
    simpa [Cat.assoc, hφ1, Cat.comp_id] using hcancel
  -- `pair S.colA S.colB` is monic; reflect the factorization upstairs
  have hnmono : Monic (pair S.colA S.colB) :=
    monic_pair_of_monicPair S.colA S.colB S.isMonicPair
  obtain ⟨hmap, hfac⟩ := monoFactor_reflect hreg hreflIso hnmono g hgFpair
  refine ⟨⟨hmap, ?_, ?_⟩⟩
  · -- `hmap ≫ S.colA = R.colA` from `hmap ≫ pair S = pair R`
    have := congrArg (· ≫ fst) hfac
    simpa [Cat.assoc, fst_pair] using this
  · have := congrArg (· ≫ snd) hfac
    simpa [Cat.assoc, snd_pair] using this

/-- **§2.218 (2b′) — `Rel(F)` is faithful for a NON-FULL `F`** that preserves the regular
    structure, reflects isos, and has split covers downstairs (the `homRep ‾Map A` case).
    `hreg.relMap x = hreg.relMap y ⟹ x = y`. -/
theorem RegularFunctor.relMap_faithful_of_reflects (hreg : RegularFunctor F)
    (hreflIso : ∀ {X Y : C} (f : X ⟶ Y), IsIso (F.map f) → IsIso f)
    (hsplit : ∀ {X Y : D} (e : X ⟶ Y), Cover e → ∃ s : Y ⟶ X, s ≫ e = Cat.id Y)
    {A B : C} (x y : BinRelQuot (𝒞 := C) A B)
    (hxy : hreg.relMap x = hreg.relMap y) : x = y := by
  refine Quotient.inductionOn₂ x y (fun R S hRS => ?_) hxy
  have heq : relClass (relImageObj hreg R) = relClass (relImageObj hreg S) := hRS
  obtain ⟨hle, hge⟩ := Quotient.exact heq
  exact Quotient.sound
    ⟨relImageObj_reflect_le_of_reflects hreg hreflIso hsplit hle,
     relImageObj_reflect_le_of_reflects hreg hreflIso hsplit hge⟩

/-- **§2.218 — the packaged faithful allegory morphism `Rel(F)`.**  For a `RegularFunctor F` that
    reflects isos and whose covers split downstairs (NOT necessarily full), the allegory morphism
    `Rel(F) = relAllegoryHom` is `AllegoryFunctor.Faithful`.  This is the form consumed by the
    §2.218 assembly (`F = homRep ‾Map A`). -/
theorem RegularFunctor.relAllegoryHom_faithful_of_reflects (hreg : RegularFunctor F)
    (hreflIso : ∀ {X Y : C} (f : X ⟶ Y), IsIso (F.map f) → IsIso f)
    (hsplit : ∀ {X Y : D} (e : X ⟶ Y), Cover e → ∃ s : Y ⟶ X, s ≫ e = Cat.id Y) :
    hreg.relAllegoryHom.Faithful :=
  fun {_a _b} R S h => hreg.relMap_faithful_of_reflects hreflIso hsplit R S h

end RelFunctor

/-! ## §2.218 BRICK 3 — the power of an allegory `(I → 𝒜)`

  For any allegory `𝒜` and index type `I`, the functor category `𝒜^I` is again an allegory,
  with ALL operations computed POINTWISE (`(R ≫ S) i = R i ≫ S i`, `(R°) i = (R i)°`,
  `(R ∩ S) i = R i ∩ S i`).  Every allegory axiom is a *pointwise* equation, so it lifts by
  `funext` from the fibre `𝒜`.

  We host the structure on a type synonym `PowerObj I 𝒜 := I → 𝒜` to keep the new `Cat`/`Allegory`
  instances from clashing with the bespoke `Cat (I → Type w)` (`powerCat`, S1_55) — `Set^I`'s own
  category structure stays the canonical one on `I → Type w`, while the allegory of a *power of an
  allegory* lives on `PowerObj`.  (For the §2.218 assembly the relevant power is `Rel(Set)^I`, an
  allegory-power, so this synonym is exactly the carrier we want.) -/

namespace PowerAllegory

/-- The carrier of the power allegory `𝒜^I`: an `I`-indexed family of objects of `𝒜`. -/
def PowerObj (I : Type w) (𝒜 : Type u) : Type (max w u) := I → 𝒜

variable {I : Type w} {𝒜 : Type u}

/-- A morphism of `𝒜^I` is a pointwise family of `𝒜`-morphisms. -/
def PowerHom [Cat.{v} 𝒜] (X Y : PowerObj I 𝒜) : Type (max w v) := ∀ i, X i ⟶ Y i

/-- **§2.218 BRICK 3 — the power category `𝒜^I`.**  Objects `I → 𝒜`, homs pointwise families,
    composition/identity pointwise.  All four category laws are pointwise (`funext`). -/
instance powerCatAlg [Cat.{v} 𝒜] : Cat.{max w v} (PowerObj I 𝒜) where
  Hom X Y := PowerHom X Y
  id X := fun i => Cat.id (X i)
  comp R S := fun i => R i ≫ S i
  id_comp R := funext fun i => Cat.id_comp (R i)
  comp_id R := funext fun i => Cat.comp_id (R i)
  assoc R S T := funext fun i => Cat.assoc (R i) (S i) (T i)

@[simp] theorem power_comp_apply [Cat.{v} 𝒜] {X Y Z : PowerObj I 𝒜}
    (R : X ⟶ Y) (S : Y ⟶ Z) (i : I) : (R ≫ S) i = R i ≫ S i := rfl

@[simp] theorem power_id_apply [Cat.{v} 𝒜] (X : PowerObj I 𝒜) (i : I) :
    (Cat.id X) i = Cat.id (X i) := rfl

/-- **§2.218 BRICK 3 — the power allegory `𝒜^I`.**  Reciprocation and intersection pointwise;
    every allegory equation lifts from the fibre by `funext`. -/
instance powerAllegory [Allegory.{v} 𝒜] : Allegory.{max w v} (PowerObj I 𝒜) where
  recip {_a _b} R := fun i => (R i)°
  inter {_a _b} R S := fun i => R i ∩ S i
  recip_recip R := funext fun i => Allegory.recip_recip (R i)
  recip_comp R S := funext fun i => Allegory.recip_comp (R i) (S i)
  recip_inter R S := funext fun i => Allegory.recip_inter (R i) (S i)
  inter_idem R := funext fun i => Allegory.inter_idem (R i)
  inter_comm R S := funext fun i => Allegory.inter_comm (R i) (S i)
  inter_assoc R S T := funext fun i => Allegory.inter_assoc (R i) (S i) (T i)
  semidistrib R S T := funext fun i => Allegory.semidistrib (R i) (S i) (T i)
  modular R S T := funext fun i => Allegory.modular (R i) (S i) (T i)

@[simp] theorem power_recip_apply [Allegory.{v} 𝒜] {X Y : PowerObj I 𝒜}
    (R : X ⟶ Y) (i : I) : (R°) i = (R i)° := rfl

@[simp] theorem power_inter_apply [Allegory.{v} 𝒜] {X Y : PowerObj I 𝒜}
    (R S : X ⟶ Y) (i : I) : (R ∩ S) i = R i ∩ S i := rfl

end PowerAllegory

/-! ## §2.218 BRICK 2c — `homRep 𝒞` packaged as a `RegularFunctor`

  Combine the five §1.62 `HomRepRegular` preservation lemmas (`homRep_preserves_prod`/
  `_pullbacks`/`_covers`/`_images`, and §1.55 `homRep_preserves_mono`) into the cross-universe
  `RegularFunctor (homRepFunctor 𝒞) : 𝒞 → (𝒞 → Type u)`.  Requires `𝒞` CAPITAL — every cover splits
  (`hproj`), the §1.543 situation — for the cover- and image-preservation. -/

/-- **§2.218 (2c).**  When every cover in the regular category `𝒞` splits (`𝒞` capital, the
    §1.543 case), the Henkin–Lubkin representation `homRep 𝒞 : 𝒞 → Set^|𝒞|` is a regular functor. -/
theorem homRep_regularFunctor {𝒞 : Type u} [Cat.{u} 𝒞] [RegularCategory 𝒞]
    (hproj : ∀ C : 𝒞, ∀ {P : 𝒞} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C) :
    RelFunctor.RegularFunctor (homRepFunctor 𝒞) where
  pres_prod := HomRepRegular.homRep_preserves_prod
  pres_pullback := HomRepRegular.homRep_preserves_pullbacks
  pres_covers := HomRepRegular.homRep_preserves_covers hproj
  pres_mono := homRep_preserves_mono 𝒞
  pres_image := HomRepRegular.homRep_preserves_images hproj

/-! ## §2.218 R2 — the carrier bridge `𝒜 ≅ Rel(Map 𝒜)` (span encoding)

  The §2.218 machinery consumes `RelObj (MapObj 𝒜)`, the allegory of (mutual-containment classes
  of) jointly-monic spans in `Map 𝒜`.  §2.148 `relMap_allegoryEquiv` gives `RelMapObj 𝒜 ≅ 𝒜`,
  but its homs are the *tabular morphisms* of `𝒜`, not spans.  We bridge the two encodings with
  the `relOf` dictionary (`MapCat`): `relOf : BinRel (Map 𝒜) a b → (a ⟶ b)` carries a span to its
  underlying allegory morphism `colA°≫colB`, respecting `≫`/`°`/`id`/`∩` (`relOf_compose`,
  `relOf_reciprocal`, `relOf_graph`, `relOf_inter`) and is an order-iso onto its image
  (`relOf_le_of_relLe` / `relLe_of_relOf_le`).  This packages a faithful
  `AllegoryFunctor 𝒜 (RelObj (Map 𝒜))` (the §2.218 `bridge`). -/

section CarrierBridge

open Freyd.Alg

-- §2.154: the carrier bridge needs only TABULAR + UNITARY (the `Map` regular structure was
-- weakened accordingly in `S2_147_MapCat`); distributivity is irrelevant here.
variable (𝒜 : Type u) [Freyd.Alg.TabularUnitaryAllegory 𝒜]

/-- The §2.218 carrier `Rel(Map 𝒜)`, with all instances pinned to `mapCat` (avoiding the
    `MapObj 𝒜 = 𝒜` `Cat`-diamond: the canonical `Cat` on objects of `Map 𝒜` is `mapCat`, not the
    allegory's `toCat`).  `RM 𝒜 := RelObj (MapObj 𝒜)`. -/
abbrev RM : Type u := RelObj (MapObj 𝒜)

-- We must NOT register a `local instance : Cat (MapObj 𝒜)`: since `MapObj 𝒜 = 𝒜` (abbrev), that
-- would hijack the SOURCE allegory homs `a ⟶ b` (`tabSpan`'s `R`, `bridgeFunctor.map`'s `R`) and
-- break `TabularAllegory.tabular R` / `relOf`.  Instead provide ONLY the target `Rel(Map 𝒜)`
-- allegory the bridge needs, with its `Cat`/`RegularCategory` args pinned to the `mapCat` ones
-- (the `MapObj 𝒜 = 𝒜` `Cat`-diamond fix from MapCat's convention note).  Everywhere a
-- `BinRel`/`BinRelQuot`/`relClass`/`RelLe` of `MapObj 𝒜` appears below, we `@`-pin `mapCat`
-- (and `mapHasBinaryProducts`/`mapHasPullbacks`) the same way §2.217 in MapCat does.
noncomputable instance instAllegRM : Freyd.Alg.Allegory.{max u v} (RM 𝒜) :=
  @relAllegory (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) (Freyd.Alg.mapRegularCategory (A := 𝒜))

/-- `relOf` is constant on a mutual-containment class (`relOf_le_of_relLe` both ways). -/
private theorem relOf_respects {a b : MapObj 𝒜}
    {R S : @BinRel (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) a b}
    (h : @RelLe (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) a b R S ∧
         @RelLe (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) a b S R) :
    Freyd.Alg.relOf R = Freyd.Alg.relOf S :=
  le_antisymm (Freyd.Alg.relOf_le_of_relLe h.1) (Freyd.Alg.relOf_le_of_relLe h.2)

/-- `relOf` lifted to mutual-containment classes (`BinRelQuot` = `Rel(Map 𝒜)` hom). -/
private noncomputable def relOfQuot {a b : MapObj 𝒜}
    (x : @BinRelQuot (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜))
          Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b) :
    @Cat.Hom 𝒜 Freyd.Alg.Allegory.toCat a b :=
  Quotient.liftOn x Freyd.Alg.relOf (fun _ _ h => relOf_respects 𝒜 h)

@[simp] private theorem relOfQuot_mk {a b : MapObj 𝒜}
    (R : @BinRel (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) a b) :
    relOfQuot 𝒜 (@relClass (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜))
      Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b R)
      = Freyd.Alg.relOf R := rfl

/-- The tabulating span of an allegory morphism `R : a ⟶ b`: the `BinRel (Map 𝒜)` table
    `⟨c; f, g⟩` of a tabulation `R = f°≫g` (`TabularAllegory.tabular`), joint-monic by §2.141. -/
noncomputable def tabSpan {a b : 𝒜} (R : a ⟶ b) :
    @BinRel (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) a b :=
  let t := TabularAllegory.tabular (𝒜 := 𝒜) R
  @BinRel.mk (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜)) a b t.choose
    ⟨t.choose_spec.choose, t.choose_spec.choose_spec.choose_spec.1⟩
    ⟨t.choose_spec.choose_spec.choose, t.choose_spec.choose_spec.choose_spec.2.1⟩
    (Freyd.Alg.mapMonicPair_of_tab _ _ t.choose_spec.choose_spec.choose_spec.2.2.2)

/-- `relOf (tabSpan R) = R`: the span tabulates `R`, so its underlying morphism is `R`. -/
theorem relOf_tabSpan {a b : 𝒜} (R : a ⟶ b) :
    Freyd.Alg.relOf (tabSpan 𝒜 R) = R :=
  (TabularAllegory.tabular (𝒜 := 𝒜) R).choose_spec.choose_spec.choose_spec.2.2.1.symm

/-- The bridge `Φ : 𝒜 ⟶ Rel(Map 𝒜)`: object `a ↦ ⟨a⟩`, hom `R ↦ [tabSpan R]`.
    Each functor law is checked through `relOf` (its left inverse): `relOf` of both sides agree
    by `relOf_tabSpan` + the dictionary (`relOf_graph`/`_compose`/`_reciprocal`/`_inter`), so the
    classes are equal (`relLe_of_relOf_le` lifts the morphism equality back to mutual
    containment). -/
noncomputable def bridgeFunctor :
    Freyd.Alg.AllegoryFunctor 𝒜 (RM 𝒜) where
  obj a := ⟨a⟩
  map {a b} R := @relClass (MapObj 𝒜) (Freyd.Alg.mapCat (𝒜 := 𝒜))
    Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b (tabSpan 𝒜 R)
  map_id a := by
    apply Quotient.sound
    refine ⟨relLe_of_relOf_le ?_, relLe_of_relOf_le ?_⟩ <;>
      rw [relOf_tabSpan, Freyd.Alg.relOf_graph] <;> exact le_refl _
  map_comp {a b c} R S := by
    apply Quotient.sound
    refine ⟨relLe_of_relOf_le ?_, relLe_of_relOf_le ?_⟩ <;>
      rw [Freyd.Alg.relOf_compose, relOf_tabSpan, relOf_tabSpan, relOf_tabSpan] <;>
      exact le_refl _
  map_recip {a b} R := by
    apply Quotient.sound
    refine ⟨relLe_of_relOf_le ?_, relLe_of_relOf_le ?_⟩ <;>
      rw [Freyd.Alg.relOf_reciprocal, relOf_tabSpan, relOf_tabSpan] <;> exact le_refl _
  map_inter {a b} R S := by
    apply Quotient.sound
    refine ⟨relLe_of_relOf_le ?_, relLe_of_relOf_le ?_⟩ <;>
      rw [Freyd.Alg.relOf_inter, relOf_tabSpan, relOf_tabSpan, relOf_tabSpan] <;>
      exact le_refl _

/-- **§2.218 R2 — the carrier bridge is FAITHFUL.**  `relOf (bridgeFunctor.map R) = R`
    (`relOf_tabSpan`), so `bridgeFunctor.map R = bridgeFunctor.map S` ⟹
    `R = relOf (…R) = relOf (…S) = S`. -/
theorem bridgeFunctor_faithful :
    (bridgeFunctor 𝒜).Faithful := by
  intro a b R S h
  have hR : relOfQuot 𝒜 ((bridgeFunctor 𝒜).map R) = R := relOf_tabSpan 𝒜 R
  have hS : relOfQuot 𝒜 ((bridgeFunctor 𝒜).map S) = S := relOf_tabSpan 𝒜 S
  rw [← hR, ← hS, h]

end CarrierBridge

end Freyd
