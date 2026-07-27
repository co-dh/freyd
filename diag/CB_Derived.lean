/-
  `diag.CB_Derived` — the operations AOP needs, DERIVED from `CartBicat`.  Nothing here is an axiom.

  functorialSemanticsForRelationalTheories.pdf §4, pp. 18–22.  The meet `Δ;(R ⊗ S);∇` is the
  paper's `∩` (p. 22, "every hom-set is a meet semi-lattice") and `⊤ := !;?` is its unit.  Both are
  defined at a single object, so neither needs an associator — that is why they come before the
  wire-bending converse, which does.
-/
import diag.CB

universe v u

namespace Freyd.Diag

open Freyd
open scoped SymMonCat
open CartBicat

variable {𝒞 : Type u} [CartBicat.{v} 𝒞]

/-- The CONVOLUTION `Δ;(R ⊗ S);∇`
    (functorialSemanticsForRelationalTheories.pdf p. 22).  Copy the input, run `R` and `S` on the
    two copies, then merge — the merge forces the two results to coincide, so this is `R ∩ S`. -/
def meet {a b : 𝒞} (R S : a ⟶ b) : a ⟶ b := Δ a ≫ (R ⊗ₕ S) ≫ ∇ b

/-- `⊤ := !;?`, the maximum arrow: discard everything, then create everything.  The unit of
    `meet` (functorialSemanticsForRelationalTheories.pdf p. 22). -/
def top (a b : 𝒞) : a ⟶ b := «!» a ≫ «?» b

/-- Every arrow is below `⊤`.  Lax counit (43) sends `R;!` under `!`, and (40) supplies the `?`. -/
theorem le_top {a b : 𝒞} (R : a ⟶ b) : R ≤ (top a b) := by
  -- `R = R;𝟙 ≤ R;(!;?) = (R;!);? ≤ !;? = ⊤`.
  have h1 : (R ≫ 𝟙 b) ≤ (R ≫ «!» b ≫ «?» b) :=
    OrderedCat.comp_mono (OrderedCat.le_refl R) («𝟙_≤_!?» b)
  have h2 : ((R ≫ «!» b) ≫ «?» b) ≤ («!» a ≫ «?» b) :=
    OrderedCat.comp_mono (lax_! R) (OrderedCat.le_refl («?» b))
  rw [Cat.comp_id] at h1
  rw [Cat.assoc] at h2
  exact OrderedCat.le_trans h1 h2

/-- `⊤` is the unit of the meet: `R ∩ ⊤ = R`
    (functorialSemanticsForRelationalTheories.pdf p. 22, unitality in Lemma 4.11).  The `⊤` strand
    is discarded by the counit law (10) and re-absorbed by the unit law (7); `runit_nat` is what
    moves `R` past the unitor. -/
theorem meet_top {a b : 𝒞} (R : a ⟶ b) : meet R (top a b) = R := by
  -- Stage the `⊗`: `R ⊗ (!;?) = ((𝟙 ⊗ !) ; (R ⊗ 𝟙)) ; (𝟙 ⊗ ?)`.
  have hR : (R ⊗ₕ («!» a ≫ «?» b))
      = ((𝟙 a ⊗ₕ «!» a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))) ≫ (𝟙 b ⊗ₕ «?» b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  -- `(𝟙 ⊗ ?);∇ = ρ`, read off the unit law (7) by cancelling `ρ ; ρ⁻¹ = 𝟙`.
  have hun : (𝟙 b ⊗ₕ «?» b) ≫ ∇ b = SymMonCat.runit b := by
    have h := «∇_unit» (𝒞 := 𝒞) b
    calc (𝟙 b ⊗ₕ «?» b) ≫ ∇ b
        = 𝟙 (b ⊗ 𝕀) ≫ (𝟙 b ⊗ₕ «?» b) ≫ ∇ b := by rw [Cat.id_comp]
      _ = (SymMonCat.runit b ≫ SymMonCat.runitInv b) ≫ (𝟙 b ⊗ₕ «?» b) ≫ ∇ b := by
            rw [SymMonCat.runit_inv]
      _ = SymMonCat.runit b ≫ (SymMonCat.runitInv b ≫ (𝟙 b ⊗ₕ «?» b) ≫ ∇ b) := by
            rw [Cat.assoc]
      _ = SymMonCat.runit b ≫ 𝟙 b := by rw [h]
      _ = SymMonCat.runit b := Cat.comp_id _
  dsimp [meet, top]
  calc Δ a ≫ (R ⊗ₕ («!» a ≫ «?» b)) ≫ ∇ b
      = Δ a ≫ (((𝟙 a ⊗ₕ «!» a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))) ≫ (𝟙 b ⊗ₕ «?» b)) ≫ ∇ b := by rw [hR]
    _ = Δ a ≫ (𝟙 a ⊗ₕ «!» a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ (𝟙 b ⊗ₕ «?» b) ≫ ∇ b := by
          simp only [Cat.assoc]
    _ = Δ a ≫ (𝟙 a ⊗ₕ «!» a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.runit b := by rw [hun]
    _ = Δ a ≫ (𝟙 a ⊗ₕ «!» a) ≫ SymMonCat.runit a ≫ R := by rw [SymMonCat.runit_nat]
    _ = (Δ a ≫ (𝟙 a ⊗ₕ «!» a) ≫ SymMonCat.runit a) ≫ R := by simp only [Cat.assoc]
    _ = 𝟙 a ≫ R := by rw [Δ_counit]
    _ = R := Cat.id_comp _

/-- Convolution is monotone in both arguments — immediate from `comp_mono` and `tensHom_mono`, and
    the reason `∩` needs no separate monotonicity axiom. -/
theorem meet_mono {a b : 𝒞} {R R' S S' : a ⟶ b}
    (hR : R ≤ R') (hS : S ≤ S') :
    (meet R S) ≤ (meet R' S') := by
  dsimp [meet]
  exact OrderedCat.comp_mono (OrderedCat.le_refl _)
    (OrderedCat.comp_mono (SymMonCat.tensHom_mono hR hS) (OrderedCat.le_refl _))

/-- `R ∩ S ≤ R`: the first half of the greatest-lower-bound property
    (functorialSemanticsForRelationalTheories.pdf p. 22).  Weaken the `S` strand all the way to `⊤`
    by `le_top`, then `meet_top` collapses it. -/
theorem meet_le_left {a b : 𝒞} (R S : a ⟶ b) :
    (meet R S) ≤ R := by
  have h := meet_mono (OrderedCat.le_refl R) (le_top S)
  rw [meet_top] at h
  exact h

/-- The meet is symmetric, by cocommutativity (9) on the copy and commutativity (6) on the
    merge, bridged by naturality of the symmetry. -/
theorem meet_comm {a b : 𝒞} (R S : a ⟶ b) : meet R S = meet S R := by
  dsimp [meet]
  calc Δ a ≫ (R ⊗ₕ S) ≫ ∇ b
      = (Δ a ≫ SymMonCat.swap a a) ≫ (R ⊗ₕ S) ≫ ∇ b := by rw [Δ_comm]
    _ = Δ a ≫ (SymMonCat.swap a a ≫ (R ⊗ₕ S)) ≫ ∇ b := by simp only [Cat.assoc]
    _ = Δ a ≫ ((S ⊗ₕ R) ≫ SymMonCat.swap b b) ≫ ∇ b := by rw [← SymMonCat.swap_nat]
    _ = Δ a ≫ (S ⊗ₕ R) ≫ SymMonCat.swap b b ≫ ∇ b := by simp only [Cat.assoc]
    _ = Δ a ≫ (S ⊗ₕ R) ≫ ∇ b := by rw [«∇_comm»]

/-- `(R ∩ S) ∩ T` with the left-leaning copy and merge trees exposed, ready for (8) and (6). -/
theorem meet_left_staged {a b : 𝒞} (R S T : a ⟶ b) :
    meet (meet R S) T
      = Δ a ≫ (Δ a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by
  dsimp [meet]
  have hsplit : ((Δ a ≫ (R ⊗ₕ S) ≫ ∇ b) ⊗ₕ T)
      = (Δ a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (∇ b ⊗ₕ 𝟙 b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  rw [hsplit]
  simp only [Cat.assoc]

/-- The mirror staging for `R ∩ (S ∩ T)`, right-leaning. -/
theorem meet_right_staged {a b : 𝒞} (R S T : a ⟶ b) :
    meet R (meet S T)
      = Δ a ≫ (𝟙 a ⊗ₕ Δ a) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ ∇ b) ≫ ∇ b := by
  dsimp [meet]
  have hsplit : (R ⊗ₕ (Δ a ≫ (S ⊗ₕ T) ≫ ∇ b))
      = (𝟙 a ⊗ₕ Δ a) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ ∇ b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  rw [hsplit]
  simp only [Cat.assoc]

/-- `R ∩ S ≤ S`, the other half of the greatest-lower-bound property. -/
theorem meet_le_right {a b : 𝒞} (R S : a ⟶ b) :
    (meet R S) ≤ S := by
  rw [meet_comm]
  exact meet_le_left S R

/-- `(R ∩ S) ∩ T = R ∩ (S ∩ T)` — Freyd's `inter_assoc` (§2.11), derived.  Both staged forms are
    normalised to `Δ;(𝟙 ⊗ Δ);(R ⊗ (S ⊗ T));(𝟙 ⊗ ∇);∇`: coassociativity (8) turns the left copy
    tree into the right one, associativity (6) does the same for the merge tree, and
    `tensAssocInv_nat` carries the re-bracketing past `(R ⊗ S) ⊗ T` in between. -/
theorem meet_assoc {a b : 𝒞} (R S T : a ⟶ b) :
    meet (meet R S) T = meet R (meet S T) := by
  rw [meet_left_staged, meet_right_staged]
  -- Insert `α ; α⁻¹ = 𝟙` after the left copy tree, then apply (8), naturality, and (6).
  calc Δ a ≫ (Δ a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b
      = Δ a ≫ (Δ a ⊗ₕ 𝟙 a) ≫ (SymMonCat.tensAssoc a a a ≫ SymMonCat.tensAssocInv a a a)
          ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by
        rw [SymMonCat.tensAssoc_inv, Cat.id_comp]
    _ = (Δ a ≫ (Δ a ⊗ₕ 𝟙 a) ≫ SymMonCat.tensAssoc a a a)
          ≫ SymMonCat.tensAssocInv a a a ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by
        simp only [Cat.assoc]
    _ = (Δ a ≫ (𝟙 a ⊗ₕ Δ a))
          ≫ SymMonCat.tensAssocInv a a a ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by
        rw [Δ_assoc]
    _ = Δ a ≫ (𝟙 a ⊗ₕ Δ a)
          ≫ (SymMonCat.tensAssocInv a a a ≫ ((R ⊗ₕ S) ⊗ₕ T)) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by
        simp only [Cat.assoc]
    _ = Δ a ≫ (𝟙 a ⊗ₕ Δ a)
          ≫ ((R ⊗ₕ (S ⊗ₕ T)) ≫ SymMonCat.tensAssocInv b b b) ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by
        rw [tensAssocInv_nat]
    _ = Δ a ≫ (𝟙 a ⊗ₕ Δ a) ≫ (R ⊗ₕ (S ⊗ₕ T))
          ≫ SymMonCat.tensAssocInv b b b ≫ (∇ b ⊗ₕ 𝟙 b) ≫ ∇ b := by simp only [Cat.assoc]
    _ = Δ a ≫ (𝟙 a ⊗ₕ Δ a) ≫ (R ⊗ₕ (S ⊗ₕ T))
          ≫ SymMonCat.tensAssocInv b b b ≫ SymMonCat.tensAssoc b b b
          ≫ (𝟙 b ⊗ₕ ∇ b) ≫ ∇ b := by rw [«∇_assoc»]
    _ = Δ a ≫ (𝟙 a ⊗ₕ Δ a) ≫ (R ⊗ₕ (S ⊗ₕ T))
          ≫ (SymMonCat.tensAssocInv b b b ≫ SymMonCat.tensAssoc b b b)
          ≫ (𝟙 b ⊗ₕ ∇ b) ≫ ∇ b := by simp only [Cat.assoc]
    _ = Δ a ≫ (𝟙 a ⊗ₕ Δ a) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ ∇ b) ≫ ∇ b := by
        rw [SymMonCat.inv_tensAssoc, Cat.id_comp]

/-- `R ∩ R = R` — Freyd's `inter_idem` (§2.11), derived.  `≤` is the glb property; `≥` is exactly
    where the lax inequation (42) and the special law meet: copying `R` and running it on both
    strands can only produce more than running it once, and `Δ;∇ = 𝟙` closes the loop. -/
theorem meet_idem {a b : 𝒞} (R : a ⟶ b) : meet R R = R := by
  refine OrderedCat.le_antisymm (meet_le_left R R) ?_
  have h : ((R ≫ Δ b) ≫ ∇ b) ≤ ((Δ a ≫ (R ⊗ₕ R)) ≫ ∇ b) :=
    OrderedCat.comp_mono (lax_Δ R) (OrderedCat.le_refl (∇ b))
  have hL : (R ≫ Δ b) ≫ ∇ b = R := by
    rw [Cat.assoc, special, Cat.comp_id]
  have hR : (Δ a ≫ (R ⊗ₕ R)) ≫ ∇ b = meet R R := by
    dsimp [meet]; rw [Cat.assoc]
  rw [hL, hR] at h
  exact h

/-- `∩` is the GREATEST lower bound: anything below both `S` and `T` is below `S ∩ T`
    (functorialSemanticsForRelationalTheories.pdf p. 22, "every hom-set is a meet semi-lattice").
    With `meet_le_left`/`meet_le_right` this completes the semilattice statement.
    Idempotency is what does the work — `R = R ∩ R ≤ S ∩ T`. -/
theorem meet_glb {a b : 𝒞} {R S T : a ⟶ b}
    (hS : R ≤ S) (hT : R ≤ T) :
    R ≤ (meet S T) := by
  have h := meet_mono hS hT
  rw [meet_idem] at h
  exact h

/-- `X ≤ Y` iff `X ∩ Y = X`.  This is the bridge between `diag`'s PRIMITIVE hom order and Freyd's
    DERIVED one (`Freyd/S2_10.lean`, where `R ⊑ S` is *defined* as `R ∩ S = R`), and it is what
    turns the `≤` forms of semi-distributivity and modularity into the equalities the `Allegory`
    class asks for. -/
theorem meet_eq_left_of_le {a b : 𝒞} {X Y : a ⟶ b} (h : X ≤ Y) :
    meet X Y = X :=
  OrderedCat.le_antisymm (meet_le_left X Y) (meet_glb (OrderedCat.le_refl X) h)

/-- `(R ∩ S)° = R° ∩ S°` — Freyd's `recip_inter` (§2.11).

    NOT proved through Lemma 4.2 (iii) (`(R ⊗ S)° = R° ⊗ S°`), which would need the Frobenius
    structure at the COMPOSITE object `a ⊗ b` — the clause of Carboni & Walters' definition that
    `functorialSemanticsForRelationalTheories.pdf` Def. 4.1 as printed omits (see `diag/CB.lean`'s
    header).  Instead: `∩` is the greatest lower bound, and `°` is an order isomorphism
    (`conv_mono` both ways, `conv_conv`), so it carries greatest lower bounds to greatest lower
    bounds.  This keeps every arrow in the proof at a simple object. -/
theorem conv_inter {a b : 𝒞} (R S : a ⟶ b) :
    conv (meet R S) = meet (conv R) (conv S) := by
  refine OrderedCat.le_antisymm ?_ ?_
  · exact meet_glb (conv_mono (meet_le_left R S))
      (conv_mono (meet_le_right R S))
  · -- `(R° ∩ S°)°` is below both `R` and `S`, hence below `R ∩ S`; apply `°` once more.
    have h1 : (conv (meet (conv R) (conv S))) ≤ R := by
      have h := conv_mono (meet_le_left (conv R) (conv S))
      rwa [conv_conv] at h
    have h2 : (conv (meet (conv R) (conv S))) ≤ S := by
      have h := conv_mono (meet_le_right (conv R) (conv S))
      rwa [conv_conv] at h
    have h3 := conv_mono (meet_glb h1 h2)
    rwa [conv_conv] at h3

/-! ### Maps (functorialSemanticsForRelationalTheories.pdf pp. 20–21)

  The paper gives the map conditions twice.  (SV)/(TOT)/(INJ)/(SUR) on p. 20 are COMONOID
  conditions; (46)–(49) of Lemma 4.4 are ADJOINT conditions; the lemma says the two agree.

  We take the ADJOINT forms as the definitions, because they are literally Freyd's `Simple` and
  `Entire` (`Freyd/S2_10.lean` §2.13) — so a `diag` map and a book map are the same predicate, with
  no translation layer — and because they are the forms every downstream AOP derivation quotes.
  The comonoid forms are recorded beside them under the paper's own equation labels.

  NOT PROVED: Lemma 4.4 itself, that the two presentations agree.  The paper's proof slides a copy
  dot past a `⊗` of two boxes, which needs the Frobenius structure at a COMPOSITE object — the
  clause of Carboni & Walters' definition that Def. 4.1 as printed omits (see `diag/CB.lean`'s
  header).  Nothing below depends on it: every result here uses only the adjoint forms. -/

/-- (46), SINGLE VALUED: `R°R ≤ 𝟙`.  Freyd's `Simple` (§2.13). -/
def SingleValued {a b : 𝒞} (R : a ⟶ b) : Prop := (conv R ≫ R) ≤ (𝟙 b)

/-- (47), TOTAL: `𝟙 ≤ RR°`.  Freyd's `Entire` (§2.13). -/
def Total {a b : 𝒞} (R : a ⟶ b) : Prop := (𝟙 a) ≤ (R ≫ conv R)

/-- (48), INJECTIVE: `RR° ≤ 𝟙`. -/
def Injective {a b : 𝒞} (R : a ⟶ b) : Prop := (R ≫ conv R) ≤ (𝟙 a)

/-- (49), SURJECTIVE: `𝟙 ≤ R°R`. -/
def Surjective {a b : 𝒞} (R : a ⟶ b) : Prop := (𝟙 b) ≤ (conv R ≫ R)

/-- A MAP is single valued and total (p. 20) — equivalently, by `lemma_4_8`, an arrow whose
    converse is its right adjoint. -/
def Map {a b : 𝒞} (R : a ⟶ b) : Prop := SingleValued R ∧ Total R

/-- (SV) as the paper writes it on p. 20: `Δ;(R ⊗ R) ≤ R;Δ`, the reverse of the lax inequation
    (42).  Recorded for reference; `SingleValued` above is the form everything uses. -/
def ineq_SV {a b : 𝒞} (R : a ⟶ b) : Prop :=
  (Δ a ≫ (R ⊗ₕ R)) ≤ (R ≫ Δ b)

/-- (TOT) as the paper writes it: `! ≤ R;!`, the reverse of the lax inequation (43). -/
def ineq_TOT {a b : 𝒞} (R : a ⟶ b) : Prop := («!» a) ≤ (R ≫ «!» b)

/-- (INJ) as the paper writes it: `(R ⊗ R);∇ ≤ ∇;R`. -/
def ineq_INJ {a b : 𝒞} (R : a ⟶ b) : Prop :=
  ((R ⊗ₕ R) ≫ ∇ b) ≤ (∇ a ≫ R)

/-- (SUR) as the paper writes it: `? ≤ ?;R`. -/
def ineq_SUR {a b : 𝒞} (R : a ⟶ b) : Prop := («?» b) ≤ («?» a ≫ R)

/-- COROLLARY 4.5 (p. 21): two maps ordered by `≤` are EQUAL.  Freyd's `map_order_discrete`
    (§2.133).  Insert the unit of `R` on the left of `S` and cancel with the counit of `S`:
    `S = 𝟙S ≤ (RR°)S = R(R°S) ≤ R(S°S) ≤ R𝟙 = R`. -/
theorem cor_4_5 {a b : 𝒞} {R S : a ⟶ b} (hR : Map R) (hS : Map S) (h : R ≤ S) :
    R = S := by
  refine OrderedCat.le_antisymm h ?_
  have h1 : (𝟙 a ≫ S) ≤ ((R ≫ conv R) ≫ S) :=
    OrderedCat.comp_mono hR.2 (OrderedCat.le_refl S)
  have h2 : (conv R ≫ S) ≤ (conv S ≫ S) :=
    OrderedCat.comp_mono (conv_mono h) (OrderedCat.le_refl S)
  have h3 : (R ≫ conv R ≫ S) ≤ (R ≫ 𝟙 b) :=
    OrderedCat.comp_mono (OrderedCat.le_refl R) (OrderedCat.le_trans h2 hS.1)
  rw [Cat.id_comp] at h1
  rw [Cat.assoc] at h1
  rw [Cat.comp_id] at h3
  exact OrderedCat.le_trans h1 h3

/-! ### The shunting rules (B&dM 4.19 and 4.20)

  The workhorses of relational program calculation: a map may be moved from one side of a
  containment to the other, at the cost of its converse.  `AOP/A4_2.lean` has both for a bare
  `Allegory` (`map_shunt_right`/`map_shunt_left`); these are the same statements in the DIAGRAMMATIC
  layer, so that `diag-export` has something to draw.  Nothing is assumed that `Map` does not
  already give: `Total f` inserts `f f°` on the way out, `SingleValued f` cancels `f° f` on the way
  back, and the two directions of each rule use exactly one of them each. -/

/-- **B&dM 4.19**, shunting on the RIGHT: for a map `f`, `R f ≤ S` iff `R ≤ S f°`. -/
theorem shunt_right {a b c : 𝒞} {f : b ⟶ c} (hf : Map f) (R : a ⟶ b) (S : a ⟶ c) :
    (R ≫ f) ≤ S ↔ R ≤ (S ≫ conv f) := by
  constructor
  · intro h
    -- `R = R𝟙 ≤ R(f f°) = (R f) f° ≤ S f°`; only `Total f` is used.
    have h1 : (R ≫ 𝟙 b) ≤ (R ≫ f ≫ conv f) :=
      OrderedCat.comp_mono (OrderedCat.le_refl R) hf.2
    have h2 : ((R ≫ f) ≫ conv f) ≤ (S ≫ conv f) :=
      OrderedCat.comp_mono h (OrderedCat.le_refl (conv f))
    rw [Cat.comp_id] at h1
    rw [Cat.assoc] at h2
    exact OrderedCat.le_trans h1 h2
  · intro h
    -- `R f ≤ (S f°) f = S (f° f) ≤ S𝟙 = S`; only `SingleValued f` is used.
    have h1 : (R ≫ f) ≤ ((S ≫ conv f) ≫ f) :=
      OrderedCat.comp_mono h (OrderedCat.le_refl f)
    have h2 : (S ≫ conv f ≫ f) ≤ (S ≫ 𝟙 c) :=
      OrderedCat.comp_mono (OrderedCat.le_refl S) hf.1
    rw [Cat.assoc] at h1
    rw [Cat.comp_id] at h2
    exact OrderedCat.le_trans h1 h2

/-- **B&dM 4.20**, shunting on the LEFT: for a map `f`, `f° R ≤ S` iff `R ≤ f S`. -/
theorem shunt_left {a b c : 𝒞} {f : b ⟶ a} (hf : Map f) (R : b ⟶ c) (S : a ⟶ c) :
    (conv f ≫ R) ≤ S ↔ R ≤ (f ≫ S) := by
  constructor
  · intro h
    -- `R = 𝟙R ≤ (f f°) R = f (f° R) ≤ f S`; `Total f` again.
    have h1 : (𝟙 b ≫ R) ≤ ((f ≫ conv f) ≫ R) :=
      OrderedCat.comp_mono hf.2 (OrderedCat.le_refl R)
    have h2 : (f ≫ conv f ≫ R) ≤ (f ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.le_refl f) h
    rw [Cat.id_comp, Cat.assoc] at h1
    exact OrderedCat.le_trans h1 h2
  · intro h
    -- `f° R ≤ f° (f S) = (f° f) S ≤ 𝟙S = S`; `SingleValued f` again.
    have h1 : (conv f ≫ R) ≤ (conv f ≫ f ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.le_refl (conv f)) h
    have h2 : ((conv f ≫ f) ≫ S) ≤ (𝟙 a ≫ S) :=
      OrderedCat.comp_mono hf.1 (OrderedCat.le_refl S)
    rw [← Cat.assoc] at h1
    rw [Cat.id_comp] at h2
    exact OrderedCat.le_trans h1 h2

/-- LEMMA 4.8 (p. 21): a map's RIGHT ADJOINT is its converse — B&dM's shunting rule.

    Being a map IS the adjunction `R ⊣ R°`: `Total` is its unit and `SingleValued` its counit.  So
    any other right adjoint `S` must agree with `R°`, by the standard uniqueness argument run in
    both directions (`S ≤ R°` uses `Total R`, `R° ≤ S` uses `SingleValued R`).

    The paper's converse half — that an arrow WITH a right adjoint is a map — is not proved here:
    its proof is the diagram chase that establishes (SV) and (TOT) in comonoid form, which is
    exactly what Lemma 4.4 needs and what the note above explains is out of reach of Def. 4.1 as
    printed. -/
theorem lemma_4_8 {a b : 𝒞} {R : a ⟶ b} {S : b ⟶ a} (hR : Map R)
    (hunit : (𝟙 a) ≤ (R ≫ S)) (hcounit : (S ≫ R) ≤ (𝟙 b)) :
    S = conv R := by
  refine OrderedCat.le_antisymm ?_ ?_
  · have h1 : (S ≫ 𝟙 a) ≤ (S ≫ R ≫ conv R) :=
      OrderedCat.comp_mono (OrderedCat.le_refl S) hR.2
    have h2 : ((S ≫ R) ≫ conv R) ≤ (𝟙 b ≫ conv R) :=
      OrderedCat.comp_mono hcounit (OrderedCat.le_refl (conv R))
    rw [Cat.comp_id] at h1
    rw [Cat.assoc, Cat.id_comp] at h2
    exact OrderedCat.le_trans h1 h2
  · have h1 : (conv R ≫ 𝟙 a) ≤ (conv R ≫ R ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.le_refl (conv R)) hunit
    have h2 : ((conv R ≫ R) ≫ S) ≤ (𝟙 b ≫ S) :=
      OrderedCat.comp_mono hR.1 (OrderedCat.le_refl S)
    rw [Cat.comp_id] at h1
    rw [Cat.assoc, Cat.id_comp] at h2
    exact OrderedCat.le_trans h1 h2

end Freyd.Diag
