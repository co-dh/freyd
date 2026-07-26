/-
  `diag.CB_Derived` — the operations AOP needs, DERIVED from `CartBicat`.  Nothing here is an axiom.

  functorialSemanticsForRelationalTheories.pdf §4, pp. 18–22.  The convolution `Δ;(R ⊗ S);∇` is the
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
def convolution {a b : 𝒞} (R S : a ⟶ b) : a ⟶ b := cop a ≫ (R ⊗ₕ S) ≫ mer b

/-- `⊤ := !;?`, the maximum arrow: discard everything, then create everything.  The unit of
    `convolution` (functorialSemanticsForRelationalTheories.pdf p. 22). -/
def top (a b : 𝒞) : a ⟶ b := dis a ≫ un b

/-- Every arrow is below `⊤`.  Lax counit (43) sends `R;!` under `!`, and (40) supplies the `?`. -/
theorem le_top {a b : 𝒞} (R : a ⟶ b) : OrderedCat.le R (top a b) := by
  -- `R = R;𝟙 ≤ R;(!;?) = (R;!);? ≤ !;? = ⊤`.
  have h1 : OrderedCat.le (R ≫ 𝟙 b) (R ≫ dis b ≫ un b) :=
    OrderedCat.comp_mono (OrderedCat.le_refl R) (ineq_40 b)
  have h2 : OrderedCat.le ((R ≫ dis b) ≫ un b) (dis a ≫ un b) :=
    OrderedCat.comp_mono (lax_dis R) (OrderedCat.le_refl (un b))
  rw [Cat.comp_id] at h1
  rw [Cat.assoc] at h2
  exact OrderedCat.le_trans h1 h2

/-- `⊤` is the unit of convolution: `R ∩ ⊤ = R`
    (functorialSemanticsForRelationalTheories.pdf p. 22, unitality in Lemma 4.11).  The `⊤` strand
    is discarded by the counit law (10) and re-absorbed by the unit law (7); `runit_nat` is what
    moves `R` past the unitor. -/
theorem convolution_top {a b : 𝒞} (R : a ⟶ b) : convolution R (top a b) = R := by
  -- Stage the `⊗`: `R ⊗ (!;?) = ((𝟙 ⊗ !) ; (R ⊗ 𝟙)) ; (𝟙 ⊗ ?)`.
  have hR : (R ⊗ₕ (dis a ≫ un b))
      = ((𝟙 a ⊗ₕ dis a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))) ≫ (𝟙 b ⊗ₕ un b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  -- `(𝟙 ⊗ ?);∇ = ρ`, read off the unit law (7) by cancelling `ρ ; ρ⁻¹ = 𝟙`.
  have hun : (𝟙 b ⊗ₕ un b) ≫ mer b = SymMonCat.runit b := by
    have h := mer_unit (𝒞 := 𝒞) b
    calc (𝟙 b ⊗ₕ un b) ≫ mer b
        = 𝟙 (b ⊗ 𝕀) ≫ (𝟙 b ⊗ₕ un b) ≫ mer b := by rw [Cat.id_comp]
      _ = (SymMonCat.runit b ≫ SymMonCat.runitInv b) ≫ (𝟙 b ⊗ₕ un b) ≫ mer b := by
            rw [SymMonCat.runit_inv]
      _ = SymMonCat.runit b ≫ (SymMonCat.runitInv b ≫ (𝟙 b ⊗ₕ un b) ≫ mer b) := by
            rw [Cat.assoc]
      _ = SymMonCat.runit b ≫ 𝟙 b := by rw [h]
      _ = SymMonCat.runit b := Cat.comp_id _
  dsimp [convolution, top]
  calc cop a ≫ (R ⊗ₕ (dis a ≫ un b)) ≫ mer b
      = cop a ≫ (((𝟙 a ⊗ₕ dis a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))) ≫ (𝟙 b ⊗ₕ un b)) ≫ mer b := by rw [hR]
    _ = cop a ≫ (𝟙 a ⊗ₕ dis a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ (𝟙 b ⊗ₕ un b) ≫ mer b := by
          simp only [Cat.assoc]
    _ = cop a ≫ (𝟙 a ⊗ₕ dis a) ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.runit b := by rw [hun]
    _ = cop a ≫ (𝟙 a ⊗ₕ dis a) ≫ SymMonCat.runit a ≫ R := by rw [SymMonCat.runit_nat]
    _ = (cop a ≫ (𝟙 a ⊗ₕ dis a) ≫ SymMonCat.runit a) ≫ R := by simp only [Cat.assoc]
    _ = 𝟙 a ≫ R := by rw [cop_counit]
    _ = R := Cat.id_comp _

/-- Convolution is monotone in both arguments — immediate from `comp_mono` and `tensHom_mono`, and
    the reason `∩` needs no separate monotonicity axiom. -/
theorem convolution_mono {a b : 𝒞} {R R' S S' : a ⟶ b}
    (hR : OrderedCat.le R R') (hS : OrderedCat.le S S') :
    OrderedCat.le (convolution R S) (convolution R' S') := by
  dsimp [convolution]
  exact OrderedCat.comp_mono (OrderedCat.le_refl _)
    (OrderedCat.comp_mono (SymMonCat.tensHom_mono hR hS) (OrderedCat.le_refl _))

/-- `R ∩ S ≤ R`: the first half of the greatest-lower-bound property
    (functorialSemanticsForRelationalTheories.pdf p. 22).  Weaken the `S` strand all the way to `⊤`
    by `le_top`, then `convolution_top` collapses it. -/
theorem convolution_le_left {a b : 𝒞} (R S : a ⟶ b) :
    OrderedCat.le (convolution R S) R := by
  have h := convolution_mono (OrderedCat.le_refl R) (le_top S)
  rw [convolution_top] at h
  exact h

/-- The convolution is symmetric, by cocommutativity (9) on the copy and commutativity (6) on the
    merge, bridged by naturality of the symmetry. -/
theorem convolution_comm {a b : 𝒞} (R S : a ⟶ b) : convolution R S = convolution S R := by
  dsimp [convolution]
  calc cop a ≫ (R ⊗ₕ S) ≫ mer b
      = (cop a ≫ SymMonCat.swap a a) ≫ (R ⊗ₕ S) ≫ mer b := by rw [cop_comm]
    _ = cop a ≫ (SymMonCat.swap a a ≫ (R ⊗ₕ S)) ≫ mer b := by simp only [Cat.assoc]
    _ = cop a ≫ ((S ⊗ₕ R) ≫ SymMonCat.swap b b) ≫ mer b := by rw [← SymMonCat.swap_nat]
    _ = cop a ≫ (S ⊗ₕ R) ≫ SymMonCat.swap b b ≫ mer b := by simp only [Cat.assoc]
    _ = cop a ≫ (S ⊗ₕ R) ≫ mer b := by rw [mer_comm]

/-- `(R ∩ S) ∩ T` with the left-leaning copy and merge trees exposed, ready for (8) and (6). -/
theorem convolution_left_staged {a b : 𝒞} (R S T : a ⟶ b) :
    convolution (convolution R S) T
      = cop a ≫ (cop a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by
  dsimp [convolution]
  have hsplit : ((cop a ≫ (R ⊗ₕ S) ≫ mer b) ⊗ₕ T)
      = (cop a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (mer b ⊗ₕ 𝟙 b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  rw [hsplit]
  simp only [Cat.assoc]

/-- The mirror staging for `R ∩ (S ∩ T)`, right-leaning. -/
theorem convolution_right_staged {a b : 𝒞} (R S T : a ⟶ b) :
    convolution R (convolution S T)
      = cop a ≫ (𝟙 a ⊗ₕ cop a) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ mer b) ≫ mer b := by
  dsimp [convolution]
  have hsplit : (R ⊗ₕ (cop a ≫ (S ⊗ₕ T) ≫ mer b))
      = (𝟙 a ⊗ₕ cop a) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ mer b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  rw [hsplit]
  simp only [Cat.assoc]

/-- `R ∩ S ≤ S`, the other half of the greatest-lower-bound property. -/
theorem convolution_le_right {a b : 𝒞} (R S : a ⟶ b) :
    OrderedCat.le (convolution R S) S := by
  rw [convolution_comm]
  exact convolution_le_left S R

/-- `(R ∩ S) ∩ T = R ∩ (S ∩ T)` — Freyd's `inter_assoc` (§2.11), derived.  Both staged forms are
    normalised to `Δ;(𝟙 ⊗ Δ);(R ⊗ (S ⊗ T));(𝟙 ⊗ ∇);∇`: coassociativity (8) turns the left copy
    tree into the right one, associativity (6) does the same for the merge tree, and
    `tensAssocInv_nat` carries the re-bracketing past `(R ⊗ S) ⊗ T` in between. -/
theorem convolution_assoc {a b : 𝒞} (R S T : a ⟶ b) :
    convolution (convolution R S) T = convolution R (convolution S T) := by
  rw [convolution_left_staged, convolution_right_staged]
  -- Insert `α ; α⁻¹ = 𝟙` after the left copy tree, then apply (8), naturality, and (6).
  calc cop a ≫ (cop a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b
      = cop a ≫ (cop a ⊗ₕ 𝟙 a) ≫ (SymMonCat.tensAssoc a a a ≫ SymMonCat.tensAssocInv a a a)
          ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by
        rw [SymMonCat.tensAssoc_inv, Cat.id_comp]
    _ = (cop a ≫ (cop a ⊗ₕ 𝟙 a) ≫ SymMonCat.tensAssoc a a a)
          ≫ SymMonCat.tensAssocInv a a a ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by
        simp only [Cat.assoc]
    _ = (cop a ≫ (𝟙 a ⊗ₕ cop a))
          ≫ SymMonCat.tensAssocInv a a a ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by
        rw [cop_assoc]
    _ = cop a ≫ (𝟙 a ⊗ₕ cop a)
          ≫ (SymMonCat.tensAssocInv a a a ≫ ((R ⊗ₕ S) ⊗ₕ T)) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by
        simp only [Cat.assoc]
    _ = cop a ≫ (𝟙 a ⊗ₕ cop a)
          ≫ ((R ⊗ₕ (S ⊗ₕ T)) ≫ SymMonCat.tensAssocInv b b b) ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by
        rw [tensAssocInv_nat]
    _ = cop a ≫ (𝟙 a ⊗ₕ cop a) ≫ (R ⊗ₕ (S ⊗ₕ T))
          ≫ SymMonCat.tensAssocInv b b b ≫ (mer b ⊗ₕ 𝟙 b) ≫ mer b := by simp only [Cat.assoc]
    _ = cop a ≫ (𝟙 a ⊗ₕ cop a) ≫ (R ⊗ₕ (S ⊗ₕ T))
          ≫ SymMonCat.tensAssocInv b b b ≫ SymMonCat.tensAssoc b b b
          ≫ (𝟙 b ⊗ₕ mer b) ≫ mer b := by rw [mer_assoc]
    _ = cop a ≫ (𝟙 a ⊗ₕ cop a) ≫ (R ⊗ₕ (S ⊗ₕ T))
          ≫ (SymMonCat.tensAssocInv b b b ≫ SymMonCat.tensAssoc b b b)
          ≫ (𝟙 b ⊗ₕ mer b) ≫ mer b := by simp only [Cat.assoc]
    _ = cop a ≫ (𝟙 a ⊗ₕ cop a) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ mer b) ≫ mer b := by
        rw [SymMonCat.inv_tensAssoc, Cat.id_comp]

/-- `R ∩ R = R` — Freyd's `inter_idem` (§2.11), derived.  `≤` is the glb property; `≥` is exactly
    where the lax inequation (42) and the special law meet: copying `R` and running it on both
    strands can only produce more than running it once, and `Δ;∇ = 𝟙` closes the loop. -/
theorem convolution_idem {a b : 𝒞} (R : a ⟶ b) : convolution R R = R := by
  refine OrderedCat.le_antisymm (convolution_le_left R R) ?_
  have h : OrderedCat.le ((R ≫ cop b) ≫ mer b) ((cop a ≫ (R ⊗ₕ R)) ≫ mer b) :=
    OrderedCat.comp_mono (lax_cop R) (OrderedCat.le_refl (mer b))
  have hL : (R ≫ cop b) ≫ mer b = R := by
    rw [Cat.assoc, special, Cat.comp_id]
  have hR : (cop a ≫ (R ⊗ₕ R)) ≫ mer b = convolution R R := by
    dsimp [convolution]; rw [Cat.assoc]
  rw [hL, hR] at h
  exact h

/-- `∩` is the GREATEST lower bound: anything below both `S` and `T` is below `S ∩ T`
    (functorialSemanticsForRelationalTheories.pdf p. 22, "every hom-set is a meet semi-lattice").
    With `convolution_le_left`/`convolution_le_right` this completes the semilattice statement.
    Idempotency is what does the work — `R = R ∩ R ≤ S ∩ T`. -/
theorem convolution_glb {a b : 𝒞} {R S T : a ⟶ b}
    (hS : OrderedCat.le R S) (hT : OrderedCat.le R T) :
    OrderedCat.le R (convolution S T) := by
  have h := convolution_mono hS hT
  rw [convolution_idem] at h
  exact h

/-- `X ≤ Y` iff `X ∩ Y = X`.  This is the bridge between `diag`'s PRIMITIVE hom order and Freyd's
    DERIVED one (`Freyd/S2_10.lean`, where `R ⊑ S` is *defined* as `R ∩ S = R`), and it is what
    turns the `≤` forms of semi-distributivity and modularity into the equalities the `Allegory`
    class asks for. -/
theorem convolution_eq_left_of_le {a b : 𝒞} {X Y : a ⟶ b} (h : OrderedCat.le X Y) :
    convolution X Y = X :=
  OrderedCat.le_antisymm (convolution_le_left X Y) (convolution_glb (OrderedCat.le_refl X) h)

/-- `(R ∩ S)† = R† ∩ S†` — Freyd's `recip_inter` (§2.11).

    NOT proved through Lemma 4.2 (iii) (`(R ⊗ S)† = R† ⊗ S†`), which would need the Frobenius
    structure at the COMPOSITE object `a ⊗ b` — the clause of Carboni & Walters' definition that
    `functorialSemanticsForRelationalTheories.pdf` Def. 4.1 as printed omits (see `diag/CB.lean`'s
    header).  Instead: `∩` is the greatest lower bound, and `†` is an order isomorphism
    (`conv_mono` both ways, `conv_conv`), so it carries greatest lower bounds to greatest lower
    bounds.  This keeps every arrow in the proof at a simple object. -/
theorem conv_inter {a b : 𝒞} (R S : a ⟶ b) :
    conv (convolution R S) = convolution (conv R) (conv S) := by
  refine OrderedCat.le_antisymm ?_ ?_
  · exact convolution_glb (conv_mono (convolution_le_left R S))
      (conv_mono (convolution_le_right R S))
  · -- `(R† ∩ S†)†` is below both `R` and `S`, hence below `R ∩ S`; apply `†` once more.
    have h1 : OrderedCat.le (conv (convolution (conv R) (conv S))) R := by
      have h := conv_mono (convolution_le_left (conv R) (conv S))
      rwa [conv_conv] at h
    have h2 : OrderedCat.le (conv (convolution (conv R) (conv S))) S := by
      have h := conv_mono (convolution_le_right (conv R) (conv S))
      rwa [conv_conv] at h
    have h3 := conv_mono (convolution_glb h1 h2)
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

/-- (46), SINGLE VALUED: `R†R ≤ 𝟙`.  Freyd's `Simple` (§2.13). -/
def SingleValued {a b : 𝒞} (R : a ⟶ b) : Prop := OrderedCat.le (conv R ≫ R) (𝟙 b)

/-- (47), TOTAL: `𝟙 ≤ RR†`.  Freyd's `Entire` (§2.13). -/
def Total {a b : 𝒞} (R : a ⟶ b) : Prop := OrderedCat.le (𝟙 a) (R ≫ conv R)

/-- (48), INJECTIVE: `RR† ≤ 𝟙`. -/
def Injective {a b : 𝒞} (R : a ⟶ b) : Prop := OrderedCat.le (R ≫ conv R) (𝟙 a)

/-- (49), SURJECTIVE: `𝟙 ≤ R†R`. -/
def Surjective {a b : 𝒞} (R : a ⟶ b) : Prop := OrderedCat.le (𝟙 b) (conv R ≫ R)

/-- A MAP is single valued and total (p. 20) — equivalently, by `lemma_4_8`, an arrow whose
    converse is its right adjoint. -/
def Map {a b : 𝒞} (R : a ⟶ b) : Prop := SingleValued R ∧ Total R

/-- (SV) as the paper writes it on p. 20: `Δ;(R ⊗ R) ≤ R;Δ`, the reverse of the lax inequation
    (42).  Recorded for reference; `SingleValued` above is the form everything uses. -/
def ineq_SV {a b : 𝒞} (R : a ⟶ b) : Prop :=
  OrderedCat.le (cop a ≫ (R ⊗ₕ R)) (R ≫ cop b)

/-- (TOT) as the paper writes it: `! ≤ R;!`, the reverse of the lax inequation (43). -/
def ineq_TOT {a b : 𝒞} (R : a ⟶ b) : Prop := OrderedCat.le (dis a) (R ≫ dis b)

/-- (INJ) as the paper writes it: `(R ⊗ R);∇ ≤ ∇;R`. -/
def ineq_INJ {a b : 𝒞} (R : a ⟶ b) : Prop :=
  OrderedCat.le ((R ⊗ₕ R) ≫ mer b) (mer a ≫ R)

/-- (SUR) as the paper writes it: `? ≤ ?;R`. -/
def ineq_SUR {a b : 𝒞} (R : a ⟶ b) : Prop := OrderedCat.le (un b) (un a ≫ R)

/-- COROLLARY 4.5 (p. 21): two maps ordered by `≤` are EQUAL.  Freyd's `map_order_discrete`
    (§2.133).  Insert the unit of `R` on the left of `S` and cancel with the counit of `S`:
    `S = 𝟙S ≤ (RR†)S = R(R†S) ≤ R(S†S) ≤ R𝟙 = R`. -/
theorem cor_4_5 {a b : 𝒞} {R S : a ⟶ b} (hR : Map R) (hS : Map S) (h : OrderedCat.le R S) :
    R = S := by
  refine OrderedCat.le_antisymm h ?_
  have h1 : OrderedCat.le (𝟙 a ≫ S) ((R ≫ conv R) ≫ S) :=
    OrderedCat.comp_mono hR.2 (OrderedCat.le_refl S)
  have h2 : OrderedCat.le (conv R ≫ S) (conv S ≫ S) :=
    OrderedCat.comp_mono (conv_mono h) (OrderedCat.le_refl S)
  have h3 : OrderedCat.le (R ≫ conv R ≫ S) (R ≫ 𝟙 b) :=
    OrderedCat.comp_mono (OrderedCat.le_refl R) (OrderedCat.le_trans h2 hS.1)
  rw [Cat.id_comp] at h1
  rw [Cat.assoc] at h1
  rw [Cat.comp_id] at h3
  exact OrderedCat.le_trans h1 h3

/-- LEMMA 4.8 (p. 21): a map's RIGHT ADJOINT is its converse — B&dM's shunting rule.

    Being a map IS the adjunction `R ⊣ R†`: `Total` is its unit and `SingleValued` its counit.  So
    any other right adjoint `S` must agree with `R†`, by the standard uniqueness argument run in
    both directions (`S ≤ R†` uses `Total R`, `R† ≤ S` uses `SingleValued R`).

    The paper's converse half — that an arrow WITH a right adjoint is a map — is not proved here:
    its proof is the diagram chase that establishes (SV) and (TOT) in comonoid form, which is
    exactly what Lemma 4.4 needs and what the note above explains is out of reach of Def. 4.1 as
    printed. -/
theorem lemma_4_8 {a b : 𝒞} {R : a ⟶ b} {S : b ⟶ a} (hR : Map R)
    (hunit : OrderedCat.le (𝟙 a) (R ≫ S)) (hcounit : OrderedCat.le (S ≫ R) (𝟙 b)) :
    S = conv R := by
  refine OrderedCat.le_antisymm ?_ ?_
  · have h1 : OrderedCat.le (S ≫ 𝟙 a) (S ≫ R ≫ conv R) :=
      OrderedCat.comp_mono (OrderedCat.le_refl S) hR.2
    have h2 : OrderedCat.le ((S ≫ R) ≫ conv R) (𝟙 b ≫ conv R) :=
      OrderedCat.comp_mono hcounit (OrderedCat.le_refl (conv R))
    rw [Cat.comp_id] at h1
    rw [Cat.assoc, Cat.id_comp] at h2
    exact OrderedCat.le_trans h1 h2
  · have h1 : OrderedCat.le (conv R ≫ 𝟙 a) (conv R ≫ R ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.le_refl (conv R)) hunit
    have h2 : OrderedCat.le ((conv R ≫ R) ≫ S) (𝟙 b ≫ S) :=
      OrderedCat.comp_mono hR.1 (OrderedCat.le_refl S)
    rw [Cat.comp_id] at h1
    rw [Cat.assoc, Cat.id_comp] at h2
    exact OrderedCat.le_trans h1 h2

end Freyd.Diag
