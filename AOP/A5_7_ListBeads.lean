/-
  Bird & de Moor, *Algebra of Programming* §5.7 — the LAX NATURALITY of the §5.6 list
  combinators, and which of them are STRICTLY natural.

  `LaxNatural F G φ` (`AOP.A5_1`, mirrored to diagram order) is `G.map R ≫ φ b ⊑ φ a ≫ F.map R`.
  Here `G` and `F` are `list` (or `list∘list`, or `× ∘ ⟨1, list⟩`) in the concrete `RelSet`
  model, where `list` is a plain function on relations rather than a bundled `Relator`, so each
  square is stated as the raw inequality — the shape `Freyd.Alg.eps_lax_natural` (`AOP.A5_7`)
  has for `∋`.

  Verdict: `cons` and `concat` are polymorphic FUNCTIONS, and their squares are equalities
  (`cons_natural` / `concat_natural`, `AOP.A5_6_ListCombinators`).  `prefix`, `suffix`,
  `subseq` and `segment` are lax ONLY: one counterexample refutes all four, because `nil` is a
  prefix, a suffix, a subsequence and a segment of every list, so the right-hand side of each
  square can reach `nil` out of a list that has no `list(R)`-image at all.
-/

module

public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.ListRel

open Freyd Freyd.Alg.RelSet.CL

variable {A B : Type}

/-! ## Splitting a `list(R)`-image along a combinator's boundary

  Each lax square reduces to the same statement: a part of a `list(R)`-image of `x` is itself
  the `list(R)`-image of the corresponding part of `x`.  For `prefix` and `suffix` the part is
  cut by an append, so `listP_cappend_split` on `R°` does the work; `subseq` needs its own
  induction because the dropped elements are not contiguous. -/

/-- `w` a prefix of a `list(R)`-image of `x` is the `list(R)`-image of a prefix of `x`. -/
public theorem listP_prefix_split (R : dE A ⟶ dE B) (x : ConsList Unit A) (y w : ConsList Unit B)
    (hxy : listP R x y) (hw : prefixP w y) : ∃ ys, prefixP ys x ∧ listP R ys w := by
  obtain ⟨v, rfl⟩ := (prefixP_iff_append w y).mp hw
  obtain ⟨ys, u, h1, -, rfl⟩ :=
    listP_cappend_split R° w v x ((listP_recip R (cappend w v) x).mpr hxy)
  exact ⟨ys, (prefixP_iff_append ys (cappend ys u)).mpr ⟨u, rfl⟩, (listP_recip R w ys).mp h1⟩

/-- `w` a suffix of a `list(R)`-image of `x` is the `list(R)`-image of a suffix of `x`. -/
public theorem listP_suffix_split (R : dE A ⟶ dE B) (x : ConsList Unit A) (y w : ConsList Unit B)
    (hxy : listP R x y) (hw : suffixP w y) : ∃ ys, suffixP ys x ∧ listP R ys w := by
  obtain ⟨u, rfl⟩ := (suffixP_iff_append w y).mp hw
  obtain ⟨p, ys, -, h2, rfl⟩ :=
    listP_cappend_split R° u w x ((listP_recip R (cappend u w) x).mpr hxy)
  exact ⟨ys, (suffixP_iff_append ys (cappend p ys)).mpr ⟨p, rfl⟩, (listP_recip R w ys).mp h2⟩

/-- `w` a subsequence of a `list(R)`-image of `x` is the `list(R)`-image of a subsequence of `x`:
    keep the elements of `x` sitting under the kept elements of the image. -/
public theorem listP_subseq_split (R : dE A ⟶ dE B) :
    ∀ (x : ConsList Unit A) (y w : ConsList Unit B),
      listP R x y → subseqP w y → ∃ ys, subseqP ys x ∧ listP R ys w
  | ConsList.wrap _, ConsList.wrap _, ConsList.wrap _, _, _ =>
      ⟨ConsList.wrap (), trivial, trivial⟩
  | ConsList.wrap _, ConsList.wrap _, ConsList.cons _ _, _, hw => hw.elim
  | ConsList.wrap _, ConsList.cons _ _, _, hxy, _ => hxy.elim
  | ConsList.cons _ _, ConsList.wrap _, _, hxy, _ => hxy.elim
  | ConsList.cons _ _, ConsList.cons _ _, ConsList.wrap _, _, _ =>
      ⟨ConsList.wrap (), trivial, trivial⟩
  | ConsList.cons a x, ConsList.cons b y, ConsList.cons c w, hxy, hw => by
      have hw' : (c = b ∧ subseqP w y) ∨ subseqP (ConsList.cons c w) y := hw
      have hR : R a b := hxy.1
      cases hw' with
      | inl h =>
          obtain ⟨ys, h1, h2⟩ := listP_subseq_split R x y w hxy.2 h.2
          exact ⟨ConsList.cons a ys, Or.inl ⟨rfl, h1⟩, by rw [h.1]; exact hR, h2⟩
      | inr h =>
          obtain ⟨ys, h1, h2⟩ := listP_subseq_split R x y (ConsList.cons c w) hxy.2 h
          exact ⟨ys, subseqP.weaken h1, h2⟩

/-! ## The six lax naturality squares -/

/-- **`prefix` is lax natural**: `list(R) prefix ⊑ prefix list(R)`. -/
public theorem prefix_lax_natural (R : dE A ⟶ dE B) :
    list R ≫ prefixR ⊑ prefixR ≫ list R :=
  le_iff.mpr fun x w h => by
    obtain ⟨y, hxy, hw⟩ := h
    exact listP_prefix_split R x y w hxy hw

/-- **`suffix` is lax natural**: `list(R) suffix ⊑ suffix list(R)`. -/
public theorem suffix_lax_natural (R : dE A ⟶ dE B) :
    list R ≫ suffixR ⊑ suffixR ≫ list R :=
  le_iff.mpr fun x w h => by
    obtain ⟨y, hxy, hw⟩ := h
    exact listP_suffix_split R x y w hxy hw

/-- **`subseq` is lax natural**: `list(R) subseq ⊑ subseq list(R)`. -/
public theorem subseq_lax_natural (R : dE A ⟶ dE B) :
    list R ≫ subseq ⊑ subseq ≫ list R :=
  le_iff.mpr fun x w h => by
    obtain ⟨y, hxy, hw⟩ := h
    exact listP_subseq_split R x y w hxy hw

/-- **`segment` is lax natural**: `list(R) segment ⊑ segment list(R)`.  `segment = suffix prefix`
    (`segment_eq`), so the square is the two previous ones stacked. -/
public theorem segment_lax_natural (R : dE A ⟶ dE B) :
    list R ≫ segment ⊑ segment ≫ list R := by
  simp only [segment_eq]
  refine le_iff.mpr fun x w h => ?_
  obtain ⟨y, hxy, z, hzy, hwz⟩ := h
  obtain ⟨zs, h1, h2⟩ := listP_suffix_split R x y z hxy hzy
  obtain ⟨ys, h3, h4⟩ := listP_prefix_split R zs z w h2 hwz
  exact ⟨ys, ⟨zs, h1, h3⟩, h4⟩

/-- **`concat` is lax natural** — the lax half of the STRICT `concat_natural`. -/
public theorem concat_lax_natural (R : dE A ⟶ dE B) :
    list (list R) ≫ concatR ⊑ concatR ≫ list R := le_of_eq (concat_natural R)

/-- **`cons` is lax natural** — the lax half of the STRICT `cons_natural`.  The `cons` is
    `AOP.A6_ConsList`'s `CL.consR`, the one `AOP.A5_6_ListCombinators` already works with. -/
public theorem cons_lax_natural (R : dE A ⟶ dE B) :
    rprodMap R (list R) ≫ consR ⊑ consR ≫ list R := le_of_eq (cons_natural R)

/-! ## Strictness: `prefix`, `suffix`, `subseq`, `segment` are lax ONLY

  One witness refutes all four.  Take `A = B = Bool`, `R` the coreflexive `{(true,true)}`, and
  the one-element list `[false]`, which has NO `list(R)`-image because `false` has no
  `R`-image.  So `list(R) φ` is empty out of `[false]` for every `φ`, while `φ list(R)` relates
  `[false]` to `nil` — `nil` is a prefix, a suffix, a subsequence and a segment of `[false]`,
  and `list(R)` relates `nil` to `nil`. -/

/-- The coreflexive `{(true,true)} : Bool ⟶ Bool`. -/
@[expose] public def trueOnly : dE Bool ⟶ dE Bool := fun p q => p = true ∧ q = true

/-- The list `[false]`. -/
@[expose] public def falseOne : ConsList Unit Bool := ConsList.cons false (ConsList.wrap ())

/-- `[false]` has no `list(trueOnly)`-image: `nil` has the wrong shape and a `cons` would need
    `trueOnly false b`. -/
public theorem trueOnly_no_image : ∀ y : ConsList Unit Bool, ¬ listP trueOnly falseOne y
  | ConsList.wrap _, h => h.elim
  | ConsList.cons _ _, h => Bool.noConfusion h.1.1

/-- **`prefix` is not strictly natural**: `prefix list(R) ⋢ list(R) prefix`. -/
public theorem prefix_not_strict :
    ∃ R : dE Bool ⟶ dE Bool, ¬ (prefixR ≫ list R ⊑ list R ≫ prefixR) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨y, hy, -⟩ :=
    le_iff.mp h falseOne (ConsList.wrap ()) ⟨ConsList.wrap (), trivial, trivial⟩
  exact trueOnly_no_image y hy

/-- **`suffix` is not strictly natural**: `suffix list(R) ⋢ list(R) suffix`. -/
public theorem suffix_not_strict :
    ∃ R : dE Bool ⟶ dE Bool, ¬ (suffixR ≫ list R ⊑ list R ≫ suffixR) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨y, hy, -⟩ :=
    le_iff.mp h falseOne (ConsList.wrap ()) ⟨ConsList.wrap (), Or.inr rfl, trivial⟩
  exact trueOnly_no_image y hy

/-- **`subseq` is not strictly natural**: `subseq list(R) ⋢ list(R) subseq`. -/
public theorem subseq_not_strict :
    ∃ R : dE Bool ⟶ dE Bool, ¬ (subseq ≫ list R ⊑ list R ≫ subseq) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨y, hy, -⟩ :=
    le_iff.mp h falseOne (ConsList.wrap ()) ⟨ConsList.wrap (), trivial, trivial⟩
  exact trueOnly_no_image y hy

/-- **`segment` is not strictly natural**: `segment list(R) ⋢ list(R) segment`. -/
public theorem segment_not_strict :
    ∃ R : dE Bool ⟶ dE Bool, ¬ (segment ≫ list R ⊑ list R ≫ segment) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨y, hy, -⟩ :=
    le_iff.mp h falseOne (ConsList.wrap ())
      ⟨ConsList.wrap (), ⟨ConsList.wrap (), falseOne, rfl⟩, trivial⟩
  exact trueOnly_no_image y hy

end Freyd.Alg.RelSet.ListRel
