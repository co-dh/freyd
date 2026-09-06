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

  `partition` is a RELATION and still STRICTLY natural (`partition_natural`): it discards
  nothing, so neither side of its square asks for an image the other does not already have.

  `setify` (§7.3) is lax only, but for the opposite reason to `prefix`'s: it discards no element,
  it MERGES them, so the right-hand side `setify P(R)` can name a set with more elements than the
  list has — one element of the list may be sent to several.  `setify_not_strict` is the witness.
-/

module

public import AOP.A5_6_ListCombinators
public import AOP.A5_7_PowerBeads

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

/-- Both Egli-Milner halves of `setify`'s square at once: every element of `x` has an `R`-image
    among the elements of a `list(R)`-image `y`, and every element of `y` is the `R`-image of one
    of `x` — the element in the matching position, found by induction along the two lists. -/
public theorem listP_inlistP_split (R : dE A ⟶ dE B) :
    ∀ (x : ConsList Unit A) (y : ConsList Unit B), listP R x y →
      (∀ a, inlistP x a → ∃ b, R a b ∧ inlistP y b)
        ∧ (∀ b, inlistP y b → ∃ a, inlistP x a ∧ R a b)
  | ConsList.wrap _, ConsList.wrap _, _ => ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons a x, ConsList.cons b y, h => by
      refine ⟨fun c hc => ?_, fun d hd => ?_⟩
      · have hc' : c = a ∨ inlistP x c := hc
        cases hc' with
        | inl he => subst he; exact ⟨b, h.1, Or.inl rfl⟩
        | inr hx =>
            obtain ⟨e, hR, he⟩ := (listP_inlistP_split R x y h.2).1 c hx
            exact ⟨e, hR, Or.inr he⟩
      · have hd' : d = b ∨ inlistP y d := hd
        cases hd' with
        | inl he => subst he; exact ⟨a, Or.inl rfl, h.1⟩
        | inr hy =>
            obtain ⟨c, hc, hR⟩ := (listP_inlistP_split R x y h.2).2 d hy
            exact ⟨c, Or.inr hc, hR⟩

/-! ## The seven lax naturality squares -/

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

/-- **`setify` is lax natural**: `list(R) setify ⊑ setify P(R)`.  The elements of a `list(R)`-image
    of `x` are an Egli-Milner `R`-image of the elements of `x` (`listP_inlistP_split`) — the same
    argument one functor over from `Tuple.setify_lax_natural` (`AOP.A7_4_CylinderBeads`), with the
    matching position an index into a list rather than a row of a tuple.  Not an equality:
    `setify_not_strict`. -/
public theorem setify_lax_natural (R : dE A ⟶ dE B) :
    list R ≫ setify ⊑ setify ≫ powerRel R := by
  refine le_iff.mpr fun x T h => ?_
  obtain ⟨y, hxy, hT⟩ := h
  -- `setify x T` IS `T = {a | a ∈ x}`, but only definitionally: name the equation before using it.
  have hTeq : T = fun b => inlistP y b := hT
  subst hTeq
  exact ⟨fun a => inlistP x a, rfl, (powerRel_apply R _ _).mpr (listP_inlistP_split R x y hxy)⟩

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

/-! ## `setify` is lax ONLY, for the opposite reason

  `prefix` is lax because it DISCARDS a suffix, so `φ list(R)` can reach a short list out of a
  source with no image at all.  `setify` discards nothing; it MERGES, and merging is what a set can
  undo.  A relation that splits one element into two lets `setify P(R)` name a two-element set out
  of a one-element list, which no `list(R)`-image of that list can `setify` to. -/

/-- The relation `{(true,true),(true,false)} : Bool ⟶ Bool` — `true` reaches both booleans, `false`
    reaches neither. -/
@[expose] public def trueSplits : dE Bool ⟶ dE Bool := fun p _ => p = true

/-- The list `[true]`. -/
@[expose] public def trueOne : ConsList Unit Bool := ConsList.cons true (ConsList.wrap ())

/-- **`setify` is not strictly natural**: `setify P(R) ⋢ list(R) setify`.  `setify[true] = {true}`
    and `P(trueSplits)` relates `{true}` to the whole of `Bool` — `true` has an image there and
    every boolean is an image of `true` — while a `list(trueSplits)`-image of `[true]` is again a
    one-element list, whose `setify` is a singleton.  The two-element set the left side names is
    therefore reached by no list the right side offers. -/
public theorem setify_not_strict :
    ∃ R : dE Bool ⟶ dE Bool, ¬ (setify ≫ powerRel R ⊑ list R ≫ setify) := by
  refine ⟨trueSplits, fun h => ?_⟩
  have hstep : (setify ≫ powerRel trueSplits) trueOne (fun _ => True) := by
    refine ⟨fun a => inlistP trueOne a, rfl, (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩⟩
    · intro a ha
      have ha' : a = true ∨ False := ha
      cases ha' with
      | inl he => exact ⟨true, he, trivial⟩
      | inr hf => exact hf.elim
    · exact fun b _ => ⟨true, Or.inl rfl, rfl⟩
  obtain ⟨y, hxy, hT⟩ := le_iff.mp h trueOne (fun _ => True) hstep
  cases y with
  | wrap _ => exact hxy.elim
  | cons b y' =>
      cases y' with
      | cons _ _ => exact hxy.2.elim
      | wrap _ =>
          -- The set is the whole of `Bool`, so both booleans are the one element of `y`.
          have h1 : true = b ∨ False := Eq.mp (congrFun hT true) trivial
          have h2 : false = b ∨ False := Eq.mp (congrFun hT false) trivial
          cases h1 with
          | inr hf => exact hf.elim
          | inl e1 =>
              cases h2 with
              | inr hf => exact hf.elim
              | inl e2 => exact Bool.noConfusion (e1.trans e2.symm)

/-! ## `partition` is strictly natural

  `partition` is `concat°` (`partition_concat`), and `concat`'s square is already an equality
  (`concat_natural`), so this one is that equality conversed — except for the side condition
  `allNonempty`, which `list(R)` carries in BOTH directions because it relates `nil` to `nil`
  and `cons` to `cons` only.  Nothing is discarded on either side, which is exactly what
  `prefix`, `suffix`, `subseq` and `segment` do and why theirs are lax only. -/

/-- A `list(R)`-image is empty exactly when its source is: `list(R)` relates `nil` to `nil` and
    `cons` to `cons`, and never one to the other. -/
public theorem listP_isNonempty (R : dE A ⟶ dE B) :
    ∀ (s : ConsList Unit A) (t : ConsList Unit B), listP R s t → (isNonempty s ↔ isNonempty t)
  | ConsList.wrap _, ConsList.wrap _, _ => Iff.rfl
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons _ _, ConsList.cons _ _, _ => Iff.rfl

/-- Segment by segment: a `list(list R)`-image has all its segments non-empty exactly when the
    source does, so `partition`'s side condition transfers along the square either way. -/
public theorem listP_allNonempty (R : dE A ⟶ dE B) :
    ∀ (ps : ConsList Unit (ConsList Unit A)) (qs : ConsList Unit (ConsList Unit B)),
      listP (list R) ps qs → (allNonempty ps ↔ allNonempty qs)
  | ConsList.wrap _, ConsList.wrap _, _ => Iff.rfl
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons s ps, ConsList.cons t qs, h =>
      and_congr (listP_isNonempty R s t h.1) (listP_allNonempty R ps qs h.2)

/-- **`partition` is STRICTLY natural**: `list(R) partition = partition list(list R)`.  A
    `list(R)`-image of a flattening is the flattening of a `list(list R)`-image of the segments
    (`listP_cconcat`, `listP_cconcat_split`), and `list(R)` keeps a segment non-empty in both
    directions (`listP_allNonempty`) — so neither side of the square asks for an image or a
    preimage the other side does not already produce. -/
public theorem partition_natural (R : dE A ⟶ dE B) :
    list R ≫ (partition : dList B ⟶ (⟨ConsList Unit (ConsList Unit B)⟩ : RelSet.{0}))
      = (partition : dList A ⟶ (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}))
        ≫ list (list R) := by
  apply hom_ext; intro x qs
  constructor
  · rintro ⟨y, hxy, hcc, hne⟩
    obtain rfl : y = cconcat qs := hcc.symm
    obtain ⟨ps, hps, rfl⟩ :=
      listP_cconcat_split R° qs x ((listP_recip R (cconcat qs) x).mpr hxy)
    rw [list_recip] at hps
    have hps' : listP (list R) ps qs := (listP_recip (list R) qs ps).mp hps
    exact ⟨ps, ⟨rfl, (listP_allNonempty R ps qs hps').mpr hne⟩, hps'⟩
  · rintro ⟨ps, ⟨hcc, hne⟩, hps⟩
    obtain rfl : x = cconcat ps := hcc.symm
    exact ⟨cconcat qs, listP_cconcat R ps qs hps, rfl, (listP_allNonempty R ps qs hps).mp hne⟩

end Freyd.Alg.RelSet.ListRel
