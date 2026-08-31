/-
  Bird & de Moor, *Algebra of Programming* §8.4  The knapsack problem (book pp. 205-207).

  Pack items into a knapsack of capacity `w` so as to maximise total value.  A packing is a
  SUBSEQUENCE of the given list of items whose total weight stays within `w`, and the problem
  is `Λ(subseq (within w)) est(R)` with `R ≜ value ≥ value°`.

  §8.4 is the book's worked instance of §8.3's BINARY THINNING (Theorem 8.2, `thinningList`):
  the specification is a catamorphism whose algebra splits as `(f₁p₁) ∪ (f₂p₂)`, and the
  theorem turns it into one fold over sorted lists of packings, thinned at every item.  What
  §8.4 has to supply is the problem side of that theorem:

  - `knap_spec`: the specification IS such a catamorphism, `subseq (within w) =
    ⦇[nil,cons](within w) ∪ [nil,π₂]⦈`.  Both `0 ≤ w` and non-negative item weights are
    needed, and the book states only the latter ("both of which are non-negative real
    numbers", p.205); `0 ≤ w` is what makes the empty packing legal.
  - `knap_mono_cons`, `knap_mono_drop`: the note's `knap-mono` rows.  `within w·cons` is NOT
    monotonic on `R` — the book's "the problem is that within w·[nil,cons] is not" — but it is
    on `Q ≜ R ∩ (weight ≤ weight°)`.
  - `knap_sort_cons`, `knap_sort_drop`: both algebras are monotonic on `P ≜ R`, the order the
    candidate lists are sorted by.
  - `knap_laws`: the note's `knap-laws` headline, Theorem 8.2 at those data.

  ASSUMED, as in the book and in `AOP.A8_3`: the sorted-list interface (8.7)-(8.11) —
  `sort P`, `listcp(F)`, `list fᵢ`, `filter pᵢ`, `merge P`, `thinlist Q`, `minlist R` — stays
  a family of abstract arrows with the laws it is used by as hypotheses.  Only the last row
  of the note's `knap-laws` is out of reach at that level: `listcp(F)=wrap+cpr` and
  `gᵢ=[list(nil),hᵢ]` compute inside a CONCRETE list implementation, and there is no `wrap`
  or `cpr` to compute with while the list object is abstract.

  B&dM's `Real` is `Int` here (the repo is Mathlib-free; only `+` and `≤` are ever used), as
  in `AOP.A7_3_Party`.
-/
module

public import AOP.A8_3
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Knapsack

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {Item : Type} {vol wt : Item → Int} {w : Int}

/-! ## `knap-defn` -/

/-- **knap-defn**: `within w`, the coreflexive on the packings whose weight fits the knapsack
    (`value ≜ total vol`, `weight ≜ total wt`). -/
@[expose] public def within (wt : Item → Int) (w : Int) : dList Item ⟶ dList Item :=
  fun x y => x = y ∧ total wt x ≤ w

public theorem within_coreflexive : Coreflexive (within wt w) :=
  le_iff.mpr fun _ _ h => h.1

/-- **knap-defn**: `R ≜ value ≥ value°` — packings by total value, `x R y` iff `x` is worth at
    least as much as `y`. -/
@[expose] public def R (vol : Item → Int) : dList Item ⟶ dList Item :=
  fun x y => total vol y ≤ total vol x

/-- `R = value ≥ value°`, point-free. -/
public theorem R_eq :
    R vol
      = graph (total vol) ≫ geq ≫ (graph (total vol) : dList Item ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro x y
  constructor
  · intro h; exact ⟨total vol x, rfl, total vol y, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    show total vol y ≤ total vol x
    rw [← (show m = total vol x from hm), ← (show n = total vol y from hn)]
    exact hmn

/-- **knap-defn**: `Q ≜ R ∩ (weight ≤ weight°)` — at least as valuable AND no heavier, the
    order that makes the cons branch monotonic. -/
@[expose] public def Q (vol wt : Item → Int) : dList Item ⟶ dList Item :=
  fun x y => total vol y ≤ total vol x ∧ total wt x ≤ total wt y

/-- `Q = R ∩ (weight ≤ weight°)`, point-free. -/
public theorem Q_eq :
    Q vol wt
      = R vol
        ∩ (graph (total wt) ≫ leq ≫ (graph (total wt) : dList Item ⟶ (⟨Int⟩ : RelSet.{0}))°) := by
  apply hom_ext; intro x y
  constructor
  · rintro ⟨hv, hwxy⟩
    exact ⟨hv, total wt x, rfl, total wt y, hwxy, rfl⟩
  · rintro ⟨hv, m, hm, n, hmn, hn⟩
    refine ⟨hv, ?_⟩
    show total wt x ≤ total wt y
    rw [← (show m = total wt x from hm), ← (show n = total wt y from hn)]
    exact hmn

public theorem Q_le_R : Q vol wt ⊑ R vol := le_iff.mpr fun _ _ h => h.1

public theorem R_refl : 𝟙 (dList Item) ⊑ R vol :=
  le_iff.mpr fun x y h => by obtain rfl : x = y := h; exact Int.le_refl _

public theorem Q_refl : 𝟙 (dList Item) ⊑ Q vol wt :=
  le_iff.mpr fun x y h => by
    obtain rfl : x = y := h; exact ⟨Int.le_refl _, Int.le_refl _⟩

public theorem Q_trans : Q vol wt ≫ Q vol wt ⊑ Q vol wt :=
  le_iff.mpr fun _ _ h => by
    obtain ⟨_, ⟨hv1, hw1⟩, ⟨hv2, hw2⟩⟩ := h
    exact ⟨Int.le_trans hv2 hv1, Int.le_trans hw1 hw2⟩

/-- `R°` is transitive — Theorem 8.2's `htransR`. -/
public theorem R_recip_trans : (R vol)° ≫ (R vol)° ⊑ (R vol)° :=
  le_iff.mpr fun x z h => by
    obtain ⟨y, h1, h2⟩ := h
    have h1' : total vol x ≤ total vol y := h1
    have h2' : total vol y ≤ total vol z := h2
    exact Int.le_trans h1' h2'

/-! ## The two algebras `[nil,cons]` and `[nil,π₂]` -/

/-- **knap-defn**: `[nil,π₂]` as a function — keep `nil`, or drop the head item.  (`[nil,cons]`
    is the initial algebra `con` itself.) -/
@[expose] public def dropFn : (Fobj Unit Item (dList Item)).carrier → ConsList Unit Item
  | Sum.inl d => ConsList.wrap d
  | Sum.inr p => p.2

/-- `[nil,cons] = con`, the initial algebra. -/
public theorem con_eq_junc :
    (graph con : (F Unit Item).obj (dList Item) ⟶ dList Item)
      = junc (sumCop (dL Unit) ⟨Item × ConsList Unit Item⟩) wrapR consR := by
  apply hom_ext; intro u r
  cases u with
  | inl d => exact (junc_sum_inl (wrapR : dL Unit ⟶ dList Item) consR d r).symm
  | inr p => exact (junc_sum_inr (wrapR : dL Unit ⟶ dList Item) consR p r).symm

/-- `[nil,π₂] = dropFn`. -/
public theorem drop_eq_junc :
    (graph dropFn : (F Unit Item).obj (dList Item) ⟶ dList Item)
      = junc (sumCop (dL Unit) ⟨Item × ConsList Unit Item⟩) wrapR
          (graph fun p : Item × ConsList Unit Item => p.2) := by
  apply hom_ext; intro u r
  cases u with
  | inl d =>
    exact (junc_sum_inl (wrapR : dL Unit ⟶ dList Item)
      (graph fun p : Item × ConsList Unit Item => p.2) d r).symm
  | inr p =>
    exact (junc_sum_inr (wrapR : dL Unit ⟶ dList Item)
      (graph fun p : Item × ConsList Unit Item => p.2) p r).symm

/-- **knap-defn**: the specification's algebra `S ≜ [nil,cons](within w) ∪ [nil,π₂]` — at each
    item, keep it if the packing still fits, or drop it. -/
@[expose] public def Salg (wt : Item → Int) (w : Int) :
    (F Unit Item).obj (dList Item) ⟶ dList Item :=
  (graph con ≫ within wt w) ∪ graph dropFn

/-- Pointwise reading of `[nil,cons](within w)`. -/
theorem con_within_apply (u : ((F Unit Item).obj (dList Item)).carrier)
    (r : ConsList Unit Item) :
    (graph con ≫ within wt w) u r ↔ r = con u ∧ total wt r ≤ w := by
  constructor
  · rintro ⟨c, hc, hcr, hwc⟩
    obtain rfl : c = con u := hc
    obtain rfl : con u = r := hcr
    exact ⟨rfl, hwc⟩
  · rintro ⟨rfl, hwr⟩
    exact ⟨con u, rfl, rfl, hwr⟩

/-- **B&dM p.206**: "the right-hand side simplifies to `([nil, {within w·cons} ∪ outr])`" —
    the base branch of the union is plain `nil`, since `within w ⊑ 𝟙` makes the filtered copy
    redundant beside the unfiltered one. -/
public theorem Salg_junc :
    Salg wt w = junc (sumCop (dL Unit) ⟨Item × ConsList Unit Item⟩) wrapR
      ((consR ≫ within wt w) ∪ graph fun p : Item × ConsList Unit Item => p.2) := by
  apply hom_ext; intro u r
  cases u with
  | inl d =>
    rw [junc_sum_inl]
    constructor
    · rintro (hc | hd)
      · exact ((con_within_apply (wt := wt) (w := w) (Sum.inl d) r).mp hc).1
      · exact (hd : r = dropFn (Sum.inl d))
    · intro hr; exact Or.inr (hr : r = ConsList.wrap d)
  | inr p =>
    rw [junc_sum_inr]
    constructor
    · rintro (hc | hd)
      · obtain ⟨hr, hwr⟩ := (con_within_apply (wt := wt) (w := w) (Sum.inr p) r).mp hc
        obtain rfl : r = con (Sum.inr p) := hr
        exact Or.inl ⟨ConsList.cons p.1 p.2, rfl, rfl, hwr⟩
      · exact Or.inr (hd : r = p.2)
    · rintro (⟨c, hc, hcr, hwc⟩ | hd)
      · refine Or.inl ((con_within_apply (wt := wt) (w := w) (Sum.inr p) r).mpr ?_)
        exact ⟨by rw [← (hcr : c = r)]; exact hc, by rw [← (hcr : c = r)]; exact hwc⟩
      · exact Or.inr (hd : r = p.2)

/-! ## `knap-mono` -/

/-- **knap-mono**, first row: `(𝟙×Q)(cons (within w)) ⊑ cons (within w)Q` — bettering a
    packing keeps it inside the knapsack, because `Q` also forbids getting heavier. -/
public theorem knap_mono_cons :
    MonotonicAlg (F := F Unit Item) (graph con ≫ within wt w) (Q vol wt) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hcon⟩ := h
    obtain ⟨rfl, hwr⟩ := (con_within_apply (wt := wt) (w := w) v r).mp hcon
    cases u with
    | inl d =>
      cases v with
      | inl d' =>
        obtain rfl : d = d' := hFv
        exact ⟨con (Sum.inl d), (con_within_apply (wt := wt) (w := w) _ _).mpr ⟨rfl, hwr⟩,
          Int.le_refl _, Int.le_refl _⟩
      | inr q => exact (hFv : False).elim
    | inr p =>
      cases v with
      | inl d' => exact (hFv : False).elim
      | inr q =>
        obtain ⟨a, x⟩ := p
        obtain ⟨b, y⟩ := q
        obtain ⟨ha, hQ⟩ := hFv
        obtain rfl : a = b := ha
        have hv : total vol y ≤ total vol x := hQ.1
        have hwxy : total wt x ≤ total wt y := hQ.2
        have hwy : wt a + total wt y ≤ w := hwr
        refine ⟨ConsList.cons a x,
          (con_within_apply (wt := wt) (w := w) (Sum.inr (a, x)) (ConsList.cons a x)).mpr
            ⟨rfl, show wt a + total wt x ≤ w by omega⟩, ?_⟩
        exact ⟨show vol a + total vol y ≤ vol a + total vol x by omega,
          show wt a + total wt x ≤ wt a + total wt y by omega⟩

/-- **knap-mono**, second row: `(𝟙×Q)π₂ ⊑ π₂Q` — dropping the head cannot undo `Q`. -/
public theorem knap_mono_drop :
    MonotonicAlg (F := F Unit Item) (graph dropFn) (Q vol wt) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = dropFn v := hr
    cases u with
    | inl d =>
      cases v with
      | inl d' =>
        obtain rfl : d = d' := hFv
        exact ⟨dropFn (Sum.inl d), rfl, Int.le_refl _, Int.le_refl _⟩
      | inr q => exact (hFv : False).elim
    | inr p =>
      cases v with
      | inl d' => exact (hFv : False).elim
      | inr q => exact ⟨p.2, rfl, hFv.2.1, hFv.2.2⟩

/-- **knap-defn**, `P ≜ R`: `[nil,cons]` is monotonic on `R`, so the candidate lists may be
    sorted in descending order of value. -/
public theorem knap_sort_cons : MonotonicAlg (F := F Unit Item) (graph con) (R vol) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = con v := hr
    cases u with
    | inl d =>
      cases v with
      | inl d' =>
        obtain rfl : d = d' := hFv
        exact ⟨con (Sum.inl d), rfl, Int.le_refl _⟩
      | inr q => exact (hFv : False).elim
    | inr p =>
      cases v with
      | inl d' => exact (hFv : False).elim
      | inr q =>
        obtain ⟨a, x⟩ := p
        obtain ⟨b, y⟩ := q
        obtain ⟨ha, hR⟩ := hFv
        obtain rfl : a = b := ha
        have hv : total vol y ≤ total vol x := hR
        exact ⟨ConsList.cons a x, rfl, show vol a + total vol y ≤ vol a + total vol x by omega⟩

/-- **knap-defn**, `P ≜ R`: `[nil,π₂]` is monotonic on `R` too. -/
public theorem knap_sort_drop : MonotonicAlg (F := F Unit Item) (graph dropFn) (R vol) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = dropFn v := hr
    cases u with
    | inl d =>
      cases v with
      | inl d' =>
        obtain rfl : d = d' := hFv
        exact ⟨dropFn (Sum.inl d), rfl, Int.le_refl _⟩
      | inr q => exact (hFv : False).elim
    | inr p =>
      cases v with
      | inl d' => exact (hFv : False).elim
      | inr q => exact ⟨p.2, rfl, hFv.2⟩

/-! ## `knap-laws` -/

/-- **knap-laws**, second row: the specification is a catamorphism,
    `subseq (within w) = ⦇[nil,cons](within w) ∪ [nil,π₂]⦈`.  The keep branch may test the
    partial packing because weights are non-negative — a subsequence of a packing that fits,
    fits — and the empty packing is legal because `0 ≤ w`. -/
public theorem knap_spec (hw : 0 ≤ w) (hwt : ∀ i, 0 ≤ wt i) :
    (subseq ≫ within wt w : dList Item ⟶ dList Item) = ⦇Salg wt w⦈ := by
  have hspec : ∀ x r : ConsList Unit Item,
      (subseq ≫ within wt w : dList Item ⟶ dList Item) x r ↔ subseqP r x ∧ total wt r ≤ w := by
    intro x r
    constructor
    · rintro ⟨y, hy, hxy, hwy⟩
      obtain rfl : y = r := hxy
      exact ⟨hy, hwy⟩
    · rintro ⟨hs, hwr⟩; exact ⟨r, hs, rfl, hwr⟩
  rw [Salg_junc]
  refine (relCata_UP (initial Unit Item) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun a x r => ?_⟩)
  · rw [hspec]
    constructor
    · rintro ⟨hs, -⟩
      cases r with
      | wrap u => rfl
      | cons b z => exact hs.elim
    · intro hr
      obtain rfl : r = ConsList.wrap d := hr
      exact ⟨trivial, hw⟩
  · rw [hspec]
    constructor
    · rintro ⟨hs, hwr⟩
      cases r with
      | wrap u =>
        exact ⟨ConsList.wrap u,
          (hspec x (ConsList.wrap u)).mpr ⟨subseqP.nil x, show (0 : Int) ≤ w from hw⟩,
          Or.inr rfl⟩
      | cons b z =>
        cases hs with
        | inl hs =>
          obtain ⟨hab, hzx⟩ := hs
          obtain rfl : b = a := hab
          have hbz : wt b + total wt z ≤ w := hwr
          have hb : 0 ≤ wt b := hwt b
          exact ⟨z, (hspec x z).mpr ⟨hzx, show total wt z ≤ w by omega⟩,
            Or.inl ⟨ConsList.cons b z, rfl, rfl, hwr⟩⟩
        | inr hs =>
          exact ⟨ConsList.cons b z, (hspec x (ConsList.cons b z)).mpr ⟨hs, hwr⟩, Or.inr rfl⟩
    · rintro ⟨y, hy, hcase⟩
      obtain ⟨hsy, hwy⟩ := (hspec x y).mp hy
      cases hcase with
      | inl hcase =>
        obtain ⟨c, hc, hcr, hwc⟩ := hcase
        obtain rfl : c = ConsList.cons a y := hc
        obtain rfl : ConsList.cons a y = r := hcr
        exact ⟨Or.inl ⟨rfl, hsy⟩, hwc⟩
      | inr hcase =>
        obtain rfl : r = y := hcase
        exact ⟨subseqP.weaken hsy, hwy⟩

/-- **knap-laws** (B&dM §8.4, p.206): the knapsack problem as a fold that thins the packings
    kept at each item —
    `Λ(subseq (within w)) est(R) ⊒ ⦇listcp(F) ⟨g₁,g₂⟩ merge R thinlist Q⦈ minlist R`.
    Theorem 8.2 (`thinningList`) at `f₁ ≜ [nil,cons]`, `p₁ ≜ within w`, `f₂ ≜ [nil,π₂]`,
    `p₂ ≜ 𝟙`, `P ≜ R`, with `knap-mono` discharging the monotonicity conditions and
    `knap_spec` the specification.  The sorted-list interface (8.7)-(8.11) is assumed, as in
    the book. -/
public theorem knap_laws {l lF : RelSet.{0}} (hw : 0 ≤ w) (hwt : ∀ i, 0 ≤ wt i)
    {sortP : PowerAllegory.powerObj (dList Item) ⟶ l}
    {sortF : ((F Unit Item).obj (dList Item) ⟶ (F Unit Item).obj (dList Item)) →
      (PowerAllegory.powerObj ((F Unit Item).obj (dList Item)) ⟶ lF)}
    {listcp : (F Unit Item).obj l ⟶ lF} {listf₁ listf₂ : lF ⟶ l}
    {filterp₁ thinlist : l ⟶ l} {minlist : l ⟶ dList Item} {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj (dList Item)) (PowerAllegory.powerObj (dList Item))}
    {mergeP : Pr.p ⟶ l}
    (hsortF : ∀ {X Y : (F Unit Item).obj (dList Item) ⟶ (F Unit Item).obj (dList Item)},
      X ⊑ Y → sortF X ⊑ sortF Y)
    (h88₁ : sortF (graph con ≫ R vol ≫ (graph con)°) ≫ listf₁ ⊑ powerRel (graph con) ≫ sortP)
    (h88₂ : sortF (graph dropFn ≫ R vol ≫ (graph dropFn)°) ≫ listf₂
      ⊑ powerRel (graph dropFn) ≫ sortP)
    (h89₁ : sortP ≫ filterp₁ ⊑ existsImage (within wt w) ≫ sortP)
    (h811 : (F Unit Item).map sortP ≫ listcp
      ⊑ cpMap (F Unit Item) (dList Item) ≫ sortF ((F Unit Item).map (R vol)))
    (h810 : prodMap Pr' Pr sortP sortP ≫ mergeP ⊑ cup Pr' ≫ sortP)
    (h86 : sortP ≫ thinlist ⊑ thinRel (Q vol wt) ≫ sortP)
    (h87 : sortP ≫ minlist ⊑ est (R vol)) :
    ⦇listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ 𝟙 l) ≫ mergeP ≫ thinlist⦈ ≫ minlist
      ⊑ Λ (subseq ≫ within wt w) ≫ est (R vol) := by
  have hm₂ : MonotonicAlg (F := F Unit Item) (graph dropFn ≫ 𝟙 (dList Item)) (Q vol wt) := by
    rw [Cat.comp_id]; exact knap_mono_drop
  have h89₂ : sortP ≫ 𝟙 l ⊑ existsImage (𝟙 (dList Item)) ≫ sortP := by
    rw [Cat.comp_id, existsImage_id, Cat.id_comp]
    exact le_refl _
  have key := thinningList (F := F Unit Item) (F_preservesRecip Unit Item) (initial Unit Item)
    (f₁ := graph con) (f₂ := graph dropFn) (p₁ := within wt w) (p₂ := 𝟙 (dList Item))
    (P := R vol) (Q := Q vol wt) (R := R vol)
    (graph_map con) (graph_map dropFn) Q_le_R Q_refl Q_trans R_recip_trans
    knap_mono_cons hm₂ hsortF knap_sort_cons knap_sort_drop h88₁ h88₂ h89₁ h89₂ h811 h810 h86 h87
  rw [Cat.comp_id (graph dropFn)] at key
  rw [knap_spec hw hwt]
  exact key

end Freyd.Alg.RelSet.Knapsack
