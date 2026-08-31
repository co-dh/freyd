/-
  Bird & de Moor, *Algebra of Programming* §8.5  The paragraph problem (book pp. 207-210).

  Break a non-empty list of words into lines of width at most `w`, minimising the waste — the
  sum of the squared white space of every line but the last.  The specification is
  `Λ(partition list⁺(fits w)) est(R)` with `R ≜ (waste w) ≤ (waste w)°`, and §8.5 is the second
  worked instance of §8.3's binary thinning (Theorem 8.2, `thinningList`).

  What §8.5 supplies is the problem side of that theorem:

  - `para_spec`: the specification is the catamorphism the theorem wants,
    `partition list⁺(fits w) = ⦇[wrap wrap,new] ∪ ([wrap wrap,glue] (ok w))⦈`, by
    `relCata_fusion` — only the algebra equation is ever unfolded, never `partition` itself.
  - `para_mono_new`, `para_mono_glue`: the note's `para-mono` rows.  `glue` is NOT monotonic on
    `R` (`para_mono_glue_false`, a three-line counterexample: the waste of a paragraph turns on
    its whole first line, so no greedy algorithm solves this), but `glue (ok w)` is monotonic
    on `Q ≜ R ∩ (head head°)`, which pins that first line.
  - `para_sort_new`, `para_sort_glue`: `P ≜ ⊤`, so both algebras are monotonic on the sorting
    order for free (`graph_monotonicAlg_topMor`).
  - `para_laws`: the note's `para-laws` headline, Theorem 8.2 at those data.

  SIDE CONDITIONS THE NOTE DOES NOT STATE.  Two hypotheses on word lengths are needed and are
  carried explicitly:
  - `hfit : ∀ a, len a ≤ w` — the note's "every word fits on a line by itself", which the
    fusion step needs;
  - `hlen : ∀ a, 0 ≤ len a` — words are not of negative length.  The fusion needs it (a line
    that fits after gluing already fitted before), and so does `para_mono_glue`: without it a
    one-line paragraph of waste `0` can be glued into a two-line one of positive waste while
    passing `ok w`, and monotonicity on `Q` fails.

  ASSUMED, as in the book and in `AOP.A8_3`: the sorted-list interface (8.7)-(8.11) stays a
  family of abstract arrows with the laws it is used by as hypotheses.  Two rows of the note
  are therefore out of reach here: `merge ⊤ = cat` and `listcp(F) = wrap+cpr` compute inside a
  CONCRETE list implementation, and the list object is abstract.

  B&dM's `Real` is `Int` (the repo is Mathlib-free), and `collect ≜ list(sqr) sum` is computed
  into the recursion `waste (cons l p) = sqr(w − width l) + waste p`, `waste (wrap l) = 0` —
  the book's `init` (drop the last line) being what makes the base case `0`.
-/
module

public import AOP.A8_3
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Paragraph

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {Word : Type} {len : Word → Int} {w : Int}

/-! ## `para-defn` -/

/-- `Line = list⁺ Word`. -/
@[expose] public abbrev Line (Word : Type) : Type := ConsList Word Word
/-- `Para = list⁺ Line`. -/
@[expose] public abbrev Para (Word : Type) : Type := ConsList (Line Word) (Line Word)
/-- The object carrying `Para`. -/
@[expose] public abbrev dPara (Word : Type) : RelSet.{0} := dCL (Line Word) (Line Word)

/-- **para-defn**: `width ≜ ⦇[length,(length×𝟙) plus succ]⦈` — the words' lengths plus one
    space between neighbours. -/
@[expose] public def widthFn (len : Word → Int) : Line Word → Int
  | ConsList.wrap a => len a
  | ConsList.cons a x => len a + widthFn len x + 1

/-- `head : Line ⟵ Para` — the first line of a paragraph. -/
@[expose] public def headLine : Para Word → Line Word
  | ConsList.wrap l => l
  | ConsList.cons l _ => l

/-- **para-defn**: `glue (a,xs)=[[a]⧺head xs]⧺tail xs` — put the word at the front of the
    first line. -/
@[expose] public def glueFn (a : Word) : Para Word → Para Word
  | ConsList.wrap l => ConsList.wrap (ConsList.cons a l)
  | ConsList.cons l p => ConsList.cons (ConsList.cons a l) p

public theorem headLine_glue (a : Word) (p : Para Word) :
    headLine (glueFn a p) = ConsList.cons a (headLine p) := by cases p <;> rfl

/-- **para-defn**: `sqr`, the summand of `collect ≜ list(sqr) sum`. -/
@[expose] public def sqr (n : Int) : Int := n * n

public theorem sqr_nonneg (n : Int) : 0 ≤ sqr n := by
  rcases Int.le_total 0 n with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -n := Int.neg_nonneg.mpr h
    have hm := Int.mul_nonneg h' h'
    rwa [Int.neg_mul_neg] at hm

public theorem sqr_eq_zero {n : Int} (h : sqr n = 0) : n = 0 := by
  rcases Int.mul_eq_zero.mp h with h | h <;> exact h

/-- **para-defn**: `waste w ≜ init list(white w) collect` with `white w x = w − width x` —
    the last line's white space is not wasted, so it is the base case that is `0`. -/
@[expose] public def wasteFn (len : Word → Int) (w : Int) : Para Word → Int
  | ConsList.wrap _ => 0
  | ConsList.cons l p => sqr (w - widthFn len l) + wasteFn len w p

public theorem wasteFn_nonneg : ∀ p : Para Word, 0 ≤ wasteFn len w p
  | ConsList.wrap _ => Int.le_refl _
  | ConsList.cons _ p => Int.add_nonneg (sqr_nonneg _) (wasteFn_nonneg p)

/-- `list⁺(fits w)`: every line of the paragraph fits. -/
@[expose] public def allFitP (len : Word → Int) (w : Int) : Para Word → Prop
  | ConsList.wrap l => widthFn len l ≤ w
  | ConsList.cons l p => widthFn len l ≤ w ∧ allFitP len w p

/-- **para-defn**: `list⁺(fits w)`, the coreflexive on paragraphs all of whose lines fit. -/
@[expose] public def allFit (len : Word → Int) (w : Int) : dPara Word ⟶ dPara Word :=
  fun p q => p = q ∧ allFitP len w p

/-- **para-defn**: `ok w`, the coreflexive on `[x]⧺xs` with `width x ≤ w` — only the FIRST
    line is tested. -/
@[expose] public def okW (len : Word → Int) (w : Int) : dPara Word ⟶ dPara Word :=
  fun p q => p = q ∧ widthFn len (headLine p) ≤ w

public theorem allFit_coreflexive : Coreflexive (allFit len w) :=
  le_iff.mpr fun _ _ h => h.1

public theorem okW_coreflexive : Coreflexive (okW len w) :=
  le_iff.mpr fun _ _ h => h.1

/-- **para-defn**: `R ≜ (waste w) ≤ (waste w)°`. -/
@[expose] public def R (len : Word → Int) (w : Int) : dPara Word ⟶ dPara Word :=
  fun p q => wasteFn len w p ≤ wasteFn len w q

/-- `R = waste ≤ waste°`, point-free. -/
public theorem R_eq :
    R len w
      = graph (wasteFn len w) ≫ leq
        ≫ (graph (wasteFn len w) : dPara Word ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro p q
  constructor
  · intro h; exact ⟨wasteFn len w p, rfl, wasteFn len w q, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    show wasteFn len w p ≤ wasteFn len w q
    rw [← (show m = wasteFn len w p from hm), ← (show n = wasteFn len w q from hn)]
    exact hmn

/-- **para-defn**: `Q ≜ R ∩ (head head°)` — no more wasteful, and with the same first line. -/
@[expose] public def Q (len : Word → Int) (w : Int) : dPara Word ⟶ dPara Word :=
  fun p q => wasteFn len w p ≤ wasteFn len w q ∧ headLine p = headLine q

/-- `Q = R ∩ (head head°)`, point-free. -/
public theorem Q_eq :
    Q len w
      = R len w ∩ (graph headLine ≫ (graph headLine : dPara Word ⟶ ⟨Line Word⟩)°) := by
  apply hom_ext; intro p q
  constructor
  · rintro ⟨hr, hh⟩; exact ⟨hr, headLine p, rfl, hh⟩
  · rintro ⟨hr, m, hm, hm'⟩
    refine ⟨hr, ?_⟩
    rw [(show m = headLine p from hm)] at hm'
    exact hm'

public theorem Q_le_R : Q len w ⊑ R len w := le_iff.mpr fun _ _ h => h.1

public theorem Q_refl : 𝟙 (dPara Word) ⊑ Q len w :=
  le_iff.mpr fun p q h => by obtain rfl : p = q := h; exact ⟨Int.le_refl _, rfl⟩

public theorem Q_trans : Q len w ≫ Q len w ⊑ Q len w :=
  le_iff.mpr fun _ _ h => by
    obtain ⟨_, ⟨hr1, hh1⟩, ⟨hr2, hh2⟩⟩ := h
    exact ⟨Int.le_trans hr1 hr2, hh1.trans hh2⟩

public theorem R_recip_trans : (R len w)° ≫ (R len w)° ⊑ (R len w)° :=
  le_iff.mpr fun p r h => by
    obtain ⟨q, h1, h2⟩ := h
    exact Int.le_trans (h2 : wasteFn len w r ≤ wasteFn len w q)
      (h1 : wasteFn len w q ≤ wasteFn len w p)

/-! ## The two algebras `[wrap wrap,new]` and `[wrap wrap,glue]` -/

/-- **para-defn**: `[wrap wrap,new]` — a single word becomes a one-word paragraph, and
    `new (a,xs)=[[a]]⧺xs` opens a new line. -/
@[expose] public def newAlgFn : ((F Word Word).obj (dPara Word)).carrier → Para Word
  | Sum.inl a => ConsList.wrap (ConsList.wrap a)
  | Sum.inr q => ConsList.cons (ConsList.wrap q.1) q.2

/-- **para-defn**: `[wrap wrap,glue]`. -/
@[expose] public def glueAlgFn : ((F Word Word).obj (dPara Word)).carrier → Para Word
  | Sum.inl a => ConsList.wrap (ConsList.wrap a)
  | Sum.inr q => glueFn q.1 q.2

/-- **para-defn**: `partition ≜ ⦇[wrap wrap,new∪glue]⦈` — every way of breaking the words into
    lines. -/
@[expose] public def partAlg : (F Word Word).obj (dPara Word) ⟶ dPara Word :=
  graph (newAlgFn (Word := Word)) ∪ graph glueAlgFn

@[expose] public def partition : dCL Word Word ⟶ dPara Word := ⦇partAlg⦈

/-- **para-defn**: the specification's algebra `S ≜ [wrap wrap,new] ∪ ([wrap wrap,glue](ok w))`,
    the note's `ab-split` row at `p₁ ≜ 𝟙`. -/
@[expose] public def Salg (len : Word → Int) (w : Int) :
    (F Word Word).obj (dPara Word) ⟶ dPara Word :=
  graph (newAlgFn (Word := Word)) ∪ (graph glueAlgFn ≫ okW len w)

/-! ## `para-mono` -/

/-- Gluing a word onto a paragraph that fits leaves a paragraph that fits, and conversely —
    the step that lets the fusion below test only the FIRST line.  Needs `0 ≤ len a`: a glued
    line is wider than the line it was glued to. -/
public theorem allFitP_glue_iff (hlen : ∀ a, 0 ≤ len a) (a : Word) (p : Para Word) :
    allFitP len w (glueFn a p)
      ↔ allFitP len w p ∧ widthFn len (headLine (glueFn a p)) ≤ w := by
  have hgrow : ∀ l : Line Word, widthFn len l ≤ widthFn len (ConsList.cons a l) := by
    intro l
    have := hlen a
    show widthFn len l ≤ len a + widthFn len l + 1
    omega
  cases p with
  | wrap l =>
    constructor
    · intro h
      exact ⟨Int.le_trans (hgrow l) h, h⟩
    · rintro ⟨-, h⟩; exact h
  | cons l p =>
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Int.le_trans (hgrow l) h1, h2⟩, h1⟩
    · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩

/-- **para-mono**, first row: `(𝟙×Q) new ⊑ new Q` — opening a new line adds the same waste to
    both paragraphs and gives them the same first line. -/
public theorem para_mono_new :
    MonotonicAlg (F := F Word Word) (graph (newAlgFn (Word := Word))) (Q len w) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = newAlgFn v := hr
    cases u with
    | inl a =>
      cases v with
      | inl a' =>
        obtain rfl : a = a' := hFv
        exact ⟨newAlgFn (Sum.inl a), rfl, Int.le_refl _, rfl⟩
      | inr q => exact (hFv : False).elim
    | inr p =>
      cases v with
      | inl a' => exact (hFv : False).elim
      | inr q =>
        obtain ⟨a, x⟩ := p
        obtain ⟨b, y⟩ := q
        obtain ⟨hab, hQ⟩ := hFv
        obtain rfl : a = b := hab
        have hxy : wasteFn len w x ≤ wasteFn len w y := hQ.1
        refine ⟨ConsList.cons (ConsList.wrap a) x, rfl, ?_, rfl⟩
        show sqr (w - len a) + wasteFn len w x ≤ sqr (w - len a) + wasteFn len w y
        omega

/-- **para-mono**, second row: `(𝟙×Q)(glue (ok w)) ⊑ glue (ok w)Q` — `Q` pins the first line,
    which is the only thing `glue` changes and the only thing `waste` reads about it. -/
public theorem para_mono_glue (hlen : ∀ a, 0 ≤ len a) :
    MonotonicAlg (F := F Word Word) (graph glueAlgFn ≫ okW len w) (Q len w) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, s, hs, hsr, hok⟩ := h
    obtain rfl : s = glueAlgFn v := hs
    obtain rfl : glueAlgFn v = r := hsr
    cases u with
    | inl a =>
      cases v with
      | inl a' =>
        obtain rfl : a = a' := hFv
        exact ⟨glueAlgFn (Sum.inl a), ⟨glueAlgFn (Sum.inl a), rfl, rfl, hok⟩,
          Int.le_refl _, rfl⟩
      | inr q => exact (hFv : False).elim
    | inr p =>
      cases v with
      | inl a' => exact (hFv : False).elim
      | inr q =>
        obtain ⟨a, x⟩ := p
        obtain ⟨b, y⟩ := q
        obtain ⟨hab, hQ⟩ := hFv
        obtain rfl : a = b := hab
        have hwaste : wasteFn len w x ≤ wasteFn len w y := hQ.1
        have hhead : headLine x = headLine y := hQ.2
        -- the two glued paragraphs have the same first line, so `ok w` transfers
        have hokx : widthFn len (headLine (glueFn a x)) ≤ w := by
          rw [headLine_glue, hhead, ← headLine_glue a y]
          exact hok
        refine ⟨glueFn a x, ⟨glueFn a x, rfl, rfl, hokx⟩, ?_, ?_⟩
        · -- the waste of a glued paragraph is that of its tail plus one term fixed by the head
          cases x with
          | wrap lx =>
            show (0 : Int) ≤ wasteFn len w (glueFn a y)
            exact wasteFn_nonneg _
          | cons lx x' =>
            cases y with
            | wrap ly =>
              -- vacuous: `waste x ≤ 0` forces `width lx = w`, and then the glued line overflows
              exfalso
              have hx0 : sqr (w - widthFn len lx) + wasteFn len w x' ≤ 0 := hwaste
              have h1 : 0 ≤ sqr (w - widthFn len lx) := sqr_nonneg _
              have h2 : 0 ≤ wasteFn len w x' := wasteFn_nonneg _
              have hz : sqr (w - widthFn len lx) = 0 := by omega
              have hlx : widthFn len lx = w := by
                have := sqr_eq_zero hz; omega
              have hly : ly = lx := (show headLine (ConsList.cons lx x') = headLine
                (ConsList.wrap ly) from hhead).symm
              have hokw : len a + widthFn len ly + 1 ≤ w := hok
              have := hlen a
              rw [hly, hlx] at hokw
              omega
            | cons ly y' =>
              have hly : ly = lx := (show headLine (ConsList.cons lx x')
                = headLine (ConsList.cons ly y') from hhead).symm
              subst hly
              show sqr (w - widthFn len (ConsList.cons a ly)) + wasteFn len w x'
                ≤ sqr (w - widthFn len (ConsList.cons a ly)) + wasteFn len w y'
              have hx : sqr (w - widthFn len ly) + wasteFn len w x'
                ≤ sqr (w - widthFn len ly) + wasteFn len w y' := hwaste
              omega
        · show headLine (glueFn a x) = headLine (glueFn a y)
          rw [headLine_glue, headLine_glue, hhead]

/-- **para-mono**, the FALSE row (B&dM p.209, "the obvious greedy algorithm does not solve this
    specification"): `(𝟙×R) glue ⊑ glue R` fails.  Words are their own lengths, `w = 10`: the
    paragraph `[10]·[0]` wastes nothing and `[9]·[0]` wastes 1, yet gluing a length-0 word onto
    each reverses that — the first line overflows to 11, the second lands exactly on 10. -/
public theorem para_mono_glue_false :
    ¬ MonotonicAlg (F := F Int Int) (graph glueAlgFn) (R (fun i : Int => i) 10) := by
  intro h
  have hRxy : wasteFn (fun i : Int => i) 10
        (ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))
      ≤ wasteFn (fun i : Int => i) 10
        (ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))) := by
    decide
  have hstep := le_iff.mp h
    (Sum.inr (0, ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))))
    (glueAlgFn (Sum.inr (0,
      ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))))
    ⟨Sum.inr (0, ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))),
      ⟨rfl, hRxy⟩, rfl⟩
  obtain ⟨s, hs, hR⟩ := hstep
  obtain rfl : s = glueAlgFn (Sum.inr (0,
    ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))) := hs
  have hbad : wasteFn (fun i : Int => i) 10
        (glueAlgFn (Sum.inr (0, ConsList.cons (ConsList.wrap (10 : Int))
          (ConsList.wrap (ConsList.wrap (0 : Int))))))
      ≤ wasteFn (fun i : Int => i) 10
        (glueAlgFn (Sum.inr (0, ConsList.cons (ConsList.wrap (9 : Int))
          (ConsList.wrap (ConsList.wrap (0 : Int)))))) := hR
  revert hbad
  decide

/-- **para-defn**, `P ≜ ⊤`: nothing is asked of the sorting order, so both algebras are
    monotonic on it. -/
public theorem para_sort_new :
    MonotonicAlg (F := F Word Word) (graph (newAlgFn (Word := Word)))
      (topMor (dPara Word) (dPara Word)) :=
  graph_monotonicAlg_topMor _

public theorem para_sort_glue :
    MonotonicAlg (F := F Word Word) (graph (glueAlgFn (Word := Word)))
      (topMor (dPara Word) (dPara Word)) :=
  graph_monotonicAlg_topMor _

/-! ## `para-laws` -/

/-- **para-laws**, second and third rows: the specification is a catamorphism,
    `partition list⁺(fits w) = ⦇[wrap wrap,new] ∪ ([wrap wrap,glue](ok w))⦈`.  Proved by
    `relCata_fusion`, so only the algebra equation below is ever unfolded: testing every line
    of the result is the same as testing the first line at every step, given that every word
    fits on a line by itself and that gluing only widens a line. -/
public theorem para_alg_fusion (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w) :
    partAlg ≫ allFit len w = (F Word Word).map (allFit len w) ≫ Salg len w := by
  apply hom_ext; intro u r
  cases u with
  | inl a =>
    constructor
    · rintro ⟨s, hs, hsr, -⟩
      refine ⟨Sum.inl a, rfl, ?_⟩
      refine Or.inl ?_
      show r = newAlgFn (Sum.inl a)
      cases hs with
      | inl hs => rw [← (hsr : s = r)]; exact hs
      | inr hs => rw [← (hsr : s = r)]; exact hs
    · rintro ⟨v, hFv, hS⟩
      cases v with
      | inl a' =>
        obtain rfl : a = a' := hFv
        have hr : r = ConsList.wrap (ConsList.wrap a) := by
          cases hS with
          | inl hS => exact hS
          | inr hS => obtain ⟨s, hs, hsr, -⟩ := hS; rw [← (hsr : s = r)]; exact hs
        exact ⟨r, Or.inl hr, rfl, by rw [hr]; exact hfit a⟩
      | inr q => exact (hFv : False).elim
  | inr p =>
    obtain ⟨a, x⟩ := p
    constructor
    · rintro ⟨s, hs, hsr, hfitS⟩
      obtain rfl : s = r := hsr
      cases hs with
      | inl hs =>
        obtain rfl : s = ConsList.cons (ConsList.wrap a) x := hs
        exact ⟨Sum.inr (a, x), ⟨rfl, rfl, hfitS.2⟩, Or.inl rfl⟩
      | inr hs =>
        obtain rfl : s = glueFn a x := hs
        obtain ⟨hfx, hok⟩ := (allFitP_glue_iff hlen a x).mp hfitS
        exact ⟨Sum.inr (a, x), ⟨rfl, rfl, hfx⟩, Or.inr ⟨glueFn a x, rfl, rfl, hok⟩⟩
    · rintro ⟨v, hFv, hS⟩
      cases v with
      | inl a' => exact (hFv : False).elim
      | inr q =>
        obtain ⟨b, y⟩ := q
        obtain ⟨hab, hy, hfy⟩ := hFv
        obtain rfl : a = b := hab
        obtain rfl : x = y := hy
        cases hS with
        | inl hS =>
          obtain rfl : r = ConsList.cons (ConsList.wrap a) x := hS
          exact ⟨ConsList.cons (ConsList.wrap a) x, Or.inl rfl, rfl, ⟨hfit a, hfy⟩⟩
        | inr hS =>
          obtain ⟨s, hs, hsr, hok⟩ := hS
          obtain rfl : s = glueFn a x := hs
          obtain rfl : glueFn a x = r := hsr
          exact ⟨glueFn a x, Or.inr rfl, rfl, (allFitP_glue_iff hlen a x).mpr ⟨hfy, hok⟩⟩

public theorem para_spec (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w) :
    partition ≫ allFit len w = ⦇Salg len w⦈ :=
  relCata_fusion (initial Word Word) (para_alg_fusion hlen hfit)

/-- **para-laws** (B&dM §8.5, p.210): a paragraph laid out as a fold that thins the layouts
    kept at each word —
    `Λ(partition list⁺(fits w)) est(R) ⊒ ⦇listcp(F) ⟨g₁,g₂⟩ merge ⊤ thinlist Q⦈ minlist R`.
    Theorem 8.2 (`thinningList`) at `f₁ ≜ [wrap wrap,new]`, `p₁ ≜ 𝟙`,
    `f₂ ≜ [wrap wrap,glue]`, `p₂ ≜ ok w`, `P ≜ ⊤`, with `para-mono` discharging the
    monotonicity conditions and `para_spec` the specification. -/
public theorem para_laws {l lF : RelSet.{0}} (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w)
    {sortP : PowerAllegory.powerObj (dPara Word) ⟶ l}
    {sortF : ((F Word Word).obj (dPara Word) ⟶ (F Word Word).obj (dPara Word)) →
      (PowerAllegory.powerObj ((F Word Word).obj (dPara Word)) ⟶ lF)}
    {listcp : (F Word Word).obj l ⟶ lF} {listf₁ listf₂ : lF ⟶ l}
    {filterp₂ thinlist : l ⟶ l} {minlist : l ⟶ dPara Word} {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj (dPara Word)) (PowerAllegory.powerObj (dPara Word))}
    {mergeP : Pr.p ⟶ l}
    (hsortF : ∀ {X Y : (F Word Word).obj (dPara Word) ⟶ (F Word Word).obj (dPara Word)},
      X ⊑ Y → sortF X ⊑ sortF Y)
    (h88₁ : sortF (graph newAlgFn ≫ topMor (dPara Word) (dPara Word) ≫ (graph newAlgFn)°)
      ≫ listf₁ ⊑ powerRel (graph (newAlgFn (Word := Word))) ≫ sortP)
    (h88₂ : sortF (graph glueAlgFn ≫ topMor (dPara Word) (dPara Word) ≫ (graph glueAlgFn)°)
      ≫ listf₂ ⊑ powerRel (graph (glueAlgFn (Word := Word))) ≫ sortP)
    (h89₂ : sortP ≫ filterp₂ ⊑ existsImage (okW len w) ≫ sortP)
    (h811 : (F Word Word).map sortP ≫ listcp ⊑ cpMap (F Word Word) (dPara Word)
      ≫ sortF ((F Word Word).map (topMor (dPara Word) (dPara Word))))
    (h810 : prodMap Pr' Pr sortP sortP ≫ mergeP ⊑ cup Pr' ≫ sortP)
    (h86 : sortP ≫ thinlist ⊑ thinRel (Q len w) ≫ sortP)
    (h87 : sortP ≫ minlist ⊑ est (R len w)) :
    ⦇listcp ≫ Pr.pair (listf₁ ≫ 𝟙 l) (listf₂ ≫ filterp₂) ≫ mergeP ≫ thinlist⦈ ≫ minlist
      ⊑ Λ (partition ≫ allFit len w) ≫ est (R len w) := by
  have hm₁ : MonotonicAlg (F := F Word Word)
      (graph (newAlgFn (Word := Word)) ≫ 𝟙 (dPara Word)) (Q len w) := by
    rw [Cat.comp_id]; exact para_mono_new
  have h89₁ : sortP ≫ 𝟙 l ⊑ existsImage (𝟙 (dPara Word)) ≫ sortP := by
    rw [Cat.comp_id, existsImage_id, Cat.id_comp]
    exact le_refl _
  have key := thinningList (F := F Word Word) (F_preservesRecip Word Word) (initial Word Word)
    (f₁ := graph newAlgFn) (f₂ := graph glueAlgFn) (p₁ := 𝟙 (dPara Word)) (p₂ := okW len w)
    (P := topMor (dPara Word) (dPara Word)) (Q := Q len w) (R := R len w)
    (graph_map newAlgFn) (graph_map glueAlgFn) Q_le_R Q_refl Q_trans R_recip_trans
    hm₁ (para_mono_glue hlen) hsortF para_sort_new para_sort_glue h88₁ h88₂ h89₁ h89₂ h811 h810
    h86 h87
  rw [Cat.comp_id (graph (newAlgFn (Word := Word)))] at key
  rw [para_spec hlen hfit]
  exact key

end Freyd.Alg.RelSet.Paragraph
