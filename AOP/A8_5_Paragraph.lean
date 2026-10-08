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
  are therefore out of reach here: `merge ⊤ = cat` and `cpL(F) = wrap+cpr` compute inside a
  CONCRETE list implementation, and the list object is abstract.
-/
module

public import AOP.A8_3
import AOP.A8_2

namespace Freyd.Alg.RelSet.Paragraph
open PowerAllegory

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {Word : Type} {len : Word → Int} {w : Int}

/-! ## `para-defn` -/

/-- `Line = L(Word)`. -/
@[expose] public abbrev Line (Word : Type) : Type := NEList Word
/-- `Para = L(Line)`. -/
@[expose] public abbrev Para (Word : Type) : Type := NEList (Line Word)
/-- The object carrying `Para`. -/
@[expose] public abbrev dPara (Word : Type) : RelSet.{0} := dNE (Line Word)

-- B&dM p.208 names the types `Line` and `Para` over one fixed `Word`, so they print by name with
-- the argument dropped; printing the unfolding made `Line ≜ L(Word)` read `L(Word) ≜ L(Word)`.
open Lean PrettyPrinter in
@[app_unexpander Line] public meta def unexpandLine : Unexpander
  | `($_ $_) => `($(mkIdent (Name.mkSimple "Line")))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Para] public meta def unexpandPara : Unexpander
  | `($_ $_) => `($(mkIdent (Name.mkSimple "Para")))
  | _ => throw ()
-- `dPara` is the object whose carrier is `Para`, so it prints as the type it carries.
open Lean PrettyPrinter in
@[app_unexpander dPara] public meta def unexpandDPara : Unexpander
  | `($_ $_) => `($(mkIdent (Name.mkSimple "Para")))
  | _ => throw ()

/-- **para-defn**: `width ≜ ⦇[length,(length×𝟙) plus succ]⦈` — the words' lengths plus one
    space between neighbours. -/
@[expose] public def widthFn (len : Word → Int) : Line Word → Int
  | ConsList.wrap a => len a
  | ConsList.cons a xs => len a + widthFn len xs + 1

/-- `head : Line ⟵ Para` — the first line of a paragraph. -/
@[expose] public def head : Para Word → Line Word
  | ConsList.wrap xs => xs
  | ConsList.cons xs _ => xs

/-- **para-defn**: `glue (a,xs)=[[a]⧺head xs]⧺tail xs` — put the word at the front of the
    first line. -/
@[expose] public def glue (a : Word) : Para Word → Para Word
  | ConsList.wrap xs => ConsList.wrap (ConsList.cons a xs)
  | ConsList.cons xs xss => ConsList.cons (ConsList.cons a xs) xss

public theorem headLine_glue (a : Word) (p : Para Word) :
    head (glue a p) = ConsList.cons a (head p) := by cases p <;> rfl

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
  | ConsList.cons xs xss => sqr (w - widthFn len xs) + wasteFn len w xss

public theorem wasteFn_nonneg : ∀ p : Para Word, 0 ≤ wasteFn len w p
  | ConsList.wrap _ => Int.le_refl _
  | ConsList.cons _ p => Int.add_nonneg (sqr_nonneg _) (wasteFn_nonneg p)

/-- `list⁺(fits w)`: every line of the paragraph fits. -/
@[expose] public def allFitP (len : Word → Int) (w : Int) : Para Word → Prop
  | ConsList.wrap xs => widthFn len xs ≤ w
  | ConsList.cons xs xss => widthFn len xs ≤ w ∧ allFitP len w xss

-- The line-length function is the SECTION'S data, not part of the names the note writes
-- (`fits(w)`, `ok(w)`), so it is an implicit binder supplied by name where a use site pins it.
/-- **para-defn**: `list⁺(fits w)`, the coreflexive on paragraphs all of whose lines fit. -/
@[expose] public def fits (w : Int) : dPara Word ⟶ dPara Word := corefl (allFitP len w)

/-- **para-defn**: `ok w`, the predicate on `[x]⧺xs` with `width x ≤ w` — only the FIRST line is
    tested. -/
@[expose] public def okP (w : Int) (xss : Para Word) : Prop := widthFn len (head xss) ≤ w

/-- `ok w` as an arrow: the coreflexive of `okP`. -/
@[expose] public def ok (w : Int) : dPara Word ⟶ dPara Word := corefl (okP (len := len) w)

public theorem fits_coreflexive : Coreflexive (fits (len := len) w) :=
  le_iff.mpr fun _ _ h => h.1

public theorem ok_coreflexive : Coreflexive (ok (len := len) w) :=
  le_iff.mpr fun _ _ h => h.1

/-- **para-defn**: `R ≜ (waste w) ≤ (waste w)°`. -/
@[expose] public def R (len : Word → Int) (w : Int) : dPara Word ⟶ dPara Word :=
  fun xss yss => wasteFn len w xss ≤ wasteFn len w yss

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
  fun xss yss => wasteFn len w xss ≤ wasteFn len w yss ∧ head xss = head yss

/-- `Q = R ∩ (head head°)`, point-free. -/
public theorem Q_eq :
    Q len w
      = R len w ∩ (graph head ≫ (graph head : dPara Word ⟶ ⟨Line Word⟩)°) := by
  apply hom_ext; intro p q
  constructor
  · rintro ⟨hr, hh⟩; exact ⟨hr, head p, rfl, hh⟩
  · rintro ⟨hr, m, hm, hm'⟩
    refine ⟨hr, ?_⟩
    rw [(show m = head p from hm)] at hm'
    exact hm'

/-- `xss R yss` iff `xss` wastes no more than `yss`: the pointwise reading of `R_eq`. -/
public theorem R_apply (xss yss : Para Word) :
    R len w xss yss ↔ wasteFn len w xss ≤ wasteFn len w yss := Iff.rfl

/-- `xss Q yss` iff `xss` wastes no more than `yss` and has the same first line. -/
public theorem Q_apply (xss yss : Para Word) :
    Q len w xss yss ↔ wasteFn len w xss ≤ wasteFn len w yss ∧ head xss = head yss := Iff.rfl

/-- `xss (fits w) yss` iff `xss = yss` and every line of `xss` is at most `w` wide. -/
public theorem fits_apply (xss yss : Para Word) :
    fits (len := len) w xss yss ↔ xss = yss ∧ allFitP len w xss := Iff.rfl

/-- `xss (ok w) yss` iff `xss = yss` and the first line of `xss` is at most `w` wide. -/
public theorem ok_apply (xss yss : Para Word) :
    ok (len := len) w xss yss ↔ xss = yss ∧ widthFn len (head xss) ≤ w := Iff.rfl

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

/-- **para-defn**: `new (a,xs)=[[a]]⧺xs` — open a new line for the word.  Named for the same
    reason `glue` is: it is one arm of the algebra the note draws, and an arm is written by its
    own name. -/
@[expose] public def new (a : Word) (xss : Para Word) : Para Word := ConsList.cons (ConsList.wrap a) xss

-- The algebras `[wrap wrap,new]` and `[wrap wrap,glue]` are the copairing `Sum.elim` of maps
-- already named, so they are written out at each use rather than given names of their own.

/-- **para-defn**: `partition ≜ ⦇[wrap wrap,new∪glue]⦈` — every way of breaking the words into
    lines. -/
@[expose] public def partAlg : (F Word Word).obj (dPara Word) ⟶ dPara Word :=
  graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2))
    ∪ graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2))

@[expose] public def partition : dCL Word Word ⟶ dPara Word := ⦇partAlg⦈

/-- **para-defn**: `start ≜ wrap wrap wrap` (B&dM p.210) — the thinned fold's base case: the one
    candidate list holding the one-line, one-word paragraph `[[a]]`. -/
@[expose] public def start (a : Word) : ConsList Unit (Para Word) :=
  ConsList.cons (ConsList.wrap (ConsList.wrap a)) (ConsList.wrap ())

/-! ### `partition`'s computation rules and its naturality square

  The paragraph `partition` is NOT `AOP.A5_6_ListCombinators`'s: that one cuts a possibly-empty
  list into segments, this one cuts a NON-EMPTY list into non-empty lines, so it is its own arrow
  and carries its own naturality square. -/

/-- `partition` at a one-word list: the one-line paragraph. -/
public theorem partition_wrap (a : Word) (yss : Para Word) :
    partition (ConsList.wrap a) yss ↔ yss =ConsList.wrap (ConsList.wrap a) := by
  unfold partition
  rw [← cataR_eq_relCata]
  exact ⟨fun h => h.elim id id, Or.inl⟩

/-- `partition` at a `cons`: partition the tail, then either open a new line or glue. -/
public theorem partition_cons (a : Word) (xs : NEList Word) (yss : Para Word) :
    partition (ConsList.cons a xs) yss ↔ ∃ xss, partition xs xss ∧ (yss = new a xss ∨ yss = glue a xss) := by
  unfold partition
  rw [← cataR_eq_relCata]
  all_goals exact Iff.rfl

section Natural
variable {A B : Type}

/-- `glue` is invisible to the lift: gluing `R`-related words onto `list⁺(list⁺(R))`-related
    paragraphs leaves them related. -/
theorem nelistP_glue_of (R : dE A ⟶ dE B) (a : A) (b : B) (p : Para A) (q : Para B)
    (hab : R a b) (h : nelistP (nelist R) p q) :
    nelistP (nelist R) (glue a p) (glue b q) := by
  cases p with
  | wrap l =>
      cases q with
      | wrap m => exact ⟨hab, h⟩
      | cons m q' => exact False.elim h
  | cons l p' =>
      cases q with
      | wrap m => exact False.elim h
      | cons m q' => exact ⟨⟨hab, h.1⟩, h.2⟩

/-- A `list⁺(list⁺(R))`-image of a glued paragraph is itself a glue — the lift passes back
    through `glue`, which only reshapes. -/
theorem nelistP_glue_split (R : dE A ⟶ dE B) (a : A) (p : Para A) (q : Para B)
    (h : nelistP (nelist R) (glue a p) q) :
    ∃ b q', R a b ∧ nelistP (nelist R) p q' ∧ q = glue b q' := by
  cases p with
  | wrap l =>
      cases q with
      | wrap m =>
          cases m with
          | wrap b => exact False.elim h
          | cons b m' => exact ⟨b, ConsList.wrap m', h.1, h.2, rfl⟩
      | cons m q' => exact False.elim h
  | cons l p' =>
      cases q with
      | wrap m => exact False.elim h
      | cons m q' =>
          cases m with
          | wrap b => exact False.elim h.1
          | cons b m' => exact ⟨b, ConsList.cons m' q', h.1.1, ⟨h.1.2, h.2⟩, rfl⟩

/-- **`partition` is STRICTLY natural**: `list⁺(R) partition = partition list⁺(list⁺(R))` —
    neither `new` nor `glue` looks at a word, so a partition of an `R`-image of a word list is
    the image of a partition of the list, and conversely. -/
public theorem partition_natural (R : dE A ⟶ dE B) :
    nelist R ≫ (partition : dNE B ⟶ dPara B)
      = (partition : dNE A ⟶ dPara A) ≫ nelist (nelist R) := by
  apply hom_ext
  intro x q
  induction x generalizing q with
  | wrap a =>
      constructor
      · rintro ⟨y, hxy, hyq⟩
        cases y with
        | wrap b =>
            rw [(partition_wrap b q).mp hyq]
            exact ⟨ConsList.wrap (ConsList.wrap a), (partition_wrap a _).mpr rfl, hxy⟩
        | cons b y' => exact False.elim hxy
      · rintro ⟨p, hxp, hpq⟩
        rw [(partition_wrap a p).mp hxp] at hpq
        cases q with
        | wrap m =>
            cases m with
            | wrap b => exact ⟨ConsList.wrap b, hpq, (partition_wrap b _).mpr rfl⟩
            | cons b m' => exact False.elim hpq
        | cons m q' => exact False.elim hpq
  | cons a x' ih =>
      constructor
      · rintro ⟨y, hxy, hyq⟩
        cases y with
        | wrap b => exact False.elim hxy
        | cons b y' =>
            obtain ⟨q', hq', harm⟩ := (partition_cons b y' q).mp hyq
            obtain ⟨p', hp', hp'q'⟩ := (ih q').mp ⟨y', hxy.2, hq'⟩
            cases harm with
            | inl h =>
                subst h
                exact ⟨new a p', (partition_cons a x' _).mpr ⟨p', hp', Or.inl rfl⟩,
                  hxy.1, hp'q'⟩
            | inr h =>
                subst h
                exact ⟨glue a p', (partition_cons a x' _).mpr ⟨p', hp', Or.inr rfl⟩,
                  nelistP_glue_of R a b p' q' hxy.1 hp'q'⟩
      · rintro ⟨p, hxp, hpq⟩
        obtain ⟨p', hp', harm⟩ := (partition_cons a x' p).mp hxp
        cases harm with
        | inl h =>
            subst h
            cases q with
            | wrap m => exact False.elim hpq
            | cons m q'' =>
                cases m with
                | wrap b =>
                    obtain ⟨y', hxy', hy'q''⟩ := (ih q'').mpr ⟨p', hp', hpq.2⟩
                    exact ⟨ConsList.cons b y', ⟨hpq.1, hxy'⟩,
                      (partition_cons b y' _).mpr ⟨q'', hy'q'', Or.inl rfl⟩⟩
                | cons b m' => exact False.elim hpq.1
        | inr h =>
            subst h
            obtain ⟨b, q'', hab, hp'q'', hq⟩ := nelistP_glue_split R a p' q hpq
            subst hq
            obtain ⟨y', hxy', hy'q''⟩ := (ih q'').mpr ⟨p', hp', hp'q''⟩
            exact ⟨ConsList.cons b y', ⟨hab, hxy'⟩,
              (partition_cons b y' _).mpr ⟨q'', hy'q'', Or.inr rfl⟩⟩

end Natural

/-- **para-defn**: the specification's algebra `S ≜ [wrap wrap,new] ∪ ([wrap wrap,glue](ok w))`,
    the note's `ab-split` row at `p₁ ≜ 𝟙`. -/
@[expose] public def Salg (len : Word → Int) (w : Int) :
    (F Word Word).obj (dPara Word) ⟶ dPara Word :=
  graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2))
    ∪ (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2))
      ≫ ok (len := len) w)

/-! ## `para-mono` -/

/-- Gluing a word onto a paragraph that fits leaves a paragraph that fits, and conversely —
    the step that lets the fusion below test only the FIRST line.  Needs `0 ≤ len a`: a glued
    line is wider than the line it was glued to. -/
public theorem allFitP_glue_iff (hlen : ∀ a, 0 ≤ len a) (a : Word) (p : Para Word) :
    allFitP len w (glue a p)
      ↔ allFitP len w p ∧ widthFn len (head (glue a p)) ≤ w := by
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
    Freyd.Alg.Pres (F := F Word Word)
      (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2)))
      (Q len w) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = _ := hr
    cases u with
    | inl a =>
      cases v with
      | inl a' =>
        obtain rfl : a = a' := hFv
        exact ⟨ConsList.wrap (ConsList.wrap a), rfl, Int.le_refl _, rfl⟩
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
    Freyd.Alg.Pres (F := F Word Word)
      (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2))
        ≫ ok (len := len) w) (Q len w) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, s, hs, hsr, hok⟩ := h
    obtain rfl : s = _ := hs
    obtain rfl := hsr
    cases u with
    | inl a =>
      cases v with
      | inl a' =>
        obtain rfl : a = a' := hFv
        exact ⟨ConsList.wrap (ConsList.wrap a), ⟨ConsList.wrap (ConsList.wrap a), rfl, rfl, hok⟩,
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
        have hhead : head x = head y := hQ.2
        -- the two glued paragraphs have the same first line, so `ok w` transfers
        have hokx : widthFn len (head (glue a x)) ≤ w := by
          rw [headLine_glue, hhead, ← headLine_glue a y]
          exact hok
        refine ⟨glue a x, ⟨glue a x, rfl, rfl, hokx⟩, ?_, ?_⟩
        · -- the waste of a glued paragraph is that of its tail plus one term fixed by the head
          cases x with
          | wrap lx =>
            show (0 : Int) ≤ wasteFn len w (glue a y)
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
              have hly : ly = lx := (show head (ConsList.cons lx x') = head
                (ConsList.wrap ly) from hhead).symm
              have hokw : len a + widthFn len ly + 1 ≤ w := hok
              have := hlen a
              rw [hly, hlx] at hokw
              omega
            | cons ly y' =>
              have hly : ly = lx := (show head (ConsList.cons lx x')
                = head (ConsList.cons ly y') from hhead).symm
              subst hly
              show sqr (w - widthFn len (ConsList.cons a ly)) + wasteFn len w x'
                ≤ sqr (w - widthFn len (ConsList.cons a ly)) + wasteFn len w y'
              have hx : sqr (w - widthFn len ly) + wasteFn len w x'
                ≤ sqr (w - widthFn len ly) + wasteFn len w y' := hwaste
              omega
        · show head (glue a x) = head (glue a y)
          rw [headLine_glue, headLine_glue, hhead]

/-- **para-mono**, the FALSE row (B&dM p.209, "the obvious greedy algorithm does not solve this
    specification"): `(𝟙×R) glue ⊑ glue R` fails.  Words are their own lengths, `w = 10`: the
    paragraph `[10]·[0]` wastes nothing and `[9]·[0]` wastes 1, yet gluing a length-0 word onto
    each reverses that — the first line overflows to 11, the second lands exactly on 10. -/
public theorem para_mono_glue_false :
    ¬ Freyd.Alg.Pres (F := F Int Int)
      (graph (Sum.elim (fun a : Int => ConsList.wrap (ConsList.wrap a)) (fun q : Int × Para Int => glue q.1 q.2)))
      (R (fun i : Int => i) 10) := by
  intro h
  have hRxy : wasteFn (fun i : Int => i) 10
        (ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))
      ≤ wasteFn (fun i : Int => i) 10
        (ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))) := by
    decide
  have hstep := le_iff.mp h
    (Sum.inr (0, ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))))
    (glue 0 (ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))))
    ⟨Sum.inr (0, ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))),
      ⟨rfl, hRxy⟩, rfl⟩
  obtain ⟨s, hs, hR⟩ := hstep
  obtain rfl : s = glue 0
    (ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))) := hs
  have hbad : wasteFn (fun i : Int => i) 10
        (glue 0 (ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))))
      ≤ wasteFn (fun i : Int => i) 10
        (glue 0 (ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))) := hR
  revert hbad
  decide

/-- **para-defn**, `P ≜ ⊤`: nothing is asked of the sorting order, so both algebras are
    monotonic on it. -/
public theorem para_sort_new :
    Freyd.Alg.Pres (F := F Word Word)
      (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2)))
      (topMor (dPara Word) (dPara Word)) :=
  Freyd.Alg.graph_pres_topMor _

public theorem para_sort_glue :
    Freyd.Alg.Pres (F := F Word Word)
      (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2)))
      (topMor (dPara Word) (dPara Word)) :=
  Freyd.Alg.graph_pres_topMor _

/-! ## `para-laws` -/

/-- **para-laws**, second and third rows: the specification is a catamorphism,
    `partition list⁺(fits w) = ⦇[wrap wrap,new] ∪ ([wrap wrap,glue](ok w))⦈`.  Proved by
    `relCata_fusion`, so only the algebra equation below is ever unfolded: testing every line
    of the result is the same as testing the first line at every step, given that every word
    fits on a line by itself and that gluing only widens a line. -/
public theorem para_alg_fusion (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w) :
    partAlg ≫ fits (len := len) w = (F Word Word).map (fits (len := len) w) ≫ Salg len w := by
  apply hom_ext; intro u r
  cases u with
  | inl a =>
    constructor
    · rintro ⟨s, hs, hsr, -⟩
      refine ⟨Sum.inl a, rfl, ?_⟩
      refine Or.inl ?_
      show r = ConsList.wrap (ConsList.wrap a)
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
        obtain rfl : s = glue a x := hs
        obtain ⟨hfx, hok⟩ := (allFitP_glue_iff hlen a x).mp hfitS
        exact ⟨Sum.inr (a, x), ⟨rfl, rfl, hfx⟩, Or.inr ⟨glue a x, rfl, rfl, hok⟩⟩
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
          obtain rfl : s = glue a x := hs
          obtain rfl : glue a x = r := hsr
          exact ⟨glue a x, Or.inr rfl, rfl, (allFitP_glue_iff hlen a x).mpr ⟨hfy, hok⟩⟩

public theorem para_spec (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w) :
    partition ≫ fits (len := len) w = ⦇Salg len w⦈ :=
  relCata_fusion (initial Word Word) (para_alg_fusion hlen hfit)

/-- B&dM's `g₁ ≜ list(new)` (§8.5, p.210): start a new line with the word. -/
@[expose] public def g₁ :=
  list (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2)))

/-- B&dM's `g₂ ≜ list(glue) filter(ok w)`: glue the word onto the last line, keep the layouts that fit. -/
@[expose] public def g₂ :=
  list (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2)))
    ≫ Filter.filter (ok (len := len) w)

/-- **para-laws**, the thinning step: Theorem 8.2 (`thinningList`) at `f₁ ≜ [wrap wrap,new]`,
    `p₁ ≜ 𝟙`, `f₂ ≜ [wrap wrap,glue]`, `p₂ ≜ ok w`, `P ≜ ⊤`.  Its specification side is the
    fold `⦇S⦈`, which `para_laws_step2` reads back as `partition list⁺(fits w)`. -/
public theorem para_laws_step1 (hlen : ∀ a, 0 ≤ len a) :
    ⦇cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
        (g₁ (Word := Word)) (g₂ (len := len) (w := w))
        ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q len w)⦈ ≫ minL (R len w)
      ⊑ Λ ⦇Salg len w⦈ ≫ est (R len w) := by
  have key := thinningList
    (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2))
    (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2)) (𝟙 _) (ok (len := len) w) (le_refl _) ok_coreflexive
    («≼» := topMor (dPara Word) (dPara Word)) (Q := Q len w) (R := R len w)
    Q_le_R ⟨Q_refl, Q_trans⟩ ⟨le_trans Q_refl Q_le_R, trans_of_recip_trans R_recip_trans⟩
    (by rw [Cat.comp_id]; exact para_mono_new) (para_mono_glue hlen)
    preorder_topMor connected_topMor para_sort_new para_sort_glue
  rw [filter_id, Cat.comp_id, Cat.comp_id] at key
  exact key

/-- **para-laws**, the specification step: `para_spec` under `Λ(−) est(R)`. -/
public theorem para_laws_step2 (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w) :
    Λ ⦇Salg len w⦈ ≫ est (R len w) = Λ (partition ≫ fits (len := len) w) ≫ est (R len w) := by
  rw [para_spec hlen hfit]

/-- **para-laws**, the algebra read as `(f₁p₁) ∪ (f₂p₂)` at `p₁ ≜ 𝟙` — the shape Theorem 8.2
    takes it in. -/
public theorem para_laws_split :
    Λ ⦇Salg len w⦈ ≫ est (R len w)
      = Λ ⦇(graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a))
              (fun q : Word × Para Word => new q.1 q.2)) ≫ 𝟙 (dPara Word))
          ∪ (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a))
              (fun q : Word × Para Word => glue q.1 q.2)) ≫ ok (len := len) w)⦈
          ≫ est (R len w) := by
  rw [Cat.comp_id]; rfl

/-- **para-laws** (B&dM §8.5, p.210): a paragraph laid out as a fold that thins the layouts
    kept at each word —
    `Λ(partition list⁺(fits w)) est(R) ⊒ ⦇cpL(F) ⟨g₁,g₂⟩ merge ⊤ thinL Q⦈ minL R`.
    Theorem 8.2 (`thinningList`) at `f₁ ≜ [wrap wrap,new]`, `p₁ ≜ 𝟙`,
    `f₂ ≜ [wrap wrap,glue]`, `p₂ ≜ ok w`, `P ≜ ⊤`, with `para-mono` discharging the
    monotonicity conditions and `para_spec` the specification. -/
public theorem para_laws (hlen : ∀ a, 0 ≤ len a) (hfit : ∀ a, len a ≤ w) :
    ⦇cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
        (g₁ (Word := Word)) (g₂ (len := len) (w := w))
        ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q len w)⦈ ≫ minL (R len w)
      ⊑ Λ (partition ≫ fits (len := len) w) ≫ est (R len w) := by
  rw [← para_laws_step2 hlen hfit]
  exact para_laws_step1 hlen

end Freyd.Alg.RelSet.Paragraph

-- printing-only (B&dM pp.207–210): the ordering is the note's `R` and the step algebra `S` (drawn
-- opened, so the letter shows only where a label names it whole); the length function `len` is the
-- section's context and is dropped, while `w` and the paragraph stay as the book writes them.
-- The predicate under the coreflexive `fits(w)` is written `fits`.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.R] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParagraphR : Unexpander
  | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.Salg] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParagraphSalg : Unexpander
  | _ => `($(mkIdent `S))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.widthFn] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParaWidth : Unexpander
  | `($_ $_ $x) => `($(mkIdent `width) $x)
  | _ => `($(mkIdent `width))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.wasteFn] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParaWaste : Unexpander
  | `($_ $_ $w $p) => `($(mkIdent `waste) $w $p)
  | `($_ $_ $w) => `($(mkIdent `waste) $w)
  | _ => `($(mkIdent `waste))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.allFitP] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParaAllFitP : Unexpander
  | `($_ $_ $w $p) => `($(mkIdent `fits) $w $p)
  | `($_ $_ $w) => `($(mkIdent `fits) $w)
  | _ => `($(mkIdent `fits))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.okP] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParaOkP : Unexpander
  | `($_ $w $xss) => `($(mkIdent `ok) $w $xss)
  | `($_ $w) => `($(mkIdent `ok) $w)
  | _ => `($(mkIdent `ok))
