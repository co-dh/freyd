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
  - `hfit : ∀ a : Word, len a ≤ w` — the note's "every word fits on a line by itself", which the
    fusion step needs;
  - `hlen : ∀ a : Word, 0 ≤ len a` — words are not of negative length.  The fusion needs it (a line
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
public import AOP.A6_FinRel
import AOP.A8_2

/-- B&dM p.208: the section's fixed data, the length `len` of a word.  Every definition below reads
    it from the one instance in scope, so the printer, which hides instance arguments, shows the
    book's `width`, not `width len`.  Named after the section's namespace, so the field prints as
    the bare `len`. -/
public class Freyd.Alg.RelSet.Paragraph (Word : Type) where
  len : Word → Int

namespace Freyd.Alg.RelSet.Paragraph
open PowerAllegory

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {Word : Type} {w : Int}

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
@[expose] public def width [Paragraph Word] : Line Word → Int
  | ConsList.wrap a => len a
  | ConsList.cons a xs => len a + width xs + 1

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
@[expose] public def waste [Paragraph Word] (w : Int) : Para Word → Int
  | ConsList.wrap _ => 0
  | ConsList.cons xs xss => sqr (w - width xs) + waste w xss

public theorem waste_nonneg [Paragraph Word] : ∀ p : Para Word, 0 ≤ waste w p
  | ConsList.wrap _ => Int.le_refl _
  | ConsList.cons _ p => Int.add_nonneg (sqr_nonneg _) (waste_nonneg p)

/-- `list⁺(fits w)`: every line of the paragraph fits. -/
@[expose] public def allFitP [Paragraph Word] (w : Int) : Para Word → Prop
  | ConsList.wrap xs => width xs ≤ w
  | ConsList.cons xs xss => width xs ≤ w ∧ allFitP w xss

/-- **para-defn**: `list⁺(fits w)`, the coreflexive on paragraphs all of whose lines fit. -/
@[expose] public def fits [Paragraph Word] (w : Int) : dPara Word ⟶ dPara Word := corefl (allFitP w)

/-- **para-defn**: `ok w`, the predicate on `[x]⧺xs` with `width x ≤ w` — only the FIRST line is
    tested. -/
@[expose] public def okP [Paragraph Word] (w : Int) (xss : Para Word) : Prop := width (head xss) ≤ w

/-- `ok w` as an arrow: the coreflexive of `okP`. -/
@[expose] public def ok [Paragraph Word] (w : Int) : dPara Word ⟶ dPara Word := corefl (okP w)

public theorem fits_coreflexive [Paragraph Word] : Coreflexive (fits (Word := Word) w) :=
  le_iff.mpr fun _ _ h => h.1

public theorem ok_coreflexive [Paragraph Word] : Coreflexive (ok (Word := Word) w) :=
  le_iff.mpr fun _ _ h => h.1

/-- **para-defn**: `R ≜ (waste w) ≤ (waste w)°`. -/
@[expose] public def R [Paragraph Word] {w : Int} : dPara Word ⟶ dPara Word :=
  fun xss yss => waste w xss ≤ waste w yss

/-- `R = waste ≤ waste°`, point-free. -/
public theorem R_eq [Paragraph Word] :
    R (w := w)
      = graph (waste w) ≫ leq
        ≫ (graph (waste w) : dPara Word ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro p q
  constructor
  · intro h; exact ⟨waste w p, rfl, waste w q, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    show waste w p ≤ waste w q
    rw [← (show m = waste w p from hm), ← (show n = waste w q from hn)]
    exact hmn

/-- **para-defn**: `Q ≜ R ∩ (head head°)` — no more wasteful, and with the same first line. -/
@[expose] public def Q [Paragraph Word] (w : Int) : dPara Word ⟶ dPara Word :=
  fun xss yss => waste w xss ≤ waste w yss ∧ head xss = head yss

/-- `Q = R ∩ (head head°)`, point-free. -/
public theorem Q_eq [Paragraph Word] :
    Q w
      = R (w := w) ∩ (graph head ≫ (graph head : dPara Word ⟶ ⟨Line Word⟩)°) := by
  apply hom_ext; intro p q
  constructor
  · rintro ⟨hr, hh⟩; exact ⟨hr, head p, rfl, hh⟩
  · rintro ⟨hr, m, hm, hm'⟩
    refine ⟨hr, ?_⟩
    rw [(show m = head p from hm)] at hm'
    exact hm'

/-- `xss R yss` iff `xss` wastes no more than `yss`: the pointwise reading of `R_eq`. -/
public theorem R_apply [Paragraph Word] (xss yss : Para Word) :
    R (w := w) xss yss ↔ waste w xss ≤ waste w yss := Iff.rfl

/-- `xss Q yss` iff `xss` wastes no more than `yss` and has the same first line. -/
public theorem Q_apply [Paragraph Word] (xss yss : Para Word) :
    Q w xss yss ↔ waste w xss ≤ waste w yss ∧ head xss = head yss := Iff.rfl

/-- `xss (fits w) yss` iff `xss = yss` and every line of `xss` is at most `w` wide. -/
public theorem fits_apply [Paragraph Word] (xss yss : Para Word) :
    fits w xss yss ↔ xss = yss ∧ allFitP w xss := Iff.rfl

/-- `xss (ok w) yss` iff `xss = yss` and the first line of `xss` is at most `w` wide. -/
public theorem ok_apply [Paragraph Word] (xss yss : Para Word) :
    ok w xss yss ↔ xss = yss ∧ width (head xss) ≤ w := Iff.rfl

public theorem Q_le_R [Paragraph Word] : Q (Word := Word) w ⊑ R (w := w) := le_iff.mpr fun _ _ h => h.1

public theorem Q_refl [Paragraph Word] : 𝟙 (dPara Word) ⊑ Q w :=
  le_iff.mpr fun p q h => by obtain rfl : p = q := h; exact ⟨Int.le_refl _, rfl⟩

public theorem Q_trans [Paragraph Word] : Q (Word := Word) w ≫ Q w ⊑ Q w :=
  le_iff.mpr fun _ _ h => by
    obtain ⟨_, ⟨hr1, hh1⟩, ⟨hr2, hh2⟩⟩ := h
    exact ⟨Int.le_trans hr1 hr2, hh1.trans hh2⟩

public theorem R_recip_trans [Paragraph Word] : (R (Word := Word) (w := w))° ≫ (R (w := w))° ⊑ (R (w := w))° :=
  le_iff.mpr fun p r h => by
    obtain ⟨q, h1, h2⟩ := h
    exact Int.le_trans (h2 : waste w r ≤ waste w q)
      (h1 : waste w q ≤ waste w p)

/-! ## The two algebras `[wrap wrap,new]` and `[wrap wrap,glue]` -/

/-- **para-defn**: `new (a,xs)=[[a]]⧺xs` — open a new line for the word.  Named for the same
    reason `glue` is: it is one arm of the algebra the note draws, and an arm is written by its
    own name. -/
@[expose] public def new (a : Word) (xss : Para Word) : Para Word := ConsList.cons (ConsList.wrap a) xss

-- The algebras `[wrap wrap,new]` and `[wrap wrap,glue]` are the copairing `Sum.elim` of maps
-- already named, so they are written out at each use rather than given names of their own.

/-- **para-defn**: `partition ≜ ⦇[wrap wrap,new∪glue]⦈` — every way of breaking the words into
    lines. -/
@[expose] public def partAlg : Alg (F Word Word) (dPara Word) :=
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
@[expose] public def S [Paragraph Word] {w : Int} :
    Alg (F Word Word) (dPara Word) :=
  graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2))
    ∪ (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2))
      ≫ ok w)

/-! ## `para-mono` -/

/-- Gluing a word onto a paragraph that fits leaves a paragraph that fits, and conversely —
    the step that lets the fusion below test only the FIRST line.  Needs `0 ≤ len a`: a glued
    line is wider than the line it was glued to. -/
public theorem allFitP_glue_iff [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) (a : Word) (p : Para Word) :
    allFitP w (glue a p)
      ↔ allFitP w p ∧ width (head (glue a p)) ≤ w := by
  have hgrow : ∀ l : Line Word, width l ≤ width (ConsList.cons a l) := by
    intro l
    have := hlen a
    show width l ≤ len a + width l + 1
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
public theorem para_mono_new [Paragraph Word] :
    Freyd.Alg.Pres (F := F Word Word)
      (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2)))
      (Q w) :=
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
        have hxy : waste w x ≤ waste w y := hQ.1
        refine ⟨ConsList.cons (ConsList.wrap a) x, rfl, ?_, rfl⟩
        show sqr (w - len a) + waste w x ≤ sqr (w - len a) + waste w y
        omega

/-- **para-mono**, second row: `(𝟙×Q)(glue (ok w)) ⊑ glue (ok w)Q` — `Q` pins the first line,
    which is the only thing `glue` changes and the only thing `waste` reads about it. -/
public theorem para_mono_glue [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) :
    Freyd.Alg.Pres (F := F Word Word)
      (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2))
        ≫ ok w) (Q w) :=
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
        have hwaste : waste w x ≤ waste w y := hQ.1
        have hhead : head x = head y := hQ.2
        -- the two glued paragraphs have the same first line, so `ok w` transfers
        have hokx : width (head (glue a x)) ≤ w := by
          rw [headLine_glue, hhead, ← headLine_glue a y]
          exact hok
        refine ⟨glue a x, ⟨glue a x, rfl, rfl, hokx⟩, ?_, ?_⟩
        · -- the waste of a glued paragraph is that of its tail plus one term fixed by the head
          cases x with
          | wrap lx =>
            show (0 : Int) ≤ waste w (glue a y)
            exact waste_nonneg _
          | cons lx x' =>
            cases y with
            | wrap ly =>
              -- vacuous: `waste x ≤ 0` forces `width lx = w`, and then the glued line overflows
              exfalso
              have hx0 : sqr (w - width lx) + waste w x' ≤ 0 := hwaste
              have h1 : 0 ≤ sqr (w - width lx) := sqr_nonneg _
              have h2 : 0 ≤ waste w x' := waste_nonneg _
              have hz : sqr (w - width lx) = 0 := by omega
              have hlx : width lx = w := by
                have := sqr_eq_zero hz; omega
              have hly : ly = lx := (show head (ConsList.cons lx x') = head
                (ConsList.wrap ly) from hhead).symm
              have hokw : len a + width ly + 1 ≤ w := hok
              have := hlen a
              rw [hly, hlx] at hokw
              omega
            | cons ly y' =>
              have hly : ly = lx := (show head (ConsList.cons lx x')
                = head (ConsList.cons ly y') from hhead).symm
              subst hly
              show sqr (w - width (ConsList.cons a ly)) + waste w x'
                ≤ sqr (w - width (ConsList.cons a ly)) + waste w y'
              have hx : sqr (w - width ly) + waste w x'
                ≤ sqr (w - width ly) + waste w y' := hwaste
              omega
        · show head (glue a x) = head (glue a y)
          rw [headLine_glue, headLine_glue, hhead]

section Counterexample

/-- The refutation's words are their own lengths. -/
@[expose] public def lenId : Paragraph Int := ⟨fun i => i⟩
attribute [local instance] lenId

/-- **para-mono**, the FALSE row (B&dM p.209, "the obvious greedy algorithm does not solve this
    specification"): `(𝟙×R) glue ⊑ glue R` fails.  Words are their own lengths, `w = 10`: the
    paragraph `[10]·[0]` wastes nothing and `[9]·[0]` wastes 1, yet gluing a length-0 word onto
    each reverses that — the first line overflows to 11, the second lands exactly on 10. -/
public theorem para_mono_glue_false :
    ¬ Freyd.Alg.Pres (F := F Int Int)
      (graph (Sum.elim (fun a : Int => ConsList.wrap (ConsList.wrap a)) (fun q : Int × Para Int => glue q.1 q.2)))
      (R (w := 10)) := by
  intro h
  have hRxy : waste 10
        (ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))
      ≤ waste 10
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
  have hbad : waste 10
        (glue 0 (ConsList.cons (ConsList.wrap (10 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int)))))
      ≤ waste 10
        (glue 0 (ConsList.cons (ConsList.wrap (9 : Int)) (ConsList.wrap (ConsList.wrap (0 : Int))))) := hR
  revert hbad
  decide

end Counterexample

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
public theorem para_alg_fusion [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) (hfit : ∀ a : Word, len a ≤ w) :
    partAlg ≫ fits w = (F Word Word).map (fits w) ≫ S (w := w) := by
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

public theorem para_spec [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) (hfit : ∀ a : Word, len a ≤ w) :
    partition ≫ fits w = ⦇S (Word := Word) (w := w)⦈ :=
  relCata_fusion (initial Word Word) (para_alg_fusion hlen hfit)

/-- B&dM's `g₁ ≜ list(new)` (§8.5, p.210): start a new line with the word. -/
@[expose] public def g₁ :=
  list (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2)))

/-- B&dM's `g₂ ≜ list(glue) filter(ok w)`: glue the word onto the last line, keep the layouts that fit. -/
@[expose] public def g₂ [Paragraph Word] :=
  list (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2)))
    ≫ Filter.filter (ok w)

/-- **para-laws**, the thinning step: Theorem 8.2 (`thinningList`) at `f₁ ≜ [wrap wrap,new]`,
    `p₁ ≜ 𝟙`, `f₂ ≜ [wrap wrap,glue]`, `p₂ ≜ ok w`, `P ≜ ⊤`.  Its specification side is the
    fold `⦇S⦈`, which `para_laws_step2` reads back as `partition list⁺(fits w)`. -/
public theorem para_laws_step1 [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) :
    ⦇cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
        (g₁ (Word := Word)) (g₂ (w := w))
        ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)⦈ ≫ minL (R (w := w))
      ⊑ Λ ⦇S (Word := Word) (w := w)⦈ ≫ est (R (w := w)) := by
  have key := thinningList
    (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => new q.1 q.2))
    (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a)) (fun q : Word × Para Word => glue q.1 q.2)) (𝟙 _) (ok w) (le_refl _) ok_coreflexive
    («≼» := topMor (dPara Word) (dPara Word)) (Q := Q w) (R := R (w := w))
    Q_le_R ⟨Q_refl, Q_trans⟩ ⟨le_trans Q_refl Q_le_R, trans_of_recip_trans R_recip_trans⟩
    (by rw [Cat.comp_id]; exact para_mono_new) (para_mono_glue hlen)
    preorder_topMor connected_topMor para_sort_new para_sort_glue
  rw [filter_id, Cat.comp_id, Cat.comp_id] at key
  exact key

/-- **para-laws**, the specification step: `para_spec` under `Λ(−) est(R)`. -/
public theorem para_laws_step2 [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) (hfit : ∀ a : Word, len a ≤ w) :
    Λ ⦇S (Word := Word) (w := w)⦈ ≫ est (R (w := w)) = Λ (partition ≫ fits w) ≫ est (R (w := w)) := by
  rw [para_spec hlen hfit]

/-- **para-laws**, the algebra read as `(f₁p₁) ∪ (f₂p₂)` at `p₁ ≜ 𝟙` — the shape Theorem 8.2
    takes it in. -/
public theorem para_laws_split [Paragraph Word] :
    Λ ⦇S (Word := Word) (w := w)⦈ ≫ est (R (w := w))
      = Λ ⦇(graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a))
              (fun q : Word × Para Word => new q.1 q.2)) ≫ 𝟙 (dPara Word))
          ∪ (graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a))
              (fun q : Word × Para Word => glue q.1 q.2)) ≫ ok w)⦈
          ≫ est (R (w := w)) := by
  rw [Cat.comp_id]; rfl

/-- **para-laws** (B&dM §8.5, p.210): a paragraph laid out as a fold that thins the layouts
    kept at each word —
    `Λ(partition list⁺(fits w)) est(R) ⊒ ⦇cpL(F) ⟨g₁,g₂⟩ merge ⊤ thinL Q⦈ minL R`.
    Theorem 8.2 (`thinningList`) at `f₁ ≜ [wrap wrap,new]`, `p₁ ≜ 𝟙`,
    `f₂ ≜ [wrap wrap,glue]`, `p₂ ≜ ok w`, `P ≜ ⊤`, with `para-mono` discharging the
    monotonicity conditions and `para_spec` the specification. -/
public theorem para_laws [Paragraph Word] (hlen : ∀ a : Word, 0 ≤ len a) (hfit : ∀ a : Word, len a ≤ w) :
    ⦇cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
        (g₁ (Word := Word)) (g₂ (w := w))
        ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)⦈ ≫ minL (R (w := w))
      ⊑ Λ (partition ≫ fits w) ≫ est (R (w := w)) := by
  rw [← para_laws_step2 hlen hfit]
  exact para_laws_step1 hlen

/-! ## The fold's body split at the two summands (B&dM pp.210–211) -/

/-- B&dM's `h₁ ≜ list(new)` (p.211): `g₁` on the pair summand. -/
@[expose] public def h₁ : dList (Word × Para Word) ⟶ dList (Para Word) :=
  list (graph (fun q : Word × Para Word => new q.1 q.2))

/-- B&dM's `h₂ ≜ list(glue) filter(ok w)` (p.211): `g₂` on the pair summand. -/
@[expose] public def h₂ [Paragraph Word] : dList (Word × Para Word) ⟶ dList (Para Word) :=
  list (graph (fun q : Word × Para Word => glue q.1 q.2)) ≫ Filter.filter (ok w)

/-- Two wraps are the map to the one-word paragraph: `wrap wrap = [[·]]`. -/
public theorem τ_τ :
    ((τ : dL Word ⟶ dCL Word Word) ≫ (τ : dL (Line Word) ⟶ dPara Word))
      = graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) := by
  apply hom_ext; intro a r
  constructor
  · rintro ⟨_, h1, h2⟩; obtain rfl : _ = ConsList.wrap a := h1; exact h2
  · intro h; exact ⟨_, rfl, h⟩

/-- A word that fits makes a one-word paragraph that passes `ok w`: `[[·]] ok(w) = [[·]]`. -/
public theorem τ_τ_ok [Paragraph Word] (hfit : ∀ a : Word, len a ≤ w) :
    graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) ≫ ok w
      = (graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word) := by
  apply hom_ext; intro a r
  constructor
  · rintro ⟨_, rfl, rfl, -⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl, hfit a⟩

/-- `merge(⊤)` on lists of paragraphs is natural in the word type, since it is `cat` (`merge_top`),
`cat` is, and composing with the paragraph relator on the inside keeps it so. -/
public theorem merge_top_strictNatural :
    StrictNatural
      (Relator.comp (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
        nelistRelator) listRelator)
      (Relator.prod
        (Relator.comp (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
          nelistRelator) listRelator)
        (Relator.comp (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
          nelistRelator) listRelator))
      (fun a => merge (topMor (dPara a.carrier) (dPara a.carrier))) := by
  have h : (fun a : RelSet.{0} => (merge (topMor (dPara a.carrier) (dPara a.carrier))
      : (relProd (dList (Para a.carrier)) (dList (Para a.carrier))).p ⟶ dList (Para a.carrier)))
      = fun a : RelSet.{0} => cat (A := Para a.carrier) := funext fun _ => merge_top
  rw [h]
  intro _ _ R
  exact strictNatural_inside (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
    nelistRelator) (@cat_strictNatural) R

/-- The one-word paragraph `wrap wrap` is STRICTLY natural, `R [[·]] = [[·]] list⁺(list⁺(R))`:
    the dot on the base arm of the fold's body once `[f,g]` is drawn as its two arms. -/
public theorem τ_τ_strictNatural :
    StrictNatural (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
        nelistRelator) (Relator.idRelator RelSet.{0})
      (fun a => (graph (fun x : a.carrier => (ConsList.wrap (ConsList.wrap x) : Para a.carrier))
        : a ⟶ dPara a.carrier)) := by
  intro x y R
  apply hom_ext; intro a r
  constructor
  · rintro ⟨b, hab, rfl⟩; exact ⟨_, rfl, hab⟩
  · rintro ⟨_, rfl, h⟩
    match r, h with
    | ConsList.wrap (ConsList.wrap b), h => exact ⟨b, h, rfl⟩

/-- `start ≜ wrap wrap wrap` is STRICTLY natural, `R [[[·]]] = [[[·]]] list(list⁺(list⁺(R)))`. -/
public theorem start_strictNatural :
    StrictNatural (Relator.comp (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0})
        nelistRelator) nelistRelator) listRelator) (Relator.idRelator RelSet.{0})
      (fun a => (graph (fun x : a.carrier => (ConsList.wrap (ConsList.wrap x) : Para a.carrier))
        : a ⟶ dPara a.carrier) ≫ τₗ ()) := by
  intro x y R
  apply hom_ext; intro a r
  constructor
  · rintro ⟨b, hab, _, rfl, rfl⟩; exact ⟨_, ⟨_, rfl, rfl⟩, hab, rfl⟩
  · rintro ⟨_, ⟨_, rfl, rfl⟩, h⟩
    match r, h with
    | ConsList.cons (ConsList.wrap (ConsList.wrap b)) (ConsList.wrap ()), ⟨h, _⟩ =>
      exact ⟨b, h, _, rfl, rfl⟩

/-- The pair `⟨start,start⟩` is LAX natural, and no more: the two copies may move apart under
    `R` on the right, where on the left they are the one word's image. -/
public theorem start_pair_laxNatural :
    LaxNatural
      (Relator.prod
        (Relator.comp (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
          nelistRelator) listRelator)
        (Relator.comp (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) nelistRelator)
          nelistRelator) listRelator))
      (Relator.idRelator RelSet.{0})
      (fun a => (relProd (dList (Para a.carrier)) (dList (Para a.carrier))).pair
        ((graph (fun x : a.carrier => (ConsList.wrap (ConsList.wrap x) : Para a.carrier))
          : a ⟶ dPara a.carrier) ≫ τₗ ())
        ((graph (fun x : a.carrier => (ConsList.wrap (ConsList.wrap x) : Para a.carrier))
          : a ⟶ dPara a.carrier) ≫ τₗ ())) :=
  laxNatural_pair (laxNatural_of_strictNatural start_strictNatural)
    (laxNatural_of_strictNatural start_strictNatural)

/-- **The fold's body split** (B&dM pp.210–211): on a single word the body keeps the one-word
    paragraph `start ≜ wrap wrap wrap`, and on a word and a list of layouts it is
    `cpr ⟨h₁,h₂⟩ merge(⊤) thinL(Q)`.  `⊑`, not `=`: on `[s,s]` `thinL(Q)` may keep both copies. -/
public theorem para_body_split [Paragraph Word] (hfit : ∀ a : Word, len a ≤ w) :
    junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((τ : dL Word ⟶ dCL Word Word) ≫ (τ : dL (Line Word) ⟶ dPara Word)
          ≫ τₗ ())
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
      ⊑ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w) :=
  calc junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((τ : dL Word ⟶ dCL Word Word) ≫ (τ : dL (Line Word) ⟶ dPara Word)
          ≫ τₗ ())
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
      = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
          ≫ τₗ ())
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc τ τ, τ_τ]
    _ ⊑ junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
          ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair (τₗ ()) (τₗ ())
          ≫ cat ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) :=
        junc_mono _ (comp_mono_left _ (τ_le_dup_cat_thinL Q_refl)) (le_refl _)
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
          ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair (τₗ ()) (τₗ ())
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [merge_top]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
              ≫ τₗ ())
            ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
              ≫ τₗ ())
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc (graph _), RelProd.map_comp_pair (graph_map _)]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
              ≫ τₗ ())
            ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
              ≫ ok w ≫ τₗ ())
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc (graph _) (ok _), τ_τ_ok hfit]
    _ ⊑ junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
              ≫ τₗ ())
            ((graph (fun a : Word => ConsList.wrap (ConsList.wrap a)) : dL Word ⟶ dPara Word)
              ≫ τₗ () ≫ Filter.filter (ok w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) :=
        junc_mono _ (comp_mono_right (RelProd.pair_mono (le_refl _)
          (comp_mono_left _ (corefl_τ_le_filter ok_coreflexive))) _) (le_refl _)
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            ((graph Sum.inl : dL Word ⟶ (F Word Word).obj (dPara Word))
              ≫ graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a))
                  (fun q : Word × Para Word => new q.1 q.2))
              ≫ τₗ ())
            ((graph Sum.inl : dL Word ⟶ (F Word Word).obj (dPara Word))
              ≫ graph (Sum.elim (fun a : Word => ConsList.wrap (ConsList.wrap a))
                  (fun q : Word × Para Word => glue q.1 q.2))
              ≫ τₗ () ≫ Filter.filter (ok w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc (graph Sum.inl) (graph (Sum.elim _ (fun q : Word × Para Word => new q.1 q.2))),
          ← Cat.assoc (graph Sum.inl) (graph (Sum.elim _ (fun q : Word × Para Word => glue q.1 q.2))),
          inl_elim, inl_elim]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            ((graph Sum.inl : dL Word ⟶ (F Word Word).obj (dPara Word)) ≫ τₗ ()
              ≫ g₁ (Word := Word))
            ((graph Sum.inl : dL Word ⟶ (F Word Word).obj (dPara Word)) ≫ τₗ ()
              ≫ g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        unfold g₁ g₂
        rw [← Cat.assoc (τₗ ()) (list _) (Filter.filter _), τ_natural, τ_natural,
          Cat.assoc]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁ ≫ cpL ≫ g₁ (Word := Word))
            ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁ ≫ cpL
              ≫ g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc _ cpL g₁, ← Cat.assoc _ cpL g₂, inl_cpL, Cat.assoc _ _ g₁,
          Cat.assoc _ _ g₂]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁
          ≫ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (h₁ (Word := Word)) (h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← RelProd.map_comp_pair (show Map (sumCop (dL Word)
            (⟨Word × ConsList Unit (Para Word)⟩ : RelSet.{0})).u₁ from graph_map _),
          ← RelProd.map_comp_pair (show Map (cpL (L := Word) (E := Word) (X := Para Word))
            from graph_map _), Cat.assoc, Cat.assoc]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁
          ≫ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            (cpr ≫ h₁ (Word := Word)) (cpr ≫ h₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc cpr, RelProd.map_comp_pair
          (show Map (cpr (A := Word) (B := Para Word)) from graph_map _)]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁
          ≫ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        ((relProd (dList (Para Word)) (dList (Para Word))).pair
            (cpr ≫ list (graph Sum.inr : dE (Word × Para Word) ⟶ dE (Word ⊕ Word × Para Word))
              ≫ g₁ (Word := Word))
            (cpr ≫ list (graph Sum.inr : dE (Word × Para Word) ⟶ dE (Word ⊕ Word × Para Word))
              ≫ g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        unfold g₁ g₂ h₁ h₂
        rw [list_inr_elim, ← Cat.assoc (list (graph Sum.inr)) (list _) (Filter.filter _),
          list_inr_elim]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁
          ≫ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        (cpr ≫ list (graph Sum.inr : dE (Word × Para Word) ⟶ dE (Word ⊕ Word × Para Word))
          ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← RelProd.map_comp_pair (show Map (cpr (A := Word) (B := Para Word)) from graph_map _),
          ← RelProd.map_comp_pair (map_list_graph (Sum.inr : Word × Para Word → Word ⊕ Word × Para Word)),
          Cat.assoc, Cat.assoc]
    _ = junc (sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩)
        ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₁
          ≫ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w))
        ((sumCop (dL Word) ⟨Word × ConsList Unit (Para Word)⟩).u₂
          ≫ cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
            (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w)) := by
        rw [← Cat.assoc (sumCop (dL Word) (⟨Word × ConsList Unit (Para Word)⟩ : RelSet.{0})).u₂ cpL,
          inr_cpL, Cat.assoc]
    _ = cpL ≫ (relProd (dList (Para Word)) (dList (Para Word))).pair
          (g₁ (Word := Word)) (g₂ (w := w))
          ≫ merge (topMor (dPara Word) (dPara Word)) ≫ thinL (Q w) :=
        (junc_unique _ rfl rfl).symm

calc_steps para_body_split

/-! ## `ParaRun`: the paragraph program on `RelRep`

The fold keeps a list of layouts: `step` puts each word on a new line of every kept layout and,
when the first line still fits, also glues it on; `RelRep.thin Q` cuts the candidates, and
`RelRep.est R` reads the least wasteful layouts off the last list. -/

section ParaRun

variable [DecidableEq Word] [Paragraph Word] (w)

omit [Paragraph Word] in
-- Structural, so a run reduces by `rfl`: the derived `DecidableEq (ConsList …)` does not.
@[expose] public def decLine : ∀ xs ys : Line Word, Decidable (xs = ys)
  | ConsList.wrap a, ConsList.wrap b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (by cases e; rfl)
  | ConsList.cons a xs, ConsList.cons b ys =>
    if h : a = b then
      match decLine xs ys with
      | isTrue e => isTrue (h ▸ e ▸ rfl)
      | isFalse n => isFalse fun e => n (by cases e; rfl)
    else isFalse fun e => h (by cases e; rfl)
  | ConsList.wrap _, ConsList.cons _ _ => isFalse fun e => by cases e
  | ConsList.cons _ _, ConsList.wrap _ => isFalse fun e => by cases e

public instance decQ : ∀ xss yss : Para Word, Decidable (Q w xss yss) :=
  fun xss yss => @decidable_of_iff _ _ (Q_apply (w := w) xss yss).symm
    (@instDecidableAnd _ _ (Int.decLe _ _) (decLine (head xss) (head yss)))

public instance decR : ∀ xss yss : Para Word, Decidable (R (w := w) xss yss) :=
  fun xss yss => decidable_of_iff _ (R_apply (w := w) xss yss).symm

/-- The thinning order `Q` as a `RelRep` test. -/
@[expose] public def Qt : RelRep (Para Word) (Para Word) := .test fun xss yss => decide (Q w xss yss)

public theorem rel_Qt : (Qt (Word := Word) w).rel = Q w := hom_ext fun _ _ => decide_eq_true_iff

/-- The waste order `R` as a `RelRep` test. -/
@[expose] public def Rt : RelRep (Para Word) (Para Word) := .test fun xss yss => decide (R (w := w) xss yss)

public theorem rel_Rt : (Rt (Word := Word) w).rel = R (w := w) := hom_ext fun _ _ => decide_eq_true_iff

/-- The step's `Λ` form: the word on a new line, and glued onto the first line when that still fits. -/
@[expose] public def step (q : Word × Para Word) : List (Para Word) :=
  if width (head (glue q.1 q.2)) ≤ w then [new q.1 q.2, glue q.1 q.2] else [new q.1 q.2]

omit [DecidableEq Word] in
/-- `step` is the pair half of `S`: `new ∪ glue (ok w)`. -/
public theorem rel_step :
    (RelRep.enum (step (Word := Word) w)).rel
      = (graph Sum.inr : (⟨Word × Para Word⟩ : RelSet.{0}) ⟶ (F Word Word).obj (dPara Word)) ≫ S (w := w) :=
  hom_ext fun q r => by
    show r ∈ step w q ↔ ∃ u, _ ∧ _
    unfold step
    constructor
    · intro h
      refine ⟨Sum.inr q, rfl, ?_⟩
      by_cases hok : width (head (glue q.1 q.2)) ≤ w
      · rw [if_pos hok] at h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl, rfl, hok⟩
      · rw [if_neg hok] at h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        subst h; exact Or.inl rfl
    · rintro ⟨u, hu, hS⟩
      obtain rfl : u = Sum.inr q := hu
      rcases hS with h | ⟨s, hs, hsr, hok⟩
      · obtain rfl : r = new q.1 q.2 := h
        split <;> simp
      · obtain rfl : s = glue q.1 q.2 := hs
        obtain rfl : glue q.1 q.2 = r := hsr
        rw [if_pos (show width (head (glue q.1 q.2)) ≤ w from hok)]
        simp

omit [DecidableEq Word] in
/-- `S` is the junction of the one-word paragraph and `step`. -/
public theorem S_eq_junc :
    S (w := w) = junc (sumCop (dL Word) ⟨Word × Para Word⟩)
      (RelRep.ofFn fun a : Word => (ConsList.wrap (ConsList.wrap a) : Para Word)).rel
      (RelRep.enum (step (Word := Word) w)).rel :=
  junc_unique _ (hom_ext fun a r => by
    show (∃ u, _ ∧ _) ↔ r ∈ [ConsList.wrap (ConsList.wrap a)]
    rw [List.mem_singleton]
    constructor
    · rintro ⟨u, hu, hS⟩
      obtain rfl : u = Sum.inl a := hu
      rcases hS with h | ⟨s, hs, hsr, -⟩
      · exact h
      · obtain rfl : s = _ := hs
        exact (hsr : _ = r).symm
    · intro h; exact ⟨Sum.inl a, rfl, Or.inl h⟩) (rel_step w).symm

/-- The layouts kept after the whole text: `⦇thin(Q)·Λ(S)⦈` as a function. -/
@[expose] public def kept : ConsList Word Word → List (Para Word) :=
  RelRep.foldList (RelRep.thinList fun xss yss => decide (Q w xss yss))
    (fun a => [ConsList.wrap (ConsList.wrap a)]) (step w)

/-- `kept` is `RelRep.foldThin Q` of the one-word paragraph and `step`. -/
public theorem kept_eq :
    RelRep.foldThin (Qt (Word := Word) w) (.ofFn fun a : Word => (ConsList.wrap (ConsList.wrap a) : Para Word))
      (.enum (step w)) = some (.enum (kept w)) := rfl

/-- The program: the least wasteful layouts among those kept. -/
@[expose] public def paragraph (xs : ConsList Word Word) : List (Para Word) :=
  RelRep.estList (fun xss yss => decide (R (w := w) xss yss)) (kept w xs)

/-- `paragraph` is `RelRep.est R` of `kept`. -/
public theorem paragraph_eq :
    RelRep.est (Rt (Word := Word) w) (.enum (kept w)) = some (.enum (paragraph w)) := rfl

/-- `Λ(kept) ⊑ Λ⦇S⦈ thin(Q)`. -/
public theorem kept_thin (hlen : ∀ a : Word, 0 ≤ len a) :
    Λ (RelRep.enum (kept (Word := Word) w)).rel ⊑ Λ ⦇S (Word := Word) (w := w)⦈ ≫ thinRel (Q w) := by
  have h := RelRep.rel_foldThin (h := kept_eq (Word := Word) w) (by rw [rel_Qt (Word := Word) w]; exact Q_refl (Word := Word))
    (by rw [rel_Qt (Word := Word) w]; exact Q_trans (Word := Word))
    (by rw [rel_Qt (Word := Word) w, ← S_eq_junc]; exact pres_union para_mono_new (para_mono_glue hlen))
  rw [← S_eq_junc, rel_Qt (Word := Word) w] at h
  exact h

/-- **The program meets its specification**: every layout `paragraph` returns is a least wasteful
    layout all of whose lines fit, `paragraph ⊑ Λ(partition list⁺(fits w)) est(R)`. -/
public theorem paragraph_le (hlen : ∀ a : Word, 0 ≤ len a) (hfit : ∀ a : Word, len a ≤ w) :
    (RelRep.enum (paragraph (Word := Word) w)).rel ⊑ Λ (partition ≫ fits w) ≫ est (R (w := w)) :=
  calc (RelRep.enum (paragraph w)).rel
      = Λ (RelRep.enum (kept w)).rel ≫ est (Rt w).rel := RelRep.rel_est (paragraph_eq w)
    _ = Λ (RelRep.enum (kept w)).rel ≫ est (R (w := w)) := by rw [rel_Rt]
    _ ⊑ (Λ ⦇S (w := w)⦈ ≫ thinRel (Q w)) ≫ est (R (w := w)) := comp_mono_right (kept_thin w hlen) _
    _ = Λ ⦇S (w := w)⦈ ≫ (thinRel (Q w) ≫ est (R (w := w))) := Cat.assoc _ _ _
    _ ⊑ Λ ⦇S (w := w)⦈ ≫ est (R (w := w)) :=
      comp_mono_left _ (thinRel_comp_est_le Q_le_R (trans_of_recip_trans R_recip_trans))
    _ = Λ (partition ≫ fits w) ≫ est (R (w := w)) := para_laws_step2 hlen hfit

attribute [local instance] lenId in
/-- **kept-run**: the words of lengths `1,2,1,3`, line width `5`: the fold keeps two layouts, the
    thinning having dropped one with the same first line and more waste at each of two words. -/
public theorem run_kept :
    kept (Word := Int) 5 (ConsList.cons 1 (ConsList.cons 2 (ConsList.cons 1 (ConsList.wrap 3))))
      = [ConsList.cons (ConsList.wrap 1) (ConsList.cons (ConsList.cons 2 (ConsList.wrap 1)) (ConsList.wrap (ConsList.wrap 3))),
         ConsList.cons (ConsList.cons 1 (ConsList.wrap 2)) (ConsList.wrap (ConsList.cons 1 (ConsList.wrap 3)))] := by
  rfl

attribute [local instance] lenId in
/-- **para-run**: on the same words the program returns the one layout of waste `1`,
    `[[1,2],[1,3]]`. -/
public theorem run_paragraph :
    paragraph (Word := Int) 5 (ConsList.cons 1 (ConsList.cons 2 (ConsList.cons 1 (ConsList.wrap 3))))
      = [ConsList.cons (ConsList.cons 1 (ConsList.wrap 2)) (ConsList.wrap (ConsList.cons 1 (ConsList.wrap 3)))] := by
  rfl

end ParaRun

end Freyd.Alg.RelSet.Paragraph

-- printing-only: B&dM p.208 writes `fits w` and `ok w` both for the predicate on a paragraph and for
-- its coreflexive; Lean needs two constants, and the coreflexives own the names `fits` and `ok`.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.allFitP] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParaAllFitP : Unexpander
  | `($_ $args*) => `($(mkIdent `fits) $args*)
  | _ => `($(mkIdent `fits))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Paragraph.okP] public meta def Freyd.Alg.RelSet.Paragraph.unexpandParaOkP : Unexpander
  | `($_ $args*) => `($(mkIdent `ok) $args*)
  | _ => `($(mkIdent `ok))
