/-
  Freyd & Scedrov, *Categories and Allegories* §2.157:
  PROJECTIVE PLANES, the associated modular lattice, and the DESARGUES Horn sentence.

  "A projective plane is a model of a certain two-sorted theory: the two sorts are
   points and lines; the unique predicate is an incidence relation which will be
   denoted as x ∈ A where it is understood that lower-case italics refer to points
   and upper-case to lines; the axioms are:
     · for all x, y there exists A such that x ∈ A and y ∈ A;
     · for all A, B there exists x such that x ∈ A and x ∈ B;
     · x ∈ A, x ∈ B, y ∈ A, y ∈ B imply x = y or A = B.
   An interesting projective plane is one such that each point is incident to at
   least three lines and each line is incident to at least three points.

   For every projective plane there is an associated modular lattice (hence an
   associated allegory): let 𝓛 be the disjoint union of the points and lines
   together with two new elements called 0 and 1.  We partially order 𝓛 by taking
   0 as the minimum, 1 as the maximum and using the incidence relation in between.

   The theorem of Desargues says that if two triangles are 'in perspective' then
   their corresponding sides meet on a line.  (That is, given p, a₁, a₂, b₁, b₂,
   c₁, c₂, u, v, w such that the triples ⟨p,a₁,a₂⟩, ⟨p,b₁,b₂⟩, ⟨p,c₁,c₂⟩,
   ⟨a₁,c₁,u⟩, ⟨a₂,c₂,u⟩, ⟨b₁,c₁,v⟩, ⟨b₂,c₂,v⟩, ⟨a₁,b₁,w⟩, ⟨a₂,b₂,w⟩ are colinear,
   then ⟨u,v,w⟩ is colinear.)

   Consider, now, the following Horn sentence for allegories:
       (A₁A₂ ∩ B₁B₂) ⊂ C₁C₂   implies
       (A₁°B₁ ∩ A₂B₂°) ⊂ (A₁°C₁ ∩ A₂C₂°)(C₁°B₁ ∩ C₂B₂°).
   It is easily verified for Rel(S).  Starting with a projective plane, writing
   a₁, a₂, b₁, … as A₁, A₂, B₁, …, passing to the associated modular lattice,
   viewing such as an allegory, one will see that this Horn sentence is equivalent
   with the theorem of Desargues.  (Note that Desargues implies modularity: given
   R, S, and T let A₁ = R°, A₂ = T, B₁ = S, B₂ = 1, C₁ = 1, C₂ = S.)"

  Formalised here:
  · `ProjectivePlane`, `ProjectivePlane.Interesting`, and the derived uniqueness
    facts (`lineThrough_unique`, `meetPoint_unique`).
  · `PElem P` — the associated lattice 𝓛 — with a `ModularLattice` instance
    (EVERY projective plane's lattice is modular; interestingness is NOT needed),
    hence via §2.156/§2.113 `Allegory (LMonObj (PElem P))`: the associated allegory.
  · `DesarguesHorn` — the displayed Horn sentence for allegories;
    `desarguesHorn_binRel` — its verification for concrete binary relations
    (the "easily verified for Rel(S)"); `desarguesHorn_implies_modular` — the
    book's parenthetical, over a bare lattice-with-bottom (`BotLattice`).
  · `Desargues P` — the book's ten-point formulation — and
    `desarguesHorn_implies_desargues_nondeg`: the Horn sentence in the associated
    allegory forces Desargues for nondegenerate configurations.
-/
module

public import Freyd.S2_156_PartitionRep

universe v u

namespace Freyd.Alg

/-! ## §2.157  The two-sorted theory of projective planes -/

/-- A PROJECTIVE PLANE (§2.157): a model of the two-sorted theory whose sorts are
    points and lines, whose unique predicate is incidence `x ∈ A`, with the three
    displayed axioms. -/
public structure ProjectivePlane : Type (u + 1) where
  /-- The sort of POINTS (lower-case italics in the book). -/
  Point : Type u
  /-- The sort of LINES (upper-case in the book). -/
  Line : Type u
  /-- The INCIDENCE relation `x ∈ A`. -/
  incid : Point → Line → Prop
  /-- Axiom 1: "for all x, y there exists A such that x ∈ A and y ∈ A". -/
  join_exists : ∀ x y : Point, ∃ A : Line, incid x A ∧ incid y A
  /-- Axiom 2: "for all A, B there exists x such that x ∈ A and x ∈ B". -/
  meet_exists : ∀ A B : Line, ∃ x : Point, incid x A ∧ incid x B
  /-- Axiom 3: "x ∈ A, x ∈ B, y ∈ A, y ∈ B imply x = y or A = B". -/
  unique : ∀ {x y : Point} {A B : Line},
    incid x A → incid x B → incid y A → incid y B → x = y ∨ A = B

namespace ProjectivePlane

variable (P : ProjectivePlane.{u})

/-- An INTERESTING projective plane (§2.157): each point is incident to at least
    three lines and each line is incident to at least three points ("at least
    three" = a pairwise-distinct triple). -/
@[expose] public def Interesting : Prop :=
  (∀ x : P.Point, ∃ A B C : P.Line, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      P.incid x A ∧ P.incid x B ∧ P.incid x C) ∧
  (∀ A : P.Line, ∃ x y z : P.Point, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      P.incid x A ∧ P.incid y A ∧ P.incid z A)

/-! ### Derived uniqueness: axiom 3 splits the two existence axioms into
    unique existence, once the given pair is distinct. -/

variable {P}

/-- Two DISTINCT points lie on a UNIQUE common line (axioms 1 + 3). -/
theorem lineThrough_unique {x y : P.Point} (hxy : x ≠ y) :
    ∃ A : P.Line, (P.incid x A ∧ P.incid y A) ∧
      ∀ B : P.Line, P.incid x B ∧ P.incid y B → B = A := by
  obtain ⟨A, hA⟩ := P.join_exists x y
  exact ⟨A, hA, fun B hB => (P.unique hB.1 hA.1 hB.2 hA.2).resolve_left hxy⟩

/-- Two DISTINCT lines meet in a UNIQUE point (axioms 2 + 3). -/
theorem meetPoint_unique {A B : P.Line} (hAB : A ≠ B) :
    ∃ x : P.Point, (P.incid x A ∧ P.incid x B) ∧
      ∀ y : P.Point, P.incid y A ∧ P.incid y B → y = x := by
  obtain ⟨x, hx⟩ := P.meet_exists A B
  exact ⟨x, hx, fun y hy => (P.unique hy.1 hy.2 hx.1 hx.2).resolve_right hAB⟩

variable (P)

/-- A chosen common line of two points (axiom 1 via choice); for `x ≠ y` it is THE
    line through them (`lineThrough_eq`). -/
@[expose] public noncomputable def lineThrough (x y : P.Point) : P.Line :=
  Classical.choose (P.join_exists x y)

public theorem lineThrough_incid_left (x y : P.Point) :
    P.incid x (P.lineThrough x y) :=
  (Classical.choose_spec (P.join_exists x y)).1

public theorem lineThrough_incid_right (x y : P.Point) :
    P.incid y (P.lineThrough x y) :=
  (Classical.choose_spec (P.join_exists x y)).2

/-- A chosen common point of two lines (axiom 2 via choice); for `A ≠ B` it is THE
    meet point (`meetPoint_eq`). -/
@[expose] public noncomputable def meetPoint (A B : P.Line) : P.Point :=
  Classical.choose (P.meet_exists A B)

public theorem meetPoint_incid_left (A B : P.Line) :
    P.incid (P.meetPoint A B) A :=
  (Classical.choose_spec (P.meet_exists A B)).1

public theorem meetPoint_incid_right (A B : P.Line) :
    P.incid (P.meetPoint A B) B :=
  (Classical.choose_spec (P.meet_exists A B)).2

variable {P}

/-- Any line through two DISTINCT points is `lineThrough` (uniqueness, axiom 3). -/
public theorem lineThrough_eq {x y : P.Point} (hxy : x ≠ y) {A : P.Line}
    (hx : P.incid x A) (hy : P.incid y A) : A = P.lineThrough x y :=
  (P.unique hx (P.lineThrough_incid_left x y) hy
    (P.lineThrough_incid_right x y)).resolve_left hxy

/-- Any common point of two DISTINCT lines is `meetPoint` (uniqueness, axiom 3). -/
public theorem meetPoint_eq {A B : P.Line} (hAB : A ≠ B) {x : P.Point}
    (hA : P.incid x A) (hB : P.incid x B) : x = P.meetPoint A B :=
  (P.unique hA hB (P.meetPoint_incid_left A B)
    (P.meetPoint_incid_right A B)).resolve_right hAB

end ProjectivePlane

/-! ## The associated lattice 𝓛(P) (§2.157)

  "let 𝓛 be the disjoint union of the points and lines together with two new
   elements called 0 and 1.  We partially order 𝓛 by taking 0 as the minimum,
   1 as the maximum and using the incidence relation in between." -/

/-- 𝓛: disjoint union of points and lines plus `0` (`bot`) and `1` (`top`). -/
public inductive PElem (P : ProjectivePlane.{u}) : Type u where
  | bot : PElem P
  | pt (x : P.Point) : PElem P
  | ln (A : P.Line) : PElem P
  | top : PElem P

namespace PElem

variable {P : ProjectivePlane.{u}}

/-- The partial order on 𝓛: `0` minimum, `1` maximum, incidence in between
    (points and lines are otherwise incomparable; each rank is discrete). -/
@[expose] public def le : PElem P → PElem P → Prop
  | bot, _ => True
  | pt _, bot => False
  | pt x, pt y => x = y
  | pt x, ln A => P.incid x A
  | pt _, top => True
  | ln _, bot => False
  | ln _, pt _ => False
  | ln A, ln B => A = B
  | ln _, top => True
  | top, bot => False
  | top, pt _ => False
  | top, ln _ => False
  | top, top => True

public theorem le_refl : ∀ a : PElem P, a.le a
  | bot => trivial
  | pt _ => rfl
  | ln _ => rfl
  | top => trivial

public theorem le_trans {a b c : PElem P} (hab : a.le b) (hbc : b.le c) : a.le c := by
  cases a <;> cases b <;> cases c <;> simp_all [le]

public theorem le_antisymm {a b : PElem P} (hab : a.le b) (hba : b.le a) : a = b := by
  cases a <;> cases b <;> simp_all [le]

public theorem bot_le (a : PElem P) : (bot : PElem P).le a := trivial

public theorem le_top : ∀ a : PElem P, a.le top
  | bot => trivial
  | pt _ => trivial
  | ln _ => trivial
  | top => trivial

public theorem eq_top_of_top_le {a : PElem P} (h : (top : PElem P).le a) : a = top := by
  cases a <;> simp_all [le]

/-! ### Meet and join

  Total functions by case analysis; the witnesses for the geometric cases are
  chosen via `lineThrough`/`meetPoint` (axioms 1 and 2 through `Classical.choice`)
  and the distinctness splits use classical decidability. -/

open Classical in
/-- Lattice JOIN on 𝓛.  Cases: `⊥` is a unit and `⊤` absorbs; two points join to
    the line through them (or the point itself, if equal); a point and a line join
    to the line when incident, else to `⊤`; two distinct lines join to `⊤`. -/
@[expose] public noncomputable def join : PElem P → PElem P → PElem P
  | bot, b => b
  | pt x, bot => pt x
  | pt x, pt y => if x = y then pt x else ln (P.lineThrough x y)
  | pt x, ln A => if P.incid x A then ln A else top
  | pt _, top => top
  | ln A, bot => ln A
  | ln A, pt y => if P.incid y A then ln A else top
  | ln A, ln B => if A = B then ln A else top
  | ln _, top => top
  | top, _ => top

open Classical in
/-- Lattice MEET on 𝓛, dual to `join`: two distinct points meet in `⊥`; a point
    and a line meet in the point when incident, else `⊥`; two distinct lines meet
    in their common point (axiom 2). -/
@[expose] public noncomputable def meet : PElem P → PElem P → PElem P
  | bot, _ => bot
  | pt _, bot => bot
  | pt x, pt y => if x = y then pt x else bot
  | pt x, ln A => if P.incid x A then pt x else bot
  | pt x, top => pt x
  | ln _, bot => bot
  | ln A, pt y => if P.incid y A then pt y else bot
  | ln A, ln B => if A = B then ln A else pt (P.meetPoint A B)
  | ln A, top => ln A
  | top, b => b

/-! ### Evaluation lemmas (one per `if`-case; the constructor cases are `rfl`) -/

public theorem join_bot_right : ∀ a : PElem P, a.join bot = a
  | bot => rfl
  | pt _ => rfl
  | ln _ => rfl
  | top => rfl

public theorem join_top_left (b : PElem P) : (top : PElem P).join b = top := rfl

public theorem join_top_right : ∀ a : PElem P, a.join top = top
  | bot => rfl
  | pt _ => rfl
  | ln _ => rfl
  | top => rfl

public theorem join_pt_pt_self (x : P.Point) : (pt x).join (pt x) = pt x := by
  simp [join]

public theorem join_pt_pt_ne {x y : P.Point} (h : x ≠ y) :
    (pt x).join (pt y) = ln (P.lineThrough x y) := by
  simp [join, h]

public theorem join_pt_ln_incid {x : P.Point} {A : P.Line} (h : P.incid x A) :
    (pt x).join (ln A) = ln A := by
  simp [join, h]

public theorem join_pt_ln_not {x : P.Point} {A : P.Line} (h : ¬P.incid x A) :
    (pt x).join (ln A) = top := by
  simp [join, h]

public theorem join_ln_pt_incid {A : P.Line} {y : P.Point} (h : P.incid y A) :
    (ln A).join (pt y) = ln A := by
  simp [join, h]

public theorem join_ln_pt_not {A : P.Line} {y : P.Point} (h : ¬P.incid y A) :
    (ln A).join (pt y) = top := by
  simp [join, h]

public theorem join_ln_ln_self (A : P.Line) : (ln A).join (ln A) = ln A := by
  simp [join]

public theorem join_ln_ln_ne {A B : P.Line} (h : A ≠ B) : (ln A).join (ln B) = top := by
  simp [join, h]

public theorem meet_top_left (b : PElem P) : (top : PElem P).meet b = b := rfl

public theorem meet_top_right : ∀ a : PElem P, a.meet top = a
  | bot => rfl
  | pt _ => rfl
  | ln _ => rfl
  | top => rfl

public theorem meet_pt_pt_self (x : P.Point) : (pt x).meet (pt x) = pt x := by
  simp [meet]

public theorem meet_pt_pt_ne {x y : P.Point} (h : x ≠ y) :
    (pt x).meet (pt y) = bot := by
  simp [meet, h]

public theorem meet_pt_ln_incid {x : P.Point} {A : P.Line} (h : P.incid x A) :
    (pt x).meet (ln A) = pt x := by
  simp [meet, h]

public theorem meet_pt_ln_not {x : P.Point} {A : P.Line} (h : ¬P.incid x A) :
    (pt x).meet (ln A) = bot := by
  simp [meet, h]

public theorem meet_ln_pt_incid {A : P.Line} {y : P.Point} (h : P.incid y A) :
    (ln A).meet (pt y) = pt y := by
  simp [meet, h]

public theorem meet_ln_pt_not {A : P.Line} {y : P.Point} (h : ¬P.incid y A) :
    (ln A).meet (pt y) = bot := by
  simp [meet, h]

public theorem meet_ln_ln_self (A : P.Line) : (ln A).meet (ln A) = ln A := by
  simp [meet]

public theorem meet_ln_ln_ne {A B : P.Line} (h : A ≠ B) :
    (ln A).meet (ln B) = pt (P.meetPoint A B) := by
  simp [meet, h]

/-! ### Order characterisations: `join` is the lub, `meet` is the glb

  Everything equational below follows from these two case analyses ONCE,
  generically.  Axiom 3 (via `lineThrough_eq`/`meetPoint_eq`) is what makes
  the geometric cases work. -/

/-- `a ⊔ b ⩽ c ↔ a ⩽ c ∧ b ⩽ c`: `join` is the least upper bound. -/
public theorem join_le_iff {a b c : PElem P} : (a.join b).le c ↔ a.le c ∧ b.le c := by
  cases a with
  | bot => simp [le, join]
  | top =>
    -- `⊤ ⊔ b = ⊤`; forward direction forces `c = ⊤`, whence `b ⩽ c` trivially.
    exact ⟨fun h => ⟨h, by rw [eq_top_of_top_le h]; exact le_top b⟩, fun ⟨h1, _⟩ => h1⟩
  | pt x =>
    cases b with
    | bot => simp [le, join]
    | top => cases c <;> simp [le, join]
    | pt y =>
      by_cases hxy : x = y
      · subst hxy; rw [join_pt_pt_self]; simp
      · rw [join_pt_pt_ne hxy]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxy (h1.trans h2.symm)⟩
        | ln C =>
          simp only [le]
          exact ⟨fun h => h ▸ ⟨P.lineThrough_incid_left x y, P.lineThrough_incid_right x y⟩,
                 fun ⟨h1, h2⟩ => (ProjectivePlane.lineThrough_eq hxy h1 h2).symm⟩
    | ln A =>
      by_cases hxA : P.incid x A
      · rw [join_pt_ln_incid hxA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨fun h => ⟨h ▸ hxA, h⟩, And.right⟩
      · rw [join_pt_ln_not hxA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxA (h2.symm ▸ h1)⟩
  | ln A =>
    cases b with
    | bot => simp [le, join]
    | top => cases c <;> simp [le, join]
    | pt y =>
      by_cases hyA : P.incid y A
      · rw [join_ln_pt_incid hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨fun h => ⟨h, h ▸ hyA⟩, And.left⟩
      · rw [join_ln_pt_not hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hyA (h1.symm ▸ h2)⟩
    | ln B =>
      by_cases hAB : A = B
      · subst hAB; rw [join_ln_ln_self]; simp
      · rw [join_ln_ln_ne hAB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | pt z => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hAB (h1.trans h2.symm)⟩

/-- `c ⩽ a ⊓ b ↔ c ⩽ a ∧ c ⩽ b`: `meet` is the greatest lower bound. -/
public theorem le_meet_iff {a b c : PElem P} : c.le (a.meet b) ↔ c.le a ∧ c.le b := by
  cases a with
  | bot => cases c <;> simp [le, meet]
  | top => cases c <;> simp [le, meet]
  | pt x =>
    cases b with
    | bot => cases c <;> simp [le, meet]
    | top => cases c <;> simp [le, meet]
    | pt y =>
      by_cases hxy : x = y
      · subst hxy; rw [meet_pt_pt_self]; simp
      · rw [meet_pt_pt_ne hxy]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxy (h1.symm.trans h2)⟩
    | ln B =>
      by_cases hxB : P.incid x B
      · rw [meet_pt_ln_incid hxB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨fun h => ⟨h, h.symm ▸ hxB⟩, And.left⟩
      · rw [meet_pt_ln_not hxB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hxB (h1 ▸ h2)⟩
  | ln A =>
    cases b with
    | bot => cases c <;> simp [le, meet]
    | top => cases c <;> simp [le, meet]
    | pt y =>
      by_cases hyA : P.incid y A
      · rw [meet_ln_pt_incid hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨fun h => ⟨h.symm ▸ hyA, h⟩, And.right⟩
      · rw [meet_ln_pt_not hyA]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C => simp [le]
        | pt z =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hyA (h2 ▸ h1)⟩
    | ln B =>
      by_cases hAB : A = B
      · subst hAB; rw [meet_ln_ln_self]
        exact ⟨fun h => ⟨h, h⟩, And.left⟩
      · rw [meet_ln_ln_ne hAB]
        cases c with
        | bot => simp [le]
        | top => simp [le]
        | ln C =>
          simp only [le]
          exact ⟨False.elim, fun ⟨h1, h2⟩ => hAB (h1.symm.trans h2)⟩
        | pt z =>
          simp only [le]
          exact ⟨fun h => ⟨h.symm ▸ P.meetPoint_incid_left A B,
                           h.symm ▸ P.meetPoint_incid_right A B⟩,
                 fun ⟨h1, h2⟩ => ProjectivePlane.meetPoint_eq hAB h1 h2⟩

/-! ### Derived lub/glb API (from the two characterisations, generically) -/

public theorem le_join_left (a b : PElem P) : a.le (a.join b) :=
  (join_le_iff.mp (le_refl _)).1

public theorem le_join_right (a b : PElem P) : b.le (a.join b) :=
  (join_le_iff.mp (le_refl _)).2

public theorem join_le {a b c : PElem P} (h1 : a.le c) (h2 : b.le c) : (a.join b).le c :=
  join_le_iff.mpr ⟨h1, h2⟩

public theorem meet_le_left (a b : PElem P) : (a.meet b).le a :=
  (le_meet_iff.mp (le_refl _)).1

public theorem meet_le_right (a b : PElem P) : (a.meet b).le b :=
  (le_meet_iff.mp (le_refl _)).2

public theorem le_meet {a b c : PElem P} (h1 : c.le a) (h2 : c.le b) : c.le (a.meet b) :=
  le_meet_iff.mpr ⟨h1, h2⟩

/-- The `ModularLattice` order (`a ⊓ b = a`) coincides with `le`. -/
public theorem le_iff_meet_eq {a b : PElem P} : a.le b ↔ a.meet b = a :=
  ⟨fun h => le_antisymm (meet_le_left a b) (le_meet (le_refl a) h),
   fun h => h ▸ meet_le_right a b⟩

/-! ### The equational lattice laws (each once, from lub/glb + antisymmetry) -/

public theorem meet_idem (a : PElem P) : a.meet a = a :=
  le_antisymm (meet_le_left a a) (le_meet (le_refl a) (le_refl a))

public theorem meet_comm (a b : PElem P) : a.meet b = b.meet a :=
  le_antisymm (le_meet (meet_le_right a b) (meet_le_left a b))
    (le_meet (meet_le_right b a) (meet_le_left b a))

public theorem meet_assoc (a b c : PElem P) : a.meet (b.meet c) = (a.meet b).meet c :=
  le_antisymm
    (le_meet
      (le_meet (meet_le_left a _) (le_trans (meet_le_right a _) (meet_le_left b c)))
      (le_trans (meet_le_right a _) (meet_le_right b c)))
    (le_meet (le_trans (meet_le_left _ c) (meet_le_left a b))
      (le_meet (le_trans (meet_le_left _ c) (meet_le_right a b)) (meet_le_right _ c)))

public theorem join_idem (a : PElem P) : a.join a = a :=
  le_antisymm (join_le (le_refl a) (le_refl a)) (le_join_left a a)

public theorem join_comm (a b : PElem P) : a.join b = b.join a :=
  le_antisymm (join_le (le_join_right b a) (le_join_left b a))
    (join_le (le_join_right a b) (le_join_left a b))

public theorem join_assoc (a b c : PElem P) : a.join (b.join c) = (a.join b).join c :=
  le_antisymm
    (join_le (le_trans (le_join_left a b) (le_join_left _ c))
      (join_le (le_trans (le_join_right a b) (le_join_left _ c)) (le_join_right _ c)))
    (join_le
      (join_le (le_join_left a _) (le_trans (le_join_left b c) (le_join_right a _)))
      (le_trans (le_join_right b c) (le_join_right a _)))

public theorem meet_absorb (a b : PElem P) : a.meet (a.join b) = a :=
  le_antisymm (meet_le_left _ _) (le_meet (le_refl a) (le_join_left a b))

public theorem join_absorb (a b : PElem P) : a.join (a.meet b) = a :=
  le_antisymm (join_le (le_refl a) (meet_le_left a b)) (le_join_left _ _)

public theorem bot_join (a : PElem P) : (bot : PElem P).join a = a := rfl

/-! ### MODULARITY (§2.157 headline)

  `c ⩽ a → a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c`.  The `⊒` half holds in any lattice; the
  `⊑` half is the case analysis below.  Since 𝓛 has height 4, once the trivial
  ranks (`⊥`, `⊤`, `c = a`) are dispatched generically, the only case with
  content is `c = pt y ⩽ a = ln A`, and THE GEOMETRY ENTERS in exactly two
  spots, both instances of axiom 3:
  · `b = pt x` with `x ≠ y`, `A ≠ (line through x, y)`: the two lines meet in
    the unique point `y` (`meetPoint_eq`), so the meet is already below `c`;
  · `b = ln B` with `y ∉ B`: `z := meetPoint A B` and `y` are two distinct
    points of `A`, so `A` IS the line through them (`lineThrough_eq`), i.e.
    `(a ⊓ b) ⊔ c = a`.
  Interestingness is NOT needed: EVERY projective plane's lattice is modular. -/

/-- The trivial `c = a` instance of the modular inequality. -/
public theorem modular_self (a b : PElem P) : (a.meet (b.join a)).le ((a.meet b).join a) :=
  le_trans (meet_le_left _ _) (le_join_right _ _)

/-- The hard modular inequality `c ⩽ a → a ⊓ (b ⊔ c) ⩽ (a ⊓ b) ⊔ c`. -/
public theorem modular_hard {a b c : PElem P} (hca : c.le a) :
    (a.meet (b.join c)).le ((a.meet b).join c) := by
  cases c with
  | bot => rw [join_bot_right]; exact le_join_left _ _
  | top =>
    cases a with
    | top => exact le_trans (le_top _) (le_join_right _ _)
    | bot => simp [le] at hca
    | pt x => simp [le] at hca
    | ln A => simp [le] at hca
  | pt y =>
    cases a with
    | bot => simp [le] at hca
    | top => rw [meet_top_left, meet_top_left]; exact le_refl _
    | pt x =>
      have h : y = x := hca
      subst h
      exact modular_self _ _
    | ln A =>
      have hyA : P.incid y A := hca
      cases b with
      | bot => exact le_trans (meet_le_right _ _) (le_join_right _ _)
      | top => rw [join_top_left, meet_top_right]; exact le_join_left _ _
      | pt x =>
        by_cases hxy : x = y
        · subst hxy; rw [join_pt_pt_self]; exact le_join_left _ _
        · rw [join_pt_pt_ne hxy]
          by_cases hAL : A = P.lineThrough x y
          · -- `A` IS the line through `x, y`; both sides collapse to `ln A`.
            have hxA : P.incid x A := by rw [hAL]; exact P.lineThrough_incid_left x y
            rw [meet_ln_pt_incid hxA, join_pt_pt_ne hxy, ← hAL, meet_ln_ln_self]
            exact le_refl _
          · -- GEOMETRY: `A` and the line through `x, y` meet in the unique
            -- common point, which is `y` (axiom 3) — so the meet is `c` itself.
            have hy : y = P.meetPoint A (P.lineThrough x y) :=
              ProjectivePlane.meetPoint_eq hAL hyA (P.lineThrough_incid_right x y)
            rw [meet_ln_ln_ne hAL, ← hy]
            exact le_join_right _ _
      | ln B =>
        by_cases hyB : P.incid y B
        · rw [join_ln_pt_incid hyB]; exact le_join_left _ _
        · -- GEOMETRY: `z := meetPoint A B` and `y` are distinct points of `A`
          -- (`y ∉ B` but `z ∈ B`), so `A` is the line through `z, y` (axiom 3).
          have hAB : A ≠ B := fun h => hyB (h ▸ hyA)
          have hz : P.incid (P.meetPoint A B) A := P.meetPoint_incid_left A B
          have hzy : P.meetPoint A B ≠ y :=
            fun h => hyB (h ▸ P.meetPoint_incid_right A B)
          rw [join_ln_pt_not hyB, meet_top_right, meet_ln_ln_ne hAB,
            join_pt_pt_ne hzy]
          exact (ProjectivePlane.lineThrough_eq hzy hz hyA :
            A = P.lineThrough (P.meetPoint A B) y)
  | ln A' =>
    cases a with
    | bot => simp [le] at hca
    | pt x => simp [le] at hca
    | top => rw [meet_top_left, meet_top_left]; exact le_refl _
    | ln A =>
      have h : A' = A := hca
      subst h
      exact modular_self _ _

/-- **𝓛(P) is modular** (§2.157): `c ⩽ a → a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c`. -/
public theorem modular_eq {a b c : PElem P} (hca : c.le a) :
    a.meet (b.join c) = (a.meet b).join c :=
  le_antisymm (modular_hard hca)
    (le_meet (join_le (meet_le_left a b) hca)
      (join_le (le_trans (meet_le_right a b) (le_join_left b c)) (le_join_right b c)))

end PElem

/-- **§2.157, "for every projective plane there is an associated modular
    lattice"** — the `ModularLattice` (§2.156) instance on 𝓛(P). -/
@[expose] public noncomputable instance instModularLatticePElem (P : ProjectivePlane.{u}) :
    ModularLattice (PElem P) where
  meet := PElem.meet
  join := PElem.join
  bot := PElem.bot
  meet_idem := PElem.meet_idem
  meet_comm := PElem.meet_comm
  meet_assoc := PElem.meet_assoc
  join_idem := PElem.join_idem
  join_comm := PElem.join_comm
  join_assoc := PElem.join_assoc
  meet_absorb := PElem.meet_absorb
  join_absorb := PElem.join_absorb
  bot_join := PElem.bot_join
  modular := fun _ _ _ h =>
    PElem.modular_eq (PElem.le_iff_meet_eq.mpr h)

/-- "(hence an associated allegory)": the §2.156/§2.113 bridge fires on 𝓛(P). -/
noncomputable example (P : ProjectivePlane.{u}) :
    Allegory (LMonObj (PElem P)) := inferInstance

/-! ## The Desargues Horn sentence (§2.157)

  "Consider, now, the following Horn sentence for allegories:
       (A₁A₂ ∩ B₁B₂) ⊂ C₁C₂   implies
       (A₁°B₁ ∩ A₂B₂°) ⊂ (A₁°C₁ ∩ A₂C₂°)(C₁°B₁ ∩ C₂B₂°)." -/

/-- The DESARGUES HORN SENTENCE for an allegory (§2.157).  Typing (composition
    in diagram order): `A₁ : p ⟶ a`, `A₂ : a ⟶ q`, `B₁ : p ⟶ b`, `B₂ : b ⟶ q`,
    `C₁ : p ⟶ c`, `C₂ : c ⟶ q`; the hypothesis lives in `p ⟶ q`, the conclusion
    in `a ⟶ b`, composed through `c`. -/
@[expose] public def DesarguesHorn (𝒜 : Type u) [Allegory.{v} 𝒜] : Prop :=
  ∀ (p q a b c : 𝒜) (A₁ : p ⟶ a) (A₂ : a ⟶ q) (B₁ : p ⟶ b) (B₂ : b ⟶ q)
    (C₁ : p ⟶ c) (C₂ : c ⟶ q),
    (A₁ ≫ A₂) ∩ (B₁ ≫ B₂) ⊑ C₁ ≫ C₂ →
    (A₁° ≫ B₁) ∩ (A₂ ≫ B₂°) ⊑
      ((A₁° ≫ C₁) ∩ (A₂ ≫ C₂°)) ≫ ((C₁° ≫ B₁) ∩ (C₂ ≫ B₂°))

/-- §2.157: "It is easily verified for Rel(S)" — the Horn sentence for CONCRETE
    binary relations, stated at the matrix level: composition
    `(R ≫ S) x z := ∃ y, R x y ∧ S y z` (diagram order), reciprocation =
    transpose, intersection pointwise, `⊑` pointwise implication.

    The element chase: given `x`, `y` with `x (A₁°B₁ ∩ A₂B₂°) y`, pick `u : p`
    with `u A₁ x`, `u B₁ y` and `v : q` with `x A₂ v`, `y B₂ v`.  Then
    `u (A₁A₂ ∩ B₁B₂) v` (through `x`, resp. through `y`), so the hypothesis
    yields `z : c` with `u C₁ z` and `z C₂ v`.  This single `z` witnesses all
    four factors of the conclusion: `x (A₁°C₁) z` through `u`; `x (A₂C₂°) z`
    through `v`; `z (C₁°B₁) y` through `u`; `z (C₂B₂°) y` through `v`. -/
public theorem desarguesHorn_binRel {p q a b c : Type u}
    (A₁ : p → a → Prop) (A₂ : a → q → Prop) (B₁ : p → b → Prop)
    (B₂ : b → q → Prop) (C₁ : p → c → Prop) (C₂ : c → q → Prop)
    (hyp : ∀ (u : p) (v : q),
      (∃ x, A₁ u x ∧ A₂ x v) ∧ (∃ y, B₁ u y ∧ B₂ y v) → ∃ z, C₁ u z ∧ C₂ z v) :
    ∀ (x : a) (y : b),
      (∃ u, A₁ u x ∧ B₁ u y) ∧ (∃ v, A₂ x v ∧ B₂ y v) →
      ∃ z, ((∃ u, A₁ u x ∧ C₁ u z) ∧ (∃ v, A₂ x v ∧ C₂ z v)) ∧
           ((∃ u, C₁ u z ∧ B₁ u y) ∧ (∃ v, C₂ z v ∧ B₂ y v)) := by
  rintro x y ⟨⟨u, hA1, hB1⟩, ⟨v, hA2, hB2⟩⟩
  obtain ⟨z, hC1, hC2⟩ := hyp u v ⟨⟨x, hA1, hA2⟩, ⟨y, hB1, hB2⟩⟩
  exact ⟨z, ⟨⟨u, hA1, hC1⟩, ⟨v, hA2, hC2⟩⟩, ⟨⟨u, hC1, hB1⟩, ⟨v, hC2, hB2⟩⟩⟩

/-! ## "Desargues implies modularity" (§2.157, parenthetical)

  The Horn sentence, read in a one-object lattice allegory (composition `= ⊔`,
  reciprocation `= id`, unit `= ⊥`, cf. §2.113/§2.156), implies the modular
  law.  This must be stated over a lattice WITHOUT modularity — `ModularLattice`
  (§2.156) bundles the conclusion — so we introduce the bare structure
  `BotLattice` (same fields minus `modular`); its order helpers below are the
  §2.156 proofs verbatim (none of them uses the modular field). -/

/-- A LATTICE WITH BOTTOM, *without* the modular law: the raw structure on
    which "Desargues implies modularity" is stated (`ModularLattice` minus
    `modular`). -/
class BotLattice (L : Type u) where
  /-- Lattice meet. -/
  meet : L → L → L
  /-- Lattice join. -/
  join : L → L → L
  /-- Bottom element `0`. -/
  bot  : L
  meet_idem  : ∀ a, meet a a = a
  meet_comm  : ∀ a b, meet a b = meet b a
  meet_assoc : ∀ a b c, meet a (meet b c) = meet (meet a b) c
  join_idem  : ∀ a, join a a = a
  join_comm  : ∀ a b, join a b = join b a
  join_assoc : ∀ a b c, join a (join b c) = join (join a b) c
  meet_absorb : ∀ a b, meet a (join a b) = a
  join_absorb : ∀ a b, join a (meet a b) = a
  /-- `0` is the unit for `⊔`. -/
  bot_join : ∀ a, join bot a = a

namespace BotLattice

variable {L : Type u} [BotLattice L]

/-- The lattice order `a ⩽ b :⇔ a ⊓ b = a` (the §2.113/§2.156 convention). -/
def le (a b : L) : Prop := meet a b = a

theorem le_refl (a : L) : le a a := meet_idem a

theorem le_trans {a b c : L} (hab : le a b) (hbc : le b c) : le a c := by
  have hab' : meet a b = a := hab
  have hbc' : meet b c = b := hbc
  show meet a c = a
  calc meet a c = meet (meet a b) c := by rw [hab']
    _ = meet a (meet b c) := (meet_assoc a b c).symm
    _ = meet a b := by rw [hbc']
    _ = a := hab'

theorem le_antisymm {a b : L} (hab : le a b) (hba : le b a) : a = b := by
  have hab' : meet a b = a := hab
  have hba' : meet b a = b := hba
  calc a = meet a b := hab'.symm
    _ = meet b a := meet_comm a b
    _ = b := hba'

/-- `a ⊓ b ⩽ a`. -/
theorem meet_lb_left (a b : L) : le (meet a b) a := by
  show meet (meet a b) a = meet a b
  rw [meet_comm (meet a b) a, meet_assoc, meet_idem]

/-- `a ⊓ b ⩽ b`. -/
theorem meet_lb_right (a b : L) : le (meet a b) b := by
  show meet (meet a b) b = meet a b
  rw [← meet_assoc, meet_idem]

/-- `x ⩽ a → x ⩽ b → x ⩽ a ⊓ b`. -/
theorem le_meet {x a b : L} (h1 : le x a) (h2 : le x b) : le x (meet a b) := by
  show meet x (meet a b) = x
  rw [meet_assoc, (h1 : meet x a = x), (h2 : meet x b = x)]

/-- `a ⩽ a ⊔ b`. -/
theorem le_join_left (a b : L) : le a (join a b) := meet_absorb a b

/-- `b ⩽ a ⊔ b`. -/
theorem le_join_right (a b : L) : le b (join a b) := by
  show meet b (join a b) = b
  rw [join_comm]; exact meet_absorb b a

/-- `a ⩽ b → a ⊔ b = b`. -/
theorem join_eq_of_le {a b : L} (h : le a b) : join a b = b := by
  have h2 : join (meet a b) b = b := by
    rw [meet_comm, join_comm]; exact join_absorb b a
  rw [(h : meet a b = a)] at h2
  exact h2

/-- `a ⩽ c → b ⩽ c → a ⊔ b ⩽ c`. -/
theorem join_le {a b c : L} (ha : le a c) (hb : le b c) : le (join a b) c := by
  show meet (join a b) c = join a b
  have h : join (join a b) c = c := by
    rw [← join_assoc, join_eq_of_le hb]; exact join_eq_of_le ha
  rw [← h]; exact meet_absorb (join a b) c

end BotLattice

/-- The §2.157 Horn sentence READ IN LATTICE NOTATION, as it comes out in a
    one-object lattice allegory: composition is `⊔`, reciprocation is the
    identity, so `A₁A₂` is `a₁ ⊔ a₂`, `A₁°B₁` is `a₁ ⊔ b₁`, and so on. -/
def LatticeDesarguesHorn (L : Type u) [BotLattice L] : Prop :=
  ∀ a₁ a₂ b₁ b₂ c₁ c₂ : L,
    BotLattice.le (BotLattice.meet (BotLattice.join a₁ a₂) (BotLattice.join b₁ b₂))
      (BotLattice.join c₁ c₂) →
    BotLattice.le (BotLattice.meet (BotLattice.join a₁ b₁) (BotLattice.join a₂ b₂))
      (BotLattice.join
        (BotLattice.meet (BotLattice.join a₁ c₁) (BotLattice.join a₂ c₂))
        (BotLattice.meet (BotLattice.join c₁ b₁) (BotLattice.join c₂ b₂)))

open BotLattice in
/-- **§2.157 (parenthetical): "Desargues implies modularity: given R, S, and T
    let A₁ = R°, A₂ = T, B₁ = S, B₂ = 1, C₁ = 1, C₂ = S."**  Reciprocation is
    the identity and the unit `1` is `⊥`, so the substitution is
    `(a₁,a₂,b₁,b₂,c₁,c₂) := (R, T, S, ⊥, ⊥, S)`; with `(R,S,T) := (b, c, a)`
    it produces the hard modular inequality, and the converse inequality holds
    in any lattice. -/
theorem desarguesHorn_implies_modular {L : Type u} [BotLattice L]
    (horn : LatticeDesarguesHorn L) {a b c : L} (hca : BotLattice.le c a) :
    meet a (join b c) = join (meet a b) c := by
  -- The Horn instance at (a₁,a₂,b₁,b₂,c₁,c₂) := (b, a, c, ⊥, ⊥, c).
  -- Hypothesis: (b ⊔ a) ⊓ (c ⊔ ⊥) ⩽ ⊥ ⊔ c, i.e. (b ⊔ a) ⊓ c ⩽ c.
  have hyp : BotLattice.le (meet (join b a) (join c bot)) (join bot c) := by
    rw [join_comm c bot, bot_join]
    exact meet_lb_right _ _
  have h := horn b a c bot bot c hyp
  -- h : (b ⊔ c) ⊓ (a ⊔ ⊥) ⩽ ((b ⊔ ⊥) ⊓ (a ⊔ c)) ⊔ ((⊥ ⊔ c) ⊓ (c ⊔ ⊥))
  rw [join_comm a bot, bot_join, join_comm b bot, bot_join, bot_join,
    join_comm c bot, bot_join, meet_idem] at h
  -- h : (b ⊔ c) ⊓ a ⩽ (b ⊓ (a ⊔ c)) ⊔ c;  now a ⊔ c = a since c ⩽ a
  rw [join_comm a c, join_eq_of_le hca, meet_comm b a,
    meet_comm (join b c) a] at h
  -- h : a ⊓ (b ⊔ c) ⩽ (a ⊓ b) ⊔ c — the hard half; the converse is generic.
  exact BotLattice.le_antisymm h
    (BotLattice.le_meet (BotLattice.join_le (meet_lb_left a b) hca)
      (BotLattice.join_le
        (BotLattice.le_trans (meet_lb_right a b) (le_join_left b c))
        (le_join_right b c)))

/-- Packaging: a `BotLattice` satisfying the Desargues Horn sentence IS a
    modular lattice (§2.156), hence a one-object allegory (§2.113). -/
def BotLattice.toModularLattice {L : Type u} [BotLattice L]
    (horn : LatticeDesarguesHorn L) : ModularLattice L where
  meet := BotLattice.meet
  join := BotLattice.join
  bot := BotLattice.bot
  meet_idem := BotLattice.meet_idem
  meet_comm := BotLattice.meet_comm
  meet_assoc := BotLattice.meet_assoc
  join_idem := BotLattice.join_idem
  join_comm := BotLattice.join_comm
  join_assoc := BotLattice.join_assoc
  meet_absorb := BotLattice.meet_absorb
  join_absorb := BotLattice.join_absorb
  bot_join := BotLattice.bot_join
  modular := fun _ _ _ h => desarguesHorn_implies_modular horn h

/-! ## The theorem of Desargues (§2.157, stretch)

  "The theorem of Desargues says that if two triangles are 'in perspective'
   then their corresponding sides meet on a line." -/

/-- Three points are COLINEAR: some line is incident to all three. -/
@[expose] public def ProjectivePlane.Colinear (P : ProjectivePlane.{u}) (x y z : P.Point) : Prop :=
  ∃ L : P.Line, P.incid x L ∧ P.incid y L ∧ P.incid z L

/-- THE THEOREM OF DESARGUES, the book's ten-point formulation: given p, a₁,
    a₂, b₁, b₂, c₁, c₂, u, v, w such that the triples ⟨p,a₁,a₂⟩, ⟨p,b₁,b₂⟩,
    ⟨p,c₁,c₂⟩, ⟨a₁,c₁,u⟩, ⟨a₂,c₂,u⟩, ⟨b₁,c₁,v⟩, ⟨b₂,c₂,v⟩, ⟨a₁,b₁,w⟩,
    ⟨a₂,b₂,w⟩ are colinear, then ⟨u,v,w⟩ is colinear. -/
@[expose] public def ProjectivePlane.Desargues (P : ProjectivePlane.{u}) : Prop :=
  ∀ p a₁ a₂ b₁ b₂ c₁ c₂ u v w : P.Point,
    P.Colinear p a₁ a₂ → P.Colinear p b₁ b₂ → P.Colinear p c₁ c₂ →
    P.Colinear a₁ c₁ u → P.Colinear a₂ c₂ u →
    P.Colinear b₁ c₁ v → P.Colinear b₂ c₂ v →
    P.Colinear a₁ b₁ w → P.Colinear a₂ b₂ w →
    P.Colinear u v w

/-- Anything on a common line of two DISTINCT points is on THE line through
    them (axiom 3 transport). -/
public theorem ProjectivePlane.incid_lineThrough_of_mem {P : ProjectivePlane.{u}}
    {x y z : P.Point} {L : P.Line} (hxy : x ≠ y)
    (hx : P.incid x L) (hy : P.incid y L) (hz : P.incid z L) :
    P.incid z (P.lineThrough x y) := by
  rw [← ProjectivePlane.lineThrough_eq hxy hx hy]
  exact hz

/-- §2.157, "writing a₁, a₂, b₁, … as A₁, A₂, B₁, …": the Horn sentence on the
    associated allegory of 𝓛(P), unfolded to lattice form (composition IS `⊔`,
    reciprocation is the identity, `∩` is `⊓`, `⊑` is the lattice order — all
    definitional through §2.156/§2.113). -/
public theorem desarguesHorn_toLattice {P : ProjectivePlane.{u}}
    (h : DesarguesHorn (LMonObj (PElem P))) :
    ∀ a₁ a₂ b₁ b₂ c₁ c₂ : PElem P,
      ((a₁.join a₂).meet (b₁.join b₂)).le (c₁.join c₂) →
      ((a₁.join b₁).meet (a₂.join b₂)).le
        (((a₁.join c₁).meet (a₂.join c₂)).join
          ((c₁.join b₁).meet (c₂.join b₂))) := by
  intro a₁ a₂ b₁ b₂ c₁ c₂ hyp
  exact PElem.le_iff_meet_eq.mpr
    (h LMonObj.star LMonObj.star LMonObj.star LMonObj.star LMonObj.star
      a₁ a₂ b₁ b₂ c₁ c₂ (PElem.le_iff_meet_eq.mp hyp))

open PElem in
/-- The computational core of `desarguesHorn_implies_desargues_nondeg`: a
    SINGLE lattice Horn instance — at the six `pt`-elements of the given
    configuration — already forces `⟨u,v,w⟩` colinear.

    Chase (all joins/meets in 𝓛(P)): `pt aᵢ ⊔ pt bᵢ` etc. are the SIDES;
    the Horn hypothesis `(A₁A₂ ∩ B₁B₂) ⊑ C₁C₂` becomes "the meet of the
    perspective lines `a₁a₂`, `b₁b₂` — which is `pt p` — lies on `c₁c₂`",
    true since `⟨p,c₁,c₂⟩` is colinear; the Horn conclusion evaluates to
    `side a₁b₁ ⊓ side a₂b₂ ⩽ (pt u) ⊔ (pt v) = line uv`, and `pt w` is below
    the left side, so `w` is on the line through `u` and `v`. -/
public theorem desargues_nondeg_of_hornPoints {P : ProjectivePlane.{u}}
    (p a₁ a₂ b₁ b₂ c₁ c₂ u v w : P.Point)
    (horn : (((pt a₁).join (pt a₂)).meet ((pt b₁).join (pt b₂))).le
        ((pt c₁).join (pt c₂)) →
      (((pt a₁).join (pt b₁)).meet ((pt a₂).join (pt b₂))).le
        ((((pt a₁).join (pt c₁)).meet ((pt a₂).join (pt c₂))).join
          (((pt c₁).join (pt b₁)).meet ((pt c₂).join (pt b₂)))))
    (h1 : P.Colinear p a₁ a₂) (h2 : P.Colinear p b₁ b₂) (h3 : P.Colinear p c₁ c₂)
    (h4 : P.Colinear a₁ c₁ u) (h5 : P.Colinear a₂ c₂ u)
    (h6 : P.Colinear b₁ c₁ v) (h7 : P.Colinear b₂ c₂ v)
    (h8 : P.Colinear a₁ b₁ w) (h9 : P.Colinear a₂ b₂ w)
    -- nondegeneracy: distinct perspective pairs and triangle vertices …
    (hpa : a₁ ≠ a₂) (hpb : b₁ ≠ b₂) (hpc : c₁ ≠ c₂)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hac₁ : a₁ ≠ c₁) (hac₂ : a₂ ≠ c₂)
    (hcb₁ : c₁ ≠ b₁) (hcb₂ : c₂ ≠ b₂)
    -- … distinct perspective lines and sides, and distinct meets
    (hLab : P.lineThrough a₁ a₂ ≠ P.lineThrough b₁ b₂)
    (hLac : P.lineThrough a₁ c₁ ≠ P.lineThrough a₂ c₂)
    (hLcb : P.lineThrough c₁ b₁ ≠ P.lineThrough c₂ b₂)
    (huv : u ≠ v) :
    P.Colinear u v w := by
  -- `p` is on both perspective lines, hence IS their meet point (axiom 3).
  obtain ⟨La, hpLa, ha1La, ha2La⟩ := h1
  obtain ⟨Lb, hpLb, hb1Lb, hb2Lb⟩ := h2
  obtain ⟨Lc, hpLc, hc1Lc, hc2Lc⟩ := h3
  have hp1 := P.incid_lineThrough_of_mem hpa ha1La ha2La hpLa
  have hp2 := P.incid_lineThrough_of_mem hpb hb1Lb hb2Lb hpLb
  have hp3 := P.incid_lineThrough_of_mem hpc hc1Lc hc2Lc hpLc
  have hmeetp : p = P.meetPoint (P.lineThrough a₁ a₂) (P.lineThrough b₁ b₂) :=
    ProjectivePlane.meetPoint_eq hLab hp1 hp2
  -- Horn hypothesis: (a₁⊔a₂) ⊓ (b₁⊔b₂) = pt p ⩽ c₁⊔c₂.
  have hyp : (((pt a₁).join (pt a₂)).meet ((pt b₁).join (pt b₂))).le
      ((pt c₁).join (pt c₂)) := by
    rw [join_pt_pt_ne hpa, join_pt_pt_ne hpb, join_pt_pt_ne hpc,
      meet_ln_ln_ne hLab, ← hmeetp]
    exact hp3
  have hconc := horn hyp
  -- `pt w` is below both sides `a₁b₁`, `a₂b₂`, hence below the Horn conclusion.
  obtain ⟨Lw1, ha1w, hb1w, hww1⟩ := h8
  obtain ⟨Lw2, ha2w, hb2w, hww2⟩ := h9
  have hwle : (pt w : PElem P).le
      (((pt a₁).join (pt b₁)).meet ((pt a₂).join (pt b₂))) := by
    apply le_meet
    · rw [join_pt_pt_ne hab₁]
      exact P.incid_lineThrough_of_mem hab₁ ha1w hb1w hww1
    · rw [join_pt_pt_ne hab₂]
      exact P.incid_lineThrough_of_mem hab₂ ha2w hb2w hww2
  have hwle2 := PElem.le_trans hwle hconc
  -- `u` and `v` ARE the meets of the corresponding sides (axiom 3) …
  obtain ⟨Lu1, ha1u, hc1u, huu1⟩ := h4
  obtain ⟨Lu2, ha2u, hc2u, huu2⟩ := h5
  obtain ⟨Lv1, hb1v, hc1v, hvv1⟩ := h6
  obtain ⟨Lv2, hb2v, hc2v, hvv2⟩ := h7
  have hu : u = P.meetPoint (P.lineThrough a₁ c₁) (P.lineThrough a₂ c₂) :=
    ProjectivePlane.meetPoint_eq hLac
      (P.incid_lineThrough_of_mem hac₁ ha1u hc1u huu1)
      (P.incid_lineThrough_of_mem hac₂ ha2u hc2u huu2)
  have hv : v = P.meetPoint (P.lineThrough c₁ b₁) (P.lineThrough c₂ b₂) :=
    ProjectivePlane.meetPoint_eq hLcb
      (P.incid_lineThrough_of_mem hcb₁ hc1v hb1v hvv1)
      (P.incid_lineThrough_of_mem hcb₂ hc2v hb2v hvv2)
  -- … so the Horn conclusion is `pt u ⊔ pt v = ln (line through u, v)`.
  rw [join_pt_pt_ne hac₁, join_pt_pt_ne hac₂, join_pt_pt_ne hcb₁,
    join_pt_pt_ne hcb₂, meet_ln_ln_ne hLac, meet_ln_ln_ne hLcb, ← hu, ← hv,
    join_pt_pt_ne huv] at hwle2
  -- `pt w ⩽ ln (lineThrough u v)` IS incidence; package the witness line.
  exact ⟨P.lineThrough u v, P.lineThrough_incid_left u v,
    P.lineThrough_incid_right u v, hwle2⟩

open PElem in
/-- **§2.157, stretch (one direction, nondegenerate configurations)**: the
    Desargues Horn sentence in the associated allegory forces the theorem of
    Desargues, for configurations where the perspective pairs, the triangle
    vertices, and the relevant sides are genuinely distinct.  (The single
    required instance is extracted by `desarguesHorn_toLattice`; the chase is
    `desargues_nondeg_of_hornPoints`.  `S2_157b_Desargues` removes the four
    hypotheses that are not part of the honest theorem of Desargues.) -/
theorem desarguesHorn_implies_desargues_nondeg {P : ProjectivePlane.{u}}
    (hHorn : DesarguesHorn (LMonObj (PElem P)))
    (p a₁ a₂ b₁ b₂ c₁ c₂ u v w : P.Point)
    (h1 : P.Colinear p a₁ a₂) (h2 : P.Colinear p b₁ b₂) (h3 : P.Colinear p c₁ c₂)
    (h4 : P.Colinear a₁ c₁ u) (h5 : P.Colinear a₂ c₂ u)
    (h6 : P.Colinear b₁ c₁ v) (h7 : P.Colinear b₂ c₂ v)
    (h8 : P.Colinear a₁ b₁ w) (h9 : P.Colinear a₂ b₂ w)
    (hpa : a₁ ≠ a₂) (hpb : b₁ ≠ b₂) (hpc : c₁ ≠ c₂)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hac₁ : a₁ ≠ c₁) (hac₂ : a₂ ≠ c₂)
    (hcb₁ : c₁ ≠ b₁) (hcb₂ : c₂ ≠ b₂)
    (hLab : P.lineThrough a₁ a₂ ≠ P.lineThrough b₁ b₂)
    (hLac : P.lineThrough a₁ c₁ ≠ P.lineThrough a₂ c₂)
    (hLcb : P.lineThrough c₁ b₁ ≠ P.lineThrough c₂ b₂)
    (huv : u ≠ v) :
    P.Colinear u v w :=
  desargues_nondeg_of_hornPoints p a₁ a₂ b₁ b₂ c₁ c₂ u v w
    (desarguesHorn_toLattice hHorn (pt a₁) (pt a₂) (pt b₁) (pt b₂) (pt c₁) (pt c₂))
    h1 h2 h3 h4 h5 h6 h7 h8 h9 hpa hpb hpc hab₁ hab₂ hac₁ hac₂ hcb₁ hcb₂
    hLab hLac hLcb huv

/-! ### Gap analysis: the full §2.157 equivalence

  The book claims the Horn sentence in the associated allegory "is equivalent
  with the theorem of Desargues".  `desarguesHorn_implies_desargues_nondeg`
  is the substantive direction restricted to nondegenerate configurations.
  What remains for the literal equivalence:

  1. `DesarguesHorn (LMonObj (PElem P)) → Desargues P` in FULL: the ten-point
     statement `Desargues P` quantifies over arbitrary (possibly degenerate)
     configurations.  When one of the thirteen nondegeneracy hypotheses fails
     (coincident perspective pairs `a₁ = a₂`, collapsed sides `a₁ = b₁`,
     coincident perspective lines `a₁a₂ = b₁b₂`, coincident sides
     `a₁c₁ = a₂c₂`, or `u = v`), the Horn instance at `pt`-elements either has
     a false hypothesis or an uninformative conclusion (a full line instead of
     a point), so each degenerate family needs its own SYNTHETIC argument that
     `⟨u,v,w⟩` is colinear — the classical (true but tedious) fact that
     degenerate Desargues configurations hold in every projective plane; some
     of those arguments re-triangulate and hence consume `Interesting`.

  2. The converse `Desargues P → DesarguesHorn (LMonObj (PElem P))`: the Horn
     quantifies over arbitrary LATTICE elements, so one must case over the
     4⁶ constructor shapes of `(A₁, …, C₂)`; the all-`pt` nondegenerate case
     is (the dual reading of) Desargues, and the remaining cases are rank
     degeneracies to be discharged by the lattice laws.  This is exactly the
     bookkeeping hidden in the book's "one will see".  -/

end Freyd.Alg
