/-
  Bird & de Moor, *Algebra of Programming* §8.6  Bitonic tours (book pp. 211-215).

  A bitonic tour of a list of cities is a PAIR of lists — the outward journey and the return —
  each a subsequence of the input of length at least two, together covering every city.  The
  specification is `Λ(tour) est(R)` with `R ≜ cost ≤ cost°`, and §8.6 is the third worked
  instance of §8.3's binary thinning (Theorem 8.2, `thinningList`).

  Both parts of a tour have length at least two throughout, so they are cons-lists over the
  SAME base functor as the input: `[a,b]` is `wrap (a,b)` and `dropl`/`dropr` are total
  functions, replacing the head of one list and consing onto the other.

  A FINDING ON THE NOTE.  `tour-mono`'s two positive rows, `(𝟙×Q) dropl ⊑ dropl Q` and
  `(𝟙×Q) dropr ⊑ dropr Q` at the book's `Q ≜ R ∩ (next₂ next₂°)` (Lean's `Qbook`), are FALSE as printed.
  `tour_mono_dropl_Q_false` and `tour_mono_dropr_Q_false` refute them on two GENUINE tours —
  each with its own two heads equal, as p.214 says every partial tour has — that are tours of
  DIFFERENT inputs.  The book says why (p.215): the cost of `dropl (a,(x,y))` is
  `cost (x,y) + tc(a,next x) − tc(head x,next x) + tc(head y,a)`, so the step reads BOTH heads
  as well as both second cities, and "the first conjunct will hold whenever `(x,y)` and
  `(u,v)` are tours of the same input".  That is a monotonicity IN CONTEXT: it is a property of
  the candidates the fold actually holds together, not of tours at large, and `Q` as printed
  does not record it.

  What is proved here instead is the row at `Q ≜ Qbook ∩ (head₂ head₂°)`, which does record it —
  `tour_mono_dropl`, `tour_mono_dropr` — and `tour_laws` is Theorem 8.2 at `Q`.  The note's
  `thinL Q` therefore has to be read at this `Q`, or Theorem 8.2 has to be replaced by its
  in-context form (`AOP.A8_1`'s `Λ_comp_thinRel_context`, which is exactly `Λ S ≫ thinRel (Q ∩
  (S°S)) = Λ S ≫ thinRel Q`).

  The note's other two rows, `(𝟙×R) dropl ⊑ dropl R` and `(𝟙×R) dropr ⊑ dropr R`, are marked
  FALSE there and are refuted here (`tour_mono_dropl_false`, `tour_mono_dropr_false`).

  The sorted-list combinators are `AOP.A8_3`'s concrete ones, so (8.6)-(8.11) are theorems.  B&dM's
  `Real` is `Int`, and `tc` is neither positive nor symmetric, as the book insists.
-/
module

public import AOP.A8_3
public import AOP.A6_FinRel
import AOP.A8_2
import AOP.A7_2_RelSet
-- Spec-only derivations on abstract types: the unhashed scan fallback is opted into here and in no executed code.
attribute [local instance low] Freyd.Alg.RelSet.FibreIndex.scan


/-- B&dM p.212: the section's fixed data, the travelling cost `tc` between two cities.  Every
    definition below reads it from the one instance in scope, so the printer, which hides instance
    arguments, shows the book's `cost`, not `cost tc`.  Named after the section's namespace, so the
    field prints as the bare `tc`. -/
public class Freyd.Alg.RelSet.Tour (City : Type) where
  tc : City × City → Int

namespace Freyd.Alg.RelSet.Tour
open PowerAllegory

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {City : Type}

/-! ## `tour-defn` -/

/-- A journey: a cons-list of cities of length at least two, `[a,b]` being `wrap (a,b)`. -/
@[expose] public abbrev Journey (City : Type) : Type := ConsList (City × City) City
/-- A bitonic tour: the outward journey and the return. -/
@[expose] public abbrev Tour (City : Type) : Type := Journey City × Journey City
/-- Named, so a declaration comparing tours holds this constant and not the product instance's inline binders. -/
public instance decEqTour [DecidableEq City] : DecidableEq (Tour City) := inferInstanceAs (DecidableEq (Journey City × Journey City))
/-- The object carrying `Tour`. -/
@[expose] public abbrev dTour (City : Type) : RelSet.{0} := ⟨Tour City⟩

/-- `Journey(R) ≜ cl(R×R,R)`: `clRelator` at the leaf relator `X ↦ X×X`, its laws `clRelator`'s.
    Named because a lane of the tour pictures is a relator CONSTANT the exporter peels. -/
@[expose] public def journeyRelator : Relator RelSet.{0} RelSet.{0} :=
  clRelator (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.idRelator RelSet.{0}))

set_option linter.unusedVariables false in
/-- `head` of a journey. -/
@[expose] public def head : Journey City → City
  | ConsList.wrap (a, b) => a
  | ConsList.cons a _ => a

set_option linter.unusedVariables false in
/-- **tour-defn**: `next ≜ tail head`, the second city of a journey. -/
@[expose] public def next : Journey City → City
  | ConsList.wrap (a, b) => b
  | ConsList.cons _ xs => head xs

/-- A journey READ AS a `list⁺`: the same cities, the leaf pair `[b,c]` taken apart into `[b]⧺[c]`. -/
@[expose, coe] public def toNE : Journey City → NEList City
  | ConsList.wrap (b, c) => ConsList.cons b (ConsList.wrap c)
  | ConsList.cons a x => ConsList.cons a (toNE x)

set_option linter.unusedVariables false in
/-- **tour-defn**: `tail([b,c])=[c]`, `tail([b]⧺xs)=xs` — a journey without its first city, a `list⁺`.
    The one place the two shapes of a journey are told apart. -/
@[expose] public def tail : Journey City → NEList City
  | ConsList.wrap (b, c) => ConsList.wrap c
  | ConsList.cons _ xs => toNE xs

/-- **tour-defn**: `[a]⧺xs`, the city `a` put in front of a `list⁺`: a journey. -/
@[expose] public def prepend (a : City) : NEList City → Journey City
  | ConsList.wrap c => ConsList.wrap (a, c)
  | ConsList.cons b xs => ConsList.cons a (prepend b xs)

/-- **tour-defn**: `replaceHead ≜ (𝟙×tail) ⧺` — the first city replaced by `a`. -/
@[expose] public def replaceHead (a : City) : Journey City → Journey City := fun xs => prepend a (tail xs)

/-- `replaceHead ≜ (𝟙×tail) ⧺`, point-free. -/
public theorem replaceHead_eq :
    (graph (fun q : City × Journey City => replaceHead q.1 q.2)
      : (⟨City × Journey City⟩ : RelSet.{0}) ⟶ ⟨Journey City⟩)
    = rprodMap (𝟙 (⟨City⟩ : RelSet.{0}))
        (graph tail : (⟨Journey City⟩ : RelSet.{0}) ⟶ dNE City)
      ≫ (graph (fun q : City × NEList City => prepend q.1 q.2)
          : (⟨City × NEList City⟩ : RelSet.{0}) ⟶ ⟨Journey City⟩) := by
  apply hom_ext; intro p q
  constructor
  · intro h; exact ⟨(p.1, tail p.2), ⟨rfl, rfl⟩, h⟩
  · rintro ⟨⟨u₁, u₂⟩, ⟨h₁, h₂⟩, h⟩
    have e₁ : p.1 = u₁ := h₁
    have e₂ : u₂ = tail p.2 := h₂
    have e : q = prepend u₁ u₂ := h
    show q = prepend p.1 (tail p.2)
    rw [e, e₁, e₂]

/-- `⧺` undoes the reading as a `list⁺`: `[a]⧺↑x = [a]⧺x`, the cons of the journey. -/
public theorem prepend_toNE (a : City) : ∀ x : Journey City, prepend a (toNE x) = ConsList.cons a x
  | ConsList.wrap (_, _) => rfl
  | ConsList.cons b x => congrArg (ConsList.cons a) (prepend_toNE b x)

public theorem replaceHead_wrap (a b c : City) :
    replaceHead a (ConsList.wrap (b, c)) = ConsList.wrap (a, c) := rfl

public theorem replaceHead_cons (a b : City) (x : Journey City) :
    replaceHead a (ConsList.cons b x) = ConsList.cons a x := prepend_toNE a x

public theorem hd_replaceHead (a : City) (x : Journey City) : head (replaceHead a x) = a := by
  rcases x with ⟨_, _⟩ | ⟨_, _⟩
  · rfl
  · rw [replaceHead_cons]; rfl

public theorem nxt_replaceHead (a : City) (x : Journey City) : next (replaceHead a x) = next x := by
  rcases x with ⟨_, _⟩ | ⟨_, _⟩
  · rfl
  · rw [replaceHead_cons]; rfl

/-- **tour-defn**: `outcost [a₀,…,aₙ]=tc (a₀,a₁)+⋯+tc (aₙ₋₁,aₙ)`. -/
@[expose] public def outcost [RelSet.Tour City] : Journey City → Int
  | ConsList.wrap (a, b) => tc (a, b)
  | ConsList.cons a xs => tc (a, head xs) + outcost xs

/-- **tour-defn**: `incost [a₀,…,aₙ]=tc (a₁,a₀)+⋯+tc (aₙ,aₙ₋₁)`. -/
@[expose] public def incost [RelSet.Tour City] : Journey City → Int
  | ConsList.wrap (a, b) => tc (b, a)
  | ConsList.cons a xs => tc (head xs, a) + incost xs

/-- **tour-defn**: `cost (xs,ys)=outcost xs+incost ys`. -/
@[expose] public def cost [RelSet.Tour City] (t : Tour City) : Int :=
  outcost t.1 + incost t.2

public theorem outcost_replaceHead [RelSet.Tour City] (a : City) (x : Journey City) :
    outcost (replaceHead a x) = outcost x - tc (head x, next x) + tc (a, next x) := by
  cases x with
  | wrap p =>
    obtain ⟨p₁, p₂⟩ := p
    show tc (a, p₂) = tc (p₁, p₂) - tc (p₁, p₂) + tc (a, p₂); omega
  | cons b x =>
    rw [replaceHead_cons]
    show tc (a, head x) + outcost x
      = tc (b, head x) + outcost x - tc (b, head x) + tc (a, head x)
    omega

public theorem incost_replaceHead [RelSet.Tour City] (a : City) (x : Journey City) :
    incost (replaceHead a x) = incost x - tc (next x, head x) + tc (next x, a) := by
  cases x with
  | wrap p =>
    obtain ⟨p₁, p₂⟩ := p
    show tc (p₂, a) = tc (p₂, p₁) - tc (p₂, p₁) + tc (p₂, a); omega
  | cons b x =>
    rw [replaceHead_cons]
    show tc (head x, a) + incost x
      = tc (head x, b) + incost x - tc (head x, b) + tc (head x, a)
    omega

/-- **tour-defn**: `dropl (a,([b]⧺xs,ys))=([a]⧺xs,[a]⧺ys)` — drop the head of the outward
    journey and start both from `a`. -/
@[expose] public def dropl (a : City) (t : Tour City) : Tour City :=
  (replaceHead a t.1, ConsList.cons a t.2)

/-- `droplFn`'s defining equation, stated so the formula printer can print it. -/
public theorem dropl_pair (a : City) (x y : Journey City) :
    dropl a (x, y) = (prepend a (tail x), ConsList.cons a y) := rfl

/-- `tail`'s two defining equations, stated so the formula printer can print them. -/
public theorem tail_wrap (b c : City) :
    tail (ConsList.wrap (b, c)) = (ConsList.wrap c : NEList City) := rfl

public theorem tail_cons (b : City) (x : Journey City) : tail (ConsList.cons b x) = toNE x := rfl

/-- **tour-defn**: `dropr (a,(xs,[b]⧺ys))=([a]⧺xs,[a]⧺ys)`. -/
@[expose] public def dropr (a : City) (t : Tour City) : Tour City :=
  (ConsList.cons a t.1, replaceHead a t.2)

/-- `dropl` point-free: `dropl = ⟨⟨π₁,π₂π₁⟩(𝟙×tail)⧺, ⟨π₁,π₂π₂⟩ cons⟩` — copy `a`, put it in
    front of the outward journey's tail, and cons it onto the return journey. -/
public theorem dropl_pointfree :
    (graph (fun p : City × Tour City => dropl p.1 p.2)
      : (⟨City × Tour City⟩ : RelSet.{0}) ⟶ dTour City)
    = rpair
        (rpair (graph Prod.fst : (⟨City × Tour City⟩ : RelSet.{0}) ⟶ ⟨City⟩)
            ((graph Prod.snd : (⟨City × Tour City⟩ : RelSet.{0}) ⟶ dTour City)
              ≫ (graph Prod.fst : dTour City ⟶ ⟨Journey City⟩))
          ≫ rprodMap (𝟙 (⟨City⟩ : RelSet.{0}))
              (graph tail : (⟨Journey City⟩ : RelSet.{0}) ⟶ dNE City)
          ≫ (graph (fun q : City × NEList City => prepend q.1 q.2)
              : (⟨City × NEList City⟩ : RelSet.{0}) ⟶ ⟨Journey City⟩))
        (rpair (graph Prod.fst : (⟨City × Tour City⟩ : RelSet.{0}) ⟶ ⟨City⟩)
            ((graph Prod.snd : (⟨City × Tour City⟩ : RelSet.{0}) ⟶ dTour City)
              ≫ (graph Prod.snd : dTour City ⟶ ⟨Journey City⟩))
          ≫ (graph (fun q : City × Journey City => ConsList.cons q.1 q.2)
              : (⟨City × Journey City⟩ : RelSet.{0}) ⟶ ⟨Journey City⟩)) := by
  rw [← replaceHead_eq]
  apply hom_ext; intro p q
  constructor
  · intro h
    have h' : q = dropl p.1 p.2 := h
    subst h'
    exact ⟨⟨(p.1, p.2.1), ⟨rfl, p.2, rfl, rfl⟩, rfl⟩, ⟨(p.1, p.2.2), ⟨rfl, p.2, rfl, rfl⟩, rfl⟩⟩
  · rintro ⟨⟨⟨u₁, u₂⟩, ⟨hu₁, y, hy, hu₂⟩, h₁⟩, ⟨⟨v₁, v₂⟩, ⟨hv₁, z, hz, hv₂⟩, h₂⟩⟩
    have e₁ : q.1 = replaceHead u₁ u₂ := h₁
    have e₂ : q.2 = ConsList.cons v₁ v₂ := h₂
    have f₁ : u₁ = p.1 := hu₁
    have f₂ : u₂ = y.1 := hu₂
    have f₃ : v₁ = p.1 := hv₁
    have f₄ : v₂ = z.2 := hv₂
    have g₁ : y = p.2 := hy
    have g₂ : z = p.2 := hz
    show q = dropl p.1 p.2
    rw [Prod.ext_iff]
    subst f₁ f₂ f₃ f₄ g₁ g₂
    exact ⟨e₁, e₂⟩

/-- **B&dM p.215**: `cost (dropl (a,(x,y))) = cost (x,y) + tc(a,next x) − tc(head x,next x)
    + tc(head y,a)` — the step reads both heads and the outward second city. -/
public theorem cost_dropl [RelSet.Tour City] (a : City) (t : Tour City) :
    cost (dropl a t)
      = cost t + tc (a, next t.1) - tc (head t.1, next t.1) + tc (head t.2, a) := by
  show outcost (replaceHead a t.1) + (tc (head t.2, a) + incost t.2)
    = outcost t.1 + incost t.2 + tc (a, next t.1) - tc (head t.1, next t.1) + tc (head t.2, a)
  rw [outcost_replaceHead]
  omega

/-- **B&dM p.215**: `cost (dropr (a,(x,y))) = cost (x,y) + tc(a,head x) − tc(next y,head y)
    + tc(next y,a)`. -/
public theorem cost_dropr [RelSet.Tour City] (a : City) (t : Tour City) :
    cost (dropr a t)
      = cost t + tc (a, head t.1) - tc (next t.2, head t.2) + tc (next t.2, a) := by
  show tc (a, head t.1) + outcost t.1 + incost (replaceHead a t.2)
    = outcost t.1 + incost t.2 + tc (a, head t.1) - tc (next t.2, head t.2) + tc (next t.2, a)
  rw [incost_replaceHead]
  omega

/-- **tour-defn**: `R ≜ cost ≤ cost°`. -/
@[expose] public def R [RelSet.Tour City] : dTour City ⟶ dTour City :=
  fun t t' => cost t ≤ cost t'

public theorem R_eq [RelSet.Tour City] :
    R = graph cost ≫ leq ≫ (graph cost : dTour City ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro t t'
  constructor
  · intro h; exact ⟨cost t, rfl, cost t', h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    show cost t ≤ cost t'
    rw [← (show m = cost t from hm), ← (show n = cost t' from hn)]
    exact hmn

/-- **tour-defn**: `Q ≜ R ∩ (next₂ next₂°)` — the book's order as printed, `next₂ ≜ next×next`. -/
@[expose] public def Qbook [RelSet.Tour City] : dTour City ⟶ dTour City :=
  fun t t' => cost t ≤ cost t' ∧ next t.1 = next t'.1 ∧ next t.2 = next t'.2

/-- `Q ≜ Qbook ∩ (head₂ head₂°)` — `Qbook` with the invariant the book appeals to on p.215 ("tours of
    the same input") written down: the two candidates start from the same city. -/
@[expose] public def Q [RelSet.Tour City] : dTour City ⟶ dTour City :=
  fun t t' => cost t ≤ cost t' ∧ (next t.1 = next t'.1 ∧ next t.2 = next t'.2)
    ∧ (head t.1 = head t'.1 ∧ head t.2 = head t'.2)

/-- **tour-defn**: `next₂ ≜ next×next`, the second cities of both journeys. -/
@[expose] public def next₂ (t : Tour City) : City × City := (next t.1, next t.2)

/-- **tour-defn**: `head₂ ≜ head×head`, the first cities of both journeys. -/
@[expose] public def head₂ (t : Tour City) : City × City := (head t.1, head t.2)

/-- `t R t′` iff `t` costs no more than `t′`: the pointwise reading of `R_eq`. -/
public theorem R_apply [RelSet.Tour City] (t t' : Tour City) : R t t' ↔ cost t ≤ cost t' := Iff.rfl

/-- `Q = R ∩ (next₂ next₂°) ∩ (head₂ head₂°)`, point-free. -/
public theorem Q_eq [RelSet.Tour City] :
    Q = R ∩ (graph next₂ ≫ (graph next₂ : dTour City ⟶ (⟨City × City⟩ : RelSet.{0}))°)
      ∩ (graph head₂ ≫ (graph head₂ : dTour City ⟶ (⟨City × City⟩ : RelSet.{0}))°) := by
  apply hom_ext; intro t t'
  constructor
  · rintro ⟨hc, ⟨hn1, hn2⟩, hh1, hh2⟩
    exact ⟨⟨hc, next₂ t, rfl, (by rw [hn1, hn2] : (next t.1, next t.2) = (next t'.1, next t'.2))⟩,
      head₂ t, rfl, (by rw [hh1, hh2] : (head t.1, head t.2) = (head t'.1, head t'.2))⟩
  · rintro ⟨⟨hc, m, hm, hm'⟩, k, hk, hk'⟩
    have hn : next₂ t = next₂ t' := (hm : m = next₂ t).symm.trans hm'
    have hh : head₂ t = head₂ t' := (hk : k = head₂ t).symm.trans hk'
    exact ⟨hc, ⟨congrArg Prod.fst hn, congrArg Prod.snd hn⟩, congrArg Prod.fst hh, congrArg Prod.snd hh⟩

/-- `t Q t′` iff `t` costs no more than `t′` and both journeys share their first two cities. -/
public theorem Q_apply [RelSet.Tour City] (t t' : Tour City) :
    Q t t' ↔ cost t ≤ cost t' ∧ (next t.1 = next t'.1 ∧ next t.2 = next t'.2)
      ∧ (head t.1 = head t'.1 ∧ head t.2 = head t'.2) := Iff.rfl

public theorem Q_le_Qbook [RelSet.Tour City] : Q (City := City) ⊑ Qbook := le_iff.mpr fun _ _ h => ⟨h.1, h.2.1⟩

public theorem Q_le_R [RelSet.Tour City] : Q (City := City) ⊑ R := le_iff.mpr fun _ _ h => h.1

public theorem Q_refl [RelSet.Tour City] : 𝟙 (dTour City) ⊑ Q :=
  le_iff.mpr fun t t' h => by
    obtain rfl : t = t' := h
    exact ⟨Int.le_refl _, ⟨rfl, rfl⟩, rfl, rfl⟩

public theorem Q_trans [RelSet.Tour City] : Q (City := City) ≫ Q ⊑ Q :=
  le_iff.mpr fun _ _ h => by
    obtain ⟨_, ⟨hc1, ⟨hn1, hn2⟩, hh1, hh2⟩, ⟨hc2, ⟨hn1', hn2'⟩, hh1', hh2'⟩⟩ := h
    exact ⟨Int.le_trans hc1 hc2, ⟨hn1.trans hn1', hn2.trans hn2'⟩,
      hh1.trans hh1', hh2.trans hh2'⟩

public theorem R_recip_trans [RelSet.Tour City] : (R (City := City))° ≫ R° ⊑ R° :=
  le_iff.mpr fun t u h => by
    obtain ⟨s, h1, h2⟩ := h
    exact Int.le_trans (h2 : cost u ≤ cost s) (h1 : cost s ≤ cost t)

/-! ## The two algebras `[start,dropl]` and `[start,dropr]` -/

/-- **tour-defn**: `start (a,b)=([a,b],[a,b])`, the one-edge tour both algebras begin at.  A `def`
    because a picture of either algebra draws this arm, and a `fun` has no name a label can write. -/
@[expose] public def start : City × City → Tour City
  | (a, b) => (ConsList.wrap (a, b), ConsList.wrap (a, b))

/-- **tour-defn**: `[start,dropl]` with `start (a,b)=([a,b],[a,b])`. -/
@[expose] public def droplAlgFn :
    (((F (City × City) City).obj (dTour City))).carrier → Tour City
  | Sum.inl p => start p
  | Sum.inr q => dropl q.1 q.2

/-- **tour-defn**: `[start,dropr]`. -/
@[expose] public def droprAlgFn :
    (((F (City × City) City).obj (dTour City))).carrier → Tour City
  | Sum.inl p => start p
  | Sum.inr q => dropr q.1 q.2

/-- **tour-defn**: `tour ≜ ⦇[start,dropl∪dropr]⦈`. -/
@[expose] public def tourAlg : Alg (F (City × City) City) (dTour City) :=
  graph (droplAlgFn (City := City)) ∪ graph droprAlgFn

@[expose] public def tour : dCL (City × City) City ⟶ dTour City := ⦇tourAlg⦈

/-! ## The `⦇tourAlg⦈` bead -/

/-- `[start,dropl∪dropr]` pointwise: a step is one of the two functions, nothing else. -/
public theorem tourAlg_apply (u : (((F (City × City) City).obj (dTour City))).carrier)
    (t : Tour City) : tourAlg u t = (t = droplAlgFn u ∨ t = droprAlgFn u) := by
  simp only [tourAlg, union_apply]; rfl

/-- Reading as a `list⁺` keeps journeys related: `cl(R×R,R)` becomes `cl(R,R)`. -/
public theorem clP_toNE {A B : Type} (R : dE A ⟶ dE B) :
    ∀ (x : Journey A) (y : Journey B), clP (rprodMap R R) R x y → clP R R (toNE x) (toNE y)
  | ConsList.wrap (_, _), ConsList.wrap (_, _), h => ⟨h.1, h.2⟩
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons _ x, ConsList.cons _ y, h => ⟨h.1, clP_toNE R x y h.2⟩

/-- `tail` keeps journeys related: `cl(R×R,R)` on the journeys gives `cl(R,R)` on the tails. -/
public theorem clP_tail {A B : Type} (R : dE A ⟶ dE B) :
    ∀ (x : Journey A) (y : Journey B), clP (rprodMap R R) R x y → clP R R (tail x) (tail y)
  | ConsList.wrap (_, _), ConsList.wrap (_, _), h => h.2
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons _ x, ConsList.cons _ y, h => clP_toNE R x y h.2

/-- `⧺` keeps related cities and related `list⁺`s related as journeys. -/
public theorem clP_prepend {A B : Type} (R : dE A ⟶ dE B) :
    ∀ {a : A} {b : B} (u : NEList A) (v : NEList B), R a b → clP R R u v →
      clP (rprodMap R R) R (prepend a u) (prepend b v)
  | _, _, ConsList.wrap _, ConsList.wrap _, hab, h => ⟨hab, h⟩
  | _, _, ConsList.wrap _, ConsList.cons _ _, _, h => h.elim
  | _, _, ConsList.cons _ _, ConsList.wrap _, _, h => h.elim
  | _, _, ConsList.cons _ u, ConsList.cons _ v, hab, h => ⟨hab, clP_prepend R u v h.1 h.2⟩

/-- Replacing the head on both sides keeps a journey `cl(R×R,R)`-related. -/
public theorem clP_replaceHead {A B : Type} (R : dE A ⟶ dE B) {a : A} {b : B} (hab : R a b)
    (x : Journey A) (y : Journey B) (h : clP (rprodMap R R) R x y) :
    clP (rprodMap R R) R (replaceHead a x) (replaceHead b y) :=
  clP_prepend R (tail x) (tail y) hab (clP_tail R x y h)

/-- The fold POINTWISE: a `cl(R×R,R)`-related journey folds to a related tour.  One
    direction only — `dropl` writes its one city into BOTH journeys, so an image pair whose two
    heads differ is reached by no journey at all. -/
public theorem cataFoldTour_lax {A B : Type} (R : dE A ⟶ dE B) :
    ∀ (x : Journey A) (x' : Journey B) (t : Tour B),
      clP (rprodMap R R) R x x' → cataFold (tourAlg (City := B)) x' t →
      ∃ t₀, cataFold (tourAlg (City := A)) x t₀ ∧ clP (rprodMap R R) R t₀.1 t.1
        ∧ clP (rprodMap R R) R t₀.2 t.2
  | ConsList.wrap (p₁, p₂), ConsList.wrap (q₁, q₂), t, h, hf => by
      rw [cataFold_wrap, tourAlg_apply] at hf
      obtain rfl : t = (ConsList.wrap (q₁, q₂), ConsList.wrap (q₁, q₂)) := hf.elim id id
      refine ⟨(ConsList.wrap (p₁, p₂), ConsList.wrap (p₁, p₂)), ?_, h, h⟩
      rw [cataFold_wrap, tourAlg_apply]
      exact Or.inl rfl
  | ConsList.wrap _, ConsList.cons _ _, _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, _, h, _ => h.elim
  | ConsList.cons a x, ConsList.cons b y, t, h, hf => by
      rw [cataFold_cons] at hf
      obtain ⟨r, hr, hstep⟩ := hf
      rw [tourAlg_apply] at hstep
      obtain ⟨r₀, hr₀, hrel₁, hrel₂⟩ := cataFoldTour_lax R x y r h.2 hr
      rcases hstep with rfl | rfl
      · refine ⟨dropl a r₀, ?_, clP_replaceHead R h.1 r₀.1 r.1 hrel₁, h.1, hrel₂⟩
        rw [cataFold_cons]
        exact ⟨r₀, hr₀, by rw [tourAlg_apply]; exact Or.inl rfl⟩
      · refine ⟨dropr a r₀, ?_, ⟨h.1, hrel₁⟩, clP_replaceHead R h.1 r₀.2 r.2 hrel₂⟩
        rw [cataFold_cons]
        exact ⟨r₀, hr₀, by rw [tourAlg_apply]; exact Or.inr rfl⟩

/-- **the `⦇tourAlg⦈` bead is LAX**: `Journey(R) ⦇tourAlg⦈ ⊑ ⦇tourAlg⦈ (Journey(R)×Journey(R))`.
    Strictness fails for the reason p.215 gives the thinning order: `dropl` writes its one city
    into BOTH journeys, so an image pair whose two heads differ is reached by no journey. -/
public theorem tour_lax_natural :
    LaxNatural (Relator.prod journeyRelator journeyRelator) journeyRelator
      (fun a : RelSet.{0} =>
        (⦇tourAlg⦈ : dCL (a.carrier × a.carrier) a.carrier ⟶ dTour a.carrier)) := by
  intro a b R
  have h : cl (prodMap (relProd a a) (relProd b b) R R) R ≫ cataR (tourAlg (City := b.carrier))
      ⊑ cataR (tourAlg (City := a.carrier))
        ≫ prodMap (relProd (⟨Journey a.carrier⟩ : RelSet.{0}) ⟨Journey a.carrier⟩)
            (relProd (⟨Journey b.carrier⟩ : RelSet.{0}) ⟨Journey b.carrier⟩)
            (cl (prodMap (relProd a a) (relProd b b) R R) R)
            (cl (prodMap (relProd a a) (relProd b b) R R) R) := by
    simp only [prodMap_eq_rprodMap]
    exact le_iff.mpr fun x t hh => by
      obtain ⟨x', hx, ht⟩ := hh
      obtain ⟨t₀, ht₀, h₁, h₂⟩ := cataFoldTour_lax R x x' t hx ht
      exact ⟨t₀, ht₀, h₁, h₂⟩
  rwa [cataR_eq_relCata, cataR_eq_relCata] at h

/-- **the point-free `dropl` is LAX** in the city type: `(R×Journey(R)×Journey(R)) dropl ⊑
    dropl (Journey(R)×Journey(R))`, the family being `dropl_pointfree`'s right-hand side. -/
public theorem dropl_lax_natural :
    LaxNatural (Relator.prod journeyRelator journeyRelator)
      (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.prod journeyRelator journeyRelator))
      (fun a : RelSet.{0} =>
        rpair
          (rpair (graph Prod.fst : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ ⟨a.carrier⟩)
              ((graph Prod.snd : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ dTour a.carrier)
                ≫ (graph Prod.fst : dTour a.carrier ⟶ ⟨Journey a.carrier⟩))
            ≫ rprodMap (𝟙 a) (graph tail : (⟨Journey a.carrier⟩ : RelSet.{0}) ⟶ dNE a.carrier)
            ≫ (graph (fun q : a.carrier × NEList a.carrier => prepend q.1 q.2)
                : (⟨a.carrier × NEList a.carrier⟩ : RelSet.{0}) ⟶ ⟨Journey a.carrier⟩))
          (rpair (graph Prod.fst : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ ⟨a.carrier⟩)
              ((graph Prod.snd : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ dTour a.carrier)
                ≫ (graph Prod.snd : dTour a.carrier ⟶ ⟨Journey a.carrier⟩))
            ≫ (graph (fun q : a.carrier × Journey a.carrier => ConsList.cons q.1 q.2)
                : (⟨a.carrier × Journey a.carrier⟩ : RelSet.{0}) ⟶ ⟨Journey a.carrier⟩))) := by
  intro a b R
  dsimp only
  rw [← dropl_pointfree, ← dropl_pointfree]
  simp only [journeyRelator, clRelator, Relator.prod, Relator.idRelator, prodMap_eq_rprodMap]
  exact le_iff.mpr fun p t ⟨q, ⟨h₁, h₂, h₃⟩, ht⟩ => by
    obtain rfl : t = dropl q.1 q.2 := ht
    exact ⟨dropl p.1 p.2, rfl, clP_replaceHead R h₁ p.2.1 q.2.1 h₂, h₁, h₃⟩

/-- **the copy `⟨⟨π₁,π₂π₁⟩,⟨π₁,π₂π₂⟩⟩` that opens `dropl` is LAX**: `(R×J(R)×J(R)) copy ⊑
    copy ((R×J(R))×(R×J(R)))` — one city copied into both pairs, so two different images of it
    are reached by no input. -/
public theorem droplCopy_lax_natural :
    LaxNatural
      (Relator.prod (Relator.prod (Relator.idRelator RelSet.{0}) journeyRelator)
        (Relator.prod (Relator.idRelator RelSet.{0}) journeyRelator))
      (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.prod journeyRelator journeyRelator))
      (fun a : RelSet.{0} =>
        rpair
          (rpair (graph Prod.fst : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ ⟨a.carrier⟩)
            ((graph Prod.snd : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ dTour a.carrier)
              ≫ (graph Prod.fst : dTour a.carrier ⟶ ⟨Journey a.carrier⟩)))
          (rpair (graph Prod.fst : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ ⟨a.carrier⟩)
            ((graph Prod.snd : (⟨a.carrier × Tour a.carrier⟩ : RelSet.{0}) ⟶ dTour a.carrier)
              ≫ (graph Prod.snd : dTour a.carrier ⟶ ⟨Journey a.carrier⟩)))) := by
  intro a b R
  simp only [journeyRelator, clRelator, Relator.prod, Relator.idRelator, prodMap_eq_rprodMap]
  exact le_iff.mpr fun p t ⟨q, ⟨h₁, h₂, h₃⟩, ht⟩ => by
    obtain ⟨⟨e₁, m, e₂, e₃⟩, e₄, m', e₅, e₆⟩ := ht
    have e₁ : t.1.1 = q.1 := e₁; have e₄ : t.2.1 = q.1 := e₄
    have e₂ : m = q.2 := e₂; have e₅ : m' = q.2 := e₅
    have e₃ : t.1.2 = m.1 := e₃; have e₆ : t.2.2 = m'.2 := e₆
    subst e₂ e₅
    exact ⟨((p.1, p.2.1), (p.1, p.2.2)), ⟨⟨rfl, p.2, rfl, rfl⟩, rfl, p.2, rfl, rfl⟩,
      ⟨e₁ ▸ h₁, e₃ ▸ h₂⟩, e₄ ▸ h₁, e₆ ▸ h₃⟩

/-- **`tail` is LAX** in the city type: `J(R) tail ⊑ tail list⁺(R)`. -/
public theorem tail_lax_natural :
    LaxNatural nelistRelator journeyRelator
      (fun a : RelSet.{0} =>
        (graph tail : (⟨Journey a.carrier⟩ : RelSet.{0}) ⟶ dNE a.carrier)) := by
  intro a b R
  simp only [journeyRelator, nelistRelator, clRelator, Relator.prod, Relator.idRelator,
    prodMap_eq_rprodMap]
  exact le_iff.mpr fun x t ⟨y, h, ht⟩ => by
    obtain rfl : t = tail y := ht
    exact ⟨tail x, rfl, clP_tail R x y h⟩

/-- **`⧺` is LAX** in the city type: `(R×list⁺(R)) ⧺ ⊑ ⧺ J(R)`. -/
public theorem prepend_lax_natural :
    LaxNatural journeyRelator (Relator.prod (Relator.idRelator RelSet.{0}) nelistRelator)
      (fun a : RelSet.{0} =>
        (graph (fun q : a.carrier × NEList a.carrier => prepend q.1 q.2)
          : (⟨a.carrier × NEList a.carrier⟩ : RelSet.{0}) ⟶ ⟨Journey a.carrier⟩)) := by
  intro a b R
  simp only [journeyRelator, nelistRelator, clRelator, Relator.prod, Relator.idRelator,
    prodMap_eq_rprodMap]
  exact le_iff.mpr fun p t ⟨q, ⟨h₁, h₂⟩, ht⟩ => by
    obtain rfl : t = prepend q.1 q.2 := ht
    exact ⟨prepend p.1 p.2, rfl, clP_prepend R p.2 q.2 h₁ h₂⟩

/-- **`cons` is LAX** in the city type: `(R×J(R)) cons ⊑ cons J(R)`. -/
public theorem journeyCons_lax_natural :
    LaxNatural journeyRelator (Relator.prod (Relator.idRelator RelSet.{0}) journeyRelator)
      (fun a : RelSet.{0} =>
        (graph (fun q : a.carrier × Journey a.carrier => ConsList.cons q.1 q.2)
          : (⟨a.carrier × Journey a.carrier⟩ : RelSet.{0}) ⟶ ⟨Journey a.carrier⟩)) := by
  intro a b R
  simp only [journeyRelator, clRelator, Relator.prod, Relator.idRelator, prodMap_eq_rprodMap]
  exact le_iff.mpr fun p t ⟨q, ⟨h₁, h₂⟩, ht⟩ => by
    obtain rfl : t = ConsList.cons q.1 q.2 := ht
    exact ⟨ConsList.cons p.1 p.2, rfl, h₁, h₂⟩

/-! ## `tour-mono` -/

/-! The four refutations share one pair of GENUINE tours — each has its own two heads equal, as
  every partial tour does (B&dM p.214) — differing only in the head they share, which is what
  makes them tours of DIFFERENT inputs.  `tc (a,b) = a·b`, so a step out of `3` costs `3·head`. -/

section Counterexample

/-- The refutations' cost, `tc (a,b) = a·b`. -/
@[expose] public def tcMul : RelSet.Tour Int := ⟨fun p => p.1 * p.2⟩
attribute [local instance] tcMul

/-- The tour `([1,0],[1,0])`, of cost `0`. -/
@[expose] public def tA : Tour Int :=
  (ConsList.wrap ((1 : Int), (0 : Int)), ConsList.wrap ((1 : Int), (0 : Int)))

/-- The tour `([0,0],[0,0])`, also of cost `0` and with the same two second cities. -/
@[expose] public def tB : Tour Int :=
  (ConsList.wrap ((0 : Int), (0 : Int)), ConsList.wrap ((0 : Int), (0 : Int)))

/-- `tA` and `tB` are `Q`-related: equal cost, equal `next₂`.  They differ only in their shared
    head, which `Q` does not record. -/
public theorem tA_Q_tB : Qbook tA tB :=
  ⟨by decide, by decide, by decide⟩

/-- **tour-mono**, first row (marked FALSE in the note; B&dM p.215): `(𝟙×R) dropl ⊑ dropl R`
    fails.  `tA` and `tB` cost the same, but continuing either to city `3` costs `tc (head,3)`
    on the return, which is `3` from `tA` and `0` from `tB`. -/
public theorem tour_mono_dropl_false :
    ¬ Freyd.Alg.Pres (F := F (Int × Int) Int) (graph droplAlgFn)
        R := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droplAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB.1⟩, rfl⟩
  obtain ⟨s, hs, hR⟩ := hstep
  obtain rfl : s = droplAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : cost (droplAlgFn (Sum.inr ((3 : Int), tA)))
      ≤ cost (droplAlgFn (Sum.inr ((3 : Int), tB))) := hR
  revert hbad
  decide

/-- **THE FINDING**: `tour-mono`'s POSITIVE first row, `(𝟙×Q) dropl ⊑ dropl Q` at
    `Q ≜ R ∩ (next₂ next₂°)`, is false as printed — `tA` and `tB` are `Q`-related genuine tours,
    and `dropl` separates them.  What it reads and `Q` does not record is the HEAD
    (`+ tc(head y,a)`, B&dM p.215); the row holds once the heads are added, which is
    `tour_mono_dropl` below. -/
public theorem tour_mono_dropl_Q_false :
    ¬ Freyd.Alg.Pres (F := F (Int × Int) Int) (graph droplAlgFn)
        (Qbook) := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droplAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB⟩, rfl⟩
  obtain ⟨s, hs, hQ⟩ := hstep
  obtain rfl : s = droplAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : Qbook (droplAlgFn (Sum.inr ((3 : Int), tA)))
      (droplAlgFn (Sum.inr ((3 : Int), tB))) := hQ
  have hbadc := hbad.1
  revert hbadc
  decide

/-- **tour-mono**, second row (marked FALSE in the note): `(𝟙×R) dropr ⊑ dropr R` fails on the
    same two tours — `dropr` reads the head through `+ tc(a,head x)`. -/
public theorem tour_mono_dropr_false :
    ¬ Freyd.Alg.Pres (F := F (Int × Int) Int) (graph droprAlgFn)
        R := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droprAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB.1⟩, rfl⟩
  obtain ⟨s, hs, hR⟩ := hstep
  obtain rfl : s = droprAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : cost (droprAlgFn (Sum.inr ((3 : Int), tA)))
      ≤ cost (droprAlgFn (Sum.inr ((3 : Int), tB))) := hR
  revert hbad
  decide

/-- **THE FINDING**, mirror: `tour-mono`'s POSITIVE second row `(𝟙×Q) dropr ⊑ dropr Q` is false
    as printed too, on the same two genuine tours. -/
public theorem tour_mono_dropr_Q_false :
    ¬ Freyd.Alg.Pres (F := F (Int × Int) Int) (graph droprAlgFn)
        (Qbook) := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droprAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB⟩, rfl⟩
  obtain ⟨s, hs, hQ⟩ := hstep
  obtain rfl : s = droprAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : Qbook (droprAlgFn (Sum.inr ((3 : Int), tA)))
      (droprAlgFn (Sum.inr ((3 : Int), tB))) := hQ
  have hbadc := hbad.1
  revert hbadc
  decide

end Counterexample

/-- **tour-mono**, first row at `Q`: `(𝟙×Q) dropl ⊑ dropl Q`.  Both deltas of `cost_dropl`
    are then the same number, and the result's own heads (`a`, `a`) and second cities
    (`next x`, `head y`) are fixed by `Q`. -/
public theorem tour_mono_dropl [RelSet.Tour City] : Freyd.Alg.Pres (F := F (City × City) City) (graph droplAlgFn)
    Q :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = droplAlgFn v := hr
    cases u with
    | inl p =>
      cases v with
      | inl p' =>
        obtain rfl : p = p' := hFv
        exact ⟨droplAlgFn (Sum.inl p), rfl, Int.le_refl _, ⟨rfl, rfl⟩, rfl, rfl⟩
      | inr q => exact (hFv : False).elim
    | inr q =>
      cases v with
      | inl p' => exact (hFv : False).elim
      | inr q' =>
        obtain ⟨a, t⟩ := q
        obtain ⟨b, t'⟩ := q'
        obtain ⟨hab, hQ⟩ := hFv
        obtain rfl : a = b := hab
        have hcost : cost t ≤ cost t' := hQ.1
        have hn1 : next t.1 = next t'.1 := hQ.2.1.1
        have hn2 : next t.2 = next t'.2 := hQ.2.1.2
        have hh1 : head t.1 = head t'.1 := hQ.2.2.1
        have hh2 : head t.2 = head t'.2 := hQ.2.2.2
        refine ⟨dropl a t, rfl, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
        · show cost (dropl a t) ≤ cost (dropl a t')
          rw [cost_dropl, cost_dropl, hn1, hh1, hh2]
          omega
        · show next (replaceHead a t.1) = next (replaceHead a t'.1)
          rw [nxt_replaceHead, nxt_replaceHead]; exact hn1
        · show head t.2 = head t'.2
          exact hh2
        · show head (replaceHead a t.1) = head (replaceHead a t'.1)
          rw [hd_replaceHead, hd_replaceHead]
        · rfl

/-- **tour-mono**, second row at `Q`: `(𝟙×Q) dropr ⊑ dropr Q`. -/
public theorem tour_mono_dropr [RelSet.Tour City] : Freyd.Alg.Pres (F := F (City × City) City) (graph droprAlgFn)
    Q :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hr⟩ := h
    obtain rfl : r = droprAlgFn v := hr
    cases u with
    | inl p =>
      cases v with
      | inl p' =>
        obtain rfl : p = p' := hFv
        exact ⟨droprAlgFn (Sum.inl p), rfl, Int.le_refl _, ⟨rfl, rfl⟩, rfl, rfl⟩
      | inr q => exact (hFv : False).elim
    | inr q =>
      cases v with
      | inl p' => exact (hFv : False).elim
      | inr q' =>
        obtain ⟨a, t⟩ := q
        obtain ⟨b, t'⟩ := q'
        obtain ⟨hab, hQ⟩ := hFv
        obtain rfl : a = b := hab
        have hcost : cost t ≤ cost t' := hQ.1
        have hn1 : next t.1 = next t'.1 := hQ.2.1.1
        have hn2 : next t.2 = next t'.2 := hQ.2.1.2
        have hh1 : head t.1 = head t'.1 := hQ.2.2.1
        have hh2 : head t.2 = head t'.2 := hQ.2.2.2
        refine ⟨dropr a t, rfl, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
        · show cost (dropr a t) ≤ cost (dropr a t')
          rw [cost_dropr, cost_dropr, hn2, hh1, hh2]
          omega
        · show head t.1 = head t'.1
          exact hh1
        · show next (replaceHead a t.2) = next (replaceHead a t'.2)
          rw [nxt_replaceHead, nxt_replaceHead]; exact hn2
        · rfl
        · show head (replaceHead a t.2) = head (replaceHead a t'.2)
          rw [hd_replaceHead, hd_replaceHead]

/-- **tour-defn**, `P ≜ ⊤`. -/
public theorem tour_sort_dropl :
    Freyd.Alg.Pres (F := F (City × City) City) (graph (droplAlgFn (City := City)))
      (topMor (dTour City) (dTour City)) :=
  Freyd.Alg.graph_pres_topMor _

public theorem tour_sort_dropr :
    Freyd.Alg.Pres (F := F (City × City) City) (graph (droprAlgFn (City := City)))
      (topMor (dTour City) (dTour City)) :=
  Freyd.Alg.graph_pres_topMor _

/-! ## `tour-laws` -/

/-- B&dM's `g₁ ≜ list[start,dropl]` (§8.6, p.215). -/
@[expose] public def g₁ := list (graph (droplAlgFn (City := City)))

/-- B&dM's `g₂ ≜ list[start,dropr]`. -/
@[expose] public def g₂ := list (graph (droprAlgFn (City := City)))

/-- **tour-laws**, the specification step: `tour ≜ ⦇[start,dropl ∪ dropr]⦈` unfolded under
    `Λ(−) est(R)`. -/
public theorem tour_laws_defn [RelSet.Tour City] :
    Λ (tour (City := City)) ≫ est (R)
      = Λ ⦇graph (droplAlgFn (City := City)) ∪ graph droprAlgFn⦈ ≫ est (R) := rfl

/-- **tour-laws** (B&dM §8.6, p.215): a least-cost bitonic tour as a fold that thins the tours
    kept at each city —
    `Λ(tour) est(R) ⊒ ⦇cpL(F) ⟨g₁,g₂⟩ merge ⊤ thinL Q⦈ minL R`.
    Theorem 8.2 (`thinningList`) at `f₁ ≜ [start,dropl]`, `f₂ ≜ [start,dropr]`,
    `p₁ = p₂ ≜ 𝟙`, `P ≜ ⊤`.  The thinning order is `Q`, NOT the note's `Q`: see
    `tour_mono_dropl_Q_false`.  `merge ⊤ = cat` (`merge_top`). -/
public theorem tour_laws [RelSet.Tour City] :
    ⦇cpL ≫ (relProd (dList (Tour City)) (dList (Tour City))).pair
        (g₁ (City := City)) g₂
        ≫ cat ≫ thinL (Q)⦈ ≫ minL (R)
      ⊑ Λ (tour (City := City)) ≫ est (R) := by
  have key := thinningList droplAlgFn droprAlgFn (𝟙 _) (𝟙 _) (le_refl _) (le_refl _)
    («≼» := topMor (dTour City) (dTour City)) (Q := Q) (R := R)
    Q_le_R ⟨Q_refl, Q_trans⟩ ⟨le_trans Q_refl Q_le_R, trans_of_recip_trans R_recip_trans⟩
    (by rw [Cat.comp_id]; exact tour_mono_dropl)
    (by rw [Cat.comp_id]; exact tour_mono_dropr)
    preorder_topMor connected_topMor tour_sort_dropl tour_sort_dropr
  rw [filter_id, Cat.comp_id, Cat.comp_id, Cat.comp_id, Cat.comp_id, merge_top] at key
  exact key

/-! ## `TourRun`: the bitonic-tour program on `RelRep`

The fold keeps a list of tours per city: `stepE` extends each kept tour by `dropl` and `dropr`
(an `enum`, two candidates per tour), `RelRep.thin Q` cuts the candidates, and `RelRep.est R`
reads the least-cost tours off the last list. -/

section TourRun

variable [DecidableEq City] [RelSet.Tour City]

public instance decQ : ∀ t t' : Tour City, Decidable (Q t t') := fun t t' => decidable_of_iff _ (Q_apply t t').symm

public instance decR : ∀ t t' : Tour City, Decidable (R t t') := fun t t' => decidable_of_iff _ (R_apply t t').symm

/-- The thinning order `Q` as a `RelRep` test. -/
@[expose] public def Qt : RelTest (Tour City) (Tour City) := .test fun t t' => decide (Q t t')

public theorem rel_Qt : (Qt (City := City)).rel = Q := hom_ext fun _ _ => decide_eq_true_iff

/-- The cost order `R` as a `RelRep` test. -/
@[expose] public def Rt : RelTest (Tour City) (Tour City) := .test fun t t' => decide (R t t')

public theorem rel_Rt : (Rt (City := City)).rel = R := hom_ext fun _ _ => decide_eq_true_iff

/-- The step's `Λ` form: a tour extended at city `a` by `dropl` and by `dropr`. -/
@[expose] public def stepE : RelRep (City × Tour City) (Tour City) := .enum fun q => [dropl q.1 q.2, dropr q.1 q.2]

omit [DecidableEq City] [RelSet.Tour City] in
/-- `stepE` is the `cons` half of the algebra `[start,dropl∪dropr]`. -/
public theorem rel_stepE :
    (stepE (City := City)).rel
      = (graph Sum.inr : (⟨City × Tour City⟩ : RelSet.{0}) ⟶ (F (City × City) City).obj (dTour City)) ≫ tourAlg :=
  hom_ext fun q t => by
    show t ∈ [dropl q.1 q.2, dropr q.1 q.2] ↔ ∃ u, _ ∧ _
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    exact ⟨fun h => ⟨Sum.inr q, rfl, by rw [tourAlg_apply]; exact h⟩, fun ⟨u, hu, ht⟩ => by
      obtain rfl : u = Sum.inr q := hu
      rw [tourAlg_apply] at ht; exact ht⟩

omit [DecidableEq City] [RelSet.Tour City] in
/-- `[start, dropl∪dropr]` is the junction of `start` and `stepE`. -/
public theorem tourAlg_eq_junc :
    tourAlg = junc (sumCop (dL (City × City)) ⟨City × Tour City⟩) (RelRep.ofFn start).rel stepE.rel :=
  junc_unique _ (hom_ext fun p t => by
    show (∃ u, _ ∧ _) ↔ t ∈ [start p]
    rw [List.mem_singleton]
    exact ⟨fun ⟨u, hu, ht⟩ => by
      obtain rfl : u = Sum.inl p := hu
      rw [tourAlg_apply] at ht; exact ht.elim id id,
      fun h => ⟨Sum.inl p, rfl, by rw [tourAlg_apply]; exact Or.inl h⟩⟩) rel_stepE.symm

/-- The tours kept after the whole input: `⦇thin(Q)·Λ[start, dropl∪dropr]⦈` as a function. -/
@[expose] public def kept : Journey City → List (Tour City) :=
  RelRep.foldList (RelRep.thinList Qt.mem) (fun p => [start p]) fun q => [dropl q.1 q.2, dropr q.1 q.2]

/-- `kept` is `RelRep.foldThin Q` of `start` and `stepE`. -/
public theorem kept_eq : RelRep.foldThin Qt (.ofFn start) stepE = .enum (kept (City := City)) := rfl

/-- The program: the least-cost tours among those kept. -/
@[expose] public def bitonic (xs : Journey City) : List (Tour City) := RelRep.estList Rt.mem (kept xs)

/-- `bitonic` is `RelRep.est R` of `kept`. -/
public theorem bitonic_eq : RelRep.est Rt (.enum (kept (City := City))) = .enum bitonic := rfl

/-- `Λ(kept) ⊑ Λ(tour) thin(Q)`. -/
public theorem kept_thin : Λ (RelRep.enum (kept (City := City))).rel ⊑ Λ tour ≫ thinRel Q := by
  have h := kept_eq (City := City) ▸ RelRep.rel_foldThin (Q := Qt) (B := .ofFn start) (S := stepE)
    (by rw [rel_Qt]; exact Q_refl)
    (by rw [rel_Qt]; exact Q_trans)
    (by rw [rel_Qt, ← tourAlg_eq_junc]; exact pres_union tour_mono_dropl tour_mono_dropr)
  rw [← tourAlg_eq_junc, rel_Qt] at h
  exact h

/-- **The program meets its specification**: every tour `bitonic` returns is a least-cost bitonic
    tour, `bitonic ⊑ Λ(tour) est(R)`. -/
public theorem bitonic_le : (RelRep.enum (bitonic (City := City))).rel ⊑ Λ tour ≫ est R :=
  calc (RelRep.enum bitonic).rel
      = Λ (RelRep.enum kept).rel ≫ est Rt.rel := by rw [← bitonic_eq]; exact RelRep.rel_est _ _
    _ = Λ (RelRep.enum kept).rel ≫ est R := by rw [rel_Rt]
    _ ⊑ (Λ tour ≫ thinRel Q) ≫ est R := comp_mono_right kept_thin _
    _ = Λ tour ≫ (thinRel Q ≫ est R) := Cat.assoc _ _ _
    _ ⊑ Λ tour ≫ est R := comp_mono_left _ (thinRel_comp_est_le Q_le_R (trans_of_recip_trans R_recip_trans))

/-- The run's cost, `tc (a,b) = (a-b)²`. -/
@[expose] public def tcSq : RelSet.Tour Int := ⟨fun p => (p.1 - p.2) * (p.1 - p.2)⟩

attribute [local instance] tcSq in
/-- **kept-run**: on the cities `[0,3,1,4,2]` the fold keeps six tours, the mirror pairs of three. -/
public theorem run_kept :
    kept (ConsList.cons (0 : Int) (ConsList.cons 3 (ConsList.cons 1 (ConsList.wrap (4, 2)))))
      = [(ConsList.wrap (0, 2), ConsList.cons 0 (ConsList.cons 3 (ConsList.cons 1 (ConsList.wrap (4, 2))))),
         (ConsList.cons 0 (ConsList.wrap (1, 2)), ConsList.cons 0 (ConsList.cons 3 (ConsList.wrap (4, 2)))),
         (ConsList.cons 0 (ConsList.cons 3 (ConsList.wrap (1, 2))), ConsList.cons 0 (ConsList.wrap (4, 2))),
         (ConsList.cons 0 (ConsList.wrap (4, 2)), ConsList.cons 0 (ConsList.cons 3 (ConsList.wrap (1, 2)))),
         (ConsList.cons 0 (ConsList.cons 3 (ConsList.wrap (4, 2))), ConsList.cons 0 (ConsList.wrap (1, 2))),
         (ConsList.cons 0 (ConsList.cons 3 (ConsList.cons 1 (ConsList.wrap (4, 2)))), ConsList.wrap (0, 2))] := by
  rfl

attribute [local instance] tcSq in
/-- **tour-run**: on the cities `[0,3,1,4,2]` the program keeps six tours and returns the two of
    least cost `16`, `([0,1,2],[0,3,4,2])` and its mirror. -/
public theorem run_tour :
    bitonic (ConsList.cons (0 : Int) (ConsList.cons 3 (ConsList.cons 1 (ConsList.wrap (4, 2)))))
      = [(ConsList.cons 0 (ConsList.wrap (1, 2)), ConsList.cons 0 (ConsList.cons 3 (ConsList.wrap (4, 2)))),
         (ConsList.cons 0 (ConsList.cons 3 (ConsList.wrap (4, 2))), ConsList.cons 0 (ConsList.wrap (1, 2)))] := by
  rfl

end TourRun

end Freyd.Alg.RelSet.Tour
