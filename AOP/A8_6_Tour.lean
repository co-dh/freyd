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
  `(𝟙×Q) dropr ⊑ dropr Q` at `Q ≜ R ∩ (next2 next2°)`, are FALSE as printed.
  `tour_mono_dropl_Q_false` and `tour_mono_dropr_Q_false` refute them on two GENUINE tours —
  each with its own two heads equal, as p.214 says every partial tour has — that are tours of
  DIFFERENT inputs.  The book says why (p.215): the cost of `dropl (a,(x,y))` is
  `cost (x,y) + tc(a,next x) − tc(head x,next x) + tc(head y,a)`, so the step reads BOTH heads
  as well as both second cities, and "the first conjunct will hold whenever `(x,y)` and
  `(u,v)` are tours of the same input".  That is a monotonicity IN CONTEXT: it is a property of
  the candidates the fold actually holds together, not of tours at large, and `Q` as printed
  does not record it.

  What is proved here instead is the row at `Qc ≜ Q ∩ (head2 head2°)`, which does record it —
  `tour_mono_dropl`, `tour_mono_dropr` — and `tour_laws` is Theorem 8.2 at `Qc`.  The note's
  `thinlist Q` therefore has to become `thinlist Qc`, or Theorem 8.2 has to be replaced by its
  in-context form (`AOP.A8_1`'s `Λ_comp_thinRel_context`, which is exactly `Λ S ≫ thinRel (Q ∩
  (S°S)) = Λ S ≫ thinRel Q`).

  The note's other two rows, `(𝟙×R) dropl ⊑ dropl R` and `(𝟙×R) dropr ⊑ dropr R`, are marked
  FALSE there and are refuted here (`tour_mono_dropl_false`, `tour_mono_dropr_false`).

  ASSUMED, as in the book and in `AOP.A8_3`: the sorted-list interface (8.7)-(8.11).  B&dM's
  `Real` is `Int`, and `tc` is neither positive nor symmetric, as the book insists.
-/
module

public import AOP.A8_3
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Tour

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {City : Type} {tc : City × City → Int}

/-! ## `tour-defn` -/

/-- A journey: a cons-list of cities of length at least two, `[a,b]` being `wrap (a,b)`. -/
@[expose] public abbrev Journey (City : Type) : Type := ConsList (City × City) City
/-- A bitonic tour: the outward journey and the return. -/
@[expose] public abbrev Tour (City : Type) : Type := Journey City × Journey City
/-- The object carrying `Tour`. -/
@[expose] public abbrev dTour (City : Type) : RelSet.{0} := ⟨Tour City⟩

/-- `head` of a journey. -/
@[expose] public def hd : Journey City → City
  | ConsList.wrap p => p.1
  | ConsList.cons a _ => a

/-- **tour-defn**: `next ≜ tail head`, the second city of a journey. -/
@[expose] public def nxt : Journey City → City
  | ConsList.wrap p => p.2
  | ConsList.cons _ x => hd x

/-- `[a]⧺x` with the old head dropped — what `dropl` does to the outward journey. -/
@[expose] public def replaceHead (a : City) : Journey City → Journey City
  | ConsList.wrap p => ConsList.wrap (a, p.2)
  | ConsList.cons _ x => ConsList.cons a x

public theorem hd_replaceHead (a : City) (x : Journey City) : hd (replaceHead a x) = a := by
  cases x <;> rfl

public theorem nxt_replaceHead (a : City) (x : Journey City) : nxt (replaceHead a x) = nxt x := by
  cases x <;> rfl

/-- **tour-defn**: `outcost [a₀,…,aₙ]=tc (a₀,a₁)+⋯+tc (aₙ₋₁,aₙ)`. -/
@[expose] public def outcost (tc : City × City → Int) : Journey City → Int
  | ConsList.wrap p => tc p
  | ConsList.cons a x => tc (a, hd x) + outcost tc x

/-- **tour-defn**: `incost [a₀,…,aₙ]=tc (a₁,a₀)+⋯+tc (aₙ,aₙ₋₁)`. -/
@[expose] public def incost (tc : City × City → Int) : Journey City → Int
  | ConsList.wrap p => tc (p.2, p.1)
  | ConsList.cons a x => tc (hd x, a) + incost tc x

/-- **tour-defn**: `cost (xs,ys)=outcost xs+incost ys`. -/
@[expose] public def cost (tc : City × City → Int) (t : Tour City) : Int :=
  outcost tc t.1 + incost tc t.2

public theorem outcost_replaceHead (a : City) (x : Journey City) :
    outcost tc (replaceHead a x) = outcost tc x - tc (hd x, nxt x) + tc (a, nxt x) := by
  cases x with
  | wrap p => show tc (a, p.2) = tc (p.1, p.2) - tc (p.1, p.2) + tc (a, p.2); omega
  | cons b x =>
    show tc (a, hd x) + outcost tc x
      = tc (b, hd x) + outcost tc x - tc (b, hd x) + tc (a, hd x)
    omega

public theorem incost_replaceHead (a : City) (x : Journey City) :
    incost tc (replaceHead a x) = incost tc x - tc (nxt x, hd x) + tc (nxt x, a) := by
  cases x with
  | wrap p => show tc (p.2, a) = tc (p.2, p.1) - tc (p.2, p.1) + tc (p.2, a); omega
  | cons b x =>
    show tc (hd x, a) + incost tc x
      = tc (hd x, b) + incost tc x - tc (hd x, b) + tc (hd x, a)
    omega

/-- **tour-defn**: `dropl (a,([b]⧺xs,ys))=([a]⧺xs,[a]⧺ys)` — drop the head of the outward
    journey and start both from `a`. -/
@[expose] public def droplFn (a : City) (t : Tour City) : Tour City :=
  (replaceHead a t.1, ConsList.cons a t.2)

/-- **tour-defn**: `dropr (a,(xs,[b]⧺ys))=([a]⧺xs,[a]⧺ys)`. -/
@[expose] public def droprFn (a : City) (t : Tour City) : Tour City :=
  (ConsList.cons a t.1, replaceHead a t.2)

/-- **B&dM p.215**: `cost (dropl (a,(x,y))) = cost (x,y) + tc(a,next x) − tc(head x,next x)
    + tc(head y,a)` — the step reads both heads and the outward second city. -/
public theorem cost_dropl (a : City) (t : Tour City) :
    cost tc (droplFn a t)
      = cost tc t + tc (a, nxt t.1) - tc (hd t.1, nxt t.1) + tc (hd t.2, a) := by
  show outcost tc (replaceHead a t.1) + (tc (hd t.2, a) + incost tc t.2)
    = outcost tc t.1 + incost tc t.2 + tc (a, nxt t.1) - tc (hd t.1, nxt t.1) + tc (hd t.2, a)
  rw [outcost_replaceHead]
  omega

/-- **B&dM p.215**: `cost (dropr (a,(x,y))) = cost (x,y) + tc(a,head x) − tc(next y,head y)
    + tc(next y,a)`. -/
public theorem cost_dropr (a : City) (t : Tour City) :
    cost tc (droprFn a t)
      = cost tc t + tc (a, hd t.1) - tc (nxt t.2, hd t.2) + tc (nxt t.2, a) := by
  show tc (a, hd t.1) + outcost tc t.1 + incost tc (replaceHead a t.2)
    = outcost tc t.1 + incost tc t.2 + tc (a, hd t.1) - tc (nxt t.2, hd t.2) + tc (nxt t.2, a)
  rw [incost_replaceHead]
  omega

/-- **tour-defn**: `R ≜ cost ≤ cost°`. -/
@[expose] public def R (tc : City × City → Int) : dTour City ⟶ dTour City :=
  fun t t' => cost tc t ≤ cost tc t'

public theorem R_eq :
    R tc = graph (cost tc) ≫ leq ≫ (graph (cost tc) : dTour City ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro t t'
  constructor
  · intro h; exact ⟨cost tc t, rfl, cost tc t', h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    show cost tc t ≤ cost tc t'
    rw [← (show m = cost tc t from hm), ← (show n = cost tc t' from hn)]
    exact hmn

/-- **tour-defn**: `Q ≜ R ∩ (next2 next2°)` — the note's order, `next2 ≜ next×next`. -/
@[expose] public def Q (tc : City × City → Int) : dTour City ⟶ dTour City :=
  fun t t' => cost tc t ≤ cost tc t' ∧ nxt t.1 = nxt t'.1 ∧ nxt t.2 = nxt t'.2

/-- `Qc ≜ Q ∩ (head2 head2°)` — `Q` with the invariant the book appeals to on p.215 ("tours of
    the same input") written down: the two candidates start from the same city. -/
@[expose] public def Qc (tc : City × City → Int) : dTour City ⟶ dTour City :=
  fun t t' => cost tc t ≤ cost tc t' ∧ (nxt t.1 = nxt t'.1 ∧ nxt t.2 = nxt t'.2)
    ∧ (hd t.1 = hd t'.1 ∧ hd t.2 = hd t'.2)

public theorem Qc_le_Q : Qc tc ⊑ Q tc := le_iff.mpr fun _ _ h => ⟨h.1, h.2.1⟩

public theorem Qc_le_R : Qc tc ⊑ R tc := le_iff.mpr fun _ _ h => h.1

public theorem Qc_refl : 𝟙 (dTour City) ⊑ Qc tc :=
  le_iff.mpr fun t t' h => by
    obtain rfl : t = t' := h
    exact ⟨Int.le_refl _, ⟨rfl, rfl⟩, rfl, rfl⟩

public theorem Qc_trans : Qc tc ≫ Qc tc ⊑ Qc tc :=
  le_iff.mpr fun _ _ h => by
    obtain ⟨_, ⟨hc1, ⟨hn1, hn2⟩, hh1, hh2⟩, ⟨hc2, ⟨hn1', hn2'⟩, hh1', hh2'⟩⟩ := h
    exact ⟨Int.le_trans hc1 hc2, ⟨hn1.trans hn1', hn2.trans hn2'⟩,
      hh1.trans hh1', hh2.trans hh2'⟩

public theorem R_recip_trans : (R tc)° ≫ (R tc)° ⊑ (R tc)° :=
  le_iff.mpr fun t u h => by
    obtain ⟨s, h1, h2⟩ := h
    exact Int.le_trans (h2 : cost tc u ≤ cost tc s) (h1 : cost tc s ≤ cost tc t)

/-! ## The two algebras `[start,dropl]` and `[start,dropr]` -/

/-- **tour-defn**: `[start,dropl]` with `start (a,b)=([a,b],[a,b])`. -/
@[expose] public def droplAlgFn :
    (((F (City × City) City).obj (dTour City))).carrier → Tour City
  | Sum.inl p => (ConsList.wrap p, ConsList.wrap p)
  | Sum.inr q => droplFn q.1 q.2

/-- **tour-defn**: `[start,dropr]`. -/
@[expose] public def droprAlgFn :
    (((F (City × City) City).obj (dTour City))).carrier → Tour City
  | Sum.inl p => (ConsList.wrap p, ConsList.wrap p)
  | Sum.inr q => droprFn q.1 q.2

/-- **tour-defn**: `tour ≜ ⦇[start,dropl∪dropr]⦈`. -/
@[expose] public def tourAlg : (F (City × City) City).obj (dTour City) ⟶ dTour City :=
  graph (droplAlgFn (City := City)) ∪ graph droprAlgFn

@[expose] public def tour : dCL (City × City) City ⟶ dTour City := ⦇tourAlg⦈

/-! ## `tour-mono` -/

/-! The four refutations share one pair of GENUINE tours — each has its own two heads equal, as
  every partial tour does (B&dM p.214) — differing only in the head they share, which is what
  makes them tours of DIFFERENT inputs.  `tc (a,b) = a·b`, so a step out of `3` costs `3·head`. -/

/-- The tour `([1,0],[1,0])`, of cost `0`. -/
@[expose] public def tA : Tour Int :=
  (ConsList.wrap ((1 : Int), (0 : Int)), ConsList.wrap ((1 : Int), (0 : Int)))

/-- The tour `([0,0],[0,0])`, also of cost `0` and with the same two second cities. -/
@[expose] public def tB : Tour Int :=
  (ConsList.wrap ((0 : Int), (0 : Int)), ConsList.wrap ((0 : Int), (0 : Int)))

/-- `tA` and `tB` are `Q`-related: equal cost, equal `next2`.  They differ only in their shared
    head, which `Q` does not record. -/
public theorem tA_Q_tB : Q (fun p : Int × Int => p.1 * p.2) tA tB :=
  ⟨by decide, by decide, by decide⟩

/-- **tour-mono**, first row (marked FALSE in the note; B&dM p.215): `(𝟙×R) dropl ⊑ dropl R`
    fails.  `tA` and `tB` cost the same, but continuing either to city `3` costs `tc (head,3)`
    on the return, which is `3` from `tA` and `0` from `tB`. -/
public theorem tour_mono_dropl_false :
    ¬ MonotonicAlg (F := F (Int × Int) Int) (graph droplAlgFn)
        (R (fun p : Int × Int => p.1 * p.2)) := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droplAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB.1⟩, rfl⟩
  obtain ⟨s, hs, hR⟩ := hstep
  obtain rfl : s = droplAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : cost (fun p : Int × Int => p.1 * p.2) (droplAlgFn (Sum.inr ((3 : Int), tA)))
      ≤ cost (fun p : Int × Int => p.1 * p.2) (droplAlgFn (Sum.inr ((3 : Int), tB))) := hR
  revert hbad
  decide

/-- **THE FINDING**: `tour-mono`'s POSITIVE first row, `(𝟙×Q) dropl ⊑ dropl Q` at
    `Q ≜ R ∩ (next2 next2°)`, is false as printed — `tA` and `tB` are `Q`-related genuine tours,
    and `dropl` separates them.  What it reads and `Q` does not record is the HEAD
    (`+ tc(head y,a)`, B&dM p.215); the row holds once the heads are added, which is
    `tour_mono_dropl` below. -/
public theorem tour_mono_dropl_Q_false :
    ¬ MonotonicAlg (F := F (Int × Int) Int) (graph droplAlgFn)
        (Q (fun p : Int × Int => p.1 * p.2)) := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droplAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB⟩, rfl⟩
  obtain ⟨s, hs, hQ⟩ := hstep
  obtain rfl : s = droplAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : Q (fun p : Int × Int => p.1 * p.2) (droplAlgFn (Sum.inr ((3 : Int), tA)))
      (droplAlgFn (Sum.inr ((3 : Int), tB))) := hQ
  have hbadc := hbad.1
  revert hbadc
  decide

/-- **tour-mono**, second row (marked FALSE in the note): `(𝟙×R) dropr ⊑ dropr R` fails on the
    same two tours — `dropr` reads the head through `+ tc(a,head x)`. -/
public theorem tour_mono_dropr_false :
    ¬ MonotonicAlg (F := F (Int × Int) Int) (graph droprAlgFn)
        (R (fun p : Int × Int => p.1 * p.2)) := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droprAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB.1⟩, rfl⟩
  obtain ⟨s, hs, hR⟩ := hstep
  obtain rfl : s = droprAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : cost (fun p : Int × Int => p.1 * p.2) (droprAlgFn (Sum.inr ((3 : Int), tA)))
      ≤ cost (fun p : Int × Int => p.1 * p.2) (droprAlgFn (Sum.inr ((3 : Int), tB))) := hR
  revert hbad
  decide

/-- **THE FINDING**, mirror: `tour-mono`'s POSITIVE second row `(𝟙×Q) dropr ⊑ dropr Q` is false
    as printed too, on the same two genuine tours. -/
public theorem tour_mono_dropr_Q_false :
    ¬ MonotonicAlg (F := F (Int × Int) Int) (graph droprAlgFn)
        (Q (fun p : Int × Int => p.1 * p.2)) := by
  intro h
  have hstep := le_iff.mp h (Sum.inr ((3 : Int), tA)) (droprAlgFn (Sum.inr ((3 : Int), tB)))
    ⟨Sum.inr ((3 : Int), tB), ⟨rfl, tA_Q_tB⟩, rfl⟩
  obtain ⟨s, hs, hQ⟩ := hstep
  obtain rfl : s = droprAlgFn (Sum.inr ((3 : Int), tA)) := hs
  have hbad : Q (fun p : Int × Int => p.1 * p.2) (droprAlgFn (Sum.inr ((3 : Int), tA)))
      (droprAlgFn (Sum.inr ((3 : Int), tB))) := hQ
  have hbadc := hbad.1
  revert hbadc
  decide


/-- **tour-mono**, first row at `Qc`: `(𝟙×Qc) dropl ⊑ dropl Qc`.  Both deltas of `cost_dropl`
    are then the same number, and the result's own heads (`a`, `a`) and second cities
    (`next x`, `head y`) are fixed by `Qc`. -/
public theorem tour_mono_dropl : MonotonicAlg (F := F (City × City) City) (graph droplAlgFn)
    (Qc tc) :=
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
        have hcost : cost tc t ≤ cost tc t' := hQ.1
        have hn1 : nxt t.1 = nxt t'.1 := hQ.2.1.1
        have hn2 : nxt t.2 = nxt t'.2 := hQ.2.1.2
        have hh1 : hd t.1 = hd t'.1 := hQ.2.2.1
        have hh2 : hd t.2 = hd t'.2 := hQ.2.2.2
        refine ⟨droplFn a t, rfl, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
        · show cost tc (droplFn a t) ≤ cost tc (droplFn a t')
          rw [cost_dropl, cost_dropl, hn1, hh1, hh2]
          omega
        · show nxt (replaceHead a t.1) = nxt (replaceHead a t'.1)
          rw [nxt_replaceHead, nxt_replaceHead]; exact hn1
        · show hd t.2 = hd t'.2
          exact hh2
        · show hd (replaceHead a t.1) = hd (replaceHead a t'.1)
          rw [hd_replaceHead, hd_replaceHead]
        · rfl

/-- **tour-mono**, second row at `Qc`: `(𝟙×Qc) dropr ⊑ dropr Qc`. -/
public theorem tour_mono_dropr : MonotonicAlg (F := F (City × City) City) (graph droprAlgFn)
    (Qc tc) :=
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
        have hcost : cost tc t ≤ cost tc t' := hQ.1
        have hn1 : nxt t.1 = nxt t'.1 := hQ.2.1.1
        have hn2 : nxt t.2 = nxt t'.2 := hQ.2.1.2
        have hh1 : hd t.1 = hd t'.1 := hQ.2.2.1
        have hh2 : hd t.2 = hd t'.2 := hQ.2.2.2
        refine ⟨droprFn a t, rfl, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
        · show cost tc (droprFn a t) ≤ cost tc (droprFn a t')
          rw [cost_dropr, cost_dropr, hn2, hh1, hh2]
          omega
        · show hd t.1 = hd t'.1
          exact hh1
        · show nxt (replaceHead a t.2) = nxt (replaceHead a t'.2)
          rw [nxt_replaceHead, nxt_replaceHead]; exact hn2
        · rfl
        · show hd (replaceHead a t.2) = hd (replaceHead a t'.2)
          rw [hd_replaceHead, hd_replaceHead]

/-- **tour-defn**, `P ≜ ⊤`. -/
public theorem tour_sort_dropl :
    MonotonicAlg (F := F (City × City) City) (graph (droplAlgFn (City := City)))
      (topMor (dTour City) (dTour City)) :=
  graph_monotonicAlg_topMor _

public theorem tour_sort_dropr :
    MonotonicAlg (F := F (City × City) City) (graph (droprAlgFn (City := City)))
      (topMor (dTour City) (dTour City)) :=
  graph_monotonicAlg_topMor _

/-! ## `tour-laws` -/

/-- **tour-laws** (B&dM §8.6, p.215): a least-cost bitonic tour as a fold that thins the tours
    kept at each city —
    `Λ(tour) est(R) ⊒ ⦇listcp(F) ⟨g₁,g₂⟩ merge ⊤ thinlist Qc⦈ minlist R`.
    Theorem 8.2 (`thinningList`) at `f₁ ≜ [start,dropl]`, `f₂ ≜ [start,dropr]`,
    `p₁ = p₂ ≜ 𝟙`, `P ≜ ⊤`.  The thinning order is `Qc`, NOT the note's `Q`: see
    `tour_mono_dropl_Q_false`. -/
public theorem tour_laws {l lF : RelSet.{0}}
    {sortP : PowerAllegory.powerObj (dTour City) ⟶ l}
    {sortF : ((F (City × City) City).obj (dTour City) ⟶ (F (City × City) City).obj (dTour City)) →
      (PowerAllegory.powerObj ((F (City × City) City).obj (dTour City)) ⟶ lF)}
    {listcp : (F (City × City) City).obj l ⟶ lF} {listf₁ listf₂ : lF ⟶ l}
    {thinlist : l ⟶ l} {minlist : l ⟶ dTour City} {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj (dTour City)) (PowerAllegory.powerObj (dTour City))}
    {mergeP : Pr.p ⟶ l}
    (hsortF : ∀ {X Y : (F (City × City) City).obj (dTour City)
        ⟶ (F (City × City) City).obj (dTour City)}, X ⊑ Y → sortF X ⊑ sortF Y)
    (h88₁ : sortF (graph droplAlgFn ≫ topMor (dTour City) (dTour City) ≫ (graph droplAlgFn)°)
      ≫ listf₁ ⊑ powerRel (graph (droplAlgFn (City := City))) ≫ sortP)
    (h88₂ : sortF (graph droprAlgFn ≫ topMor (dTour City) (dTour City) ≫ (graph droprAlgFn)°)
      ≫ listf₂ ⊑ powerRel (graph (droprAlgFn (City := City))) ≫ sortP)
    (h811 : (F (City × City) City).map sortP ≫ listcp
      ⊑ cpMap (F (City × City) City) (dTour City)
        ≫ sortF ((F (City × City) City).map (topMor (dTour City) (dTour City))))
    (h810 : prodMap Pr' Pr sortP sortP ≫ mergeP ⊑ cup Pr' ≫ sortP)
    (h86 : sortP ≫ thinlist ⊑ thinRel (Qc tc) ≫ sortP)
    (h87 : sortP ≫ minlist ⊑ est (R tc)) :
    ⦇listcp ≫ Pr.pair (listf₁ ≫ 𝟙 l) (listf₂ ≫ 𝟙 l) ≫ mergeP ≫ thinlist⦈ ≫ minlist
      ⊑ Λ (tour (City := City)) ≫ est (R tc) := by
  have hm₁ : MonotonicAlg (F := F (City × City) City)
      (graph (droplAlgFn (City := City)) ≫ 𝟙 (dTour City)) (Qc tc) := by
    rw [Cat.comp_id]; exact tour_mono_dropl
  have hm₂ : MonotonicAlg (F := F (City × City) City)
      (graph (droprAlgFn (City := City)) ≫ 𝟙 (dTour City)) (Qc tc) := by
    rw [Cat.comp_id]; exact tour_mono_dropr
  have h89 : sortP ≫ 𝟙 l ⊑ existsImage (𝟙 (dTour City)) ≫ sortP := by
    rw [Cat.comp_id, existsImage_id, Cat.id_comp]
    exact le_refl _
  have key := thinningList (F := F (City × City) City)
    (F_preservesRecip (City × City) City) (initial (City × City) City)
    (f₁ := graph droplAlgFn) (f₂ := graph droprAlgFn)
    (p₁ := 𝟙 (dTour City)) (p₂ := 𝟙 (dTour City))
    (P := topMor (dTour City) (dTour City)) (Q := Qc tc) (R := R tc)
    (graph_map droplAlgFn) (graph_map droprAlgFn) Qc_le_R Qc_refl Qc_trans R_recip_trans
    hm₁ hm₂ hsortF tour_sort_dropl tour_sort_dropr h88₁ h88₂ h89 h89 h811 h810 h86 h87
  rw [Cat.comp_id (graph (droplAlgFn (City := City))),
    Cat.comp_id (graph (droprAlgFn (City := City)))] at key
  exact key

end Freyd.Alg.RelSet.Tour
