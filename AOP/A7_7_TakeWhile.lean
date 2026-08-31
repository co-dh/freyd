/-
  `takeWhile` derived by SHRINK — a port of AoPA `Examples/GC/TakeWhile.agda`
  (Mu–Oliveira, "Programming from Galois connections").

  SPEC (program-independent).  For a predicate `p`, a valid answer to `takeWhile p` on a list `l`
  is any prefix of `l` all of whose elements satisfy `p`:
      `twSpec l out  :=  out ≼ l  ∧  every element of out satisfies p`.
  The wanted answer is the LONGEST such prefix.  In AoPA this is `(mapR (p¿) ○ _≼_) ↾ _≽_`:
  the relation "a `p`-satisfying prefix" (`mapR (p¿) ○ _≼_`) shrunk by the prefix order `_≽_`
  so that only the longest survives.

  HEADLINE (this repo).  The longest-prefix requirement is exactly Bird & de Moor's `max`, and the
  AoPA shrink `S ↾ R` is `Λ S ≫ est R` (`A7_6.shrink_eq_Λ_comp_est`).  So the derivation's
  headline is the morphism equation
      `graph (twCL p)  =  Λ twSpec ≫ est prefDom`                    (`takeWhile_eq_Λ_est`)
  where `prefDom w z := z ≼ w` (dominance = "w is at least as long"), and equivalently the shrink
  form
      `graph (twCL p)  =  twSpec ↾ prefSub`                             (`takeWhile_eq_shrink`)
  with `prefSub = prefDom°` the sub-prefix order (`w ≼ z`) — AoPA's `spec ↾ ≽`, up to the
  min/max and argument-order conventions.  Both come out of `RelSet.eq_Λ_comp_est` (the two
  halves it consumes — achievability and prefix-domination — are proved here directly).

  PROGRAM EMERGENCE.  `twCL p` is not hand-written and then verified: it is PRODUCED as the
  catamorphism of its base/step by the cons-list fold-uniqueness law (`CL.consFold_unique`),
  mirroring AoPA's `foldR-fold`/`greedy-cata` step:
      `graph (twCL p)  =  cataR (consScalarAlg (fun _ => []) (twStep p))`   (`takeWhile_emerges`).

  BOOK ROUTE (the second half of this file).  The same problem derived B&dM's own way
  (Ex 7.39, the note's `sec-takewhile`): the GREEDY THEOREM 7.2 (`AOP.A7_2.greedy`) applied to
  the spec `takewhile p = Λ(prefix list(p)) est(R°)` with `R = length ≤ length°`, closing the
  greedy `⊒` into `=` by `eq_of_le_entire_simple` (program entire, spec simple).  Both routes
  produce the same algebra `[nil,(π₁p→cons,⊸ nil)]` = `consScalarAlg (fun _ => []) (twStep p)`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
module

public import AOP.A7_6_Shrink
public import AOP.A7_4_Horner
public import AOP.A7_2
public import AOP.A6_ConsList
public import AOP.A6_GenFold

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.GCTakeWhile

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL

variable {E : Type}

/-! ## Supporting list facts (AoPA `Examples/GC/List.agda`, `Nat.agda`) -/

/-- The underlying list of a `ConsList Unit E` (AoPA's `μ ListF` unfolded). -/
def flat : ConsList Unit E → List E
  | ConsList.wrap _   => []
  | ConsList.cons x xs => x :: flat xs

/-- `AllP p l` — every element of `l` satisfies `p` (AoPA `mapR (p ¿)` restricted to the
    diagonal). -/
def AllP (p : E → Bool) : List E → Prop
  | []      => True
  | x :: xs => p x = true ∧ AllP p xs

/-- The prefix relation `u ≼ w` (AoPA `_≼_ = foldR ListF [ nil , (nil ○ !) ⊔ cons ]`):
    `[] ≼ w` always, and `x∷u ≼ x∷w` iff `u ≼ w`. -/
def Pre : List E → List E → Prop
  | []      , _       => True
  | _ :: _  , []      => False
  | x :: xs , y :: ys => x = y ∧ Pre xs ys

/-- Prefix antisymmetry (AoPA: `_≼_` is a partial order; underlies `≼-isPreorder` + antisymmetry
    used for the shrink's uniqueness). -/
theorem pre_antisym : ∀ {a b : List E}, Pre a b → Pre b a → a = b
  | []      , []      , _  , _  => rfl
  | []      , _ :: _  , _  , hb => (hb).elim
  | _ :: _  , []      , ha , _  => (ha).elim
  | x :: xs , y :: ys , ha , hb => by
      have hxy : x = y := ha.1
      have := pre_antisym ha.2 hb.2      -- xs = ys
      rw [hxy, this]

/-! ## The program `twCL` and its base/step -/

/-- The step of `takeWhile`: keep the head iff it satisfies `p`, else stop. -/
public def twStep (p : E → Bool) (x : E) (c : List E) : List E :=
  match p x with
  | true  => x :: c
  | false => []

/-- `takeWhile p` on `ConsList Unit E`.  Defined by the very recursion whose base/step is
    `(fun _ => [])` / `twStep p`, so `CL.consFold_unique` produces it as a catamorphism. -/
def twCL (p : E → Bool) : ConsList Unit E → List E
  | ConsList.wrap _    => []
  | ConsList.cons x xs => twStep p x (twCL p xs)

/-! ## The spec (program-independent) -/

/-- `twSpec p c out`: `out` is a `p`-satisfying prefix of the list `flat c`. -/
def twSpec (p : E → Bool) : dCL Unit E ⟶ (⟨List E⟩ : RelSet.{0}) :=
  fun c out => Pre out (flat c) ∧ AllP p out

/-- Dominance order on answers: `w` dominates `z` when `z ≼ w` (`w` is at least as long).
    `est prefDom` selects the LONGEST prefix. -/
def prefDom : (⟨List E⟩ : RelSet.{0}) ⟶ ⟨List E⟩ := fun w z => Pre z w

/-! ## Program emergence (AoPA `foldR-fold`) -/

/-- **The program is produced by the fold law.**  `twCL p` obeys the cons-list recursion of its
    base/step, so it IS the catamorphism of `consScalarAlg (fun _ => []) (twStep p)`. -/
theorem takeWhile_emerges (p : E → Bool) :
    (graph (twCL p) : dCL Unit E ⟶ ⟨List E⟩)
      = cataR (consScalarAlg (fun _ : Unit => ([] : List E)) (twStep p)) :=
  consFold_unique (fun _ => []) (twStep p) (twCL p) (fun _ => rfl) (fun _ _ => rfl)

/-! ## The two halves the headline consumes -/

/-- Achievability: `twCL p c` is itself a `p`-satisfying prefix of `flat c`. -/
theorem tw_sound (p : E → Bool) (c : ConsList Unit E) : twSpec p c (twCL p c) := by
  induction c with
  | wrap u => exact ⟨trivial, trivial⟩
  | cons x xs ih =>
      show Pre (twStep p x (twCL p xs)) (x :: flat xs) ∧ AllP p (twStep p x (twCL p xs))
      unfold twStep
      cases hpx : p x with
      | false => exact ⟨trivial, trivial⟩
      | true  => exact ⟨⟨rfl, ih.1⟩, ⟨hpx, ih.2⟩⟩

/-- Domination: every `p`-satisfying prefix `out` of `flat c` is a prefix of `twCL p c`
    (so `twCL p c` is the longest). -/
theorem tw_best (p : E → Bool) (c : ConsList Unit E) (out : List E)
    (h : twSpec p c out) : Pre out (twCL p c) := by
  induction c generalizing out with
  | wrap u =>
      -- flat (wrap u) = []; a prefix of [] is [], and twCL = []
      cases out with
      | nil => exact trivial
      | cons y ys => exact (h.1).elim
  | cons x xs ih =>
      cases out with
      | nil => exact trivial
      | cons y ys =>
          -- h.1 : Pre (y::ys) (x :: flat xs) = (y = x) ∧ Pre ys (flat xs)
          -- h.2 : AllP p (y::ys) = (p y = true) ∧ AllP p ys
          have hyx : y = x := h.1.1
          have hpre : Pre ys (flat xs) := h.1.2
          have hpy : p y = true := h.2.1
          have htail : AllP p ys := h.2.2
          show Pre (y :: ys) (twStep p x (twCL p xs))
          unfold twStep
          have hpx : p x = true := by rw [← hyx]; exact hpy
          rw [hpx]
          exact ⟨hyx, ih ys ⟨hpre, htail⟩⟩

/-! ## Headlines -/

/-- **Morphism-equation headline (max form).**  `graph (twCL p) = Λ twSpec ≫ est prefDom` —
    `takeWhile p` is exactly `max prefDom · Λ twSpec`, the longest `p`-satisfying prefix, as a
    relation (not merely pointwise).  Via `RelSet.eq_Λ_comp_est`, fed the two halves above and
    prefix antisymmetry. -/
theorem takeWhile_eq_Λ_est (p : E → Bool) :
    (graph (twCL p) : dCL Unit E ⟶ ⟨List E⟩) = Λ (twSpec p) ≫ est (prefDom (E := E)) :=
  eq_Λ_comp_est (prefDom (E := E))
    (fun x y h1 h2 => pre_antisym h2 h1)               -- antisymmetry of prefDom
    (twCL p) (twSpec p)
    (tw_sound p)                                        -- achievability
    (fun c v hv => tw_best p c v hv)                    -- domination (longest)

/-- **Shrink-form headline (AoPA `spec ↾ ≽`).**  `graph (twCL p) = twSpec ↾ prefDom°`.  This is
    the AoPA shrink presentation: the `p`-satisfying-prefix relation, shrunk by the prefix order,
    equals `takeWhile`.  Immediate from the max form by `shrink_eq_Λ_comp_est`
    (`est R = est R°`). -/
theorem takeWhile_eq_shrink (p : E → Bool) :
    (graph (twCL p) : dCL Unit E ⟶ ⟨List E⟩) = twSpec p ↾ (prefDom (E := E))° := by
  rw [shrink_eq_Λ_comp_est]
  exact takeWhile_eq_Λ_est p

/-! ## Executable sanity checks -/

/-- `takeWhile (· < 3) [1,2,5,1] = [1,2]`. -/
example : twCL (fun n => decide (n < 3)) (ofList [1, 2, 5, 1]) = [1, 2] := by decide
/-- Everything satisfies `p` ⇒ the whole list. -/
example : twCL (fun n => decide (n < 9)) (ofList [1, 2, 5]) = [1, 2, 5] := by decide
/-- Head fails ⇒ empty. -/
example : twCL (fun n => decide (n < 1)) (ofList [1, 2]) = [] := by decide

/-! ## The BOOK route (Ex 7.39, note `sec-takewhile`): the greedy theorem on the book spec

  Note-name ↦ Lean-name: `p` (a coreflexive) ↦ `pcor p`, `R ≜ length ≤ length°` ↦ `lenLE`,
  `prefix` ↦ `prefixR` (a Lean keyword forces the suffix), `list(p)` ↦ `listP p`, `S` ↦ `Salg p`,
  `takewhile(p)` ↦ `takewhile p`; the program algebra `[nil,(π₁p→cons,⊸ nil)]` is the AoPA
  route's `consScalarAlg (fun _ => []) (twStep p)`, shared verbatim. -/

/-- The note's coreflexive `p : A⟶A` — the partial identity on the `p`-passers. -/
@[expose] public def pcor (p : E → Bool) : dE E ⟶ dE E := fun x y => x = y ∧ p x = true

/-- The note's `R ≜ length ≤ length°`, the length preorder: `xs lenLE ys ⟺ |xs| ≤ |ys|`. -/
@[expose] public def lenLE : (⟨List E⟩ : RelSet.{0}) ⟶ ⟨List E⟩ :=
  fun xs ys => xs.length ≤ ys.length

/-- `R°` is transitive — the greedy theorem's preorder hypothesis, at `R ≜ length ≤ length°`. -/
public theorem lenLE_recip_trans : (lenLE (E := E))° ≫ lenLE° ⊑ lenLE° :=
  le_iff.mpr fun xs zs h => by
    obtain ⟨ys, h1, h2⟩ := h
    exact Nat.le_trans h2 h1

/-- `prefix`'s algebra `[nil, ⊸ nil ∪ cons]`, on the carrier `[A]` itself. -/
@[expose] public def prefAlg : Fobj Unit E (dCL Unit E) ⟶ dCL Unit E :=
  junc (sumCop (dL Unit) ⟨E × ConsList Unit E⟩) wrapR
    ((graph fun _ => ConsList.wrap ()) ∪ consR)

/-- `prefix ≜ ⦇[nil, ⊸ nil ∪ cons]⦈` — at each `cons`, stop or keep the head. -/
@[expose] public def prefixR : dCL Unit E ⟶ dCL Unit E := cataR prefAlg

/-- `(p×𝟙) cons : A×[A] ⟶ [A]` — keep a head that passes `p` onto the folded tail. -/
@[expose] public def pcons (p : E → Bool) :
    (⟨E × List E⟩ : RelSet.{0}) ⟶ (⟨List E⟩ : RelSet.{0}) :=
  rprodMap (pcor p) (Cat.id (⟨List E⟩ : RelSet.{0})) ≫ graph fun q => q.1 :: q.2

/-- `list(p)`'s algebra `[nil, (p×𝟙) cons]`, carried to the raw-list carrier. -/
@[expose] public def listPAlg (p : E → Bool) :
    Fobj Unit E (⟨List E⟩ : RelSet.{0}) ⟶ ⟨List E⟩ :=
  junc (sumCop (dL Unit) ⟨E × List E⟩) (graph fun _ => []) (pcons p)

/-- `list(p) ≜ ⦇[nil, (p×𝟙) cons]⦈` — the coreflexive "every element passes `p`" (not entire). -/
@[expose] public def listP (p : E → Bool) : dCL Unit E ⟶ (⟨List E⟩ : RelSet.{0}) :=
  cataR (listPAlg p)

/-- The note's `S ≜ [nil, ⊸ nil ∪ (p×𝟙) cons]` — `prefix`'s algebra with one extra `p`. -/
@[expose] public def Salg (p : E → Bool) :
    Fobj Unit E (⟨List E⟩ : RelSet.{0}) ⟶ ⟨List E⟩ :=
  junc (sumCop (dL Unit) ⟨E × List E⟩) (graph fun _ => [])
    ((graph fun _ => []) ∪ pcons p)

/-- Ex 7.39's specification: `takewhile(p) ≜ Λ(prefix list(p)) est(R°)` — the longest prefix
    all of whose elements pass `p`. -/
@[expose] public def takewhile (p : E → Bool) : dCL Unit E ⟶ (⟨List E⟩ : RelSet.{0}) :=
  (prefixR ≫ listP p)%∋ ≫ est(lenLE°)

/-! ### Pointwise unfolds of the three `junc` algebras -/

theorem junc_inl {a b c : RelSet.{0}} (T : a ⟶ c) (U : b ⟶ c) (x : a.carrier) (z : c.carrier) :
    junc (sumCop a b) T U (Sum.inl x) z ↔ T x z := by
  constructor
  · rintro (⟨x', hx', hT⟩ | ⟨y', hy', -⟩)
    · cases Sum.inl.inj hx'; exact hT
    · nomatch hy'
  · intro h
    exact Or.inl ⟨x, rfl, h⟩

theorem junc_inr {a b c : RelSet.{0}} (T : a ⟶ c) (U : b ⟶ c) (y : b.carrier) (z : c.carrier) :
    junc (sumCop a b) T U (Sum.inr y) z ↔ U y z := by
  constructor
  · rintro (⟨x', hx', -⟩ | ⟨y', hy', hU⟩)
    · nomatch hx'
    · cases Sum.inr.inj hy'; exact hU
  · intro h
    exact Or.inr ⟨y, rfl, h⟩

public theorem pcons_apply (p : E → Bool) (x : E) (c ws : List E) :
    pcons p (x, c) ws ↔ p x = true ∧ ws = x :: c := by
  constructor
  · rintro ⟨q, ⟨⟨hx, hp⟩, hc⟩, hw⟩
    obtain ⟨qx, qc⟩ := q
    have hx' : x = qx := hx
    have hc' : c = qc := hc
    subst hx'
    subst hc'
    exact ⟨hp, hw⟩
  · rintro ⟨hp, hw⟩
    exact ⟨(x, c), ⟨⟨rfl, hp⟩, rfl⟩, hw⟩

theorem prefAlg_inl (d : Unit) (ys : ConsList Unit E) :
    prefAlg (Sum.inl d) ys ↔ ys = ConsList.wrap () := by
  unfold prefAlg; exact junc_inl _ _ _ _

theorem prefAlg_inr (x : E) (r ys : ConsList Unit E) :
    prefAlg (Sum.inr (x, r)) ys ↔ ys = ConsList.wrap () ∨ ys = ConsList.cons x r := by
  unfold prefAlg; exact junc_inr _ _ _ _

public theorem listPAlg_inl (p : E → Bool) (d : Unit) (ws : List E) :
    listPAlg p (Sum.inl d) ws ↔ ws = [] := by
  unfold listPAlg; exact junc_inl _ _ _ _

public theorem listPAlg_inr (p : E → Bool) (x : E) (c ws : List E) :
    listPAlg p (Sum.inr (x, c)) ws ↔ p x = true ∧ ws = x :: c := by
  unfold listPAlg; exact (junc_inr _ _ _ _).trans (pcons_apply p x c ws)

theorem Salg_inl (p : E → Bool) (d : Unit) (ws : List E) :
    Salg p (Sum.inl d) ws ↔ ws = [] := by
  unfold Salg; exact junc_inl _ _ _ _

theorem Salg_inr (p : E → Bool) (x : E) (c ws : List E) :
    Salg p (Sum.inr (x, c)) ws ↔ ws = [] ∨ (p x = true ∧ ws = x :: c) := by
  unfold Salg
  refine (junc_inr _ _ _ _).trans ?_
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((pcons_apply p x c ws).mp h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((pcons_apply p x c ws).mpr h)

/-! ### Supporting facts: `nil` prefixes everything, prefixes of equal length agree -/

/-- `nil` is a prefix of every list — the entire half of `prefix`. -/
theorem prefix_wrap : ∀ xs : ConsList Unit E, prefixR xs (ConsList.wrap ())
  | ConsList.wrap _ => (prefAlg_inl _ _).mpr rfl
  | ConsList.cons _ t =>
      ⟨ConsList.wrap (), prefix_wrap t, (prefAlg_inr _ _ _).mpr (Or.inl rfl)⟩

/-- Two prefixes of one list of equal length are equal. -/
theorem pre_eq_of_length : ∀ {a b v : List E}, Pre a v → Pre b v → a.length = b.length → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hlen => absurd hlen.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, hlen => absurd hlen (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, [], ha, _, _ => ha.elim
  | x :: xs, y :: ys, _ :: zs, ha, hb, hlen => by
      obtain ⟨hxz, hpa⟩ := ha
      obtain ⟨hyz, hpb⟩ := hb
      rw [hxz, hyz, pre_eq_of_length hpa hpb (Nat.succ.inj hlen)]

/-- The two routes' specifications agree pointwise: `xs (prefix list(p)) ws` iff `ws` is a
    `p`-passing prefix of the list `xs` carries. -/
theorem spec_iff (p : E → Bool) (u : ConsList Unit E) (ws : List E) :
    (prefixR ≫ listP p) u ws ↔ Pre ws (flat u) ∧ AllP p ws := by
  induction u generalizing ws with
  | wrap d =>
      constructor
      · rintro ⟨ys, hpre, hlp⟩
        have hys : ys = ConsList.wrap () := (prefAlg_inl d ys).mp hpre
        subst hys
        have hws : ws = [] := (listPAlg_inl p () ws).mp hlp
        subst hws
        exact ⟨trivial, trivial⟩
      · rintro ⟨hpre, -⟩
        cases ws with
        | nil =>
            exact ⟨ConsList.wrap (), (prefAlg_inl d _).mpr rfl, (listPAlg_inl p () _).mpr rfl⟩
        | cons y ys => exact hpre.elim
  | cons x t ih =>
      constructor
      · rintro ⟨ys, hpre, hlp⟩
        obtain ⟨r', hr', hstep⟩ := hpre
        rcases (prefAlg_inr x r' ys).mp hstep with hwrap | hcons
        · subst hwrap
          have hws : ws = [] := (listPAlg_inl p () ws).mp hlp
          subst hws
          exact ⟨trivial, trivial⟩
        · subst hcons
          obtain ⟨w', hw', hstep2⟩ := hlp
          obtain ⟨hp, hws⟩ := (listPAlg_inr p x w' ws).mp hstep2
          subst hws
          obtain ⟨hPre, hAll⟩ := (ih w').mp ⟨r', hr', hw'⟩
          exact ⟨⟨rfl, hPre⟩, hp, hAll⟩
      · rintro ⟨hpre, hall⟩
        cases ws with
        | nil => exact ⟨ConsList.wrap (), prefix_wrap _, (listPAlg_inl p () _).mpr rfl⟩
        | cons y ws' =>
            obtain ⟨hyx, hpre'⟩ := hpre
            obtain ⟨hpy, hall'⟩ := hall
            obtain ⟨ys', hys', hlp'⟩ := (ih ws').mpr ⟨hpre', hall'⟩
            refine ⟨ConsList.cons x ys', ⟨ys', hys', (prefAlg_inr x ys' _).mpr (Or.inr rfl)⟩,
              ws', hlp', (listPAlg_inr p x ws' _).mpr ⟨?_, ?_⟩⟩
            · rw [← hyx]; exact hpy
            · rw [hyx]

/-! ### The chain, one theorem per row of the note's `takewhile-laws` table -/

/-- The `takewhile-alg` display's headline: `α prefix list(p) = F(prefix list(p)) S` — building
    the list and then keeping a `p`-passing prefix of it is keeping one of the tail first, and
    then building with `S`.  (Fusion cannot derive this — `list(p)` is not entire and no algebra
    meets the side condition — so it is proved pointwise and fed to @cata-defining below.) -/
public theorem takewhile_alg_comm (p : E → Bool) :
    (initial Unit E).α ≫ (prefixR ≫ listP p)
      = (F Unit E).map (prefixR ≫ listP p) ≫ Salg p := by
  apply hom_ext; intro u ws
  constructor
  · rintro ⟨m, hm, hX⟩
    have hm' : m = con u := hm
    subst hm'
    cases u with
    | inl d =>
        obtain ⟨ys, hpre, hlp⟩ := hX
        have hys : ys = ConsList.wrap () := (prefAlg_inl d ys).mp hpre
        subst hys
        exact ⟨Sum.inl d, rfl, (Salg_inl p d ws).mpr ((listPAlg_inl p () ws).mp hlp)⟩
    | inr q =>
        obtain ⟨x, t⟩ := q
        obtain ⟨ys, hpre, hlp⟩ := hX
        obtain ⟨r', hr', hstep⟩ := hpre
        rcases (prefAlg_inr x r' ys).mp hstep with hwrap | hcons
        · subst hwrap
          have hws : ws = [] := (listPAlg_inl p () ws).mp hlp
          exact ⟨Sum.inr (x, []), ⟨rfl, ConsList.wrap (), prefix_wrap t,
            (listPAlg_inl p () _).mpr rfl⟩, (Salg_inr p x [] ws).mpr (Or.inl hws)⟩
        · subst hcons
          obtain ⟨w', hw', hstep2⟩ := hlp
          obtain ⟨hp, hws⟩ := (listPAlg_inr p x w' ws).mp hstep2
          exact ⟨Sum.inr (x, w'), ⟨rfl, r', hr', hw'⟩,
            (Salg_inr p x w' ws).mpr (Or.inr ⟨hp, hws⟩)⟩
  · rintro ⟨v, hv, hS⟩
    cases u with
    | inl d =>
        cases v with
        | inl d' =>
            exact ⟨ConsList.wrap d, rfl, ConsList.wrap (), (prefAlg_inl d _).mpr rfl,
              (listPAlg_inl p () _).mpr ((Salg_inl p d' ws).mp hS)⟩
        | inr q => exact hv.elim
    | inr q =>
        obtain ⟨x, t⟩ := q
        cases v with
        | inl d' => exact hv.elim
        | inr q' =>
            obtain ⟨x', w'⟩ := q'
            obtain ⟨hx, hXw⟩ := hv
            cases hx
            rcases (Salg_inr p x w' ws).mp hS with hws | ⟨hp, hws⟩
            · subst hws
              exact ⟨ConsList.cons x t, rfl, ConsList.wrap (), prefix_wrap _,
                (listPAlg_inl p () _).mpr rfl⟩
            · subst hws
              obtain ⟨ys', hys', hlp'⟩ := hXw
              exact ⟨ConsList.cons x t, rfl, ConsList.cons x ys',
                ⟨ys', hys', (prefAlg_inr x ys' _).mpr (Or.inr rfl)⟩,
                w', hlp', (listPAlg_inr p x w' _).mpr ⟨hp, rfl⟩⟩

/-- The `takewhile-alg` row: `prefix list(p) = ⦇S⦈`, read off the defining equation above by
    @cata-defining (the Eilenberg–Wright universal property). -/
public theorem takewhile_alg (p : E → Bool) : prefixR ≫ listP p = cataR (Salg p) := by
  rw [cataR_eq_relCata]
  exact (relCata_UP (initial Unit E) (Salg p) (prefixR ≫ listP p)).mp (takewhile_alg_comm p)

/-- The `takewhile-mono` row: `F(R°) S ⊑ S R°` — shortening the tail and then taking the step
    lands inside taking the step and then shortening the result. -/
public theorem takewhile_mono (p : E → Bool) :
    MonotonicAlg (F := F Unit E) (Salg p) lenLE° := by
  show (F Unit E).map lenLE° ≫ Salg p ⊑ Salg p ≫ lenLE°
  apply le_iff.mpr
  intro u ws h
  obtain ⟨v, hv, hS⟩ := h
  cases u with
  | inl d =>
      cases v with
      | inl d' =>
          have hws : ws = [] := (Salg_inl p d' ws).mp hS
          subst hws
          exact ⟨[], (Salg_inl p d []).mpr rfl, Nat.le_refl 0⟩
      | inr q => exact hv.elim
  | inr q =>
      obtain ⟨x, c⟩ := q
      cases v with
      | inl d' => exact hv.elim
      | inr q' =>
          obtain ⟨x', c'⟩ := q'
          obtain ⟨hx, hlen⟩ := hv
          cases hx
          rcases (Salg_inr p x c' ws).mp hS with hws | ⟨hp, hws⟩
          · subst hws
            exact ⟨[], (Salg_inr p x c []).mpr (Or.inl rfl), Nat.le_refl 0⟩
          · subst hws
            exact ⟨x :: c, (Salg_inr p x c (x :: c)).mpr (Or.inr ⟨hp, rfl⟩),
              Nat.succ_le_succ hlen⟩

/-- The greedy row: `⦇Λ(S) est(R°)⦈ ⊑ Λ(⦇S⦈) est(R°)` — Theorem 7.2 at the preorder `R°`,
    with `takewhile-mono` for its hypothesis: one longest `p`-prefix kept at each `cons`
    refines every `p`-prefix collected and one chosen at the end. -/
public theorem takewhile_greedy (p : E → Bool) :
    cataR ((Salg p)%∋ ≫ est(lenLE°)) ⊑ (cataR (Salg p))%∋ ≫ est(lenLE°) := by
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact greedy (F_preservesRecip Unit E) (initial Unit E) lenLE_recip_trans (takewhile_mono p)

theorem twStep_pos {p : E → Bool} {x : E} (h : p x = true) (c : List E) : twStep p x c = x :: c := by
  unfold twStep; rw [h]

theorem twStep_neg {p : E → Bool} {x : E} (h : p x = false) (c : List E) : twStep p x c = [] := by
  unfold twStep; rw [h]

/-- The `takewhile-step` row: `Λ(S) est(R°) = [nil,(π₁p→cons,⊸ nil)]` — the longest of the
    lists the algebra allows is the `cons` where the head passes `p`, and `nil` where it does
    not.  The right side is the AoPA route's algebra, so both routes share one program. -/
public theorem takewhile_step (p : E → Bool) :
    (Salg p)%∋ ≫ est(lenLE°) = consScalarAlg (fun _ : Unit => ([] : List E)) (twStep p) := by
  apply hom_ext; intro u ws
  rw [Λ_comp_est_apply]
  cases u with
  | inl d =>
      constructor
      · rintro ⟨hS, -⟩
        exact (Salg_inl p d ws).mp hS
      · intro h0
        have hws : ws = [] := h0
        subst hws
        refine ⟨(Salg_inl p d []).mpr rfl, fun z hz => ?_⟩
        have hz' : z = [] := (Salg_inl p d z).mp hz
        subst hz'
        exact Nat.le_refl 0
  | inr q =>
      obtain ⟨x, c⟩ := q
      constructor
      · rintro ⟨hS, hmax⟩
        show ws = twStep p x c
        rcases (Salg_inr p x c ws).mp hS with hws | ⟨hp, hws⟩
        · subst hws
          cases hpx : p x with
          | false => rw [twStep_neg hpx]
          | true =>
              have hz := hmax (x :: c) ((Salg_inr p x c _).mpr (Or.inr ⟨hpx, rfl⟩))
              exact absurd hz (Nat.not_succ_le_zero _)
        · rw [twStep_pos hp, hws]
      · intro h0
        have hws : ws = twStep p x c := h0
        cases hpx : p x with
        | true =>
            rw [twStep_pos hpx] at hws
            subst hws
            refine ⟨(Salg_inr p x c _).mpr (Or.inr ⟨hpx, rfl⟩), fun z hz => ?_⟩
            rcases (Salg_inr p x c z).mp hz with hz' | ⟨-, hz'⟩
            · subst hz'; exact Nat.zero_le _
            · subst hz'; exact Nat.le_refl _
        | false =>
            rw [twStep_neg hpx] at hws
            subst hws
            refine ⟨(Salg_inr p x c _).mpr (Or.inl rfl), fun z hz => ?_⟩
            rcases (Salg_inr p x c z).mp hz with hz' | ⟨hp', hz'⟩
            · subst hz'; exact Nat.le_refl _
            · rw [hpx] at hp'; nomatch hp'

/-- The simplicity row: `takewhile(p)° takewhile(p) ⊑ 𝟙` — two prefixes of one list of equal
    length are equal, so `takewhile(p)` is THE longest `p`-prefix, not A longest. -/
public theorem takewhile_simple (p : E → Bool) : Simple (takewhile p) := by
  show (takewhile p)° ≫ takewhile p ⊑ Cat.id _
  apply le_iff.mpr
  intro ws zs h
  obtain ⟨u, h1, h2⟩ := h
  have h1' := (Λ_comp_est_apply (prefixR ≫ listP p) ((lenLE (E := E))°) u ws).mp h1
  have h2' := (Λ_comp_est_apply (prefixR ≫ listP p) ((lenLE (E := E))°) u zs).mp h2
  exact pre_eq_of_length ((spec_iff p u ws).mp h1'.1).1 ((spec_iff p u zs).mp h2'.1).1
    (Nat.le_antisymm (h2'.2 ws h1'.1) (h1'.2 zs h2'.1))

/-- **Ex 7.39's headline** (the note's `takewhile-laws`): `takewhile(p) = ⦇[nil,(π₁p→cons,⊸ nil)]⦈`.
    The greedy `⊒` becomes `=`: the program is entire (a reduce of maps, via `takeWhile_emerges`)
    and the specification is simple, so `eq_of_le_entire_simple` closes the gap. -/
public theorem takewhile_eq_cata (p : E → Bool) :
    takewhile p = cataR (consScalarAlg (fun _ : Unit => ([] : List E)) (twStep p)) := by
  have hle : cataR (consScalarAlg (fun _ : Unit => ([] : List E)) (twStep p)) ⊑ takewhile p := by
    rw [← takewhile_step p]
    show cataR ((Salg p)%∋ ≫ est(lenLE°)) ⊑ (prefixR ≫ listP p)%∋ ≫ est(lenLE°)
    rw [takewhile_alg p]
    exact takewhile_greedy p
  have hentire : Entire (cataR (consScalarAlg (fun _ : Unit => ([] : List E)) (twStep p))) := by
    rw [← takeWhile_emerges p]
    exact graph_entire _
  exact (eq_of_le_entire_simple hentire (takewhile_simple p) hle).symm

/-- The entirety row: `Λ(prefix list(p)) est(R°)` is entire — `nil` is always a `p`-prefix and
    the longest exists; read off the headline, whose program is a reduce of maps. -/
public theorem takewhile_entire (p : E → Bool) : Entire (takewhile p) := by
  rw [takewhile_eq_cata p, ← takeWhile_emerges p]
  exact graph_entire _

end Freyd.Alg.RelSet.GCTakeWhile
