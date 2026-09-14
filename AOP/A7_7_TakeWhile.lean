/-
  `takeWhile` derived by SHRINK — a port of AoPA `Examples/GC/TakeWhile.agda`
  (Mu–Oliveira, "Programming from Galois connections").

  SPEC (program-independent).  For a predicate `p`, a valid answer to `takeWhile p` on a list `x`
  is any prefix of `x` all of whose elements satisfy `p`:
      `twSpec x out  :=  out ≼ x  ∧  every element of out satisfies p`.
  The wanted answer is the LONGEST such prefix.  In AoPA this is `(mapR (p¿) ○ _≼_) ↾ _≽_`:
  the relation "a `p`-satisfying prefix" (`mapR (p¿) ○ _≼_`) shrunk by the prefix order `_≼_`
  so that only the longest survives.

  HEADLINE (this repo).  The longest-prefix requirement is exactly Bird & de Moor's `max`, and the
  AoPA shrink `S ↾ R` is `Λ S ≫ est R` (`A7_6.shrink_eq_Λ_comp_est`).  So the derivation's
  headline is the morphism equation
      `graph (twCL p)  =  Λ twSpec ≫ est prefix`                    (`takeWhile_eq_Λ_est`)
  where `prefix x ys` is "`ys` is an initial segment of `x`" (dominance = "`x` is at least as
  long"), and equivalently the shrink form
      `graph (twCL p)  =  twSpec ↾ prefix°`                            (`takeWhile_eq_shrink`)
  with `prefix°` the sub-prefix order — AoPA's `spec ↾ ≽`, up to the min/max and argument-order
  conventions.  Both come out of `RelSet.eq_Λ_comp_est` (the two halves it consumes —
  achievability and prefix-domination — are proved here directly).

  ONE CARRIER.  Every arrow here lives on the cons-list object `dList A = dCL Unit A`, the initial
  algebra the folds run over; the pointwise helpers are `ConsList Unit A → …`, and the prefix
  order is `ListRel.prefixP`, not a second copy on raw `List A`.

  PROGRAM EMERGENCE.  `twCL p` is not hand-written and then verified: it is PRODUCED as the
  catamorphism of its base/step by the cons-list fold-uniqueness law (`CL.consFold_unique`),
  mirroring AoPA's `foldR-fold`/`greedy-cata` step:
      `graph (twCL p)  =  cataR (consScalarAlg (fun _ => nil) (twStep p))`   (`takeWhile_emerges`).

  BOOK ROUTE (the second half of this file).  The same problem derived B&dM's own way
  (Ex 7.39, the note's `sec-takewhile`): the GREEDY THEOREM 7.2 (`AOP.A7_2.greedy`) applied to
  the spec `takewhile p = Λ(prefix list(p)) est(R°)` with `R = length ≤ length°`, closing the
  greedy `⊒` into `=` by `eq_of_le_entire_simple` (program entire, spec simple).  Both routes
  produce the same algebra `[nil,(π₁p→cons,⊸ nil)]` = `consScalarAlg (fun _ => nil) (twStep p)`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
module

public import AOP.A7_6_Shrink
public import AOP.A7_4_Horner
public import AOP.A7_2
public import AOP.A6_ConsList
public import AOP.A6_GenFold
public import AOP.A5_7_ListBeads

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.GCTakeWhile

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL
-- `prefix` is ListRel's arrow, not a second copy: the note's bead finds its naturality by the
-- head constant.  Opened by name because this section's `listP p` clashes with ListRel's `listP`.
open Freyd.Alg.RelSet.ListRel
  (dList prefixR prefAlg prefixP prefix_cata clen junc_sum_inl junc_sum_inr)

variable {A : Type}

/-! ## Supporting list facts (AoPA `Examples/GC/List.agda`, `Nat.agda`) -/

/-- `AllP p x` — every element of `x` satisfies `p` (AoPA `mapR (p ¿)` restricted to the
    diagonal). -/
def AllP (p : A → Bool) : ConsList Unit A → Prop
  | ConsList.wrap _   => True
  | ConsList.cons x xs => p x = true ∧ AllP p xs

/-- Prefix antisymmetry (AoPA: `_≼_` is a partial order; underlies `≼-isPreorder` + antisymmetry
    used for the shrink's uniqueness). -/
theorem prefixP_antisym : ∀ {x y : ConsList Unit A}, prefixP x y → prefixP y x → x = y
  | ConsList.wrap _  , ConsList.wrap _  , _  , _  => rfl
  | ConsList.wrap _  , ConsList.cons _ _, _  , hb => hb.elim
  | ConsList.cons _ _, ConsList.wrap _  , ha , _  => ha.elim
  | ConsList.cons a x, ConsList.cons b y, ha , hb => by
      have hab : a = b := ha.1
      have := prefixP_antisym ha.2 hb.2      -- x = y
      rw [hab, this]

/-! ## The program `twCL` and its base/step -/

/-- The step of `takeWhile`: keep the head iff it satisfies `p`, else stop. -/
public def twStep (p : A → Bool) (x : A) (c : ConsList Unit A) : ConsList Unit A :=
  match p x with
  | true  => ConsList.cons x c
  | false => ConsList.wrap ()

/-- `takeWhile p` on `ConsList Unit A`.  Defined by the very recursion whose base/step is
    `(fun _ => nil)` / `twStep p`, so `CL.consFold_unique` produces it as a catamorphism. -/
def twCL (p : A → Bool) : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _    => ConsList.wrap ()
  | ConsList.cons x xs => twStep p x (twCL p xs)

/-! ## The spec (program-independent) -/

/-- `twSpec p x out`: `out` is a `p`-satisfying prefix of `x`. -/
def twSpec (p : A → Bool) : dList A ⟶ dList A :=
  fun x out => prefixP out x ∧ AllP p out

/-! ## Program emergence (AoPA `foldR-fold`) -/

/-- **The program is produced by the fold law.**  `twCL p` obeys the cons-list recursion of its
    base/step, so it IS the catamorphism of `consScalarAlg (fun _ => nil) (twStep p)`. -/
theorem takeWhile_emerges (p : A → Bool) :
    (graph (twCL p) : dList A ⟶ dList A)
      = cataR (consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p)) :=
  consFold_unique (fun _ => ConsList.wrap ()) (twStep p) (twCL p) (fun _ => rfl) (fun _ _ => rfl)

/-! ## The two halves the headline consumes -/

/-- Achievability: `twCL p x` is itself a `p`-satisfying prefix of `x`. -/
theorem tw_sound (p : A → Bool) (x : ConsList Unit A) : twSpec p x (twCL p x) := by
  induction x with
  | wrap u => exact ⟨trivial, trivial⟩
  | cons a xs ih =>
      show prefixP (twStep p a (twCL p xs)) (ConsList.cons a xs)
        ∧ AllP p (twStep p a (twCL p xs))
      unfold twStep
      cases hpa : p a with
      | false => exact ⟨trivial, trivial⟩
      | true  => exact ⟨⟨rfl, ih.1⟩, ⟨hpa, ih.2⟩⟩

/-- Domination: every `p`-satisfying prefix `out` of `x` is a prefix of `twCL p x`
    (so `twCL p x` is the longest). -/
theorem tw_best (p : A → Bool) (x : ConsList Unit A) (out : ConsList Unit A)
    (h : twSpec p x out) : prefixP out (twCL p x) := by
  induction x generalizing out with
  | wrap u =>
      -- a prefix of `nil` is `nil`, and `twCL p nil = nil`
      cases out with
      | wrap v => exact trivial
      | cons b ys => exact (h.1).elim
  | cons a xs ih =>
      cases out with
      | wrap v => exact trivial
      | cons b ys =>
          -- h.1 : prefixP (cons b ys) (cons a xs) = (b = a) ∧ prefixP ys xs
          -- h.2 : AllP p (cons b ys) = (p b = true) ∧ AllP p ys
          have hba : b = a := h.1.1
          have hpre : prefixP ys xs := h.1.2
          have hpb : p b = true := h.2.1
          have htail : AllP p ys := h.2.2
          show prefixP (ConsList.cons b ys) (twStep p a (twCL p xs))
          unfold twStep
          have hpa : p a = true := by rw [← hba]; exact hpb
          rw [hpa]
          exact ⟨hba, ih ys ⟨hpre, htail⟩⟩

/-! ## Headlines -/

/-- **Morphism-equation headline (max form).**  `graph (twCL p) = Λ twSpec ≫ est prefix` —
    `takeWhile p` is exactly `max prefix · Λ twSpec`, the longest `p`-satisfying prefix, as a
    relation (not merely pointwise).  Via `RelSet.eq_Λ_comp_est`, fed the two halves above and
    prefix antisymmetry. -/
theorem takeWhile_eq_Λ_est (p : A → Bool) :
    (graph (twCL p) : dList A ⟶ dList A) = Λ (twSpec p) ≫ est (prefixR (A := A)) :=
  eq_Λ_comp_est (prefixR (A := A))
    (fun x y h1 h2 => prefixP_antisym h2 h1)             -- antisymmetry of prefix
    (twCL p) (twSpec p)
    (tw_sound p)                                        -- achievability
    (fun x v hv => tw_best p x v hv)                     -- domination (longest)

/-- **Shrink-form headline (AoPA `spec ↾ ≽`).**  `graph (twCL p) = twSpec ↾ prefix°`.  This is
    the AoPA shrink presentation: the `p`-satisfying-prefix relation, shrunk by the prefix order,
    equals `takeWhile`.  Immediate from the max form by `shrink_eq_Λ_comp_est`
    (`est R = est R°`). -/
theorem takeWhile_eq_shrink (p : A → Bool) :
    (graph (twCL p) : dList A ⟶ dList A) = twSpec p ↾ (prefixR (A := A))° := by
  rw [shrink_eq_Λ_comp_est]
  exact takeWhile_eq_Λ_est p

/-! ## Executable sanity checks -/

/-- `takeWhile (· < 3) [1,2,5,1] = [1,2]`. -/
example : twCL (fun n => decide (n < 3)) (ofList [1, 2, 5, 1]) = ofList [1, 2] := rfl
/-- Everything satisfies `p` ⇒ the whole list. -/
example : twCL (fun n => decide (n < 9)) (ofList [1, 2, 5]) = ofList [1, 2, 5] := rfl
/-- Head fails ⇒ the empty list. -/
example : twCL (fun n => decide (n < 1)) (ofList [1, 2]) = ConsList.wrap () := rfl

/-! ## The BOOK route (Ex 7.39, note `sec-takewhile`): the greedy theorem on the book spec

  Note-name ↦ Lean-name: `p` (a coreflexive) ↦ `pcor p`, `R ≜ length ≤ length°` ↦ `lenLE`,
  `prefix` ↦ `prefixR` (a Lean keyword forces the suffix), `list(p)` ↦ `listP p`, `S` ↦ `Salg p`,
  `takewhile(p)` ↦ `takewhile p`; the program algebra `[nil,(π₁p→cons,⊸ nil)]` is the AoPA
  route's `consScalarAlg (fun _ => nil) (twStep p)`, shared verbatim. -/

/-- The note's coreflexive `p : A⟶A` — the partial identity on the `p`-passers. -/
@[expose] public def pcor (p : A → Bool) : dE A ⟶ dE A := fun x y => x = y ∧ p x = true

/-- The note's `R ≜ length ≤ length°`, the length preorder: `xs lenLE ys ⟺ |xs| ≤ |ys|`. -/
@[expose] public def lenLE : dList A ⟶ dList A :=
  fun xs ys => clen xs ≤ clen ys

/-- `R°` is reflexive — the greedy theorem's preorder hypothesis, at `R ≜ length ≤ length°`. -/
public theorem lenLE_recip_refl : 𝟙 (dList A) ⊑ (lenLE (A := A))° :=
  le_iff.mpr fun _ _ h => by cases h; exact Nat.le_refl _

/-- `R°` is transitive — the greedy theorem's preorder hypothesis, at `R ≜ length ≤ length°`. -/
public theorem lenLE_recip_trans : (lenLE (A := A))° ≫ lenLE° ⊑ lenLE° :=
  le_iff.mpr fun xs zs h => by
    obtain ⟨ys, h1, h2⟩ := h
    exact Nat.le_trans h2 h1

/-- `(p×𝟙) cons : A×[A] ⟶ [A]` — keep a head that passes `p` onto the folded tail. -/
@[expose] public def pcons (p : A → Bool) :
    (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  rprodMap (pcor p) (𝟙 (dList A)) ≫ consR

/-- `list(p)`'s algebra `[nil, (p×𝟙) cons]`. -/
@[expose] public def listPAlg (p : A → Bool) :
    (F Unit A).obj (dList A) ⟶ dList A :=
  junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (pcons p)

/-- `list(p)` — the relator `list` AT the coreflexive `p`, which is what the name says and what a
    picture must draw: `p` on the object wire, `list` running past it untouched. -/
@[expose] public def listP (p : A → Bool) : dList A ⟶ dList A := ListRel.list (pcor p)

/-- `list(p) = ⦇[nil, (p×𝟙) cons]⦈` — `list_cata` at the coreflexive; every §7.7 proof below reads
    `list(p)` through this fold, so it is rewritten in before the algebra is destructured. -/
public theorem listP_cata (p : A → Bool) : listP p = cataR (listPAlg p) := by
  rw [cataR_eq_relCata]; unfold listP listPAlg pcons; exact ListRel.list_cata (pcor p)

/-- `⊸ nil : A×[A] ⟶ [A]` — discard the pair, return `nil`; `S`'s `stop` operand. -/
@[expose] public def discNil : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  graph fun _ => ConsList.wrap ()

/-- The note's `S ≜ [nil, ⊸ nil ∪ (p×𝟙) cons]` — `prefix`'s algebra with one extra `p`. -/
@[expose] public def Salg (p : A → Bool) :
    (F Unit A).obj (dList A) ⟶ dList A :=
  junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (discNil ∪ pcons p)

/-- Ex 7.39's specification: `takewhile(p) ≜ Λ(prefix list(p)) est(R°)` — the longest prefix
    all of whose elements pass `p`. -/
@[expose] public def takewhile (p : A → Bool) : dList A ⟶ dList A :=
  (prefixR ≫ listP p)%∋ ≫ est(lenLE°)

/-! ### Pointwise unfolds of the three `junc` algebras -/

public theorem pcons_apply (p : A → Bool) (a : A) (c ws : ConsList Unit A) :
    pcons p (a, c) ws ↔ p a = true ∧ ws = ConsList.cons a c := by
  constructor
  · rintro ⟨q, ⟨⟨ha, hp⟩, hc⟩, hw⟩
    obtain ⟨qa, qc⟩ := q
    have ha' : a = qa := ha
    have hc' : c = qc := hc
    subst ha'
    subst hc'
    exact ⟨hp, hw⟩
  · rintro ⟨hp, hw⟩
    exact ⟨(a, c), ⟨⟨rfl, hp⟩, rfl⟩, hw⟩

theorem prefAlg_inl (D : Unit) (ys : ConsList Unit A) :
    prefAlg (Sum.inl D) ys ↔ ys = ConsList.wrap () := by
  unfold prefAlg; exact junc_sum_inl _ _ _ _

theorem prefAlg_inr (a : A) (r ys : ConsList Unit A) :
    prefAlg (Sum.inr (a, r)) ys ↔ ys = ConsList.wrap () ∨ ys = ConsList.cons a r := by
  unfold prefAlg; exact junc_sum_inr _ _ _ _

public theorem listPAlg_inl (p : A → Bool) (D : Unit) (ws : ConsList Unit A) :
    listPAlg p (Sum.inl D) ws ↔ ws = ConsList.wrap () := by
  unfold listPAlg; exact junc_sum_inl _ _ _ _

public theorem listPAlg_inr (p : A → Bool) (a : A) (c ws : ConsList Unit A) :
    listPAlg p (Sum.inr (a, c)) ws ↔ p a = true ∧ ws = ConsList.cons a c := by
  unfold listPAlg; exact (junc_sum_inr _ _ _ _).trans (pcons_apply p a c ws)

theorem Salg_inl (p : A → Bool) (D : Unit) (ws : ConsList Unit A) :
    Salg p (Sum.inl D) ws ↔ ws = ConsList.wrap () := by
  unfold Salg; exact junc_sum_inl _ _ _ _

theorem Salg_inr (p : A → Bool) (a : A) (c ws : ConsList Unit A) :
    Salg p (Sum.inr (a, c)) ws
      ↔ ws = ConsList.wrap () ∨ (p a = true ∧ ws = ConsList.cons a c) := by
  unfold Salg
  refine (junc_sum_inr _ _ _ _).trans ?_
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((pcons_apply p a c ws).mp h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((pcons_apply p a c ws).mpr h)

/-! ### Supporting facts: prefixes of equal length agree -/

/-- Two prefixes of one list of equal length are equal. -/
theorem prefixP_eq_of_clen : ∀ {x y v : ConsList Unit A},
    prefixP x v → prefixP y v → clen x = clen y → x = y
  | ConsList.wrap _, ConsList.wrap _, _, _, _, _ => rfl
  | ConsList.wrap _, ConsList.cons _ _, _, _, _, hlen => absurd hlen.symm (Nat.succ_ne_zero _)
  | ConsList.cons _ _, ConsList.wrap _, _, _, _, hlen => absurd hlen (Nat.succ_ne_zero _)
  | ConsList.cons _ _, ConsList.cons _ _, ConsList.wrap _, ha, _, _ => ha.elim
  | ConsList.cons a x, ConsList.cons b y, ConsList.cons _ z, ha, hb, hlen => by
      obtain ⟨haz, hpa⟩ := ha
      obtain ⟨hbz, hpb⟩ := hb
      rw [haz, hbz, prefixP_eq_of_clen hpa hpb (Nat.succ.inj hlen)]

/-- The two routes' specifications agree pointwise: `x (prefix list(p)) ws` iff `ws` is a
    `p`-passing prefix of `x`. -/
theorem spec_iff (p : A → Bool) (u : ConsList Unit A) (ws : ConsList Unit A) :
    (prefixR ≫ listP p) u ws ↔ prefixP ws u ∧ AllP p ws := by
  rw [listP_cata]
  induction u generalizing ws with
  | wrap D =>
      constructor
      · rintro ⟨ys, hpre, hlp⟩
        cases ys with
        | wrap E =>
            have hws : ws = ConsList.wrap () := (listPAlg_inl p E ws).mp hlp
            subst hws
            exact ⟨trivial, trivial⟩
        | cons b y => exact False.elim hpre
      · rintro ⟨hpre, -⟩
        cases ws with
        | wrap E =>
            exact ⟨ConsList.wrap (), prefixP.nil _, (listPAlg_inl p () _).mpr rfl⟩
        | cons b ys => exact hpre.elim
  | cons a t ih =>
      constructor
      · rintro ⟨ys, hpre, hlp⟩
        cases ys with
        | wrap E =>
            have hws : ws = ConsList.wrap () := (listPAlg_inl p E ws).mp hlp
            subst hws
            exact ⟨trivial, trivial⟩
        | cons b y =>
            have hpre' : b = a ∧ prefixP y t := hpre
            obtain ⟨w', hw', hstep2⟩ := hlp
            obtain ⟨hp, hws⟩ := (listPAlg_inr p b w' ws).mp hstep2
            subst hws
            obtain ⟨hPre, hAll⟩ := (ih w').mp ⟨y, hpre'.2, hw'⟩
            exact ⟨⟨hpre'.1, hPre⟩, hp, hAll⟩
      · rintro ⟨hpre, hall⟩
        cases ws with
        | wrap E => exact ⟨ConsList.wrap (), prefixP.nil _, (listPAlg_inl p () _).mpr rfl⟩
        | cons b ws' =>
            obtain ⟨hba, hpre'⟩ := hpre
            obtain ⟨hpb, hall'⟩ := hall
            obtain ⟨ys', hys', hlp'⟩ := (ih ws').mpr ⟨hpre', hall'⟩
            refine ⟨ConsList.cons a ys', ⟨rfl, hys'⟩,
              ws', hlp', (listPAlg_inr p a ws' _).mpr ⟨?_, ?_⟩⟩
            · rw [← hba]; exact hpb
            · rw [hba]

/-! ### The chain, one theorem per row of the note's `takewhile-alg` table -/

/-- `list(p)` at `nil` is `nil` — the fold's computation rule on the `wrap` summand. -/
public theorem listP_wrap (p : A → Bool) (D : Unit) (ws : ConsList Unit A) :
    listP p (ConsList.wrap D) ws ↔ ws = ConsList.wrap () := by
  rw [listP_cata]; exact listPAlg_inl p D ws

/-- `list(p)` at a `cons`: the head must pass `p`, and what is left is a `list(p)` of the tail —
    the fold's computation rule on the `cons` summand. -/
public theorem listP_cons (p : A → Bool) (a : A) (t : ConsList Unit A) (ws : ConsList Unit A) :
    listP p (ConsList.cons a t) ws
      ↔ p a = true ∧ ∃ w', listP p t w' ∧ ws = ConsList.cons a w' := by
  rw [listP_cata]
  constructor
  · rintro ⟨w', hw', hstep⟩
    obtain ⟨hp, hws⟩ := (listPAlg_inr p a w' ws).mp hstep
    exact ⟨hp, w', hw', hws⟩
  · rintro ⟨hp, w', hw', hws⟩
    exact ⟨w', hw', (listPAlg_inr p a w' ws).mpr ⟨hp, hws⟩⟩

/-- `[nil, ⊸ nil ∪ (p×X) cons]` — `prefix`'s algebra with `list(p)`'s own `p` on the head it keeps
    and the strand `X` the chain has already pushed onto the tail.  `X ≜ list(p)` is the third row
    of the note's `takewhile-alg`, `X ≜ prefix list(p)` its fourth. -/
@[expose] public def prefConsAlg (p : A → Bool) {C : RelSet.{0}}
    (X : C ⟶ dList A) : Fobj Unit A C ⟶ dList A :=
  junc (sumCop (dL Unit) ⟨A × C.carrier⟩)
    (wrapR : dL Unit ⟶ dList A)
    ((graph (fun _ => (ConsList.wrap () : ConsList Unit A))
        : (⟨A × C.carrier⟩ : RelSet.{0}) ⟶ dList A)
      ∪ (rprodMap (pcor p) X ≫ consR))

/-- The `nil` arm of `[nil, ⊸ nil ∪ (p×X) cons]`. -/
public theorem prefConsAlg_inl (p : A → Bool) {C : RelSet.{0}}
    (X : C ⟶ dList A) (D : Unit) (ws : ConsList Unit A) :
    prefConsAlg p X (Sum.inl D) ws ↔ ws = ConsList.wrap () := junc_sum_inl _ _ _ _

/-- The `cons` arm of `[nil, ⊸ nil ∪ (p×X) cons]`: stop with `nil`, or keep a `p`-passing head on
    an `X` of the tail. -/
public theorem prefConsAlg_inr (p : A → Bool) {C : RelSet.{0}}
    (X : C ⟶ dList A) (a : A) (t : C.carrier) (ws : ConsList Unit A) :
    prefConsAlg p X (Sum.inr (a, t)) ws
      ↔ ws = ConsList.wrap () ∨ (p a = true ∧ ∃ w', X t w' ∧ ws = ConsList.cons a w') := by
  refine (junc_sum_inr _ _ _ _).trans ?_
  constructor
  · rintro (h | ⟨⟨a', w'⟩, ⟨⟨ha, hp⟩, hX⟩, hws⟩)
    · exact Or.inl h
    · cases ha; exact Or.inr ⟨hp, w', hX, hws⟩
  · rintro (h | ⟨hp, w', hX, hws⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(a, w'), ⟨⟨rfl, hp⟩, hX⟩, hws⟩

/-- Row 2 of `takewhile-alg`: `α prefix list(p) = F(prefix)[nil,⊸ nil ∪ cons] list(p)` — the fold's
    computation rule at `prefix ≜ ⦇[nil,⊸ nil ∪ cons]⦈`, with `list(p)` carried along. -/
public theorem takewhile_alg_step1 (p : A → Bool) :
    (initial Unit A).α ≫ (prefixR ≫ listP p)
      = (F Unit A).map prefixR ≫ prefAlg ≫ listP p := by
  have h : (initial Unit A).α ≫ prefixR = (F Unit A).map prefixR ≫ prefAlg :=
    (relCata_UP (initial Unit A) prefAlg prefixR).mpr prefix_cata
  rw [← Cat.assoc, h, Cat.assoc]

/-- `[nil,⊸ nil ∪ cons] list(p) = [nil,⊸ nil ∪ (p×list(p)) cons]` — `list(p)` after `prefix`'s
    algebra is `list(p)` on the tail it conses to and one `p` on the head it keeps. -/
public theorem prefAlg_comp_listP (p : A → Bool) :
    prefAlg ≫ listP p = prefConsAlg p (listP p) := by
  apply hom_ext; intro v ws
  cases v with
  | inl D =>
      rw [prefConsAlg_inl]
      constructor
      · rintro ⟨ys, hpre, hlp⟩
        obtain rfl : ys = ConsList.wrap () := (prefAlg_inl D ys).mp hpre
        exact (listP_wrap p () ws).mp hlp
      · intro hws
        exact ⟨ConsList.wrap (), (prefAlg_inl D _).mpr rfl, (listP_wrap p () ws).mpr hws⟩
  | inr q =>
      obtain ⟨a, t⟩ := q
      rw [prefConsAlg_inr]
      constructor
      · rintro ⟨ys, hpre, hlp⟩
        rcases (prefAlg_inr a t ys).mp hpre with h | h
        · subst h; exact Or.inl ((listP_wrap p () ws).mp hlp)
        · subst h; exact Or.inr ((listP_cons p a t ws).mp hlp)
      · rintro (hws | hc)
        · exact ⟨ConsList.wrap (), (prefAlg_inr a t _).mpr (Or.inl rfl),
            (listP_wrap p () ws).mpr hws⟩
        · exact ⟨ConsList.cons a t, (prefAlg_inr a t _).mpr (Or.inr rfl),
            (listP_cons p a t ws).mpr hc⟩

/-- Row 3 of `takewhile-alg`: `F(prefix)[nil,⊸ nil ∪ cons] list(p)
    = F(prefix)[nil,⊸ nil ∪ (p×list(p)) cons]` — `list(p)` moves through the algebra. -/
public theorem takewhile_alg_step2 (p : A → Bool) :
    (F Unit A).map prefixR ≫ prefAlg ≫ listP p
      = (F Unit A).map prefixR ≫ prefConsAlg p (listP p) := by
  rw [prefAlg_comp_listP]

/-- Row 4 of `takewhile-alg`: `F(prefix)[nil,⊸ nil ∪ (p×list(p)) cons]
    = [nil,⊸ nil ∪ (p×(prefix list(p))) cons]` — the relator's tape joins the strand it runs
    alongside, `prefix` landing on the tail `list(p)` already holds.  `⊸ nil` swallows it because
    `nil` prefixes every list. -/
public theorem takewhile_alg_step3 (p : A → Bool) :
    (F Unit A).map prefixR ≫ prefConsAlg p (listP p)
      = prefConsAlg p (prefixR ≫ listP p) := by
  apply hom_ext; intro u ws
  cases u with
  | inl D =>
      rw [prefConsAlg_inl]
      constructor
      · rintro ⟨v, hv, h⟩
        cases v with
        | inl D' => exact (prefConsAlg_inl p (listP p) D' ws).mp h
        | inr q => exact hv.elim
      · intro hws
        exact ⟨Sum.inl D, rfl, (prefConsAlg_inl p (listP p) D ws).mpr hws⟩
  | inr q =>
      obtain ⟨a, t⟩ := q
      rw [prefConsAlg_inr]
      constructor
      · rintro ⟨v, hv, h⟩
        cases v with
        | inl D' => exact hv.elim
        | inr q' =>
            obtain ⟨a', r⟩ := q'
            obtain ⟨ha, hr⟩ := hv
            cases ha
            rcases (prefConsAlg_inr p (listP p) a r ws).mp h with hws | ⟨hp, w', hw', hws⟩
            · exact Or.inl hws
            · exact Or.inr ⟨hp, w', ⟨r, hr, hw'⟩, hws⟩
      · rintro (hws | ⟨hp, w', ⟨r, hr, hw'⟩, hws⟩)
        · exact ⟨Sum.inr (a, ConsList.wrap ()), ⟨rfl, prefixP.nil t⟩,
            (prefConsAlg_inr p (listP p) a (ConsList.wrap ()) ws).mpr (Or.inl hws)⟩
        · exact ⟨Sum.inr (a, r), ⟨rfl, hr⟩,
            (prefConsAlg_inr p (listP p) a r ws).mpr (Or.inr ⟨hp, w', hw', hws⟩)⟩

/-- Row 5 of `takewhile-alg`: `[nil,⊸ nil ∪ (p×(prefix list(p))) cons] = F(prefix list(p)) S` —
    `prefix list(p)` leaves the algebra for the relator's tape, and `S` is what is left. -/
public theorem takewhile_alg_step4 (p : A → Bool) :
    prefConsAlg p (prefixR ≫ listP p)
      = (F Unit A).map (prefixR ≫ listP p) ≫ Salg p := by
  rw [listP_cata]
  apply hom_ext; intro u ws
  cases u with
  | inl D =>
      rw [prefConsAlg_inl]
      constructor
      · intro hws; exact ⟨Sum.inl D, rfl, (Salg_inl p D ws).mpr hws⟩
      · rintro ⟨v, hv, hS⟩
        cases v with
        | inl D' => exact (Salg_inl p D' ws).mp hS
        | inr q => exact hv.elim
  | inr q =>
      obtain ⟨a, t⟩ := q
      rw [prefConsAlg_inr]
      constructor
      · rintro (hws | ⟨hp, w', hX, hws⟩)
        · exact ⟨Sum.inr (a, ConsList.wrap ()), ⟨rfl, ConsList.wrap (), prefixP.nil t,
            (listPAlg_inl p () _).mpr rfl⟩, (Salg_inr p a (ConsList.wrap ()) ws).mpr (Or.inl hws)⟩
        · exact ⟨Sum.inr (a, w'), ⟨rfl, hX⟩, (Salg_inr p a w' ws).mpr (Or.inr ⟨hp, hws⟩)⟩
      · rintro ⟨v, hv, hS⟩
        cases v with
        | inl D' => exact hv.elim
        | inr q' =>
            obtain ⟨a', w'⟩ := q'
            obtain ⟨ha, hX⟩ := hv
            cases ha
            rcases (Salg_inr p a w' ws).mp hS with hws | ⟨hp, hws⟩
            · exact Or.inl hws
            · exact Or.inr ⟨hp, w', hX, hws⟩

/-- The `takewhile-alg` display's headline: `α prefix list(p) = F(prefix list(p)) S` — building
    the list and then keeping a `p`-passing prefix of it is keeping one of the tail first, and
    then building with `S`.  (Fusion cannot derive this — `list(p)` is not entire and no algebra
    meets the side condition — so the display's four steps are proved pointwise and composed
    here, and the result is fed to @cata-defining below.) -/
public theorem takewhile_alg_comm (p : A → Bool) :
    (initial Unit A).α ≫ (prefixR ≫ listP p)
      = (F Unit A).map (prefixR ≫ listP p) ≫ Salg p :=
  (takewhile_alg_step1 p).trans ((takewhile_alg_step2 p).trans
    ((takewhile_alg_step3 p).trans (takewhile_alg_step4 p)))

/-- The `takewhile-alg` row: `prefix list(p) = ⦇S⦈`, read off the defining equation above by
    @cata-defining (the Eilenberg–Wright universal property). -/
public theorem takewhile_alg (p : A → Bool) : prefixR ≫ listP p = cataR (Salg p) := by
  rw [cataR_eq_relCata]
  exact (relCata_UP (initial Unit A) (Salg p) (prefixR ≫ listP p)).mp (takewhile_alg_comm p)

/-! ### `takewhile-mono`, a law to a step

    `F(R°)` is `𝟙×R°` on the `cons` summand, so that branch of `F(R°)S⊑SR°` is the note's
    display: `R°` distributes into the two operands of the `∪`, `⊸` swallows it on the constant
    branch, it slides past `cons` on the other, and `nil R°=nil` puts it back on both so it can
    leave past the join. -/

/-- `(𝟙×R°)⊸ nil⊑⊸ nil` — `⊸` discards the pair, so nothing that ran on it survives. -/
public theorem takewhile_mono_disc :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ discNil
      ⊑ discNil :=
  le_iff.mpr fun _ _ h => h.elim fun _ hy => hy.2

/-- `(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)=(𝟙×R°)⊸ nil ∪ (p×R°) cons` — `R°` reaches each operand of the
    `∪` on its own, and on the `cons` one it stands beside `p` as the pair's second strand. -/
public theorem takewhile_mono_fork (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ (discNil ∪ pcons p)
      = rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ discNil
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ consR := by
  have hcons : rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ pcons p
      = rprodMap (pcor p) (lenLE (A := A))° ≫ consR := by
    unfold pcons
    rw [← Cat.assoc, rprodMap_comp, Cat.id_comp, Cat.comp_id]
  rw [DistributiveAllegory.comp_union_distrib, hcons]

/-- `(p×R°) cons⊑(p×𝟙) cons R°` — a shorter tail makes a shorter list, so the `R°` the pair
    carried in comes back out on the built list. -/
public theorem takewhile_mono_slide (p : A → Bool) :
    rprodMap (pcor p) (lenLE (A := A))° ≫ consR
      ⊑ pcons p ≫ lenLE° := by
  refine le_iff.mpr fun q ws h => ?_
  obtain ⟨a, c⟩ := q
  obtain ⟨⟨a', c'⟩, ⟨⟨_, hpa⟩, hlen⟩, hws⟩ := h
  subst hws
  exact ⟨ConsList.cons a c, (pcons_apply p a c (ConsList.cons a c)).mpr ⟨hpa, rfl⟩,
    Nat.succ_le_succ hlen⟩

/-- `⊸ nil R°=⊸ nil` — `nil` is the shortest list, so it is above only itself. -/
public theorem takewhile_mono_nil :
    discNil ≫ (lenLE (A := A))°
      = discNil := by
  refine hom_ext fun _ ws => ⟨?_, ?_⟩
  · rintro ⟨vs, hvs, hlen⟩
    subst hvs
    cases ws with
    | wrap u => rfl
    | cons a as => exact absurd (Nat.le_zero.mp hlen) (Nat.succ_ne_zero (clen as))
  · rintro rfl
    exact ⟨ConsList.wrap (), rfl, Nat.le_refl 0⟩

/-- The step both mono chains share: **`(𝟙×R°) pcons(p) ⊑ pcons(p) R°`** — `p` still holds of the
    head, and a shorter tail makes a shorter `cons`. -/
public theorem pcons_slide (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ pcons p ⊑ pcons p ≫ lenLE° :=
  le_iff.mpr fun q ws h => by
    obtain ⟨a, c⟩ := q
    obtain ⟨q', hq, hp⟩ := h
    obtain ⟨a', c'⟩ := q'
    obtain ⟨ha, hlen⟩ := hq
    cases ha
    obtain ⟨hpa, hws⟩ := (pcons_apply p a c' ws).mp hp
    subst hws
    exact ⟨ConsList.cons a c, (pcons_apply p a c (ConsList.cons a c)).mpr ⟨hpa, rfl⟩,
      Nat.succ_le_succ hlen⟩

/-- **`takewhile-mono`'s second step**: `(𝟙×R°)⊸ nil ∪ (p×R°) cons ⊑ ⊸ nil ∪ (p×R°) cons` —
    `takewhile_mono_disc` on the constant operand, the other left where it stands. -/
public theorem takewhile_mono_step2 (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ discNil
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ consR
      ⊑ discNil ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ consR :=
  union_mono takewhile_mono_disc (le_refl _)

/-- **`takewhile-mono`'s third step**: `⊸ nil ∪ (p×R°) cons ⊑ ⊸ nil ∪ (p×𝟙) cons R°` —
    `takewhile_mono_slide` on the `cons` operand. -/
public theorem takewhile_mono_step3 (p : A → Bool) :
    (discNil : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A)
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ consR
      ⊑ discNil ∪ rprodMap (pcor p) (𝟙 (dList A)) ≫ consR ≫ lenLE° := by
  refine union_mono (le_refl _) ?_
  rw [← Cat.assoc]
  exact takewhile_mono_slide p

/-- **`takewhile-mono`'s fourth step**: `⊸ nil ∪ (p×𝟙) cons R° = ⊸ nil R° ∪ (p×𝟙) cons R°` —
    `nil R°=nil`, so the constant operand may carry the `R°` the other one already has. -/
public theorem takewhile_mono_step4 (p : A → Bool) :
    (discNil : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A)
        ∪ rprodMap (pcor p) (𝟙 (dList A)) ≫ consR ≫ lenLE°
      = discNil ≫ (lenLE (A := A))°
        ∪ rprodMap (pcor p) (𝟙 (dList A)) ≫ consR ≫ lenLE° := by
  rw [takewhile_mono_nil]

/-- The `cons` branch of `F(R°)S⊑SR°`, the note's `takewhile-mono` chain step by step. -/
public theorem takewhile_mono_cons (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))°
        ≫ (discNil ∪ pcons p)
      ⊑ (discNil ∪ pcons p) ≫ lenLE° :=
  calc rprodMap (𝟙 (dE A)) (lenLE (A := A))°
          ≫ (discNil ∪ pcons p)
      = rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ discNil
          ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ consR :=
        takewhile_mono_fork p
    _ ⊑ discNil ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ consR :=
        takewhile_mono_step2 p
    _ ⊑ discNil ∪ rprodMap (pcor p) (𝟙 (dList A)) ≫ consR ≫ lenLE° := takewhile_mono_step3 p
    _ = discNil ≫ (lenLE (A := A))°
          ∪ rprodMap (pcor p) (𝟙 (dList A)) ≫ consR ≫ lenLE° := takewhile_mono_step4 p
    _ = (discNil ∪ pcons p) ≫ lenLE° := by
        rw [← Cat.assoc]
        exact (union_comp_distrib _ _ _).symm

/-- The `takewhile-mono` row: `F(R°) S ⊑ S R°` — shortening the tail and then taking the step
    lands inside taking the step and then shortening the result. -/
public theorem takewhile_mono (p : A → Bool) :
    MonotonicAlg (F := F Unit A) (Salg p) lenLE° := by
  show (F Unit A).map lenLE° ≫ Salg p ⊑ Salg p ≫ lenLE°
  apply le_iff.mpr
  intro u ws h
  obtain ⟨v, hv, hS⟩ := h
  cases u with
  | inl D =>
      cases v with
      | inl d' =>
          have hws : ws = ConsList.wrap () := (Salg_inl p d' ws).mp hS
          subst hws
          exact ⟨ConsList.wrap (), (Salg_inl p D _).mpr rfl, Nat.le_refl 0⟩
      | inr q => exact hv.elim
  | inr q =>
      cases v with
      | inl d' => exact hv.elim
      | inr q' =>
          -- `Salg`'s `cons` summand IS the `∪` the chain above works on, and `F(R°)` there is `𝟙×R°`.
          obtain ⟨vs, hvs, hlen⟩ :=
            le_iff.mp (takewhile_mono_cons p) q ws ⟨q', hv, (junc_sum_inr _ _ _ _).mp hS⟩
          exact ⟨vs, (junc_sum_inr _ _ _ _).mpr hvs, hlen⟩

/-- The `takewhile-laws` first row: **`(prefix list(p))%∋ est(R°) = (⦇S⦈)%∋ est(R°)`** — the
    specification is the fold (`takewhile_alg`), under a transpose and a choice that neither
    touch, so the row holds at every `R`. -/
public theorem takewhile_laws_step1 (p : A → Bool) (R : dList A ⟶ dList A) :
    (prefixR ≫ listP p)%∋ ≫ est(R°) = (cataR (Salg p))%∋ ≫ est(R°) := by
  rw [takewhile_alg]

/-- The greedy row: `⦇Λ(S) est(R°)⦈ ⊑ Λ(⦇S⦈) est(R°)` — Theorem 7.2 at the preorder `R°`,
    with `takewhile-mono` for its hypothesis: one longest `p`-prefix kept at each `cons`
    refines every `p`-prefix collected and one chosen at the end. -/
public theorem takewhile_greedy (p : A → Bool) :
    cataR ((Salg p)%∋ ≫ est(lenLE°)) ⊑ (cataR (Salg p))%∋ ≫ est(lenLE°) := by
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact greedy (F_preservesRecip Unit A) (initial Unit A) lenLE_recip_trans (takewhile_mono p)

theorem twStep_pos {p : A → Bool} {a : A} (h : p a = true) (c : ConsList Unit A) :
    twStep p a c = ConsList.cons a c := by
  unfold twStep; rw [h]

theorem twStep_neg {p : A → Bool} {a : A} (h : p a = false) (c : ConsList Unit A) :
    twStep p a c = ConsList.wrap () := by
  unfold twStep; rw [h]

/-- The algebra's cons branch at a point: stop with `nil`, or keep a head that passes `p`. -/
theorem discNil_union_pcons_apply (p : A → Bool) (a : A) (c ws : ConsList Unit A) :
    (discNil ∪ pcons p) (a, c) ws
      ↔ ws = ConsList.wrap () ∨ (p a = true ∧ ws = ConsList.cons a c) :=
  (junc_sum_inr (wrapR : dL Unit ⟶ dList A) (discNil ∪ pcons p) (a, c) ws).symm.trans
    (Salg_inr p a c ws)

/-- Step 1 of `takewhile-step`: `S%∋ est(R°) = [nil%∋ est(R°),(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]` —
    the power transpose of a coproduct is the coproduct of the transposes, and `est(R°)` after a
    coproduct is the coproduct of the composites. -/
public theorem takewhile_step1 (p : A → Bool) (R : dList A ⟶ dList A) :
    (Salg p)%∋ ≫ est(R°)
      = junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩)
          ((wrapR : dL Unit ⟶ dList A)%∋ ≫ est(R°))
          ((discNil ∪ pcons p)%∋ ≫ est(R°)) := by
  unfold Salg; exact junc_Λ_est _ _ _ R°

/-- `nil%∋ est(R) = nil` for any REFLEXIVE `R` — `nil` is a map, so its singleton has one element
    and the `R`-greatest of a one-element set is that element.  The `nil` arm of every algebra of
    §7.7; the order never enters beyond `𝟙 ⊑ R`. -/
public theorem Λ_nil_comp_est {R : dList A ⟶ dList A} (hrefl : 𝟙 (dList A) ⊑ R) :
    (wrapR : dL Unit ⟶ dList A)%∋ ≫ est(R) = wrapR :=
  Λ_map_comp_est (graph_map _) hrefl

/-- Step 2 of `takewhile-step`: `nil%∋ est(R°) = nil` — `nil` is a map, so its singleton has one
    element and the `R°`-greatest of a one-element set is that element. -/
public theorem takewhile_step2 (p : A → Bool) {R : dList A ⟶ dList A}
    (hrefl : 𝟙 (dList A) ⊑ R°) :
    junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩)
        ((wrapR : dL Unit ⟶ dList A)%∋ ≫ est(R°))
        ((discNil ∪ pcons p)%∋ ≫ est(R°))
      = junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩)
          (wrapR : dL Unit ⟶ dList A)
          ((discNil ∪ pcons p)%∋ ≫ est(R°)) := by
  rw [Λ_nil_comp_est hrefl]

/-- Step 3 of `takewhile-step`: `(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°) = (π₁p→cons,⊸ nil)` — the branch
    offers `{nil}` where `p` fails on the head and `{nil, cons(a,xs)}` where it holds, and `nil`
    loses the second. -/
public theorem takewhile_step3 (p : A → Bool) :
    junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩)
        (wrapR : dL Unit ⟶ dList A)
        ((discNil ∪ pcons p)%∋ ≫ est(lenLE°))
      = consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p) := by
  apply hom_ext; intro u ws
  cases u with
  | inl D => rw [junc_sum_inl]; exact Iff.rfl
  | inr q =>
      obtain ⟨a, c⟩ := q
      rw [junc_sum_inr, Λ_comp_est_apply]
      constructor
      · rintro ⟨hS, hmax⟩
        show ws = twStep p a c
        rcases (discNil_union_pcons_apply p a c ws).mp hS with hws | ⟨hp, hws⟩
        · subst hws
          cases hpa : p a with
          | false => rw [twStep_neg hpa]
          | true =>
              have hz := hmax (ConsList.cons a c)
                ((discNil_union_pcons_apply p a c _).mpr (Or.inr ⟨hpa, rfl⟩))
              exact absurd hz (Nat.not_succ_le_zero _)
        · rw [twStep_pos hp, hws]
      · intro h0
        have hws : ws = twStep p a c := h0
        cases hpa : p a with
        | true =>
            rw [twStep_pos hpa] at hws
            subst hws
            refine ⟨(discNil_union_pcons_apply p a c _).mpr (Or.inr ⟨hpa, rfl⟩), fun z hz => ?_⟩
            rcases (discNil_union_pcons_apply p a c z).mp hz with hz' | ⟨-, hz'⟩
            · subst hz'; exact Nat.zero_le _
            · subst hz'; exact Nat.le_refl _
        | false =>
            rw [twStep_neg hpa] at hws
            subst hws
            refine ⟨(discNil_union_pcons_apply p a c _).mpr (Or.inl rfl), fun z hz => ?_⟩
            rcases (discNil_union_pcons_apply p a c z).mp hz with hz' | ⟨hp', hz'⟩
            · subst hz'; exact Nat.le_refl _
            · rw [hpa] at hp'; nomatch hp'

/-- The `takewhile-step` row: `Λ(S) est(R°) = [nil,(π₁p→cons,⊸ nil)]` — the longest of the
    lists the algebra allows is the `cons` where the head passes `p`, and `nil` where it does
    not.  The right side is the AoPA route's algebra, so both routes share one program. -/
public theorem takewhile_step (p : A → Bool) :
    (Salg p)%∋ ≫ est(lenLE°)
      = consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p) :=
  (takewhile_step1 p lenLE).trans
    ((takewhile_step2 p lenLE_recip_refl).trans (takewhile_step3 p))

/-- The `takewhile-laws` last row: **`⦇S%∋ est(R°)⦈ = ⦇[nil,(π₁p→cons,⊸ nil)]⦈`** — the greedy
    algebra IS the one-step take-while (`takewhile_step`), so the fold on the left is the fold the
    program runs. -/
public theorem takewhile_laws_step3 (p : A → Bool) :
    cataR ((Salg p)%∋ ≫ est(lenLE°))
      = cataR (consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p)) := by
  rw [takewhile_step]

/-- The simplicity row: `takewhile(p)° takewhile(p) ⊑ 𝟙` — two prefixes of one list of equal
    length are equal, so `takewhile(p)` is THE longest `p`-prefix, not A longest. -/
public theorem takewhile_simple (p : A → Bool) : Simple (takewhile p) := by
  show (takewhile p)° ≫ takewhile p ⊑ 𝟙 _
  apply le_iff.mpr
  intro ws zs h
  obtain ⟨u, h1, h2⟩ := h
  have h1' := (Λ_comp_est_apply (prefixR ≫ listP p) ((lenLE (A := A))°) u ws).mp h1
  have h2' := (Λ_comp_est_apply (prefixR ≫ listP p) ((lenLE (A := A))°) u zs).mp h2
  exact prefixP_eq_of_clen ((spec_iff p u ws).mp h1'.1).1 ((spec_iff p u zs).mp h2'.1).1
    (Nat.le_antisymm (h2'.2 ws h1'.1) (h1'.2 zs h2'.1))

/-- **Ex 7.39's headline** (the note's `takewhile-laws`): `takewhile(p) = ⦇[nil,(π₁p→cons,⊸ nil)]⦈`.
    The greedy `⊒` becomes `=`: the program is entire (a reduce of maps, via `takeWhile_emerges`)
    and the specification is simple, so `eq_of_le_entire_simple` closes the gap. -/
public theorem takewhile_eq_cata (p : A → Bool) :
    takewhile p
      = cataR (consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p)) := by
  have hle : cataR (consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p))
      ⊑ takewhile p := by
    rw [← takewhile_step p]
    show cataR ((Salg p)%∋ ≫ est(lenLE°)) ⊑ (prefixR ≫ listP p)%∋ ≫ est(lenLE°)
    rw [takewhile_alg p]
    exact takewhile_greedy p
  have hentire : Entire
      (cataR (consScalarAlg (fun _ : Unit => (ConsList.wrap () : ConsList Unit A)) (twStep p))) := by
    rw [← takeWhile_emerges p]
    exact graph_entire _
  exact (eq_of_le_entire_simple hentire (takewhile_simple p) hle).symm

/-- The entirety row: `Λ(prefix list(p)) est(R°)` is entire — `nil` is always a `p`-prefix and
    the longest exists; read off the headline, whose program is a reduce of maps. -/
public theorem takewhile_entire (p : A → Bool) : Entire (takewhile p) := by
  rw [takewhile_eq_cata p, ← takeWhile_emerges p]
  exact graph_entire _

-- printing-only: the note calls the algebra `S` and the element-wise lift `list(p)`.  The predicate
-- is an argument of the lift — it is what the lift lifts — but not of the algebra's name.
open Lean PrettyPrinter in
@[app_unexpander Salg] public meta def unexpandSalg : Unexpander
  | _ => `($(mkIdent `S))

notation:max "list(" p ")" => listP p

end Freyd.Alg.RelSet.GCTakeWhile
