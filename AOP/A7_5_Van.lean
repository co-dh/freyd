/-
  Bird & de Moor, *Algebra of Programming* §7.5  The security van problem (book pp. 184-190).

  A bank has a known sequence of transactions; the cash on hand must stay between `0` and `N`,
  and a security van can be called to top it up or take a surplus away.  Cut the sequence into
  the fewest consecutive stretches each of which one van visit can serve.

  §7.5 illustrates the idea the chapter ends on: when the monotonicity condition FAILS, refine
  the ORDER.  `S ≜ [nil,new∪old]` is not monotonic on `R ≜ length ≤ length°` — (7.15) is false —
  but it is monotonic on `R;H ≜ R∩(R°⇒H)`, which breaks a tie between equally short schedules
  by making one's first segment a prefix of the other's, and `R;H ⊑ R` keeps the answer.

  WHAT IS PROVED HERE (the note's `van-defn`, `van-mono`, `van-laws`):

  - `van_spec`       — `partition list(secure) = ⦇S⦈` (book p.185, "appeal to fusion").
  - `van_7_14`       — (7.14) `(𝟙×R)new ⊑ (new∪old)R`, the half that does hold.
  - `van_7_15_false` — (7.15) `(𝟙×R)old ⊑ (new∪old)R` REFUTED, on the book's own witness.
  - `van_mono`       — (7.17) `(𝟙×(R;H))old ⊑ (new∪old)(R;H)`, the note's `van-mono` headline.
  - `van_mono_new`   — (7.16) `(𝟙×(R;H))new ⊑ (new∪old)(R;H)`.
  - `van_mono_alg`   — the two together: `MonotonicAlg S (R;H)`, the greedy theorem's hypothesis.
  - `van_laws`       — `Λ(partition list(secure)) est(R) ⊒ ⦇[nil,(ok→glue,new)]⦈` (book p.188).

  TWO SIDE CONDITIONS THE NOTE DOES NOT STATE, both of them the book's.

  1.  `hsingle`, the book's "N is assumed to be at least as large as any single transaction"
      (p.184): every one-transaction stretch is secure.  `van_spec` is FALSE without it —
      `van_spec_false_without_hsingle` refutes it at `N = 0` on the single transaction `5`,
      where `partition list(secure)` is empty and `⦇S⦈` still returns `[[5]]`, because `new`
      carries no security test.  Transactions are therefore an abstract type `A` with an
      `amount : A → Int`, as `AOP.A8_5`'s words carry a `len`, and `hsingle` bounds them.

  2.  `secure` is closed under dropping the FIRST transaction (`secureP_tail`).  The note's
      `van-laws` cites `secure prefix ⊑ prefix secure` — PREFIX-closure — for the fusion row,
      but prefix-closure is what (7.19)-(7.21) need; the fusion's forward direction peels a
      transaction off the FRONT of the first segment and needs what is left to be secure, which
      is one step of the SUFFIX-closure the book only reaches on p.188.  Both are proved here
      (`secure_prefix`, `secureP_tail`); only the second is used by `van_spec`.

  MIRRORING: diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; B&dM's `min R` is `est R`, `bmax` and
  `bmin` are `max` and `min` on `Int`.
-/
module

public import AOP.A5_6_ListCombinators
public import AOP.A7_1
public import AOP.A7_2_Pres
public import AOP.A6_FinRel
import AOP.A7_2

/-- B&dM p.184: the section's fixed data, the van's capacity `N`.  Every arrow below reads it from
    the one instance in scope, so the printer, which hides instance arguments, shows the book's
    `old`, not `old amount N`.  The class is named after the section's namespace, so its field is
    the bare `N`; it takes no parameter, which a field whose type does not mention it would print. -/
public class Freyd.Alg.RelSet.Van where
  N : Int

/-- B&dM p.184: the other fixed datum, each transaction's `amount`, over the transaction type. -/
public class Freyd.Alg.RelSet.Van.Amount (A : Type) where
  amount : A → Int

namespace Freyd.Alg.RelSet.Van

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-! ## `van-defn` -/

/-- A SEGMENT: the consecutive transactions one van visit serves. -/
@[expose] public abbrev Seg (A : Type) : Type := ConsList Unit A
/-- A SCHEDULE: the transactions cut into segments, one van visit each. -/
@[expose] public abbrev Sched (A : Type) : Type := ConsList Unit (Seg A)
/-- The object carrying schedules. -/
@[expose] public abbrev dSched (A : Type) : RelSet.{0} := ⟨Sched A⟩

/-- The WIRE STACK a schedule rides, `list list`, as one relator: `schedRelator.obj a` is
    `dSched a.carrier` and `schedRelator.map S` is `list(list S)`.  Spelled with the identity
    relator at the bottom, which is how the picture reads the stack off a panel's lanes. -/
@[expose] public def schedRelator : Relator RelSet.{0} RelSet.{0} :=
  ((Relator.idRelator RelSet.{0}).comp listRelator).comp listRelator

/-- **van-defn**: `ceiling ≜ Λ(prefix sum) est(≥)`, the highest the balance reaches over the
    stretch — as the book's own fold `⦇[zero,omax plus]⦈` (p.188), `omax a = bmax(a,0)`.  The
    empty prefix counts, so `ceiling` is never negative. -/
@[expose] public def ceilingFn [Amount A] : Seg A → Int
  | ConsList.wrap _ => 0
  | ConsList.cons a x => max (Amount.amount a + ceilingFn x) 0

/-- **van-defn**: `floor ≜ Λ(prefix sum) est(≤)`, the lowest the balance reaches — the book's
    `⦇[zero,omin plus]⦈`. -/
@[expose] public def floorFn [Amount A] : Seg A → Int
  | ConsList.wrap _ => 0
  | ConsList.cons a x => min (Amount.amount a + floorFn x) 0

/-- `ceiling : [A] ⟶ Int` as an arrow, the graph of `ceilingFn` — the note's `ceiling` cell. -/
@[expose] public def ceiling [Amount A] : dList A ⟶ (⟨Int⟩ : RelSet.{0}) :=
  graph (ceilingFn)

/-- `floor : [A] ⟶ Int` as an arrow, the graph of `floorFn`. -/
@[expose] public def floor [Amount A] : dList A ⟶ (⟨Int⟩ : RelSet.{0}) :=
  graph (floorFn)

public theorem ceilingFn_nonneg [Amount A] : ∀ x : Seg A, 0 ≤ ceilingFn x
  | ConsList.wrap _ => Int.le_refl 0
  | ConsList.cons a x => by simp only [ceilingFn]; omega

public theorem floorFn_nonpos [Amount A] : ∀ x : Seg A, floorFn x ≤ 0
  | ConsList.wrap _ => Int.le_refl 0
  | ConsList.cons a x => by simp only [floorFn]; omega

/-- **van-defn**: `secure`, the stretches one van visit can serve — the book's p.185
    `bmax(ceiling x, ceiling x − floor x) ≤ N`, which says some starting reserve keeps the cash
    between `0` and `N` throughout. -/
@[expose] public def secureP [Amount A] [Van] (xs : Seg A) : Prop :=
  max (ceilingFn xs) (ceilingFn xs - floorFn xs) ≤ N

public instance decSecureP [Amount A] [Van] (x : Seg A) :
    Decidable (secureP x) := Int.decLe _ _

/-- **van-defn**: `secure` as a coreflexive on stretches. -/
@[expose] public def secure [Amount A] [Van] : dList A ⟶ dList A :=
  corefl (secureP)

public theorem secure_coreflexive [Amount A] [Van] : Coreflexive (secure (A := A)) :=
  le_iff.mpr fun _ _ h => h.1

/-! ### `secure` is the coreflexive of the book's p.185 test -/

/-- **van-secure**: `⟨ceiling,ceiling−floor⟩`, the pair the p.185 predicate compares. -/
@[expose] public def «⟨ceiling,ceiling−floor⟩» [Amount A] : dList A ⟶ (⟨Int × Int⟩ : RelSet.{0}) :=
  graph fun (x : Seg A) => (ceilingFn x, ceilingFn x - floorFn x)

/-- **van-secure**: `bmax`, the larger of the two. -/
@[expose] public def bmax : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := graph fun p => max p.1 p.2

/-- **van-secure**: `≤N`, the coreflexive on `Int` the test has to land in. -/
@[expose] public def «≤N» [Van] : (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := fun a b => a = b ∧ a ≤ N

/-- **van-secure**: `secure⟨ceiling,ceiling−floor⟩bmax=⟨ceiling,ceiling−floor⟩bmax(≤N)` (book p.185).
    The test is a map, so sliding the coreflexive across it says exactly that `secure` holds at the
    stretches whose test value is at most `N` — which is what "the coreflexive corresponding to this
    predicate" means. -/
public theorem secure_bmax [Amount A] [Van] :
    secure (A := A) ≫ «⟨ceiling,ceiling−floor⟩» ≫ bmax = «⟨ceiling,ceiling−floor⟩» ≫ bmax ≫ «≤N» := by
  apply hom_ext; intro x n
  constructor
  · rintro ⟨y, ⟨rfl, hs⟩, p, rfl, rfl⟩
    exact ⟨_, rfl, _, rfl, rfl, hs⟩
  · rintro ⟨p, rfl, m, rfl, rfl, hle⟩
    exact ⟨x, ⟨rfl, hle⟩, _, rfl, rfl⟩

/-! ### `secure` is prefix-closed, and closed under dropping the first transaction -/

public theorem ceilingFn_mono [Amount A] :
    ∀ {p x : Seg A}, prefixP p x → ceilingFn p ≤ ceilingFn x
  | ConsList.wrap _, x, _ => ceilingFn_nonneg x
  | ConsList.cons _ _, ConsList.wrap _, h => False.elim h
  | ConsList.cons a p, ConsList.cons b x, h => by
    obtain ⟨rfl, hp⟩ := h
    have hih := ceilingFn_mono hp
    simp only [ceilingFn]; omega

public theorem floorFn_anti [Amount A] :
    ∀ {p x : Seg A}, prefixP p x → floorFn x ≤ floorFn p
  | ConsList.wrap _, x, _ => floorFn_nonpos x
  | ConsList.cons _ _, ConsList.wrap _, h => False.elim h
  | ConsList.cons a p, ConsList.cons b x, h => by
    obtain ⟨rfl, hp⟩ := h
    have hih := floorFn_anti hp
    simp only [floorFn]; omega

/-- **`secure` is prefix-closed** (book p.185): a prefix reaches neither as high nor as low. -/
public theorem secureP_prefix [Amount A] [Van] {p x : Seg A} (h : prefixP p x) (hs : secureP x) :
    secureP p := by
  have hc : ceilingFn p ≤ ceilingFn x := ceilingFn_mono h
  have hf : floorFn x ≤ floorFn p := floorFn_anti h
  have hcp := ceilingFn_nonneg p
  have hfp := floorFn_nonpos p
  simp only [secureP] at hs ⊢
  omega

/-- **van-laws**, the fusion row's stated side condition: `secure prefix ⊑ prefix secure`. -/
public theorem secure_prefix [Amount A] [Van] :
    secure ≫ «prefix» ⊑ («prefix» : dList A ⟶ dList A) ≫ secure :=
  le_iff.mpr fun x p h => by
    obtain ⟨y, ⟨rfl, hs⟩, hp⟩ := h
    exact ⟨p, hp, rfl, secureP_prefix hp hs⟩

/-- **What the fusion actually needs**: dropping the FIRST transaction of a secure stretch
    leaves a secure stretch — one step of the suffix-closure the book proves on p.188. -/
public theorem secureP_tail [Amount A] [Van] {a : A} {x : Seg A} (h : secureP (ConsList.cons a x)) :
    secureP x := by
  have hc := ceilingFn_nonneg x
  have hf := floorFn_nonpos x
  simp only [secureP, ceilingFn, floorFn] at h ⊢
  omega

/-! ### The orders `R`, `H`, `R;H` and `|R|` -/

/-- **van-defn**: `R ≜ length ≤ length°` — fewer van visits is better. -/
@[expose] public def R {A : Type} : dSched A ⟶ dSched A := fun p q => clen p ≤ clen q

/-- `R = length ≤ length°`, point-free. -/
public theorem R_eq :
    R (A := A) = graph (fun xss : Sched A => (clen xss : Int)) ≫ leq
      ≫ (graph (fun xss : Sched A => (clen xss : Int)) : dSched A ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro p q
  constructor
  · intro h
    exact ⟨(clen p : Int), rfl, (clen q : Int), Int.ofNat_le.mpr h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    have h1 : m = (clen p : Int) := hm
    have h2 : n = (clen q : Int) := hn
    subst h1
    subst h2
    exact Int.ofNat_le.mp hmn

/-- `head : Seg ⟵ Sched`, a partial map — the empty schedule has no first segment. -/
@[expose] public def head {A : Type} : dSched A ⟶ (⟨Seg A⟩ : RelSet.{0}) :=
  fun p s => ∃ t, p = ConsList.cons s t

-- THE ONE-POINT OBJECT IS THE NOTE'S `𝟏`, and an object a picture labels has to be written the
-- way the picture writes it.  A NOTATION and not an abbreviation: `𝟏` is a bold digit, which is
-- no Lean identifier.
notation:max "𝟏" => Freyd.Alg.RelSet.CL.dL Unit

/-- **van-defn**: `H ≜ (head prefix° head°)∪(nil° nil)` — `nil` being `wrapR` out of the one
    point `𝟏`, so `nil° nil` is the coreflexive on the empty schedule. -/
@[expose] public def H {A : Type} : dSched A ⟶ dSched A :=
  (head (A := A) ≫ («prefix» : dList A ⟶ dList A)° ≫ (head (A := A))°) ∪ ((τ : 𝟏 ⟶ dSched A)° ≫ τ)

/-- `H` pointwise: one schedule's first segment is a prefix of the other's, or both are empty. -/
public theorem Hrel_apply {p q : Sched A} :
    H (A := A) p q ↔ (∃ s t s' t', p = ConsList.cons s t ∧ q = ConsList.cons s' t' ∧ prefixP s s')
      ∨ (p = ConsList.wrap () ∧ q = ConsList.wrap ()) := by
  constructor
  · rintro (⟨s, ⟨t, hp⟩, s', hpre, ⟨t', hq⟩⟩ | ⟨u, hp, hq⟩)
    · exact Or.inl ⟨s, t, s', t', hp, hq, hpre⟩
    · exact Or.inr ⟨hp, hq⟩
  · rintro (⟨s, t, s', t', hp, hq, hpre⟩ | ⟨hp, hq⟩)
    · exact Or.inl ⟨s, ⟨t, hp⟩, s', hpre, ⟨t', hq⟩⟩
    · exact Or.inr ⟨(), hp, hq⟩

/-- **van-defn**: `R;H ≜ R∩(R°⇒H)` — strictly shorter, or the same length with the first
    segment a prefix of the other's. -/
@[expose] public def «R;H» {A : Type} : dSched A ⟶ dSched A := fun p q =>
  clen p ≤ clen q ∧ (clen q ≤ clen p → H (A := A) p q)

/-- `R;H = R ∩ (R° ⇒ H)`, the book's p.187 definition of the refined order. -/
public theorem RH_eq : «R;H» (A := A) = R (A := A) ∩ ((R (A := A))° ⇨ H (A := A)) := by
  apply le_antisymm
  · refine le_inter (le_iff.mpr fun p q h => h.1) ((le_impl_iff _ _ _).mpr ?_)
    exact le_iff.mpr fun p q h => h.1.2 h.2
  · refine le_iff.mpr fun p q h => ⟨h.1, fun hle => ?_⟩
    exact le_iff.mp (impl_cancel ((R (A := A))°) (H (A := A))) p q ⟨h.2, hle⟩

/-- **van-defn**: `|R| ≜ R∩¬R°`, the strict part `R` splits into. -/
@[expose] public def «|R|» {A : Type} : dSched A ⟶ dSched A := fun xss yss => clen xss < clen yss

/-- **van-defn**: `R∩H` — no longer, AND with the first segment a prefix of the other's.  The §7.5
    displays draw it as ONE bead, so it is one arrow here: a bead is an arrow, and an arrow the note
    hangs a naturality verdict on needs a declaration to hang it from. -/
@[expose] public def RinterH {A : Type} : dSched A ⟶ dSched A := R (A := A) ∩ H (A := A)

/-- **van-mono**, second row: `R;H = |R|∪(R∩H)` — the split the monotonicity proof
    distributes over.  It is also all the certification `|R| ≜ R∩¬R°` gets: the allegory
    carries no complement, so the strict part is named by this equation rather than by `¬`. -/
public theorem RH_eq_strict : «R;H» (A := A) = «|R|» (A := A) ∪ RinterH (A := A) := by
  apply hom_ext; intro p q
  constructor
  · rintro ⟨hle, hH⟩
    rcases Nat.lt_or_ge (clen p) (clen q) with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr ⟨hle, hH hge⟩
  · rintro (hlt | ⟨hle, hH⟩)
    · exact ⟨Nat.le_of_lt hlt, fun hge => absurd hge (Nat.not_le_of_lt hlt)⟩
    · exact ⟨hle, fun _ => hH⟩

public theorem RH_le_R : «R;H» (A := A) ⊑ R (A := A) := le_iff.mpr fun _ _ h => h.1

public theorem RH_refl : 𝟙 (dSched A) ⊑ «R;H» (A := A) :=
  le_iff.mpr fun p q h => by
    obtain rfl : p = q := h
    refine ⟨Nat.le_refl _, fun _ => ?_⟩
    cases p with
    | wrap u => exact Hrel_apply.mpr (Or.inr ⟨rfl, rfl⟩)
    | cons s t => exact Hrel_apply.mpr (Or.inl ⟨s, t, s, t, rfl, rfl, prefixP.refl s⟩)

public theorem RH_trans : «R;H» (A := A) ≫ «R;H» (A := A) ⊑ «R;H» (A := A) :=
  le_iff.mpr fun p r h => by
    obtain ⟨q, ⟨h1, hH1⟩, ⟨h2, hH2⟩⟩ := h
    refine ⟨Nat.le_trans h1 h2, fun hle => ?_⟩
    have e1 : clen q ≤ clen p := Nat.le_trans h2 hle
    have e2 : clen r ≤ clen q := Nat.le_trans hle h1
    rcases Hrel_apply.mp (hH1 e1) with ⟨s, t, s', t', hp, hq, hpr⟩ | ⟨hp, hq⟩
    · rcases Hrel_apply.mp (hH2 e2) with ⟨u, v, u', v', hq', hr, hpr'⟩ | ⟨hq', -⟩
      · rw [hq] at hq'
        injection hq' with hsu htv
        subst hsu
        subst htv
        exact Hrel_apply.mpr (Or.inl ⟨s, t, u', v', hp, hr, prefixP.trans hpr hpr'⟩)
      · rw [hq] at hq'; nomatch hq'
    · rcases Hrel_apply.mp (hH2 e2) with ⟨u, v, u', v', hq', -, -⟩ | ⟨-, hr⟩
      · rw [hq] at hq'; nomatch hq'
      · exact Hrel_apply.mpr (Or.inr ⟨hp, hr⟩)

public theorem R_recip_trans : (R (A := A))° ≫ (R (A := A))° ⊑ (R (A := A))° :=
  le_iff.mpr fun p r h => by
    obtain ⟨q, h1, h2⟩ := h
    exact Nat.le_trans (h2 : clen r ≤ clen q) (h1 : clen q ≤ clen p)

/-! ### `new`, `glue`, `old`, `ok` and the two algebras -/

/-- **van-defn**: `new ≜ (wrap×𝟙) cons` — the transaction opens a segment of its own. -/
@[expose] public def newFn (p : A × Sched A) : Sched A :=
  ConsList.cons (ConsList.cons p.1 (ConsList.wrap ())) p.2

@[expose] public def new {A : Type} : (⟨A × Sched A⟩ : RelSet.{0}) ⟶ dSched A :=
  graph newFn

/-- **van-defn**: `glue ≜ (𝟙×cons°) assocl (cons×𝟙) cons` — the transaction goes on the front
    of the first segment, so the schedule must have one. -/
@[expose] public def glue {A : Type} : (⟨A × Sched A⟩ : RelSet.{0}) ⟶ dSched A :=
  fun p yss => ∃ xs xss, p.2 = ConsList.cons xs xss ∧ yss = ConsList.cons (ConsList.cons p.1 xs) xss

/-- **van-defn**: `ok`, the test the final program runs — the schedule is non-empty and
    `[a]⧺head xs` is secure. -/
@[expose] public def okR [Amount A] [Van] :
    (⟨A × Sched A⟩ : RelSet.{0}) ⟶ ⟨A × Sched A⟩ := fun p q =>
  p = q ∧ ∃ xs xss, p.2 = ConsList.cons xs xss ∧ secureP (ConsList.cons p.1 xs)

/-- **van-defn**: `old ≜ (𝟙×cons°) assocl ((cons secure)×𝟙) cons` — `glue` restricted to a
    first segment that stays secure. -/
@[expose] public def old [Amount A] [Van] :
    (⟨A × Sched A⟩ : RelSet.{0}) ⟶ dSched A := fun p yss =>
  ∃ xs xss, p.2 = ConsList.cons xs xss ∧ yss = ConsList.cons (ConsList.cons p.1 xs) xss
    ∧ secureP (ConsList.cons p.1 xs)

/-- **van-laws**, the last row's reason read as an equation: `ok` is exactly where `old`
    returns anything, so `old = ok glue`. -/
public theorem old_eq_ok_glue [Amount A] [Van] : old = okR ≫ glue (A := A) := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · rintro ⟨s, t, hx, hr, hsec⟩
    exact ⟨(a, x), ⟨rfl, s, t, hx, hsec⟩, s, t, hx, hr⟩
  · rintro ⟨q, ⟨hq, s, t, hx, hsec⟩, s', t', hx', hr⟩
    obtain rfl : q = (a, x) := hq.symm
    rw [hx] at hx'
    injection hx' with h1 h2
    subst h1
    subst h2
    exact ⟨s, t, hx, hr, hsec⟩

/-- **`old` is NO map**: at the empty schedule it returns nothing — `old` has to glue the
    transaction onto a FIRST SEGMENT, and there is none — so it is not entire.  `old_eq_ok_glue`
    says where it does return: on `ok`.  The note must therefore draw `old` chamfered, not as a
    rectangle. -/
public theorem old_not_map [Amount A] [Van] (a : A) : ¬ Map (old (A := A)) := by
  intro h
  obtain ⟨_, s, t, hx, _⟩ := entire_total h.1 (a, ConsList.wrap ())
  cases hx

/-! ### `new`, `glue`, `old` point-free, as B&dM write them on p.185 -/

/-- The re-bracketing B&dM write as `assocl` (p.185); the note's pictures draw nothing for it,
    a product being flat there. -/
@[expose] public def assocl {A B C : Type} :
    (⟨A × B × C⟩ : RelSet.{0}) ⟶ ⟨(A × B) × C⟩ := graph fun p => ((p.1, p.2.1), p.2.2)

/-- **`assocl` is STRICTLY natural** in all three arguments: `(S×(list S×list(list S))) assocl =
    assocl ((S×list S)×list(list S))`.  Re-bracketing looks at no element and discards none, so
    both sides relate `(a,(s,x))` to `((b,t),y)` exactly when `S a b`, `list S s t` and
    `list(list S) x y`. -/
public theorem assocl_natural :
    StrictNatural
      (Relator.prod (Relator.prod (Relator.idRelator RelSet.{0}) listRelator) schedRelator)
      (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.prod listRelator schedRelator))
      (fun a => assocl (A := a.carrier) (B := Seg a.carrier) (C := Sched a.carrier)) := by
  intro x y S
  simp only [Relator.prod, prodMap_eq_rprodMap]
  apply hom_ext; rintro ⟨a, s, u⟩ q
  constructor
  · rintro ⟨⟨a', s', u'⟩, ⟨hS, hs, hu⟩, rfl⟩
    exact ⟨((a, s), u), rfl, ⟨hS, hs⟩, hu⟩
  · rintro ⟨m, rfl, hm⟩
    exact ⟨(q.1.1, q.1.2, q.2), ⟨hm.1.1, hm.1.2, hm.2⟩, rfl⟩

/-- **van-defn**: `new = (wrap×𝟙) cons` (book p.185) — the transaction becomes a segment of its
    own, and that segment is consed onto the schedule. -/
public theorem new_eq :
    new (A := A) = rprodMap (τₗ () : dE A ⟶ dList A) (𝟙 (dSched A)) ≫ consR := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · intro h
    obtain rfl : r = ConsList.cons (ConsList.cons a (ConsList.wrap ())) x := h
    exact ⟨(ConsList.cons a (ConsList.wrap ()), x), ⟨rfl, rfl⟩, rfl⟩
  · rintro ⟨⟨s, y⟩, ⟨hs, hy⟩, hr⟩
    obtain rfl : s = ConsList.cons a (ConsList.wrap ()) := hs
    obtain rfl : x = y := hy
    exact hr

/-- **van-defn**: `glue = (𝟙×cons°) assocl (cons×𝟙) cons` (book p.185) — `cons°` splits the
    schedule into its first segment and the rest, the transaction goes on the front of that
    segment, and the lengthened segment is consed back on. -/
public theorem glue_eq :
    glue (A := A) = rprodMap (𝟙 (dE A)) ((consR : (⟨Seg A × Sched A⟩ : RelSet.{0}) ⟶ dSched A)°)
      ≫ assocl
      ≫ rprodMap (consR : (⟨A × Seg A⟩ : RelSet.{0}) ⟶ dList A) (𝟙 (dSched A))
      ≫ consR := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · rintro ⟨s, t, hx, hr⟩
    exact ⟨(a, s, t), ⟨rfl, hx⟩, ((a, s), t), rfl, (ConsList.cons a s, t), ⟨rfl, rfl⟩, hr⟩
  · rintro ⟨⟨a', s, t⟩, ⟨ha, hx⟩, w, hw, ⟨u, v⟩, ⟨hu, hv⟩, hr⟩
    obtain rfl : a = a' := ha
    obtain rfl : w = ((a, s), t) := hw
    obtain rfl : u = ConsList.cons a s := hu
    obtain rfl : t = v := hv
    exact ⟨s, t, hx, hr⟩

/-- **van-defn**: `old = (𝟙×cons°) assocl ((cons secure)×𝟙) cons` (book p.185) — `glue` with the
    lengthened first segment required to stay secure. -/
public theorem old_eq [Amount A] [Van] :
    old
      = rprodMap (𝟙 (dE A)) ((consR : (⟨Seg A × Sched A⟩ : RelSet.{0}) ⟶ dSched A)°)
        ≫ assocl
        ≫ rprodMap ((consR : (⟨A × Seg A⟩ : RelSet.{0}) ⟶ dList A) ≫ secure)
            (𝟙 (dSched A))
        ≫ consR := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · rintro ⟨s, t, hx, hr, hsec⟩
    exact ⟨(a, s, t), ⟨rfl, hx⟩, ((a, s), t), rfl, (ConsList.cons a s, t),
      ⟨⟨ConsList.cons a s, rfl, rfl, hsec⟩, rfl⟩, hr⟩
  · rintro ⟨⟨a', s, t⟩, ⟨ha, hx⟩, w, hw, ⟨u, v⟩, ⟨⟨z, hz, hzu, hsec⟩, hv⟩, hr⟩
    obtain rfl : a = a' := ha
    obtain rfl : w = ((a, s), t) := hw
    obtain rfl : z = ConsList.cons a s := hz
    obtain rfl : u = ConsList.cons a s := hzu.symm
    obtain rfl : t = v := hv
    exact ⟨s, t, hx, hr, hsec⟩

/-- **van-defn**: `S ≜ [nil,new∪old]`, the algebra whose fold is every splitting of the
    transactions into secure segments. -/
@[expose] public def S [Amount A] [Van] :
    Alg (F Unit A) (dSched A) :=
  junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
    (new (A := A) ∪ old)

/-- **van-defn**: `ok` as the BOOLEAN the final program tests — the schedule has a first segment
    and `[a]⧺head` stays secure — `okR` as a boolean, which is the form a branch can test and so
    the form the picture reads the test off. -/
@[expose] public def ok [Amount A] [Van] : A × Sched A → Bool
  | (_, ConsList.wrap _) => false
  | (a, ConsList.cons s _) => decide (secureP (ConsList.cons a s))

/-- **van-defn**: `glue` as a MAP.  `glue` returns nothing at the empty schedule, and a branch of
    `progFn` has to return something there; `ok` is false exactly there, so the value is never
    taken and the empty schedule is what it is. -/
@[expose] public def glueFn : A × Sched A → Sched A
  | (_, ConsList.wrap _) => ConsList.wrap ()
  | (a, ConsList.cons s t) => ConsList.cons (ConsList.cons a s) t

/-- **van-laws**, the final program's algebra `[nil,(ok→glue,new)]`: glue the transaction onto
    the open segment wherever that segment stays secure, and call the van where it does not. -/
@[expose] public def progFn [Amount A] [Van] (p : A × Sched A) : Sched A :=
  match ok p with
  | true  => glueFn p
  | false => newFn p

public theorem okP_cons [Amount A] [Van] {a : A} {s : Seg A} {t : Sched A} :
    ok (a, ConsList.cons s t) = decide (secureP (ConsList.cons a s)) := rfl

/-- `ok` holds, so the transaction is glued onto the first segment. -/
public theorem progFn_pos [Amount A] [Van] {a : A} {s : Seg A} {t : Sched A}
    (h : secureP (ConsList.cons a s)) :
    progFn (a, ConsList.cons s t) = ConsList.cons (ConsList.cons a s) t := by
  unfold progFn; rw [okP_cons, decide_eq_true h]; rfl

/-- `ok` fails, so the van is called: the transaction opens a segment of its own. -/
public theorem progFn_neg [Amount A] [Van] {a : A} {s : Seg A} {t : Sched A}
    (h : ¬ secureP (ConsList.cons a s)) :
    progFn (a, ConsList.cons s t) = newFn (a, ConsList.cons s t) := by
  unfold progFn; rw [okP_cons, decide_eq_false h]

/-- The empty schedule has no first segment, so `ok` fails there too. -/
public theorem progFn_wrap [Amount A] [Van] {a : A} {D : Unit} :
    progFn (a, ConsList.wrap D) = newFn (a, ConsList.wrap D) := rfl

@[expose] public def progAlg [Amount A] [Van] :
    Alg (F Unit A) (dSched A) :=
  junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
    (graph (progFn))

/-- **van-laws**, the greedy fold `⦇S%∋ est(R;H)⦈` the note's §13.4 draws: at each transaction
    `S` offers both the new segment and the glued one, and `est(R;H)` keeps the `R;H`-least. -/
@[expose] public def greedyFold [Amount A] [Van] : dList A ⟶ dSched A :=
  ⦇Λ S ≫ est («R;H» (A := A))⦈

/-! ## `van-defn`'s fusion: `partition list(secure) = ⦇S⦈` -/

/-- Every segment of the schedule is secure. -/
@[expose] public def allSecureP [Amount A] [Van] : Sched A → Prop
  | ConsList.wrap _ => True
  | ConsList.cons s p => secureP s ∧ allSecureP p

public theorem listP_secure_iff [Amount A] [Van] : ∀ ps r : Sched A,
    listP secure ps r ↔ (ps = r ∧ allSecureP ps)
  | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => ⟨rfl, trivial⟩, fun _ => rfl⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨fun h => False.elim h, fun h => nomatch h.1⟩
  | ConsList.cons _ _, ConsList.wrap _ => ⟨fun h => False.elim h, fun h => nomatch h.1⟩
  | ConsList.cons s p, ConsList.cons s' r => by
    show (secure s s' ∧ listP secure p r) ↔ _
    rw [listP_secure_iff p r]
    constructor
    · rintro ⟨⟨rfl, hs⟩, rfl, hall⟩
      exact ⟨rfl, hs, hall⟩
    · rintro ⟨heq, hs, hall⟩
      injection heq with h1 h2
      subst h1
      subst h2
      exact ⟨⟨rfl, hs⟩, rfl, hall⟩

public theorem partSecure_apply [Amount A] [Van] (x : Seg A) (r : Sched A) :
    (partition ≫ list secure) x r
      ↔ (cconcat r = x ∧ allNonempty r ∧ allSecureP r) := by
  constructor
  · rintro ⟨ps, ⟨hcat, hne⟩, hlist⟩
    obtain ⟨rfl, hall⟩ := (listP_secure_iff ps r).mp hlist
    exact ⟨hcat, hne, hall⟩
  · rintro ⟨hcat, hne, hall⟩
    exact ⟨r, ⟨hcat, hne⟩, (listP_secure_iff r r).mpr ⟨rfl, hall⟩⟩

public theorem eq_nil_of_cconcat_nil : ∀ r : Sched A,
    cconcat r = ConsList.wrap () → allNonempty r → r = ConsList.wrap ()
  | ConsList.wrap _, _, _ => rfl
  | ConsList.cons s p, h, hn => by
    cases s with
    | wrap _ => exact False.elim hn.1
    | cons b s' => simp [cconcat, cappend] at h

-- The algebra `[nil,new ∪ glue]` is spelled out at each of its three occurrences instead of being
-- named: a name prints as the name, and the note's fusion row is about WHAT the fold folds.
/-- **`partition = ⦇[nil,new ∪ glue]⦈`** (book p.185): cutting the transactions into non-empty
    segments is the fold that either opens a segment of its own for the head transaction (`new`)
    or puts it on the front of the segment already there (`glue`). -/
public theorem partition_cata :
    (partition : dList A ⟶ dSched A)
      = ⦇(junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
            (new (A := A) ∪ glue (A := A)) : Alg (F Unit A) (dSched A))⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp ((cata_square_junc_iff _ _ _).mpr ⟨?_, ?_⟩)
  · intro D r
    show (cconcat r = ConsList.wrap D ∧ allNonempty r) ↔ r = ConsList.wrap D
    constructor
    · rintro ⟨hcat, hne⟩
      exact eq_nil_of_cconcat_nil r hcat hne
    · intro h
      obtain rfl : r = ConsList.wrap D := h
      exact ⟨rfl, trivial⟩
  · intro a x r
    show (cconcat r = ConsList.cons a x ∧ allNonempty r)
      ↔ ∃ y, (cconcat y = x ∧ allNonempty y) ∧ (new (A := A) ∪ glue (A := A)) (a, y) r
    constructor
    · rintro ⟨hcat, hne⟩
      cases r with
      | wrap _ => simp [cconcat] at hcat
      | cons s p =>
        cases s with
        | wrap _ => exact False.elim hne.1
        | cons b s' =>
          simp only [cconcat, cappend] at hcat
          injection hcat with hba hcat'
          subst hba
          cases s' with
          | wrap _ =>
            refine ⟨p, ⟨hcat', hne.2⟩, Or.inl ?_⟩
            show ConsList.cons (ConsList.cons b (ConsList.wrap ())) p = newFn (b, p)
            rfl
          | cons c s'' =>
            exact ⟨ConsList.cons (ConsList.cons c s'') p, ⟨hcat', trivial, hne.2⟩,
              Or.inr ⟨ConsList.cons c s'', p, rfl, rfl⟩⟩
    · rintro ⟨y, ⟨hcat, hne⟩, hS⟩
      cases hS with
      | inl hS =>
        obtain rfl : r = newFn (a, y) := hS
        refine ⟨?_, trivial, hne⟩
        show cappend (ConsList.cons a (ConsList.wrap ())) (cconcat y) = ConsList.cons a x
        simp only [cappend]
        rw [hcat]
      | inr hS =>
        obtain ⟨s, t, hy, hr⟩ := hS
        subst hy
        subst hr
        refine ⟨?_, trivial, hne.2⟩
        show cappend (ConsList.cons a s) (cconcat t) = ConsList.cons a x
        simp only [cappend]
        rw [show cappend s (cconcat t) = x from hcat]

/-- **The fusion condition** (book p.185, `R S = (F S) Q` at `R = [nil,new ∪ glue]`,
    `S = list(secure)`, `Q = [nil,new ∪ old]`): testing every segment for security AFTER the
    algebra is testing it BEFORE — `glue` becomes `old` because a segment the head is glued onto
    is secure once the longer one is (`secureP_tail`), and the one-transaction segment `new`
    opens is secure by the book's standing assumption (`hsingle`). -/
public theorem van_fusion_cond [Amount A] [Van]
    (hsingle : ∀ a : A, secureP (ConsList.cons a (ConsList.wrap ()))) :
    (junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
          (new (A := A) ∪ glue (A := A)) : Alg (F Unit A) (dSched A))
        ≫ list secure
      = (F Unit A).map (list secure) ≫ S := by
  have hnil : (τ : dL Unit ⟶ dSched A) ≫ list secure = τ := by
    apply hom_ext; intro d r
    constructor
    · rintro ⟨s, hs, hlist⟩
      obtain rfl : s = ConsList.wrap d := hs
      show r = ConsList.wrap d
      exact ((listP_secure_iff (ConsList.wrap d) r).mp hlist).1.symm
    · intro h
      obtain rfl : r = ConsList.wrap d := h
      exact ⟨ConsList.wrap d, rfl, (listP_secure_iff _ _).mpr ⟨rfl, trivial⟩⟩
  have hstep : (new (A := A) ∪ glue (A := A)) ≫ list secure
      = rprodMap (𝟙 (dE A)) (list secure) ≫ (new (A := A) ∪ old) := by
    apply hom_ext; rintro ⟨a, y⟩ r
    constructor
    · rintro ⟨z, hz, hlist⟩
      cases hz with
      | inl hz =>
        obtain rfl : z = newFn (a, y) := hz
        obtain ⟨rfl, hall⟩ := (listP_secure_iff _ r).mp hlist
        exact ⟨(a, y), ⟨rfl, (listP_secure_iff y y).mpr ⟨rfl, hall.2⟩⟩, Or.inl rfl⟩
      | inr hz =>
        obtain ⟨s, t, hy, hr⟩ := hz
        subst hy
        subst hr
        obtain ⟨rfl, hall⟩ := (listP_secure_iff _ r).mp hlist
        exact ⟨(a, ConsList.cons s t),
          ⟨rfl, (listP_secure_iff _ _).mpr ⟨rfl, secureP_tail hall.1, hall.2⟩⟩,
          Or.inr ⟨s, t, rfl, rfl, hall.1⟩⟩
    · rintro ⟨⟨b, y'⟩, ⟨hab, hy'⟩, hS⟩
      obtain rfl : a = b := hab
      obtain ⟨rfl, hall⟩ := (listP_secure_iff y y').mp hy'
      cases hS with
      | inl hS =>
        obtain rfl : r = newFn (a, y) := hS
        exact ⟨newFn (a, y), Or.inl rfl,
          (listP_secure_iff _ _).mpr ⟨rfl, hsingle a, hall⟩⟩
      | inr hS =>
        obtain ⟨s, t, hy, hr, hsec⟩ := hS
        subst hy
        subst hr
        exact ⟨ConsList.cons (ConsList.cons a s) t, Or.inr ⟨s, t, rfl, rfl⟩,
          (listP_secure_iff _ _).mpr ⟨rfl, hsec, hall.2⟩⟩
  have hS : S
      = junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
          (new (A := A) ∪ old) := rfl
  rw [junc_comp, hS, Fmap_comp_junc, hnil, hstep]

/-- **van-laws**, the fusion row's first step: `partition` replaced by the fold it is. -/
public theorem van_spec_step1 [Amount A] [Van] :
    partition ≫ list secure
      = ⦇(junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
            (new (A := A) ∪ glue (A := A)) : Alg (F Unit A) (dSched A))⦈
          ≫ list secure := by
  rw [partition_cata]

/-- **van-laws**, the fusion row's second step: the fold law `(|R|) S = (|Q|) ⟸ R S = (F S) Q`
    (`relCata_fusion`) at the condition above absorbs `list(secure)` into the algebra. -/
public theorem van_spec_step2 [Amount A] [Van]
    (hsingle : ∀ a : A, secureP (ConsList.cons a (ConsList.wrap ()))) :
    ⦇(junc (sumCop (dL Unit) ⟨A × Sched A⟩) (τ : dL Unit ⟶ dSched A)
          (new (A := A) ∪ glue (A := A)) : Alg (F Unit A) (dSched A))⦈
        ≫ list secure
      = ⦇S⦈ :=
  relCata_fusion (initial Unit A) (van_fusion_cond hsingle)

/-- **van-defn** / **van-laws**, second row (book p.185, "appeal to fusion"):
    `partition list(secure) = ⦇[nil,new∪old]⦈` — keeping only secure segments is what turns
    `glue` into `old`.  The forward direction peels the head transaction off the first segment
    and needs the rest of it secure (`secureP_tail`); the backward direction needs the book's
    standing assumption that a single transaction is never larger than `N` (`hsingle`). -/
public theorem van_spec [Amount A] [Van]
    (hsingle : ∀ a : A, secureP (ConsList.cons a (ConsList.wrap ()))) :
    partition ≫ list (secure (A := A)) = ⦇S⦈ :=
  van_spec_step1.trans (van_spec_step2 hsingle)

/-! ## `van-mono`: (7.14) holds, (7.15) is FALSE, (7.16) and (7.17) hold on `R;H` -/

/-- **(7.14)'s first step** (book p.186, "since `cons` is monotonic on `R` (exercise)"):
    `(𝟙×R)cons ⊑ cons R` — consing a segment onto the shorter of two schedules leaves the
    shorter schedule, both sides having gained exactly one segment. -/
public theorem cons_mono_R :
    rprodMap (𝟙 (⟨Seg A⟩ : RelSet.{0})) (R (A := A))
        ≫ (consR : (⟨Seg A × Sched A⟩ : RelSet.{0}) ⟶ dSched A)
      ⊑ consR ≫ R (A := A) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hss, hR⟩, hcons⟩ := h
    obtain ⟨s, x⟩ := u
    obtain ⟨s', y⟩ := v
    obtain rfl : r = ConsList.cons s' y := hcons
    obtain rfl : s = s' := hss
    refine ⟨ConsList.cons s x, rfl, ?_⟩
    show clen x + 1 ≤ clen y + 1
    have : clen x ≤ clen y := hR
    omega

/-- **(7.14)'s second step** (book p.186, "definition of `new`"): `(𝟙×R)new = (wrap×R)cons` —
    `new` IS `(wrap×𝟙)cons` (`new_eq`), and the `R` on the second component slides past the
    `wrap` on the first, the two acting on disjoint halves of the pair. -/
public theorem new_eq_cons :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (R (A := A)) ≫ new (A := A)
      = rprodMap (τₗ () : dE A ⟶ dList A) (R (A := A))
        ≫ (consR : (⟨Seg A × Sched A⟩ : RelSet.{0}) ⟶ dSched A) := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · rintro ⟨⟨b, y⟩, ⟨hab, hR⟩, hnew⟩
    obtain rfl : a = b := hab
    obtain rfl : r = newFn (a, y) := hnew
    exact ⟨(ConsList.cons a (ConsList.wrap ()), y), ⟨rfl, hR⟩, rfl⟩
  · rintro ⟨⟨s, y⟩, ⟨hs, hR⟩, hr⟩
    obtain rfl : s = ConsList.cons a (ConsList.wrap ()) := hs
    exact ⟨(a, y), ⟨rfl, hR⟩, hr⟩

/-- **@van-714's second step**: `(wrap×R)cons ⊑ new R` — the `R` on the schedule half moves
    below the `cons`, which lengthens both sides by one segment.  The chain's FIRST step is
    `new_eq_cons`, which already states `(𝟙×R)new = (wrap×R)cons`. -/
public theorem van_7_14_step2 :
    rprodMap (τₗ () : dE A ⟶ dList A) (R (A := A))
        ≫ (consR : (⟨Seg A × Sched A⟩ : RelSet.{0}) ⟶ dSched A)
      ⊑ new (A := A) ≫ R (A := A) := by
  rw [← new_eq_cons]
  exact le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hR⟩, hnew⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : r = newFn (b, y) := hnew
    obtain rfl : a = b := hab
    refine ⟨newFn (a, x), rfl, ?_⟩
    show clen x + 1 ≤ clen y + 1
    have : clen x ≤ clen y := hR
    omega

/-- **(7.14)** (book p.186): `(𝟙×R)new ⊑ (new∪old)R` — opening a segment of its own for the
    new transaction keeps the schedule no longer than opening one on a longer schedule. -/
public theorem van_7_14 [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (R (A := A)) ≫ new (A := A)
      ⊑ (new (A := A) ∪ old) ≫ R (A := A) := by
  rw [new_eq_cons]
  exact le_trans van_7_14_step2 (comp_mono_right (le_union_left _ _) _)

section

/-- The setting of the book's (7.15) witness: each transaction is its own amount, `N = 10`. -/
@[expose] public def book10 : Van := ⟨10⟩

/-- The book's transactions in the witnesses below: each is its own amount. -/
@[expose] public def bookAmount : Amount Int := ⟨fun i => i⟩

attribute [local instance] book10 bookAmount

/-- **(7.15) IS FALSE** (book p.186, and the note's `van-laws` says so): gluing the
    transaction onto a shorter schedule need not be beaten by gluing it onto this one, because
    the shorter schedule's first segment need not stay secure.

    The witness is the book's own, at `N = 10` and the transaction `0`: `[[0]]` and `[[20]]`
    are schedules of the same length, `[0]⧺[0]` is secure and `[0]⧺[20]` is not.  So `old`
    fires on the left and neither `new` (which lengthens the schedule) nor `old` (which the
    security test blocks) can answer on the right. -/
public theorem van_7_15_false :
    ¬ (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) (R (A := Int)) ≫ old (A := Int)
      ⊑ (new (A := Int) ∪ old (A := Int)) ≫ R (A := Int)) := by
  intro h
  have hsec : secureP (A := Int)
      (ConsList.cons (0 : Int) (ConsList.cons (0 : Int) (ConsList.wrap ()))) := by
    simp only [secureP, ceilingFn, floorFn, book10, bookAmount]; omega
  have hbad : ¬ secureP (A := Int)
      (ConsList.cons (0 : Int) (ConsList.cons (20 : Int) (ConsList.wrap ()))) := by
    simp only [secureP, ceilingFn, floorFn, book10, bookAmount]; omega
  have hstep := le_iff.mp h
    ((0 : Int), ConsList.cons (ConsList.cons (20 : Int) (ConsList.wrap ())) (ConsList.wrap ()))
    (ConsList.cons (ConsList.cons (0 : Int) (ConsList.cons (0 : Int) (ConsList.wrap ())))
      (ConsList.wrap ()))
    ⟨((0 : Int), ConsList.cons (ConsList.cons (0 : Int) (ConsList.wrap ())) (ConsList.wrap ())),
      ⟨rfl, Nat.le_refl 1⟩,
      ConsList.cons (0 : Int) (ConsList.wrap ()), ConsList.wrap (), rfl, rfl, hsec⟩
  obtain ⟨r', hr', hlen⟩ := hstep
  cases hr' with
  | inl hr' =>
    obtain rfl : r' = newFn ((0 : Int),
      ConsList.cons (ConsList.cons (20 : Int) (ConsList.wrap ())) (ConsList.wrap ())) := hr'
    have : (2 : Nat) ≤ 1 := hlen
    omega
  | inr hr' =>
    obtain ⟨s, t, hy, -, hsec'⟩ := hr'
    injection hy with hs ht
    subst hs
    exact hbad hsec'

end

/-- **(7.18)** (book p.187): `(𝟙×⊤)new ⊑ new H` — whatever the two second components are,
    both sides open the segment `[a]` of their own, so the two first segments are equal and
    `H` holds outright. -/
public theorem van_7_18 :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (relTop : dSched A ⟶ dSched A) ≫ new (A := A)
      ⊑ new (A := A) ≫ H (A := A) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, -⟩, hnew⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : r = newFn (b, y) := hnew
    obtain rfl : a = b := hab
    exact ⟨newFn (a, x), rfl, Hrel_apply.mpr (Or.inl ⟨ConsList.cons a (ConsList.wrap ()), x,
      ConsList.cons a (ConsList.wrap ()), y, rfl, rfl,
      prefixP.refl (ConsList.cons a (ConsList.wrap ()))⟩)⟩

/-- **(7.19)** (book p.187): `(𝟙×⊤)old ⊑ new H` — `old` leaves `[a]` at the front of the first
    segment it lengthens, and `[a]` is what `new` makes that segment, so `[a]` is a prefix of
    it whatever the two second components are. -/
public theorem van_7_19 [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (relTop : dSched A ⟶ dSched A) ≫ old
      ⊑ new (A := A) ≫ H (A := A) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, -⟩, s, t, -, hr, -⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : a = b := hab
    subst hr
    exact ⟨newFn (a, x), rfl, Hrel_apply.mpr (Or.inl ⟨ConsList.cons a (ConsList.wrap ()), x,
      ConsList.cons a s, t, rfl, rfl, ⟨rfl, prefixP.nil s⟩⟩)⟩

/-- **(7.20)** (book p.187): `(𝟙×|R|)old ⊑ new R` — `old` keeps the schedule's length, so a
    STRICTLY shorter schedule stays no longer than the one `new` builds, which is one segment
    longer than the schedule it started from. -/
public theorem van_7_20 [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («|R|» (A := A)) ≫ old ⊑ new (A := A) ≫ R (A := A) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hlt⟩, s, t, hv, hr, -⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : a = b := hab
    subst hv
    subst hr
    refine ⟨newFn (a, x), rfl, ?_⟩
    show clen x + 1 ≤ clen t + 1
    have : clen x < clen t + 1 := hlt
    omega

/-- **(7.21)** (book p.187): `(𝟙×(R∩H))old ⊑ old (R∩H)` — `H` makes the one first segment a
    prefix of the other's, so prefix-closure of `secure` (`secureP_prefix`) lets `old` fire on
    this side too, and it keeps both the length and the prefix. -/
public theorem van_7_21 [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (R (A := A) ∩ H (A := A)) ≫ old
      ⊑ old ≫ (R (A := A) ∩ H (A := A)) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hle, hH⟩, s, t, hv, hr, hsec⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : a = b := hab
    subst hv
    subst hr
    rcases Hrel_apply.mp hH with ⟨s₀, t₀, s', t', hx, hy', hpre⟩ | ⟨-, hy'⟩
    · subst hx
      injection hy' with hs ht
      subst hs
      subst ht
      have hsec₀ : secureP (ConsList.cons a s₀) :=
        secureP_prefix (show prefixP (ConsList.cons a s₀) (ConsList.cons a s) from
          ⟨rfl, hpre⟩) hsec
      exact ⟨ConsList.cons (ConsList.cons a s₀) t₀, ⟨s₀, t₀, rfl, rfl, hsec₀⟩, hle,
        Hrel_apply.mpr (Or.inl ⟨ConsList.cons a s₀, t₀, ConsList.cons a s, t, rfl, rfl, ⟨rfl, hpre⟩⟩)⟩
    · nomatch hy'

/-- **(7.19) and (7.20) intersected** (book p.187): `(𝟙×|R|)old ⊑ new (R∩H)` — `new` is a
    function, so what it is `H`-below and `R`-below it is `(R∩H)`-below, and `|R| ⊑ ⊤` feeds
    (7.19). -/
public theorem van_strict_old [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («|R|» (A := A)) ≫ old
      ⊑ new (A := A) ≫ (R (A := A) ∩ H (A := A)) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hv, hold⟩ := h
    obtain ⟨w, hw, hR⟩ :=
      le_iff.mp (van_7_20) u r ⟨v, hv, hold⟩
    obtain ⟨w', hw', hH⟩ :=
      le_iff.mp (van_7_19) u r ⟨v, ⟨hv.1, trivial⟩, hold⟩
    obtain rfl : w = newFn u := hw
    obtain rfl : w' = newFn u := hw'
    exact ⟨newFn u, rfl, hR, hH⟩

/-- **`X∩Y ⊑ X;Y`** (book p.188): a pair related by both `R` and `H` is related by the refined
    order, whose second half only has to supply `H` where `R` holds in both directions. -/
public theorem inter_le_RH : R (A := A) ∩ H (A := A) ⊑ «R;H» (A := A) :=
  le_iff.mpr fun _ _ h => ⟨h.1, fun _ => h.2⟩

/-- **@van-716's first step**: `(𝟙×(R;H))new ⊑ (𝟙×R)new` — the refined order is an order on
    schedules, `R;H ⊑ R`, and `new` is applied to it unchanged. -/
public theorem van_mono_new_step1 :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («R;H» (A := A)) ≫ new (A := A)
      ⊑ rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (R (A := A)) ≫ new (A := A) :=
  comp_mono_right (rprodMap_mono (le_iff.mpr fun _ _ h => h) RH_le_R) _

/-- **@van-716's second step**: `(𝟙×R)new ⊑ new R ∩ new H` — (7.14) as far as its `new R` line,
    and (7.18) `(𝟙×⊤)new ⊑ new H`, which `R ⊑ ⊤` feeds. -/
public theorem van_mono_new_step2 :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (R (A := A)) ≫ new (A := A)
      ⊑ (new (A := A) ≫ R (A := A)) ∩ (new (A := A) ≫ H (A := A)) :=
  le_inter
    (by rw [new_eq_cons]; exact van_7_14_step2)
    (le_trans
      (comp_mono_right
        (rprodMap_mono (le_iff.mpr fun _ _ h => h) (le_iff.mpr fun _ _ _ => trivial)) _)
      van_7_18)

/-- **@van-716's third step**: `new R ∩ new H = new (R∩H)` — `new` is a map, and a map
    distributes over `∩`. -/
public theorem van_mono_new_step3 :
    (new (A := A) ≫ R (A := A)) ∩ (new (A := A) ≫ H (A := A)) = new (A := A) ≫ RinterH (A := A) := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · rintro ⟨⟨w, hw, hR⟩, w', hw', hH⟩
    obtain rfl : w = newFn (a, x) := hw
    obtain rfl : w' = newFn (a, x) := hw'
    exact ⟨newFn (a, x), rfl, hR, hH⟩
  · rintro ⟨w, hw, hR, hH⟩
    obtain rfl : w = newFn (a, x) := hw
    exact ⟨⟨newFn (a, x), rfl, hR⟩, newFn (a, x), rfl, hH⟩

/-- **@van-716's fourth step**: `new (R∩H) ⊑ new (R;H)` — `X∩Y ⊑ X;Y`. -/
public theorem van_mono_new_step4 :
    new (A := A) ≫ RinterH (A := A) ⊑ new (A := A) ≫ «R;H» (A := A) :=
  comp_mono_left _ (show RinterH (A := A) ⊑ «R;H» (A := A) from inter_le_RH)

/-- **(7.16)** (book p.187): `(𝟙×(R;H))new ⊑ (new∪old)(R;H)` — the `new` half of the
    monotonicity on the refined order.  Both sides start `[a]`, so `H` holds outright and
    (7.18) `(𝟙×⊤)new ⊑ new H` is what carries the tie. -/
public theorem van_mono_new [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («R;H» (A := A)) ≫ new (A := A)
      ⊑ (new (A := A) ∪ old) ≫ «R;H» (A := A) :=
  calc rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («R;H» (A := A)) ≫ new (A := A)
      ⊑ rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (R (A := A)) ≫ new (A := A) := van_mono_new_step1
    _ ⊑ (new (A := A) ≫ R (A := A)) ∩ (new (A := A) ≫ H (A := A)) := van_mono_new_step2
    _ = new (A := A) ≫ RinterH (A := A) := van_mono_new_step3
    _ ⊑ new (A := A) ≫ «R;H» (A := A) := van_mono_new_step4
    _ ⊑ (new (A := A) ∪ old) ≫ «R;H» (A := A) := comp_mono_right (le_union_left _ _) _

/-- **@van-mono's first step**: `(𝟙×(R;H))old = (𝟙×|R|)old ∪ (𝟙×(R∩H))old` — `R;H = |R|∪(R∩H)`
    (`RH_eq_strict`), and both `𝟙×−` and `−≫old` distribute over `∪`. -/
public theorem van_mono_step1 [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («R;H» (A := A)) ≫ old
      = rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («|R|» (A := A)) ≫ old
        ∪ rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (RinterH (A := A)) ≫ old := by
  rw [RH_eq_strict, ← union_comp_distrib]
  congr 1
  apply hom_ext; rintro ⟨a, x⟩ ⟨b, y⟩
  constructor
  · rintro ⟨hab, hs | hi⟩
    · exact Or.inl ⟨hab, hs⟩
    · exact Or.inr ⟨hab, hi⟩
  · rintro (⟨hab, hs⟩ | ⟨hab, hi⟩)
    · exact ⟨hab, Or.inl hs⟩
    · exact ⟨hab, Or.inr hi⟩

/-- **@van-mono's second step**: `(𝟙×|R|)old ∪ (𝟙×(R∩H))old ⊑ new (R∩H) ∪ old (R∩H)` — (7.19)
    and (7.20) on the strict part, (7.21) on `R∩H`. -/
public theorem van_mono_step2 [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («|R|» (A := A)) ≫ old
        ∪ rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (RinterH (A := A)) ≫ old
      ⊑ new (A := A) ≫ RinterH (A := A) ∪ old ≫ RinterH (A := A) :=
  union_mono van_strict_old van_7_21

/-- **@van-mono's `old` operand, last link**: `old (R∩H) ⊑ old (R;H)`, the mirror of
    `van_mono_new_step4`.  The `old` lane of the display runs through this one, NOT through
    `(𝟙×|R|)old`: the strict operand crosses to `new` at `van_strict_old`. -/
public theorem van_mono_old_step4 [Amount A] [Van] :
    old ≫ RinterH (A := A) ⊑ old ≫ «R;H» (A := A) :=
  comp_mono_left _ (show RinterH (A := A) ⊑ «R;H» (A := A) from inter_le_RH)

/-- **@van-mono's third step**: `new (R∩H) ∪ old (R∩H) ⊑ new (R;H) ∪ old (R;H)` — `X∩Y ⊑ X;Y`
    on each operand. -/
public theorem van_mono_step3 [Amount A] [Van] :
    new (A := A) ≫ RinterH (A := A) ∪ old ≫ RinterH (A := A)
      ⊑ new (A := A) ≫ «R;H» (A := A) ∪ old ≫ «R;H» (A := A) :=
  union_mono van_mono_new_step4 van_mono_old_step4

/-- **@van-mono's last step with the sides the display draws**: `new (R∩H) ∪ old (R∩H) ⊑
    (new ∪ old)(R;H)` — `van_mono_step3` with the `(R;H)` factored back out of the union, which
    is the shape the row after it is drawn in. -/
public theorem van_mono_step4 [Amount A] [Van] :
    new (A := A) ≫ RinterH (A := A) ∪ old ≫ RinterH (A := A)
      ⊑ (new (A := A) ∪ old) ≫ «R;H» (A := A) :=
  calc new (A := A) ≫ RinterH (A := A) ∪ old ≫ RinterH (A := A)
      ⊑ new (A := A) ≫ «R;H» (A := A) ∪ old ≫ «R;H» (A := A) := van_mono_step3
    _ = (new (A := A) ∪ old) ≫ «R;H» (A := A) := (union_comp_distrib _ _ _).symm

/-- **van-mono** (book p.187's (7.17)): `(𝟙×(R;H))old ⊑ (new∪old)(R;H)` — gluing the
    transaction onto a better schedule for the rest gets no further than gluing it on, or
    calling the van, and bettering the whole schedule after.

    Two cases, which are the book's (7.19)-(7.21): on the strict part `|R|` the answer is
    `new`, and `[a]` is a prefix of `[a]⧺s`, so `H` holds even when the lengths come out
    equal; on `R∩H` the first segments are nested, so prefix-closure of `secure` lets `old`
    fire on this side too. -/
public theorem van_mono [Amount A] [Van] :
    rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («R;H» (A := A)) ≫ old
      ⊑ (new (A := A) ∪ old) ≫ «R;H» (A := A) :=
  calc rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («R;H» (A := A)) ≫ old
      = rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) («|R|» (A := A)) ≫ old
        ∪ rprodMap (𝟙 (⟨A⟩ : RelSet.{0})) (RinterH (A := A)) ≫ old := van_mono_step1
    _ ⊑ new (A := A) ≫ RinterH (A := A) ∪ old ≫ RinterH (A := A) := van_mono_step2
    _ ⊑ (new (A := A) ∪ old) ≫ «R;H» (A := A) := van_mono_step4

/-- **van-laws**, the greedy theorem's hypothesis: `MonotonicAlg S (R;H)`, the two halves
    `van_mono_new` (7.16) and `van_mono` (7.17) together with the `nil` case. -/
public theorem van_mono_alg [Amount A] [Van] :
    Freyd.Alg.Pres (F := F Unit A) S («R;H» (A := A)) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hS⟩ := h
    cases u with
    | inl D =>
      cases v with
      | inl d' =>
        rw [S, junc_sum_inl] at hS
        obtain rfl : r = ConsList.wrap d' := hS
        refine ⟨ConsList.wrap D, ?_, Nat.le_refl _, fun _ => Hrel_apply.mpr (Or.inr ⟨rfl, rfl⟩)⟩
        rw [S, junc_sum_inl]
        rfl
      | inr q => exact False.elim hFv
    | inr p =>
      cases v with
      | inl d' => exact False.elim hFv
      | inr q =>
        rw [S, junc_sum_inr] at hS
        have key : ((new (A := A) ∪ old) ≫ «R;H» (A := A)) p r := by
          cases hS with
          | inl hnew =>
            exact le_iff.mp (van_mono_new) p r ⟨q, hFv, hnew⟩
          | inr hold =>
            exact le_iff.mp (van_mono) p r ⟨q, hFv, hold⟩
        obtain ⟨w, hw, hRHw⟩ := key
        refine ⟨w, ?_, hRHw⟩
        rw [S, junc_sum_inr]
        exact hw

/-! ## `van-laws` -/

/-- **van-laws**, the last row: the program refines the greedy choice —
    `⦇[nil,(ok→glue,new)]⦈ ⊑ ⦇ΛS est(R;H)⦈`, because `old ⊑ new (R;H)°`: `old` returns the
    shorter result wherever it returns one, and `ok` is where it does. -/
public theorem prog_le_greedy [Amount A] [Van] :
    progAlg ⊑ Λ S ≫ est («R;H» (A := A)) := by
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- the program's answer is one of `new` and `old`
    refine le_iff.mpr fun u r h => ?_
    cases u with
    | inl D =>
      rw [progAlg, junc_sum_inl] at h
      rw [S, junc_sum_inl]
      exact h
    | inr p =>
      rw [progAlg, junc_sum_inr] at h
      rw [S, junc_sum_inr]
      obtain ⟨a, x⟩ := p
      obtain rfl : r = progFn (a, x) := h
      cases x with
      | wrap u => exact Or.inl rfl
      | cons s t =>
        refine Decidable.byCases (p := secureP (ConsList.cons a s))
          (fun hs => ?_) (fun hs => ?_)
        · refine Or.inr ⟨s, t, rfl, ?_, hs⟩
          exact progFn_pos hs
        · exact Or.inl (progFn_neg hs)
  · -- and it is `(R;H)`-at-least-as-good as every one of them
    refine le_iff.mpr fun r r' h => ?_
    obtain ⟨u, hS, hprog⟩ := h
    show «R;H» (A := A) r' r
    have hS' : S u r := hS
    cases u with
    | inl D =>
      rw [S, junc_sum_inl] at hS'
      rw [progAlg, junc_sum_inl] at hprog
      obtain rfl : r = ConsList.wrap D := hS'
      obtain rfl : r' = ConsList.wrap D := hprog
      exact ⟨Nat.le_refl _, fun _ => Hrel_apply.mpr (Or.inr ⟨rfl, rfl⟩)⟩
    | inr p =>
      rw [S, junc_sum_inr] at hS'
      rw [progAlg, junc_sum_inr] at hprog
      clear hS
      obtain ⟨a, x⟩ := p
      obtain rfl : r' = progFn (a, x) := hprog
      cases x with
      | wrap u =>
        have hr : r = newFn (a, ConsList.wrap u) := by
          cases hS' with
          | inl hnew => exact hnew
          | inr hold =>
            obtain ⟨s, t, hx, -, -⟩ := hold
            nomatch hx
        subst hr
        exact ⟨Nat.le_refl _, fun _ => Hrel_apply.mpr (Or.inl ⟨ConsList.cons a (ConsList.wrap ()),
          ConsList.wrap u, ConsList.cons a (ConsList.wrap ()), ConsList.wrap u, rfl, rfl,
          prefixP.refl _⟩)⟩
      | cons s t =>
        refine Decidable.byCases (p := secureP (ConsList.cons a s))
          (fun hs => ?_) (fun hs => ?_)
        · rw [progFn_pos hs]
          cases hS' with
          | inl hnew =>
            obtain rfl : r = newFn (a, ConsList.cons s t) := hnew
            exact ⟨Nat.le_succ _, fun hle => absurd hle (Nat.not_succ_le_self (clen t + 1))⟩
          | inr hold =>
            obtain ⟨s', t', hx, hr, -⟩ := hold
            injection hx with h1 h2
            subst h1
            subst h2
            subst hr
            exact ⟨Nat.le_refl _, fun _ => Hrel_apply.mpr (Or.inl ⟨ConsList.cons a s, t,
              ConsList.cons a s, t, rfl, rfl, prefixP.refl _⟩)⟩
        · rw [progFn_neg hs]
          have hr : r = newFn (a, ConsList.cons s t) := by
            cases hS' with
            | inl hnew => exact hnew
            | inr hold =>
              obtain ⟨s', t', hx, -, hsec⟩ := hold
              injection hx with h1 h2
              subst h1
              exact absurd hsec hs
          subst hr
          exact ⟨Nat.le_refl _, fun _ => Hrel_apply.mpr (Or.inl ⟨ConsList.cons a (ConsList.wrap ()),
            ConsList.cons s t, ConsList.cons a (ConsList.wrap ()), ConsList.cons s t,
            rfl, rfl, prefixP.refl _⟩)⟩

/-- **@van-laws' greedy row**: Theorem 7.2 at `R;H`, whose hypothesis is `van_mono_alg` and whose
    transitivity is `RH_trans`. -/
public theorem van_greedy [Amount A] [Van] :
    (⦇Λ S ≫ est («R;H» (A := A))⦈ : dList A ⟶ dSched A) ⊑ Λ ⦇S⦈ ≫ est («R;H» (A := A)) :=
  greedy (initial Unit A) RH_trans van_mono_alg

/-- **van-laws** (B&dM §7.5, p.188): the fewest secure segments the transactions can be cut
    into are one pass along them, the next transaction glued onto the open segment wherever
    that segment stays secure and the van called where it does not —
    `Λ(partition list(secure)) est(R) ⊒ ⦇[nil,(ok→glue,new)]⦈`.

    The chain is the note's: `partition list(secure) = ⦇S⦈` (`van_spec`); `R;H ⊑ R`, so
    `est(R;H) ⊑ est(R)`; the greedy theorem at `R;H`, whose hypothesis is `van_mono_alg`; and
    the program refining the greedy choice (`prog_le_greedy`). -/
public theorem van_laws [Amount A] [Van]
    (hsingle : ∀ a : A, secureP (ConsList.cons a (ConsList.wrap ()))) :
    ⦇progAlg⦈ ⊑ Λ (partition ≫ list secure) ≫ est (R (A := A)) :=
  calc (⦇progAlg⦈ : dList A ⟶ dSched A)
      ⊑ ⦇Λ S ≫ est («R;H» (A := A))⦈ := relCata_mono (initial Unit A) prog_le_greedy
    _ ⊑ Λ ⦇S⦈ ≫ est («R;H» (A := A)) := van_greedy
    _ ⊑ Λ ⦇S⦈ ≫ est (R (A := A)) := comp_mono_left _ (est_mono RH_le_R)
    _ = Λ (partition ≫ list secure) ≫ est (R (A := A)) := by rw [van_spec hsingle]

calc_steps van_laws

section

/-- The setting of the refutation below: each transaction is its own amount, `N = 0`. -/
@[expose] public def book0 : Van := ⟨0⟩

attribute [local instance] book0 bookAmount

/-- **`van_spec` needs `hsingle`**: without the book's "N is at least as large as any single
    transaction", `partition list(secure)` and `⦇S⦈` differ.  At `N = 0` the one transaction
    `5` has no secure splitting at all, yet `new` carries no security test, so `⦇S⦈` still
    answers `[[5]]`. -/
public theorem van_spec_false_without_hsingle :
    partition ≫ list (secure (A := Int)) ≠ ⦇S (A := Int)⦈ := by
  intro hEq
  have hsq := (cata_square_junc_iff (τ : dL Unit ⟶ dSched Int)
    (new (A := Int) ∪ old (A := Int)) ⦇S (A := Int)⦈).mp
    (relCata_cancel (initial Unit Int) (S (A := Int)))
  have hcata : ⦇S (A := Int)⦈
      (ConsList.cons (5 : Int) (ConsList.wrap ()))
      (ConsList.cons (ConsList.cons (5 : Int) (ConsList.wrap ())) (ConsList.wrap ())) :=
    (hsq.2 (5 : Int) (ConsList.wrap ()) _).mpr
      ⟨ConsList.wrap (), (hsq.1 () (ConsList.wrap ())).mpr rfl, Or.inl rfl⟩
  rw [← hEq] at hcata
  obtain ⟨-, -, hall⟩ := (partSecure_apply (A := Int) _ _).mp hcata
  have hbad : ¬ secureP (A := Int) (ConsList.cons (5 : Int) (ConsList.wrap ())) := by
    simp only [secureP, ceilingFn, floorFn, book0, bookAmount]; omega
  exact hbad hall.1

end

-- printing-only unexpanders: the note's spelling.  §7.5 writes a segment `[Int]` and a schedule
-- `[[Int]]` — the brackets ARE the names, `Seg`/`Sched` being what the Lean side calls them — and
-- `glue`/`assocl` are arrows of one shape at every index, so the objects they are taken at are not
-- part of the name (`glue≜(𝟙×cons°) assocl (cons×𝟙) cons`).  No statement and no `stmt_key` moves.
open Lean PrettyPrinter in
@[app_unexpander Seg] public meta def unexpandSeg : Unexpander
  | `($_ $A) => `([$A])
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander Sched] public meta def unexpandSched : Unexpander
  | `($_ $A) => `([[$A]])
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander dSched] public meta def unexpandDSched : Unexpander
  | `($_ $A) => `([[$A]])
  | _ => throw ()

end Freyd.Alg.RelSet.Van

namespace Freyd.Alg.RelSet.Van

-- KEPT: each pointwise function below prints the name of the arrow it is the graph of (`ceiling`,
-- `floor`, `glue`, `new`, and `secure` for the predicate under the coreflexive), and both live in
-- this namespace, so one bare identifier cannot resolve to both: only a rule can print the second.
open Lean PrettyPrinter in
@[app_unexpander ceilingFn] public meta def unexpandCeilingFn : Unexpander
  | `($_ $x) => `($(mkIdent `ceiling) $x)
  | _ => `($(mkIdent `ceiling))

open Lean PrettyPrinter in
@[app_unexpander floorFn] public meta def unexpandFloorFn : Unexpander
  | `($_ $x) => `($(mkIdent `floor) $x)
  | _ => `($(mkIdent `floor))

open Lean PrettyPrinter in
@[app_unexpander glueFn] public meta def unexpandGlueFn : Unexpander
  | _ => `($(mkIdent `glue))

open Lean PrettyPrinter in
@[app_unexpander newFn] public meta def unexpandNewFn : Unexpander
  | _ => `($(mkIdent `new))

end Freyd.Alg.RelSet.Van

-- "`x` is secure" is the note's word for the predicate under the coreflexive `secure` (kept, as above).
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Van.secureP] public meta def Freyd.Alg.RelSet.Van.unexpandSecureP : Unexpander
  | `($_ $x) => `($(mkIdent `secure) $x)
  | _ => `($(mkIdent `secure))

namespace Freyd.Alg.RelSet.Van

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel PowerAllegory

section VanRun

variable {A : Type} [Amount A] [Van]

/-- The order `R`, fewer segments, as a Boolean. -/
@[expose] public def rlen (xss yss : Sched A) : Bool := decide (clen xss ≤ clen yss)

/-- `R` as a `RelRep` test. -/
@[expose] public def Rt : RelTest (Sched A) (Sched A) := .test rlen

omit [Amount A] [Van] in
public theorem rel_Rt : (Rt (A := A)).rel = R := hom_ext fun _ _ => decide_eq_true_iff

/-- `S`'s offers at one transaction: `new`, and `glue` where `ok` holds. -/
@[expose] public def offers (p : A × Sched A) : List (Sched A) := newFn p :: if ok p then [glueFn p] else []

/-- The step's `Λ` form: `offers` as an `enum`. -/
@[expose] public def stepE : RelRep (A × Sched A) (Sched A) := .enum offers

/-- `stepE` is the `cons` half of `S≜[nil,new ∪ old]`. -/
public theorem rel_stepE : (stepE (A := A)).rel = new ∪ old := hom_ext fun p v => by
  obtain ⟨a, t⟩ := p
  rw [union_apply]
  show v ∈ newFn (a, t) :: (if ok (a, t) then [glueFn (a, t)] else []) ↔ graph newFn (a, t) v ∨ old (a, t) v
  rw [graph_apply]
  cases t with
  | wrap d =>
    simp only [ok, Bool.false_eq_true, if_false, List.mem_singleton, old, reduceCtorEq, false_and, exists_false,
      or_false]
  | cons s t =>
    by_cases hs : secureP (ConsList.cons a s)
    · simp only [okP_cons, hs, decide_true, if_true, glueFn, List.mem_cons, List.not_mem_nil,
        or_false, old, ConsList.cons.injEq]
      exact or_congr_right ⟨fun h => ⟨s, t, ⟨rfl, rfl⟩, h, hs⟩, fun ⟨_, _, ⟨e1, e2⟩, h, _⟩ => e1 ▸ e2 ▸ h⟩
    · simp only [okP_cons, decide_eq_false hs, Bool.false_eq_true, if_false, List.mem_singleton, old,
        ConsList.cons.injEq]
      exact ⟨Or.inl, fun h => h.elim id fun ⟨_, _, ⟨e1, e2⟩, _, h⟩ => absurd (e1 ▸ h) hs⟩

/-- The greedy step: the `R`-least of `S`'s offers. -/
@[expose] public def stepG (p : A × Sched A) : List (Sched A) := RelRep.estList rlen (offers p)

/-- At each transaction the one `R`-least offer is the program's `[nil,(ok→glue,new)]`: `glue` keeps
    the count of segments where `new` adds one. -/
public theorem stepG_prog (p : A × Sched A) : stepG p = [progFn p] := by
  obtain ⟨a, t⟩ := p
  cases t with
  | wrap d => simp [stepG, offers, RelRep.estList, rlen, ok, progFn]
  | cons s t =>
    by_cases hs : secureP (ConsList.cons a s) <;>
      simp [stepG, offers, RelRep.estList, rlen, ok, progFn, glueFn, newFn, clen, hs]

/-- **The program as a function**: the greedy fold, `nil` at the end and `stepG` at each transaction. -/
@[expose] public def van : Seg A → List (Sched A) := RelRep.foldList id (fun d => [ConsList.wrap d]) stepG

variable [DecidableEq A]

/-- `stepG` is `RelRep.est R` of `stepE`. -/
public theorem stepG_eq : RelRep.est Rt (stepE (A := A)) = .enum stepG := rfl

/-- `stepG` computes `Λ(new ∪ old) est(R)`. -/
public theorem rel_stepG : (RelRep.enum (stepG (A := A))).rel = Λ (new ∪ old) ≫ est R := by
  rw [← stepG_eq, RelRep.rel_est, rel_stepE, rel_Rt]

/-- `van` is `RelRep.fold` of `nil` and the greedy step. -/
public theorem van_eq : RelRep.fold (.ofFn ConsList.wrap) (.enum stepG) = .enum (van (A := A)) := rfl

/-- **The program meets its specification**: every schedule `van` returns is a fewest-segment cut of
    the transactions into secure segments. -/
public theorem van_le (hsingle : ∀ a : A, secureP (ConsList.cons a (ConsList.wrap ()))) :
    (RelRep.enum (van (A := A))).rel ⊑ Λ (partition ≫ list secure) ≫ est (R (A := A)) :=
  calc (RelRep.enum (van (A := A))).rel
      = ⦇(junc (sumCop (dL Unit) ⟨A × Sched A⟩) (RelRep.ofFn ConsList.wrap).rel (RelRep.enum stepG).rel
          : Alg (F Unit A) (dSched A))⦈ := by rw [← van_eq]; exact RelRep.rel_fold _ _
    _ = ⦇progAlg⦈ := by
        rw [RelRep.rel_ofFn, show (RelRep.enum (stepG (A := A))).rel = graph progFn from
          (congrArg (fun f => (RelRep.enum f).rel) (funext stepG_prog)).trans (RelRep.rel_ofFn progFn)]
        rfl
    _ ⊑ Λ (partition ≫ list secure) ≫ est R := van_laws hsingle

end VanRun

section

attribute [local instance] book10 bookAmount

/-- **offers-run**: at `3` over `[[5,-2]]`, `S` offers a new segment and the glued one. -/
public theorem run_offers :
    offers ((3 : Int), ConsList.cons (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ()))) (ConsList.wrap ()))
      = [ConsList.cons (ConsList.cons 3 (ConsList.wrap ()))
            (ConsList.cons (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ()))) (ConsList.wrap ())),
         ConsList.cons (ConsList.cons 3 (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ())))) (ConsList.wrap ())] := by
  rfl

/-- **glue-run**: `[3,5,-2]` is secure, so `est(R)` keeps the one-segment offer. -/
public theorem run_glue :
    stepG ((3 : Int), ConsList.cons (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ()))) (ConsList.wrap ()))
      = [ConsList.cons (ConsList.cons 3 (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ())))) (ConsList.wrap ())] := by
  rfl

/-- **new-run**: `[4,3,5,-2]` reaches `12 > 10`, so `S` offers only the new segment. -/
public theorem run_new :
    stepG ((4 : Int), ConsList.cons (ConsList.cons 3 (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ()))))
        (ConsList.wrap ()))
      = [ConsList.cons (ConsList.cons 4 (ConsList.wrap ()))
          (ConsList.cons (ConsList.cons 3 (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ())))) (ConsList.wrap ()))] := by
  rfl

/-- **van-run**: two van visits, `[4]` and `[3,5,-2]`. -/
public theorem run_van :
    van (ConsList.cons (4 : Int) (ConsList.cons 3 (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ())))))
      = [ConsList.cons (ConsList.cons 4 (ConsList.wrap ()))
          (ConsList.cons (ConsList.cons 3 (ConsList.cons 5 (ConsList.cons (-2) (ConsList.wrap ())))) (ConsList.wrap ()))] := by
  rfl

end

end Freyd.Alg.RelSet.Van
