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
      carries no security test.  Transactions are therefore an abstract type `Tx` with an
      `amount : Tx → Int`, as `AOP.A8_5`'s words carry a `len`, and `hsingle` bounds them.

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

public import AOP.A8_2
public import AOP.A7_2
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Van

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {Tx : Type} {amount : Tx → Int} {N : Int}

/-! ## `van-defn` -/

/-- A SEGMENT: the consecutive transactions one van visit serves. -/
@[expose] public abbrev Seg (Tx : Type) : Type := ConsList Unit Tx
/-- A SCHEDULE: the transactions cut into segments, one van visit each. -/
@[expose] public abbrev Sched (Tx : Type) : Type := ConsList Unit (Seg Tx)
/-- The object carrying schedules. -/
@[expose] public abbrev dSched (Tx : Type) : RelSet.{0} := ⟨Sched Tx⟩

/-- **van-defn**: `ceiling ≜ Λ(prefix sum) est(≥)`, the highest the balance reaches over the
    stretch — as the book's own fold `⦇[zero,omax plus]⦈` (p.188), `omax a = bmax(a,0)`.  The
    empty prefix counts, so `ceiling` is never negative. -/
@[expose] public def ceilingFn (amount : Tx → Int) : Seg Tx → Int
  | ConsList.wrap _ => 0
  | ConsList.cons a x => max (amount a + ceilingFn amount x) 0

/-- **van-defn**: `floor ≜ Λ(prefix sum) est(≤)`, the lowest the balance reaches — the book's
    `⦇[zero,omin plus]⦈`. -/
@[expose] public def floorFn (amount : Tx → Int) : Seg Tx → Int
  | ConsList.wrap _ => 0
  | ConsList.cons a x => min (amount a + floorFn amount x) 0

public theorem ceilingFn_nonneg : ∀ x : Seg Tx, 0 ≤ ceilingFn amount x
  | ConsList.wrap _ => Int.le_refl 0
  | ConsList.cons a x => by simp only [ceilingFn]; omega

public theorem floorFn_nonpos : ∀ x : Seg Tx, floorFn amount x ≤ 0
  | ConsList.wrap _ => Int.le_refl 0
  | ConsList.cons a x => by simp only [floorFn]; omega

/-- **van-defn**: `secure`, the stretches one van visit can serve — the book's p.185
    `bmax(ceiling x, ceiling x − floor x) ≤ N`, which says some starting reserve keeps the cash
    between `0` and `N` throughout. -/
@[expose] public def secureP (amount : Tx → Int) (N : Int) (x : Seg Tx) : Prop :=
  max (ceilingFn amount x) (ceilingFn amount x - floorFn amount x) ≤ N

public instance decSecureP (amount : Tx → Int) (N : Int) (x : Seg Tx) :
    Decidable (secureP amount N x) := Int.decLe _ _

/-- **van-defn**: `secure` as a coreflexive on stretches. -/
@[expose] public def secure (amount : Tx → Int) (N : Int) : dList Tx ⟶ dList Tx :=
  fun x y => x = y ∧ secureP amount N x

public theorem secure_coreflexive : Coreflexive (secure amount N) :=
  le_iff.mpr fun _ _ h => h.1

/-! ### `secure` is the coreflexive of the book's p.185 test -/

/-- **van-secure**: `⟨ceiling,ceiling−floor⟩`, the pair the p.185 predicate compares. -/
@[expose] public def ceilSpread (amount : Tx → Int) : dList Tx ⟶ (⟨Int × Int⟩ : RelSet.{0}) :=
  graph fun x => (ceilingFn amount x, ceilingFn amount x - floorFn amount x)

/-- **van-secure**: `bmax`, the larger of the two. -/
@[expose] public def bmax : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := graph fun p => max p.1 p.2

/-- **van-secure**: `≤N`, the coreflexive on `Int` the test has to land in. -/
@[expose] public def leN (N : Int) : (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := fun a b => a = b ∧ a ≤ N

/-- **van-secure**: `secure⟨ceiling,ceiling−floor⟩bmax=⟨ceiling,ceiling−floor⟩bmax(≤N)` (book p.185).
    The test is a map, so sliding the coreflexive across it says exactly that `secure` holds at the
    stretches whose test value is at most `N` — which is what "the coreflexive corresponding to this
    predicate" means. -/
public theorem secure_bmax :
    secure amount N ≫ ceilSpread amount ≫ bmax = ceilSpread amount ≫ bmax ≫ leN N := by
  apply hom_ext; intro x n
  constructor
  · rintro ⟨y, ⟨rfl, hs⟩, p, rfl, rfl⟩
    exact ⟨_, rfl, _, rfl, rfl, hs⟩
  · rintro ⟨p, rfl, m, rfl, rfl, hle⟩
    exact ⟨x, ⟨rfl, hle⟩, _, rfl, rfl⟩

/-! ### `secure` is prefix-closed, and closed under dropping the first transaction -/

public theorem ceilingFn_mono :
    ∀ {p x : Seg Tx}, prefixP p x → ceilingFn amount p ≤ ceilingFn amount x
  | ConsList.wrap _, x, _ => ceilingFn_nonneg x
  | ConsList.cons _ _, ConsList.wrap _, h => False.elim h
  | ConsList.cons a p, ConsList.cons b x, h => by
    obtain ⟨rfl, hp⟩ := h
    have hih := ceilingFn_mono hp
    simp only [ceilingFn]; omega

public theorem floorFn_anti :
    ∀ {p x : Seg Tx}, prefixP p x → floorFn amount x ≤ floorFn amount p
  | ConsList.wrap _, x, _ => floorFn_nonpos x
  | ConsList.cons _ _, ConsList.wrap _, h => False.elim h
  | ConsList.cons a p, ConsList.cons b x, h => by
    obtain ⟨rfl, hp⟩ := h
    have hih := floorFn_anti hp
    simp only [floorFn]; omega

/-- **`secure` is prefix-closed** (book p.185): a prefix reaches neither as high nor as low. -/
public theorem secureP_prefix {p x : Seg Tx} (h : prefixP p x) (hs : secureP amount N x) :
    secureP amount N p := by
  have hc : ceilingFn amount p ≤ ceilingFn amount x := ceilingFn_mono h
  have hf : floorFn amount x ≤ floorFn amount p := floorFn_anti h
  have hcp := ceilingFn_nonneg (amount := amount) p
  have hfp := floorFn_nonpos (amount := amount) p
  simp only [secureP] at hs ⊢
  omega

/-- **van-laws**, the fusion row's stated side condition: `secure prefix ⊑ prefix secure`. -/
public theorem secure_prefix :
    secure amount N ≫ prefixR ⊑ (prefixR : dList Tx ⟶ dList Tx) ≫ secure amount N :=
  le_iff.mpr fun x p h => by
    obtain ⟨y, ⟨rfl, hs⟩, hp⟩ := h
    exact ⟨p, hp, rfl, secureP_prefix hp hs⟩

/-- **What the fusion actually needs**: dropping the FIRST transaction of a secure stretch
    leaves a secure stretch — one step of the suffix-closure the book proves on p.188. -/
public theorem secureP_tail {a : Tx} {x : Seg Tx} (h : secureP amount N (ConsList.cons a x)) :
    secureP amount N x := by
  have hc := ceilingFn_nonneg (amount := amount) x
  have hf := floorFn_nonpos (amount := amount) x
  simp only [secureP, ceilingFn, floorFn] at h ⊢
  omega

/-! ### The orders `R`, `H`, `R;H` and `|R|` -/

/-- **van-defn**: `R ≜ length ≤ length°` — fewer van visits is better. -/
@[expose] public def R (Tx : Type) : dSched Tx ⟶ dSched Tx := fun p q => clen p ≤ clen q

/-- `R = length ≤ length°`, point-free. -/
public theorem R_eq :
    R Tx = graph (fun p : Sched Tx => (clen p : Int)) ≫ leq
      ≫ (graph (fun p : Sched Tx => (clen p : Int)) : dSched Tx ⟶ (⟨Int⟩ : RelSet.{0}))° := by
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
@[expose] public def headR (Tx : Type) : dSched Tx ⟶ (⟨Seg Tx⟩ : RelSet.{0}) :=
  fun p s => ∃ t, p = ConsList.cons s t

/-- **van-defn**: `H ≜ (head prefix° head°)∪(nil° nil)` — one schedule's first segment is a
    prefix of the other's, or both are empty. -/
@[expose] public def Hrel (Tx : Type) : dSched Tx ⟶ dSched Tx := fun p q =>
  (∃ s t s' t', p = ConsList.cons s t ∧ q = ConsList.cons s' t' ∧ prefixP s s')
    ∨ (p = ConsList.wrap () ∧ q = ConsList.wrap ())

/-- **van-defn**: `R;H ≜ R∩(R°⇒H)` — strictly shorter, or the same length with the first
    segment a prefix of the other's. -/
@[expose] public def RH (Tx : Type) : dSched Tx ⟶ dSched Tx := fun p q =>
  clen p ≤ clen q ∧ (clen q ≤ clen p → Hrel Tx p q)

/-- `R;H = R ∩ (R° ⇒ H)`, the book's p.187 definition of the refined order. -/
public theorem RH_eq : RH Tx = R Tx ∩ ((R Tx)° ⇨ Hrel Tx) := by
  apply le_antisymm
  · refine le_inter (le_iff.mpr fun p q h => h.1) ((le_impl_iff _ _ _).mpr ?_)
    exact le_iff.mpr fun p q h => h.1.2 h.2
  · refine le_iff.mpr fun p q h => ⟨h.1, fun hle => ?_⟩
    exact le_iff.mp (impl_cancel ((R Tx)°) (Hrel Tx)) p q ⟨h.2, hle⟩

/-- `H = (head prefix° head°)∪(nil° nil)`, point-free — `nil` being `wrapR` out of the one
    point `dL Unit`, so `nil° nil` is the coreflexive on the empty schedule. -/
public theorem H_eq :
    Hrel Tx = (headR Tx ≫ (prefixR : dList Tx ⟶ dList Tx)° ≫ (headR Tx)°)
      ∪ ((wrapR : dL Unit ⟶ dSched Tx)° ≫ wrapR) := by
  apply hom_ext; intro p q
  constructor
  · rintro (⟨s, t, s', t', hp, hq, hpre⟩ | ⟨hp, hq⟩)
    · exact Or.inl ⟨s, ⟨t, hp⟩, s', hpre, ⟨t', hq⟩⟩
    · exact Or.inr ⟨(), hp, hq⟩
  · rintro (⟨s, ⟨t, hp⟩, s', hpre, ⟨t', hq⟩⟩ | ⟨u, hp, hq⟩)
    · exact Or.inl ⟨s, t, s', t', hp, hq, hpre⟩
    · exact Or.inr ⟨hp, hq⟩

/-- **van-defn**: `|R| ≜ R∩¬R°`, the strict part `R` splits into. -/
@[expose] public def strictR (Tx : Type) : dSched Tx ⟶ dSched Tx := fun p q => clen p < clen q

/-- **van-defn**: `R∩H` — no longer, AND with the first segment a prefix of the other's.  The §7.5
    displays draw it as ONE bead, so it is one arrow here: a bead is an arrow, and an arrow the note
    hangs a naturality verdict on needs a declaration to hang it from. -/
@[expose] public def RinterH (Tx : Type) : dSched Tx ⟶ dSched Tx := R Tx ∩ Hrel Tx

/-- **van-mono**, second row: `R;H = |R|∪(R∩H)` — the split the monotonicity proof
    distributes over.  It is also all the certification `|R| ≜ R∩¬R°` gets: the allegory
    carries no complement, so the strict part is named by this equation rather than by `¬`. -/
public theorem RH_eq_strict : RH Tx = strictR Tx ∪ RinterH Tx := by
  apply hom_ext; intro p q
  constructor
  · rintro ⟨hle, hH⟩
    rcases Nat.lt_or_ge (clen p) (clen q) with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr ⟨hle, hH hge⟩
  · rintro (hlt | ⟨hle, hH⟩)
    · exact ⟨Nat.le_of_lt hlt, fun hge => absurd hge (Nat.not_le_of_lt hlt)⟩
    · exact ⟨hle, fun _ => hH⟩

public theorem RH_le_R : RH Tx ⊑ R Tx := le_iff.mpr fun _ _ h => h.1

public theorem RH_refl : 𝟙 (dSched Tx) ⊑ RH Tx :=
  le_iff.mpr fun p q h => by
    obtain rfl : p = q := h
    refine ⟨Nat.le_refl _, fun _ => ?_⟩
    cases p with
    | wrap u => exact Or.inr ⟨rfl, rfl⟩
    | cons s t => exact Or.inl ⟨s, t, s, t, rfl, rfl, prefixP.refl s⟩

public theorem RH_trans : RH Tx ≫ RH Tx ⊑ RH Tx :=
  le_iff.mpr fun p r h => by
    obtain ⟨q, ⟨h1, hH1⟩, ⟨h2, hH2⟩⟩ := h
    refine ⟨Nat.le_trans h1 h2, fun hle => ?_⟩
    have e1 : clen q ≤ clen p := Nat.le_trans h2 hle
    have e2 : clen r ≤ clen q := Nat.le_trans hle h1
    rcases hH1 e1 with ⟨s, t, s', t', hp, hq, hpr⟩ | ⟨hp, hq⟩
    · rcases hH2 e2 with ⟨u, v, u', v', hq', hr, hpr'⟩ | ⟨hq', -⟩
      · rw [hq] at hq'
        injection hq' with hsu htv
        subst hsu
        subst htv
        exact Or.inl ⟨s, t, u', v', hp, hr, prefixP.trans hpr hpr'⟩
      · rw [hq] at hq'; nomatch hq'
    · rcases hH2 e2 with ⟨u, v, u', v', hq', -, -⟩ | ⟨-, hr⟩
      · rw [hq] at hq'; nomatch hq'
      · exact Or.inr ⟨hp, hr⟩

public theorem R_recip_trans : (R Tx)° ≫ (R Tx)° ⊑ (R Tx)° :=
  le_iff.mpr fun p r h => by
    obtain ⟨q, h1, h2⟩ := h
    exact Nat.le_trans (h2 : clen r ≤ clen q) (h1 : clen q ≤ clen p)

/-! ### `new`, `glue`, `old`, `ok` and the two algebras -/

/-- **van-defn**: `new ≜ (wrap×𝟙) cons` — the transaction opens a segment of its own. -/
@[expose] public def newFn (p : Tx × Sched Tx) : Sched Tx :=
  ConsList.cons (ConsList.cons p.1 (ConsList.wrap ())) p.2

@[expose] public def newR (Tx : Type) : (⟨Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx :=
  graph newFn

/-- **van-defn**: `glue ≜ (𝟙×cons°) assocl (cons×𝟙) cons` — the transaction goes on the front
    of the first segment, so the schedule must have one. -/
@[expose] public def glueR (Tx : Type) : (⟨Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx :=
  fun p r => ∃ s t, p.2 = ConsList.cons s t ∧ r = ConsList.cons (ConsList.cons p.1 s) t

/-- **van-defn**: `ok`, the test the final program runs — the schedule is non-empty and
    `[a]⧺head xs` is secure. -/
@[expose] public def okR (amount : Tx → Int) (N : Int) :
    (⟨Tx × Sched Tx⟩ : RelSet.{0}) ⟶ ⟨Tx × Sched Tx⟩ := fun p q =>
  p = q ∧ ∃ s t, p.2 = ConsList.cons s t ∧ secureP amount N (ConsList.cons p.1 s)

/-- **van-defn**: `old ≜ (𝟙×cons°) assocl ((cons secure)×𝟙) cons` — `glue` restricted to a
    first segment that stays secure. -/
@[expose] public def oldR (amount : Tx → Int) (N : Int) :
    (⟨Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx := fun p r =>
  ∃ s t, p.2 = ConsList.cons s t ∧ r = ConsList.cons (ConsList.cons p.1 s) t
    ∧ secureP amount N (ConsList.cons p.1 s)

/-- **van-laws**, the last row's reason read as an equation: `ok` is exactly where `old`
    returns anything, so `old = ok glue`. -/
public theorem old_eq_ok_glue : oldR amount N = okR amount N ≫ glueR Tx := by
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

/-! ### `new`, `glue`, `old` point-free, as B&dM write them on p.185 -/

/-- The re-bracketing B&dM write as `assocl` (p.185); the note's pictures draw nothing for it,
    a product being flat there. -/
@[expose] public def assoclR (A B C : Type) :
    (⟨A × B × C⟩ : RelSet.{0}) ⟶ ⟨(A × B) × C⟩ := graph fun p => ((p.1, p.2.1), p.2.2)

/-- **van-defn**: `new = (wrap×𝟙) cons` (book p.185) — the transaction becomes a segment of its
    own, and that segment is consed onto the schedule. -/
public theorem new_eq :
    newR Tx = rprodMap (singleR () : dE Tx ⟶ dList Tx) (𝟙 (dSched Tx)) ≫ consR := by
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
    glueR Tx = rprodMap (𝟙 (dE Tx)) ((consR : (⟨Seg Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx)°)
      ≫ assoclR Tx (Seg Tx) (Sched Tx)
      ≫ rprodMap (consR : (⟨Tx × Seg Tx⟩ : RelSet.{0}) ⟶ dList Tx) (𝟙 (dSched Tx))
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
public theorem old_eq :
    oldR amount N
      = rprodMap (𝟙 (dE Tx)) ((consR : (⟨Seg Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx)°)
        ≫ assoclR Tx (Seg Tx) (Sched Tx)
        ≫ rprodMap ((consR : (⟨Tx × Seg Tx⟩ : RelSet.{0}) ⟶ dList Tx) ≫ secure amount N)
            (𝟙 (dSched Tx))
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
@[expose] public def Salg (amount : Tx → Int) (N : Int) :
    (F Unit Tx).obj (dSched Tx) ⟶ dSched Tx :=
  junc (sumCop (dL Unit) ⟨Tx × Sched Tx⟩) (wrapR : dL Unit ⟶ dSched Tx)
    (newR Tx ∪ oldR amount N)

/-- **van-laws**, the final program's algebra `[nil,(ok→glue,new)]`: glue the transaction onto
    the open segment wherever that segment stays secure, and call the van where it does not. -/
@[expose] public def progFn (amount : Tx → Int) (N : Int) : Tx × Sched Tx → Sched Tx
  | (a, ConsList.wrap _) =>
      ConsList.cons (ConsList.cons a (ConsList.wrap ())) (ConsList.wrap ())
  | (a, ConsList.cons s t) =>
      if secureP amount N (ConsList.cons a s) then ConsList.cons (ConsList.cons a s) t
      else ConsList.cons (ConsList.cons a (ConsList.wrap ())) (ConsList.cons s t)

@[expose] public def progAlg (amount : Tx → Int) (N : Int) :
    (F Unit Tx).obj (dSched Tx) ⟶ dSched Tx :=
  junc (sumCop (dL Unit) ⟨Tx × Sched Tx⟩) (wrapR : dL Unit ⟶ dSched Tx)
    (graph (progFn amount N))

/-- **van-laws**, the greedy fold `⦇S%∋ est(R;H)⦈` the note's §13.4 draws: at each transaction
    `S` offers both the new segment and the glued one, and `est(R;H)` keeps the `R;H`-least. -/
@[expose] public def greedyFold (amount : Tx → Int) (N : Int) : dList Tx ⟶ dSched Tx :=
  ⦇Λ (Salg amount N) ≫ est (RH Tx)⦈

/-! ## `van-defn`'s fusion: `partition list(secure) = ⦇S⦈` -/

/-- Every segment of the schedule is secure. -/
@[expose] public def allSecureP (amount : Tx → Int) (N : Int) : Sched Tx → Prop
  | ConsList.wrap _ => True
  | ConsList.cons s p => secureP amount N s ∧ allSecureP amount N p

public theorem listP_secure_iff : ∀ ps r : Sched Tx,
    listP (secure amount N) ps r ↔ (ps = r ∧ allSecureP amount N ps)
  | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => ⟨rfl, trivial⟩, fun _ => trivial⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨fun h => False.elim h, fun h => nomatch h.1⟩
  | ConsList.cons _ _, ConsList.wrap _ => ⟨fun h => False.elim h, fun h => nomatch h.1⟩
  | ConsList.cons s p, ConsList.cons s' r => by
    show (secure amount N s s' ∧ listP (secure amount N) p r) ↔ _
    rw [listP_secure_iff p r]
    constructor
    · rintro ⟨⟨rfl, hs⟩, rfl, hall⟩
      exact ⟨rfl, hs, hall⟩
    · rintro ⟨heq, hs, hall⟩
      injection heq with h1 h2
      subst h1
      subst h2
      exact ⟨⟨rfl, hs⟩, rfl, hall⟩

public theorem partSecure_apply (x : Seg Tx) (r : Sched Tx) :
    (partition ≫ list (secure amount N)) x r
      ↔ (cconcat r = x ∧ allNonempty r ∧ allSecureP amount N r) := by
  constructor
  · rintro ⟨ps, ⟨hcat, hne⟩, hlist⟩
    obtain ⟨rfl, hall⟩ := (listP_secure_iff ps r).mp hlist
    exact ⟨hcat, hne, hall⟩
  · rintro ⟨hcat, hne, hall⟩
    exact ⟨r, ⟨hcat, hne⟩, (listP_secure_iff r r).mpr ⟨rfl, hall⟩⟩

public theorem eq_nil_of_cconcat_nil : ∀ r : Sched Tx,
    cconcat r = ConsList.wrap () → allNonempty r → r = ConsList.wrap ()
  | ConsList.wrap _, _, _ => rfl
  | ConsList.cons s p, h, hn => by
    cases s with
    | wrap _ => exact False.elim hn.1
    | cons b s' => simp [cconcat, cappend] at h

/-- **van-defn** / **van-laws**, second row (book p.185, "appeal to fusion"):
    `partition list(secure) = ⦇[nil,new∪old]⦈` — keeping only secure segments is what turns
    `glue` into `old`.  The forward direction peels the head transaction off the first segment
    and needs the rest of it secure (`secureP_tail`); the backward direction needs the book's
    standing assumption that a single transaction is never larger than `N` (`hsingle`). -/
public theorem van_spec
    (hsingle : ∀ a : Tx, secureP amount N (ConsList.cons a (ConsList.wrap ()))) :
    partition ≫ list (secure amount N) = ⦇Salg amount N⦈ := by
  refine (relCata_UP (initial Unit Tx) _ _).mp ((cata_square_junc_iff _ _ _).mpr ⟨?_, ?_⟩)
  · intro d r
    rw [partSecure_apply]
    constructor
    · rintro ⟨hcat, hne, -⟩
      show r = ConsList.wrap d
      exact eq_nil_of_cconcat_nil r hcat hne
    · intro h
      obtain rfl : r = ConsList.wrap d := h
      exact ⟨rfl, trivial, trivial⟩
  · intro a x r
    simp only [partSecure_apply]
    constructor
    · rintro ⟨hcat, hne, hall⟩
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
            refine ⟨p, ⟨hcat', hne.2, hall.2⟩, Or.inl ?_⟩
            show ConsList.cons (ConsList.cons b (ConsList.wrap ())) p = newFn (b, p)
            rfl
          | cons c s'' =>
            exact ⟨ConsList.cons (ConsList.cons c s'') p,
              ⟨hcat', ⟨trivial, hne.2⟩, secureP_tail hall.1, hall.2⟩,
              Or.inr ⟨ConsList.cons c s'', p, rfl, rfl, hall.1⟩⟩
    · rintro ⟨y, ⟨hcat, hne, hall⟩, hS⟩
      cases hS with
      | inl hS =>
        obtain rfl : r = newFn (a, y) := hS
        refine ⟨?_, ⟨trivial, hne⟩, hsingle a, hall⟩
        show cappend (ConsList.cons a (ConsList.wrap ())) (cconcat y) = ConsList.cons a x
        simp only [cappend]
        rw [hcat]
      | inr hS =>
        obtain ⟨s, t, hy, hr, hsec⟩ := hS
        subst hy
        subst hr
        refine ⟨?_, ⟨trivial, hne.2⟩, hsec, hall.2⟩
        show cappend (ConsList.cons a s) (cconcat t) = ConsList.cons a x
        simp only [cappend]
        rw [show cappend s (cconcat t) = x from hcat]

/-! ## `van-mono`: (7.14) holds, (7.15) is FALSE, (7.16) and (7.17) hold on `R;H` -/

/-- **(7.14)'s first step** (book p.186, "since `cons` is monotonic on `R` (exercise)"):
    `(𝟙×R)cons ⊑ cons R` — consing a segment onto the shorter of two schedules leaves the
    shorter schedule, both sides having gained exactly one segment. -/
public theorem cons_mono_R :
    rprodMap (𝟙 (⟨Seg Tx⟩ : RelSet.{0})) (R Tx)
        ≫ (consR : (⟨Seg Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx)
      ⊑ consR ≫ R Tx :=
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
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (R Tx) ≫ newR Tx
      = rprodMap (singleR () : dE Tx ⟶ dList Tx) (R Tx)
        ≫ (consR : (⟨Seg Tx × Sched Tx⟩ : RelSet.{0}) ⟶ dSched Tx) := by
  apply hom_ext; rintro ⟨a, x⟩ r
  constructor
  · rintro ⟨⟨b, y⟩, ⟨hab, hR⟩, hnew⟩
    obtain rfl : a = b := hab
    obtain rfl : r = newFn (a, y) := hnew
    exact ⟨(ConsList.cons a (ConsList.wrap ()), y), ⟨rfl, hR⟩, rfl⟩
  · rintro ⟨⟨s, y⟩, ⟨hs, hR⟩, hr⟩
    obtain rfl : s = ConsList.cons a (ConsList.wrap ()) := hs
    exact ⟨(a, y), ⟨rfl, hR⟩, hr⟩

/-- **(7.14)** (book p.186): `(𝟙×R)new ⊑ (new∪old)R` — opening a segment of its own for the
    new transaction keeps the schedule no longer than opening one on a longer schedule. -/
public theorem van_7_14 :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (R Tx) ≫ newR Tx
      ⊑ (newR Tx ∪ oldR amount N) ≫ R Tx :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hR⟩, hnew⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : r = newFn (b, y) := hnew
    obtain rfl : a = b := hab
    refine ⟨newFn (a, x), Or.inl rfl, ?_⟩
    show clen x + 1 ≤ clen y + 1
    have : clen x ≤ clen y := hR
    omega

/-- **(7.15) IS FALSE** (book p.186, and the note's `van-laws` says so): gluing the
    transaction onto a shorter schedule need not be beaten by gluing it onto this one, because
    the shorter schedule's first segment need not stay secure.

    The witness is the book's own, at `N = 10` and the transaction `0`: `[[0]]` and `[[20]]`
    are schedules of the same length, `[0]⧺[0]` is secure and `[0]⧺[20]` is not.  So `old`
    fires on the left and neither `new` (which lengthens the schedule) nor `old` (which the
    security test blocks) can answer on the right. -/
public theorem van_7_15_false :
    ¬ (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) (R Int) ≫ oldR (fun i : Int => i) 10
      ⊑ (newR Int ∪ oldR (fun i : Int => i) 10) ≫ R Int) := by
  intro h
  have hsec : secureP (fun i : Int => i) 10
      (ConsList.cons (0 : Int) (ConsList.cons (0 : Int) (ConsList.wrap ()))) := by
    simp only [secureP, ceilingFn, floorFn]; omega
  have hbad : ¬ secureP (fun i : Int => i) 10
      (ConsList.cons (0 : Int) (ConsList.cons (20 : Int) (ConsList.wrap ()))) := by
    simp only [secureP, ceilingFn, floorFn]; omega
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

/-- **(7.18)** (book p.187): `(𝟙×⊤)new ⊑ new H` — whatever the two second components are,
    both sides open the segment `[a]` of their own, so the two first segments are equal and
    `H` holds outright. -/
public theorem van_7_18 :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (relTop (dSched Tx) (dSched Tx)) ≫ newR Tx
      ⊑ newR Tx ≫ Hrel Tx :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, -⟩, hnew⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : r = newFn (b, y) := hnew
    obtain rfl : a = b := hab
    exact ⟨newFn (a, x), rfl, Or.inl ⟨ConsList.cons a (ConsList.wrap ()), x,
      ConsList.cons a (ConsList.wrap ()), y, rfl, rfl,
      prefixP.refl (ConsList.cons a (ConsList.wrap ()))⟩⟩

/-- **(7.19)** (book p.187): `(𝟙×⊤)old ⊑ new H` — `old` leaves `[a]` at the front of the first
    segment it lengthens, and `[a]` is what `new` makes that segment, so `[a]` is a prefix of
    it whatever the two second components are. -/
public theorem van_7_19 :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (relTop (dSched Tx) (dSched Tx)) ≫ oldR amount N
      ⊑ newR Tx ≫ Hrel Tx :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, -⟩, s, t, -, hr, -⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : a = b := hab
    subst hr
    exact ⟨newFn (a, x), rfl, Or.inl ⟨ConsList.cons a (ConsList.wrap ()), x,
      ConsList.cons a s, t, rfl, rfl, ⟨rfl, prefixP.nil s⟩⟩⟩

/-- **(7.20)** (book p.187): `(𝟙×|R|)old ⊑ new R` — `old` keeps the schedule's length, so a
    STRICTLY shorter schedule stays no longer than the one `new` builds, which is one segment
    longer than the schedule it started from. -/
public theorem van_7_20 :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (strictR Tx) ≫ oldR amount N ⊑ newR Tx ≫ R Tx :=
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
public theorem van_7_21 :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (R Tx ∩ Hrel Tx) ≫ oldR amount N
      ⊑ oldR amount N ≫ (R Tx ∩ Hrel Tx) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hle, hH⟩, s, t, hv, hr, hsec⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : a = b := hab
    subst hv
    subst hr
    rcases hH with ⟨s₀, t₀, s', t', hx, hy', hpre⟩ | ⟨-, hy'⟩
    · subst hx
      injection hy' with hs ht
      subst hs
      subst ht
      have hsec₀ : secureP amount N (ConsList.cons a s₀) :=
        secureP_prefix (show prefixP (ConsList.cons a s₀) (ConsList.cons a s) from
          ⟨rfl, hpre⟩) hsec
      exact ⟨ConsList.cons (ConsList.cons a s₀) t₀, ⟨s₀, t₀, rfl, rfl, hsec₀⟩, hle,
        Or.inl ⟨ConsList.cons a s₀, t₀, ConsList.cons a s, t, rfl, rfl, ⟨rfl, hpre⟩⟩⟩
    · nomatch hy'

/-- **(7.19) and (7.20) intersected** (book p.187): `(𝟙×|R|)old ⊑ new (R∩H)` — `new` is a
    function, so what it is `H`-below and `R`-below it is `(R∩H)`-below, and `|R| ⊑ ⊤` feeds
    (7.19). -/
public theorem van_strict_old :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (strictR Tx) ≫ oldR amount N
      ⊑ newR Tx ≫ (R Tx ∩ Hrel Tx) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hv, hold⟩ := h
    obtain ⟨w, hw, hR⟩ :=
      le_iff.mp (van_7_20 (amount := amount) (N := N)) u r ⟨v, hv, hold⟩
    obtain ⟨w', hw', hH⟩ :=
      le_iff.mp (van_7_19 (amount := amount) (N := N)) u r ⟨v, ⟨hv.1, trivial⟩, hold⟩
    obtain rfl : w = newFn u := hw
    obtain rfl : w' = newFn u := hw'
    exact ⟨newFn u, rfl, hR, hH⟩

/-- **`X∩Y ⊑ X;Y`** (book p.188): a pair related by both `R` and `H` is related by the refined
    order, whose second half only has to supply `H` where `R` holds in both directions. -/
public theorem inter_le_RH : R Tx ∩ Hrel Tx ⊑ RH Tx :=
  le_iff.mpr fun _ _ h => ⟨h.1, fun _ => h.2⟩

/-- **(7.16)** (book p.187): `(𝟙×(R;H))new ⊑ (new∪old)(R;H)` — the `new` half of the
    monotonicity on the refined order.  Both sides start `[a]`, so `H` holds outright and
    (7.18) `(𝟙×⊤)new ⊑ new H` is what carries the tie. -/
public theorem van_mono_new :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (RH Tx) ≫ newR Tx
      ⊑ (newR Tx ∪ oldR amount N) ≫ RH Tx :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hRH⟩, hnew⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : r = newFn (b, y) := hnew
    obtain rfl : a = b := hab
    refine ⟨newFn (a, x), Or.inl rfl, ?_, fun _ => ?_⟩
    · show clen x + 1 ≤ clen y + 1
      have : clen x ≤ clen y := hRH.1
      omega
    · exact Or.inl ⟨ConsList.cons a (ConsList.wrap ()), x,
        ConsList.cons a (ConsList.wrap ()), y, rfl, rfl,
        prefixP.refl (ConsList.cons a (ConsList.wrap ()))⟩

/-- **van-mono** (book p.187's (7.17)): `(𝟙×(R;H))old ⊑ (new∪old)(R;H)` — gluing the
    transaction onto a better schedule for the rest gets no further than gluing it on, or
    calling the van, and bettering the whole schedule after.

    Two cases, which are the book's (7.19)-(7.21): on the strict part `|R|` the answer is
    `new`, and `[a]` is a prefix of `[a]⧺s`, so `H` holds even when the lengths come out
    equal; on `R∩H` the first segments are nested, so prefix-closure of `secure` lets `old`
    fire on this side too. -/
public theorem van_mono :
    rprodMap (𝟙 (⟨Tx⟩ : RelSet.{0})) (RH Tx) ≫ oldR amount N
      ⊑ (newR Tx ∪ oldR amount N) ≫ RH Tx :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, ⟨hab, hRH⟩, s, t, hv, hr, hsec⟩ := h
    obtain ⟨a, x⟩ := u
    obtain ⟨b, y⟩ := v
    obtain rfl : a = b := hab
    subst hv
    subst hr
    by_cases hlen : clen (ConsList.cons s t) ≤ clen x
    · -- equal lengths: `H` gives `x = [s₀]⧺t₀` with `s₀` a prefix of `s`, so `old` fires here too
      rcases hRH.2 hlen with ⟨s₀, t₀, s', t', hx, hy', hpre⟩ | ⟨-, hy'⟩
      · subst hx
        injection hy' with hs ht
        subst hs
        subst ht
        have hsec₀ : secureP amount N (ConsList.cons a s₀) :=
          secureP_prefix (show prefixP (ConsList.cons a s₀) (ConsList.cons a s) from
            ⟨rfl, hpre⟩) hsec
        refine ⟨ConsList.cons (ConsList.cons a s₀) t₀,
          Or.inr ⟨s₀, t₀, rfl, rfl, hsec₀⟩, hRH.1, fun _ => ?_⟩
        exact Or.inl ⟨ConsList.cons a s₀, t₀, ConsList.cons a s, t, rfl, rfl, ⟨rfl, hpre⟩⟩
      · nomatch hy'
    · -- strictly shorter: `new` answers, and `[a]` is a prefix of `[a]⧺s`
      refine ⟨newFn (a, x), Or.inl rfl, ?_, fun _ => ?_⟩
      · show clen x + 1 ≤ clen t + 1
        have h2 : ¬ (clen t + 1 ≤ clen x) := hlen
        omega
      · exact Or.inl ⟨ConsList.cons a (ConsList.wrap ()), x, ConsList.cons a s, t, rfl, rfl,
          ⟨rfl, prefixP.nil s⟩⟩

/-- **van-laws**, the greedy theorem's hypothesis: `MonotonicAlg S (R;H)`, the two halves
    `van_mono_new` (7.16) and `van_mono` (7.17) together with the `nil` case. -/
public theorem van_mono_alg :
    MonotonicAlg (F := F Unit Tx) (Salg amount N) (RH Tx) :=
  le_iff.mpr fun u r h => by
    obtain ⟨v, hFv, hS⟩ := h
    cases u with
    | inl d =>
      cases v with
      | inl d' =>
        rw [Salg, junc_sum_inl] at hS
        obtain rfl : r = ConsList.wrap d' := hS
        refine ⟨ConsList.wrap d, ?_, Nat.le_refl _, fun _ => Or.inr ⟨rfl, rfl⟩⟩
        rw [Salg, junc_sum_inl]
        rfl
      | inr q => exact False.elim hFv
    | inr p =>
      cases v with
      | inl d' => exact False.elim hFv
      | inr q =>
        rw [Salg, junc_sum_inr] at hS
        have key : ((newR Tx ∪ oldR amount N) ≫ RH Tx) p r := by
          cases hS with
          | inl hnew =>
            exact le_iff.mp (van_mono_new (amount := amount) (N := N)) p r ⟨q, hFv, hnew⟩
          | inr hold =>
            exact le_iff.mp (van_mono (amount := amount) (N := N)) p r ⟨q, hFv, hold⟩
        obtain ⟨w, hw, hRHw⟩ := key
        refine ⟨w, ?_, hRHw⟩
        rw [Salg, junc_sum_inr]
        exact hw

/-! ## `van-laws` -/

/-- **van-laws**, the last row: the program refines the greedy choice —
    `⦇[nil,(ok→glue,new)]⦈ ⊑ ⦇Λ(S) est(R;H)⦈`, because `old ⊑ new (R;H)°`: `old` returns the
    shorter result wherever it returns one, and `ok` is where it does. -/
public theorem prog_le_greedy :
    progAlg amount N ⊑ Λ (Salg amount N) ≫ est (RH Tx) := by
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- the program's answer is one of `new` and `old`
    refine le_iff.mpr fun u r h => ?_
    cases u with
    | inl d =>
      rw [progAlg, junc_sum_inl] at h
      rw [Salg, junc_sum_inl]
      exact h
    | inr p =>
      rw [progAlg, junc_sum_inr] at h
      rw [Salg, junc_sum_inr]
      obtain ⟨a, x⟩ := p
      obtain rfl : r = progFn amount N (a, x) := h
      cases x with
      | wrap u => exact Or.inl rfl
      | cons s t =>
        refine Decidable.byCases (p := secureP amount N (ConsList.cons a s))
          (fun hs => ?_) (fun hs => ?_)
        · refine Or.inr ⟨s, t, rfl, ?_, hs⟩
          show progFn amount N (a, ConsList.cons s t) = ConsList.cons (ConsList.cons a s) t
          simp only [progFn, if_pos hs]
        · refine Or.inl ?_
          show progFn amount N (a, ConsList.cons s t) = newFn (a, ConsList.cons s t)
          simp only [progFn, if_neg hs]
          rfl
  · -- and it is `(R;H)`-at-least-as-good as every one of them
    refine le_iff.mpr fun r r' h => ?_
    obtain ⟨u, hS, hprog⟩ := h
    show RH Tx r' r
    have hS' : Salg amount N u r := hS
    cases u with
    | inl d =>
      rw [Salg, junc_sum_inl] at hS'
      rw [progAlg, junc_sum_inl] at hprog
      obtain rfl : r = ConsList.wrap d := hS'
      obtain rfl : r' = ConsList.wrap d := hprog
      exact ⟨Nat.le_refl _, fun _ => Or.inr ⟨rfl, rfl⟩⟩
    | inr p =>
      rw [Salg, junc_sum_inr] at hS'
      rw [progAlg, junc_sum_inr] at hprog
      clear hS
      obtain ⟨a, x⟩ := p
      obtain rfl : r' = progFn amount N (a, x) := hprog
      cases x with
      | wrap u =>
        have hr : r = newFn (a, ConsList.wrap u) := by
          cases hS' with
          | inl hnew => exact hnew
          | inr hold =>
            obtain ⟨s, t, hx, -, -⟩ := hold
            nomatch hx
        subst hr
        exact ⟨Nat.le_refl _, fun _ => Or.inl ⟨ConsList.cons a (ConsList.wrap ()),
          ConsList.wrap u, ConsList.cons a (ConsList.wrap ()), ConsList.wrap u, rfl, rfl,
          prefixP.refl _⟩⟩
      | cons s t =>
        refine Decidable.byCases (p := secureP amount N (ConsList.cons a s))
          (fun hs => ?_) (fun hs => ?_)
        · have hprog' : progFn amount N (a, ConsList.cons s t)
              = ConsList.cons (ConsList.cons a s) t := by simp only [progFn, if_pos hs]
          rw [hprog']
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
            exact ⟨Nat.le_refl _, fun _ => Or.inl ⟨ConsList.cons a s, t, ConsList.cons a s, t,
              rfl, rfl, prefixP.refl _⟩⟩
        · have hprog' : progFn amount N (a, ConsList.cons s t)
              = newFn (a, ConsList.cons s t) := by simp only [progFn, if_neg hs]; rfl
          rw [hprog']
          have hr : r = newFn (a, ConsList.cons s t) := by
            cases hS' with
            | inl hnew => exact hnew
            | inr hold =>
              obtain ⟨s', t', hx, -, hsec⟩ := hold
              injection hx with h1 h2
              subst h1
              exact absurd hsec hs
          subst hr
          exact ⟨Nat.le_refl _, fun _ => Or.inl ⟨ConsList.cons a (ConsList.wrap ()),
            ConsList.cons s t, ConsList.cons a (ConsList.wrap ()), ConsList.cons s t,
            rfl, rfl, prefixP.refl _⟩⟩

/-- **van-laws** (B&dM §7.5, p.188): the fewest secure segments the transactions can be cut
    into are one pass along them, the next transaction glued onto the open segment wherever
    that segment stays secure and the van called where it does not —
    `Λ(partition list(secure)) est(R) ⊒ ⦇[nil,(ok→glue,new)]⦈`.

    The chain is the note's: `partition list(secure) = ⦇S⦈` (`van_spec`); `R;H ⊑ R`, so
    `est(R;H) ⊑ est(R)`; the greedy theorem at `R;H`, whose hypothesis is `van_mono_alg`; and
    the program refining the greedy choice (`prog_le_greedy`). -/
public theorem van_laws
    (hsingle : ∀ a : Tx, secureP amount N (ConsList.cons a (ConsList.wrap ()))) :
    ⦇progAlg amount N⦈ ⊑ Λ (partition ≫ list (secure amount N)) ≫ est (R Tx) := by
  have hgreedy : ⦇Λ (Salg amount N) ≫ est (RH Tx)⦈
      ⊑ Λ ⦇Salg amount N⦈ ≫ est (RH Tx) :=
    greedy (F_preservesRecip Unit Tx) (initial Unit Tx) RH_trans van_mono_alg
  calc (⦇progAlg amount N⦈ : dList Tx ⟶ dSched Tx)
      ⊑ ⦇Λ (Salg amount N) ≫ est (RH Tx)⦈ :=
        relCata_mono (initial Unit Tx) prog_le_greedy
    _ ⊑ Λ ⦇Salg amount N⦈ ≫ est (RH Tx) := hgreedy
    _ ⊑ Λ ⦇Salg amount N⦈ ≫ est (R Tx) := comp_mono_left _ (est_mono RH_le_R)
    _ = Λ (partition ≫ list (secure amount N)) ≫ est (R Tx) := by rw [van_spec hsingle]

/-- **`van_spec` needs `hsingle`**: without the book's "N is at least as large as any single
    transaction", `partition list(secure)` and `⦇S⦈` differ.  At `N = 0` the one transaction
    `5` has no secure splitting at all, yet `new` carries no security test, so `⦇S⦈` still
    answers `[[5]]`. -/
public theorem van_spec_false_without_hsingle :
    partition ≫ list (secure (fun i : Int => i) 0) ≠ ⦇Salg (fun i : Int => i) 0⦈ := by
  intro hEq
  have hsq := (cata_square_junc_iff (wrapR : dL Unit ⟶ dSched Int)
    (newR Int ∪ oldR (fun i : Int => i) 0) ⦇Salg (fun i : Int => i) 0⦈).mp
    (relCata_cancel (initial Unit Int) (Salg (fun i : Int => i) 0))
  have hcata : ⦇Salg (fun i : Int => i) 0⦈
      (ConsList.cons (5 : Int) (ConsList.wrap ()))
      (ConsList.cons (ConsList.cons (5 : Int) (ConsList.wrap ())) (ConsList.wrap ())) :=
    (hsq.2 (5 : Int) (ConsList.wrap ()) _).mpr
      ⟨ConsList.wrap (), (hsq.1 () (ConsList.wrap ())).mpr rfl, Or.inl rfl⟩
  rw [← hEq] at hcata
  obtain ⟨-, -, hall⟩ := (partSecure_apply (amount := fun i : Int => i) (N := 0) _ _).mp hcata
  have hbad : ¬ secureP (fun i : Int => i) 0 (ConsList.cons (5 : Int) (ConsList.wrap ())) := by
    simp only [secureP, ceilingFn, floorFn]; omega
  exact hbad hall.1

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

open Lean PrettyPrinter in
@[app_unexpander glueR] public meta def unexpandGlueR : Unexpander
  | `($_ $_) => `($(mkIdent `glue))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander assoclR] public meta def unexpandAssoclR : Unexpander
  | `($_ $_ $_ $_) => `($(mkIdent `assocl))
  | _ => throw ()

end Freyd.Alg.RelSet.Van
