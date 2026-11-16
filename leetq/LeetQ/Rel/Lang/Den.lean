/-
  `⟦−⟧`: the meaning of a core term `Tm` as an arrow of `Rel(Set)` (`doc/rel-denotation-design.md` §1, §2, §7.3).
  Total and structural: each node is the `T` its `Gen.*_sound` lemma proves, written with the allegory's operators
  (`≫ ° ∩ ∪ 𝟙 𝟘`, D3 = E); `μ`, `ν` are `lfp`, `gfp`, defined for every body, so no monotonicity is assumed here.
-/
import LeetQ.Run.Lang.Tm
import LeetQ.Rel.Rep
import LeetQ.Rel.ObjOrder
import Freyd.Junc

namespace LeetQ.Rel.Lang

open QLean.Kernel LeetQ.Rel LeetQ.Rel.Rep Freyd Freyd.Alg Freyd.Alg.RelSet

/-- An arrow `A ⟶ B` of `Rel(Set)` between the elements of two objects. -/
abbrev Den (A B : Obj) := (⟨A.El⟩ : RelSet.{0}) ⟶ ⟨B.El⟩

/-- The meaning of each variable `k`, at the objects the term asks for. -/
abbrev Val := Nat → (A B : Obj) → Den A B

/-- No variable bound: what a closed term (`share`) is read under. -/
def Val.empty : Val := fun _ _ _ => 𝟘

open Classical in
/-- `ρ` with the variable `k` bound to `X : A ⟶ B`. A use of `k` at other objects is ill-typed and reads `𝟘`, so
    the binder hides every outer `k`, as `Tm.fv` drops it. -/
noncomputable def Val.bind (ρ : Val) (k : Nat) {A B : Obj} (X : Den A B) : Val := fun j A' B' =>
  if j = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ X else 𝟘) else ρ j A' B'

theorem Val.bind_ne {ρ : Val} {k j : Nat} {A B : Obj} {X : Den A B} (h : j ≠ k) : ρ.bind k X j = ρ j := by
  funext A' B'; simp [Val.bind, h]

theorem Val.bind_same {ρ ρ' : Val} {k : Nat} {A B : Obj} {X : Den A B} : ρ.bind k X k = ρ'.bind k X k := by
  funext A' B'; simp [Val.bind]

/-! ### Fixed points -/

/-- The least fixed point of `Φ`, below every pre-fixed point: defined for every `Φ`, a fixed point when `Φ` is
    monotone (`lfp_fix`). -/
def lfp {A B : Obj} (Φ : Den A B → Den A B) : Den A B := fun x y => ∀ Y : Den A B, Φ Y ⊑ Y → Y x y

/-- The greatest fixed point of `Φ`, above every post-fixed point. -/
def gfp {A B : Obj} (Φ : Den A B → Den A B) : Den A B := fun x y => ∃ Y : Den A B, Y ⊑ Φ Y ∧ Y x y

variable {A B C : Obj} {Φ Ψ : Den A B → Den A B} {Y : Den A B}

theorem le_refl' (X : Den A B) : X ⊑ X := le_iff.2 fun _ _ h => h

theorem lfp_le (h : Φ Y ⊑ Y) : lfp Φ ⊑ Y := le_iff.2 fun _ _ hx => hx Y h

theorem le_gfp (h : Y ⊑ Φ Y) : Y ⊑ gfp Φ := le_iff.2 fun _ _ hy => ⟨Y, h, hy⟩

theorem lfp_fix (hΦ : ∀ X Y : Den A B, X ⊑ Y → Φ X ⊑ Φ Y) : Φ (lfp Φ) = lfp Φ := by
  have h1 : Φ (lfp Φ) ⊑ lfp Φ :=
    le_iff.2 fun x y hx Y hY => le_iff.1 hY x y (le_iff.1 (hΦ _ _ (lfp_le hY)) x y hx)
  exact hom_ext fun x y => ⟨le_iff.1 h1 x y, le_iff.1 (lfp_le (hΦ _ _ h1)) x y⟩

theorem gfp_fix (hΦ : ∀ X Y : Den A B, X ⊑ Y → Φ X ⊑ Φ Y) : Φ (gfp Φ) = gfp Φ := by
  have h1 : gfp Φ ⊑ Φ (gfp Φ) :=
    le_iff.2 fun x y ⟨Y, hY, hy⟩ => le_iff.1 (hΦ _ _ (le_gfp hY)) x y (le_iff.1 hY x y hy)
  exact hom_ext fun x y => ⟨le_iff.1 (le_gfp (hΦ _ _ h1)) x y, le_iff.1 h1 x y⟩

/-- `lfp` is monotone in its body, pointwise: no monotonicity of either body is needed. -/
theorem lfp_mono (h : ∀ X, Φ X ⊑ Ψ X) : lfp Φ ⊑ lfp Ψ :=
  le_iff.2 fun _ _ hx Y hY => hx Y (le_iff.2 fun a b h' => le_iff.1 hY a b (le_iff.1 (h Y) a b h'))

theorem gfp_mono (h : ∀ X, Φ X ⊑ Ψ X) : gfp Φ ⊑ gfp Ψ :=
  le_iff.2 fun _ _ ⟨Y, hY, hy⟩ => ⟨Y, le_iff.2 fun a b h' => le_iff.1 (h Y) a b (le_iff.1 hY a b h'), hy⟩

/-! ### The named meanings: each the `T` of its node's `Gen.*_sound` lemma -/

/-- A table's value rows are the values its `rep` relates. -/
theorem valRow {A B : Obj} (U : Rel A B) (b : B.El) : (∃ p, U.val.row p = b) ↔ ∃ a, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.key.row p, p, rfl, e⟩, fun ⟨_, p, _, e⟩ => ⟨p, e⟩⟩

/-- `R − S`, pointwise. -/
abbrev diffDen (TR TS : Den A B) : Den A B := fun x y => TR x y ∧ ¬ TS x y

/-- `R\S` within the universes `UB`, `UC`: the book's left division where `R` has a column, every pair of the
    universes where it has none. -/
abbrev ldivDen (TR : Den A B) (TS : Den A C) (TB : Den B B) (TC : Den C C) : Den B C :=
  fun b c => (∀ a, TR a b → TS a c) ∧ ((∃ a, TR a b) ∨ ((∃ b', TB b' b) ∧ ∃ c', TC c' c))

/-- `R/S` within the universes `UA`, `UB`, the mirror of `ldivDen`. -/
abbrev rdivDen (TR : Den A C) (TS : Den B C) (TA : Den A A) (TB : Den B B) : Den A B :=
  fun x y => (∀ c, TS y c → TR x c) ∧ ((∃ c, TS y c) ∨ ((∃ a, TA a x) ∧ ∃ b, TB b y))

/-- `nil`: every source to the empty array. -/
abbrev nilDen : Den A (.arr B) := fun _ Y => Y = []

/-- `at(k)`: the element at position `k`. -/
abbrev atDen (k : Nat) : Den (.arr B) B := fun xs x => ∃ h : k < xs.length, x = xs[k]'h

/-- `succ` on the universe `TU`: `u` and its successor both in it. -/
abbrev succDen (TU : Den .long .long) : Den .long .long :=
  fun u w => (∃ v, TU u v) ∧ w = Ew.intStep Ew.add Alg.nul u 1 ∧ ∃ v, TU w v

/-- `≤` on the universe `TU`. -/
abbrev leqDen (TU : Den .long .long) : Den .long .long := fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ a ≤ b

/-- `<` on the universe `TU`. -/
abbrev ltDen (TU : Den .long .long) : Den .long .long := fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ a < b

/-- The value verb `k` on the universe `TU`: `Int64`'s step, not the null and, for `+ - *`, not wrapped. -/
abbrev arithDen (k : UInt8) (TU : Den .long .long) : Den (.prod .long .long) .long :=
  (fun (p : (Obj.prod .long .long).El) (w : Obj.long.El) => w = Ew.intStep k Alg.nul p.1 p.2 ∧ w ≠ Alg.nul ∧
    (if k == Ew.add then (0 ≤ p.2 ↔ p.1 ≤ w) else if k == Ew.sub then (0 ≤ p.2 ↔ w ≤ p.1)
     else if k == Ew.mul then (Ew.intStep Ew.idiv Alg.nul w p.1 = p.2 ∨ p.1 = 0) else True) : Den (.prod .long .long) .long) ≫ TU

/-- `fold(e, S)`: a chain of values `ys`, its last from `e`, each the step `S` of the element and the next value. -/
abbrev foldDen {E V : Obj} (Te : Den V V) (TS : Den (.prod E V) V) : Den (.arr E) V :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm))) ∧
    (∀ t (ht : t < xs.length), TS (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
      (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
    w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm)

/-- `fold(e, S)` given a family: at the key `i`, the fold whose start is the fibre of `e` at `i` and whose step is
    `S` at `i`, keeping the key. -/
abbrev foldIDen {I E V : Obj} (Te : Den I (.prod V V)) (TS : Den (.prod E (.prod I V)) (.prod I V)) :
    Den (.prod I (.arr E)) V :=
  fun p w => foldDen (fun a b => Te p.1 (a, b)) (fun q v => TS (q.1, (p.1, q.2)) (p.1, v)) p.2 w

/-- `Rᴵ`: the family `R : I ⟶ A×B` as one relation of the key and the source. -/
abbrev flatDen {I A B : Obj} (T : Den I (.prod A B)) : Den (.prod I A) B := fun x b => T x.1 (x.2, b)

/-- `est(Q)` keeps `b` of `xs` unless some other `c` of `xs` fails `Q` at `(b, c)`. -/
abbrev estDen (TQ : Den (.prod B B) (.prod B B)) : Den (.arr B) B :=
  fun xs b => b ∈ xs ∧ ¬ ∃ c, c ∈ xs ∧ c ≠ b ∧ ¬ TQ (b, c) (b, c)

/-- `Λ(T)` with `𝒫B` held as `[B]` (D2 = C): `a` to the one list of its image strictly ascending by `Obj.lt`, the
    order `Rel.Canon` puts a table's rows in; no list where that image has no such list. -/
abbrev lamDen (T : Den A B) : Den A (.arr B) := fun a ys => ys.Pairwise B.lt ∧ ∀ b, b ∈ ys ↔ T a b

/-- `E(T) = Λ(∋ T)`: an array to the canonical list of the images of its elements. -/
abbrev EDen (T : Den A B) : Den (.arr A) (.arr B) := lamDen ((fun xs a => a ∈ xs : Den (.arr A) A) ≫ T)

/-- `thin(Q)` as `CRel.thinOn` computes it: the canonical list of the `c` of `xs` that no `b` of `xs` beats
    strictly, `Q` read as its pair test as in `estDen`. -/
abbrev thinDen (TQ : Den (.prod B B) (.prod B B)) : Den (.arr B) (.arr B) :=
  lamDen fun xs c => c ∈ xs ∧ ¬ ∃ b, b ∈ xs ∧ TQ (b, c) (b, c) ∧ ¬ TQ (c, b) (c, b)

/-! ### `⟦−⟧` -/

/-- `⟦t⟧ρ`, one clause per constructor. `𝟘` at the nodes whose meaning is not settled yet: `prim` and `arg` (the
    row's meaning, `Row`), `call` (a `let` node). -/
noncomputable def Tm.den : Val → {A B : Obj} → {d : Bool} → Tm A B d → Den A B
  | _, _, _, _, .val R => rep R
  | _, _, _, _, .uni U => rep (Alg.idU U)
  | _, _, _, _, .zero => 𝟘
  | _, _, _, _, .id => 𝟙 _
  | ρ, _, _, _, .top V => relTop ≫ V.den ρ
  | _, _, _, _, .outl => graph Prod.fst
  | _, _, _, _, .outr => graph Prod.snd
  | ρ, _, _, _, .comp R S => R.den ρ ≫ S.den ρ
  | ρ, _, _, _, .conv R => (R.den ρ)°
  | ρ, _, _, _, .meet R S => R.den ρ ∩ S.den ρ
  | ρ, _, _, _, .join R S => R.den ρ ∪ S.den ρ
  | ρ, _, _, _, .diff R S => diffDen (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .dom R => 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)°
  | ρ, _, _, _, .ran R => 𝟙 _ ∩ (R.den ρ)° ≫ (R.den ρ)°°
  | ρ, _, _, _, .ldiv R S U V => ldivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, _, .rdiv R S U V => rdivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, _, .pair R S => rpair (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .prod R S => rprodMap (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .junc R S => Freyd.Alg.junc (sumCop _ _) (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .juncD R S => Freyd.Alg.junc (sumCop _ _) (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .lam R => lamDen (R.den ρ)
  | ρ, _, _, _, .E R => EDen (R.den ρ)
  | ρ, _, _, _, .est Q => estDen (Q.den ρ)
  | ρ, _, _, _, .thin Q => thinDen (Q.den ρ)
  | _, _, _, _, .nil => nilDen
  | _, _, _, _, .prim _ => 𝟘
  | _, _, _, _, .atPos k => atDen k
  | ρ, _, _, _, .own R => R.den ρ
  | ρ, _, _, _, .succ U => succDen (U.den ρ)
  | ρ, _, _, _, .arith k U => arithDen k (U.den ρ)
  | ρ, _, _, _, .leq U => leqDen (U.den ρ)
  | ρ, _, _, _, .lt U => ltDen (U.den ρ)
  | ρ, _, _, _, .fold e S => foldDen (e.den ρ) (S.den ρ)
  | _, _, _, _, .share _ R => R.den Val.empty
  | ρ, _, _, _, .foldI e S => foldIDen (e.den ρ) (S.den ρ)
  | ρ, _, _, _, .flat R => flatDen (R.den ρ)
  | ρ, A, B, _, .var k => ρ k A B
  | _, _, _, _, .call .. => 𝟘
  | _, _, _, _, .arg .. => 𝟘
  | ρ, _, _, _, .nu k _ b => gfp fun X => b.den (ρ.bind k X)
  | ρ, _, _, _, .mu k _ _ b => lfp fun X => b.den (ρ.bind k X)
  | ρ, _, _, _, .refold k _ _ b => lfp fun X => b.den (ρ.bind k X)

/-- `⟦t⟧` reads `ρ` only at the variables free in `t`. -/
theorem Tm.den_congr : ∀ {A B : Obj} {d : Bool} (t : Tm A B d) (ρ ρ' : Val), (∀ i ∈ t.fv, ρ i = ρ' i) →
    t.den ρ = t.den ρ' := by
  intro A B d t
  induction t with
  | var k => intro ρ ρ' h; simp only [Tm.den, h k (by simp [Tm.fv])]
  | top V ih => intro ρ ρ' h; simp only [Tm.den, ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])]
  | comp R S ihR ihS | meet R S ihR ihS | join R S ihR ihS | diff R S ihR ihS | pair R S ihR ihS
  | prod R S ihR ihS | junc R S ihR ihS | juncD R S ihR ihS | fold R S ihR ihS | foldI R S ihR ihS =>
    intro ρ ρ' h
    simp only [Tm.den, ihR ρ ρ' fun i hi => h i (by simp [Tm.fv, hi]), ihS ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])]
  | conv R ih | dom R ih | ran R ih | own R ih | est R ih | succ R ih | arith _ R ih | leq R ih | lt R ih
  | flat R ih | lam R ih | E R ih | thin R ih =>
    intro ρ ρ' h; simp only [Tm.den, ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])]
  | ldiv R S U V ihR ihS ihU ihV | rdiv R S U V ihR ihS ihU ihV =>
    intro ρ ρ' h
    simp only [Tm.den, ihR ρ ρ' fun i hi => h i (by simp [Tm.fv, hi]), ihS ρ ρ' fun i hi => h i (by simp [Tm.fv, hi]),
      ihU ρ ρ' fun i hi => h i (by simp [Tm.fv, hi]), ihV ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])]
  | nu k _ b _ ih | mu k _ _ b ih | refold k _ _ b _ ih =>
    intro ρ ρ' h
    simp only [Tm.den]
    congr 1; funext X
    refine ih _ _ fun i hi => ?_
    by_cases e : i = k
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact h i (by simp [Tm.fv, hi, e])
  | _ => intro ρ ρ' _; rfl

/-! ### Monotonicity -/

/-- `ρ'` grows `ρ` at the variable `k` and agrees with it at every other. -/
def Val.Grow (k : Nat) (ρ ρ' : Val) : Prop := (∀ A B, ρ k A B ⊑ ρ' k A B) ∧ ∀ i, i ≠ k → ρ i = ρ' i

/-- `X ⊑ Y` read with the sign `s`: `true` keeps it, `false` turns it round. -/
def sle (s : Bool) {A B : Obj} (X Y : Den A B) : Prop := cond s (X ⊑ Y) (Y ⊑ X)

theorem Val.Grow.congr {k : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') {A B : Obj} {d : Bool} {t : Tm A B d}
    (h : t.fv.contains k = false) : t.den ρ = t.den ρ' :=
  t.den_congr ρ ρ' fun i hi => g.2 i fun e => by subst e; simp [hi] at h

theorem Val.Grow.bind {k j : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') (hj : j ≠ k) {A B : Obj} (X : Den A B) :
    Grow k (ρ.bind j X) (ρ'.bind j X) := by
  refine ⟨fun A' B' => ?_, fun i hi => ?_⟩
  · rw [Val.bind_ne (Ne.symm hj), Val.bind_ne (Ne.symm hj)]; exact g.1 A' B'
  · by_cases e : i = j
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact g.2 i hi

/-- Binding `k` to a larger `Y` grows the valuation at `k`. -/
theorem Val.Grow.of_le {k : Nat} {ρ : Val} {X Y : Den A B} (hXY : X ⊑ Y) : Grow k (ρ.bind k X) (ρ.bind k Y) := by
  refine ⟨fun A' B' => ?_, fun i hi => by rw [Val.bind_ne hi, Val.bind_ne hi]⟩
  simp only [Val.bind, if_true]
  by_cases h : A = A' ∧ B = B'
  · obtain ⟨rfl, rfl⟩ := h; simpa using hXY
  · simp only [dif_neg h]; exact le_refl' _

section ops
variable {D E F : Obj}

theorem comp_le' {X X' : Den A B} {Y Y' : Den B C} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ≫ Y ⊑ X' ≫ Y' :=
  le_iff.2 fun a c h => by
    rw [comp_apply] at h ⊢; obtain ⟨b, h1, h2⟩ := h; exact ⟨b, le_iff.1 hX _ _ h1, le_iff.1 hY _ _ h2⟩

theorem conv_le' {X X' : Den A B} (hX : X ⊑ X') : X° ⊑ X'° :=
  le_iff.2 fun a b h => by rw [recip_apply] at h ⊢; exact le_iff.1 hX _ _ h

theorem inter_le' {X X' Y Y' : Den A B} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ∩ Y ⊑ X' ∩ Y' :=
  le_iff.2 fun a b h => by rw [inter_apply] at h ⊢; exact ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

theorem union_le' {X X' Y Y' : Den A B} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ∪ Y ⊑ X' ∪ Y' :=
  le_iff.2 fun a b h => by rw [union_apply] at h ⊢; exact h.imp (le_iff.1 hX _ _) (le_iff.1 hY _ _)

theorem diff_le {X X' Y Y' : Den A B} (hX : X ⊑ X') (hY : Y' ⊑ Y) : diffDen X Y ⊑ diffDen X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, fun h' => h.2 (le_iff.1 hY _ _ h')⟩

theorem ldiv_le {R : Den A B} {S S' : Den A C} {U U' : Den B B} {V V' : Den C C} (hS : S ⊑ S') (hU : U ⊑ U')
    (hV : V ⊑ V') : ldivDen R S U V ⊑ ldivDen R S' U' V' :=
  le_iff.2 fun _ _ h => ⟨fun a ha => le_iff.1 hS _ _ (h.1 a ha),
    h.2.imp id fun ⟨⟨b', hb⟩, c', hc⟩ => ⟨⟨b', le_iff.1 hU _ _ hb⟩, c', le_iff.1 hV _ _ hc⟩⟩

theorem rdiv_le {R R' : Den A C} {S : Den B C} {U U' : Den A A} {V V' : Den B B} (hR : R ⊑ R') (hU : U ⊑ U')
    (hV : V ⊑ V') : rdivDen R S U V ⊑ rdivDen R' S U' V' :=
  le_iff.2 fun _ _ h => ⟨fun c hc => le_iff.1 hR _ _ (h.1 c hc),
    h.2.imp id fun ⟨⟨a, ha⟩, b, hb⟩ => ⟨⟨a, le_iff.1 hU _ _ ha⟩, b, le_iff.1 hV _ _ hb⟩⟩

theorem pair_le {X X' : Den A B} {Y Y' : Den A C} (hX : X ⊑ X') (hY : Y ⊑ Y') : rpair X Y ⊑ rpair X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

theorem prod_le {X X' : Den A B} {Y Y' : Den C D} (hX : X ⊑ X') (hY : Y ⊑ Y') : rprodMap X Y ⊑ rprodMap X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

theorem junc_le {X X' : Den A C} {Y Y' : Den B C} (hX : X ⊑ X') (hY : Y ⊑ Y') :
    Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) X Y ⊑ Freyd.Alg.junc (sumCop _ _) X' Y' :=
  le_iff.2 fun x c h => by
    simp only [Freyd.Alg.junc, union_apply, comp_apply] at h ⊢
    exact h.imp (fun ⟨b, h1, h2⟩ => ⟨b, h1, le_iff.1 hX _ _ h2⟩) (fun ⟨b, h1, h2⟩ => ⟨b, h1, le_iff.1 hY _ _ h2⟩)

end ops

theorem sle.refl {s : Bool} (X : Den A B) : sle s X X := by cases s <;> exact le_refl' X

theorem sle.of_eq {s : Bool} {X Y : Den A B} (h : X = Y) : sle s X Y := h ▸ sle.refl X

theorem sle.map1 {A' B' : Obj} {f : Den A B → Den A' B'} (hf : ∀ {X X'}, X ⊑ X' → f X ⊑ f X') :
    ∀ {s X X'}, sle s X X' → sle s (f X) (f X')
  | true, _, _, h | false, _, _, h => hf h

theorem sle.map2 {A' B' A'' B'' : Obj} {f : Den A B → Den A' B' → Den A'' B''}
    (hf : ∀ {X X' Y Y'}, X ⊑ X' → Y ⊑ Y' → f X Y ⊑ f X' Y') :
    ∀ {s X X' Y Y'}, sle s X X' → sle s Y Y' → sle s (f X Y) (f X' Y')
  | true, _, _, _, _, h1, h2 | false, _, _, _, _, h1, h2 => hf h1 h2

/-- The second argument antitone: `diff`. -/
theorem sle.anti2 {f : Den A B → Den A B → Den A B} (hf : ∀ {X X' Y Y'}, X ⊑ X' → Y' ⊑ Y → f X Y ⊑ f X' Y') :
    ∀ {s X X' Y Y'}, sle s X X' → sle (!s) Y Y' → sle s (f X Y) (f X' Y')
  | true, _, _, _, _, h1, h2 | false, _, _, _, _, h1, h2 => hf h1 h2

theorem sle.map3 {A' B' A'' B'' A''' B''' : Obj} {f : Den A B → Den A' B' → Den A'' B'' → Den A''' B'''}
    (hf : ∀ {X X' Y Y' Z Z'}, X ⊑ X' → Y ⊑ Y' → Z ⊑ Z' → f X Y Z ⊑ f X' Y' Z') :
    ∀ {s X X' Y Y' Z Z'}, sle s X X' → sle s Y Y' → sle s Z Z' → sle s (f X Y Z) (f X' Y' Z')
  | true, _, _, _, _, _, _, h1, h2, h3 | false, _, _, _, _, _, _, h1, h2, h3 => hf h1 h2 h3

theorem sle.lfp {s : Bool} (h : ∀ X, sle s (Φ X) (Ψ X)) : sle s (lfp Φ) (lfp Ψ) := by
  cases s
  · exact lfp_mono h
  · exact lfp_mono h

theorem sle.gfp {s : Bool} (h : ∀ X, sle s (Φ X) (Ψ X)) : sle s (gfp Φ) (gfp Ψ) := by
  cases s
  · exact gfp_mono h
  · exact gfp_mono h

/-- **Polarity**: where `t.pol s k`, growing the variable `k` moves `⟦t⟧` with the sign `s`. `den_mono` and
    `den_anti` are its two signs, one induction. -/
theorem Tm.den_pol (k : Nat) : ∀ {A B : Obj} {d : Bool} (t : Tm A B d) (s : Bool) (ρ ρ' : Val),
    t.pol s k = true → Val.Grow k ρ ρ' → sle s (t.den ρ) (t.den ρ') := by
  intro A B d t
  induction t with
  | var j =>
    intro s ρ ρ' hp g
    simp only [Tm.den]
    by_cases e : j = k
    · subst e; simp only [Tm.pol, beq_self_eq_true, if_true] at hp; subst hp; exact g.1 _ _
    · rw [g.2 j e]; exact sle.refl _
  | top V ih => intro s ρ ρ' hp g; exact sle.map1 (comp_le' (le_refl' _)) (ih s ρ ρ' hp g)
  | conv R ih => intro s ρ ρ' hp g; exact sle.map1 conv_le' (ih s ρ ρ' hp g)
  | own R ih => intro s ρ ρ' hp g; exact ih s ρ ρ' hp g
  | dom R ih =>
    intro s ρ ρ' hp g
    exact sle.map1 (fun h => inter_le' (le_refl' _) (comp_le' h (conv_le' h))) (ih s ρ ρ' hp g)
  | ran R ih =>
    intro s ρ ρ' hp g
    exact sle.map1 (fun h => inter_le' (le_refl' _) (comp_le' (conv_le' h) (conv_le' (conv_le' h)))) (ih s ρ ρ' hp g)
  | comp R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 comp_le' (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | meet R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 inter_le' (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | join R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 union_le' (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | pair R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 pair_le (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | prod R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 prod_le (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | junc R S ihR ihS | juncD R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 junc_le (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | diff R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.anti2 diff_le (ihR s ρ ρ' hp.1 g) (ihS (!s) ρ ρ' hp.2 g)
  | ldiv R S U V _ ihS ihU ihV =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [Tm.den, g.congr hp.1.1.1]
    exact sle.map3 ldiv_le (ihS s ρ ρ' hp.1.1.2 g) (ihU s ρ ρ' hp.1.2 g) (ihV s ρ ρ' hp.2 g)
  | rdiv R S U V ihR _ ihU ihV =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [Tm.den, g.congr hp.1.1.2]
    exact sle.map3 rdiv_le (ihR s ρ ρ' hp.1.1.1 g) (ihU s ρ ρ' hp.1.2 g) (ihV s ρ ρ' hp.2 g)
  | nu j _ b _ ih | mu j _ _ b ih | refold j _ _ b _ ih =>
    intro s ρ ρ' hp g
    simp only [Tm.den]
    by_cases e : j = k
    · subst e
      have hb : ∀ {A' B' : Obj} (X : Den A' B'), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
        by_cases e' : i = j
        · subst e'; exact Val.bind_same
        · rw [Val.bind_ne e', Val.bind_ne e', g.2 i e']
      simp only [hb]; exact sle.refl _
    · simp only [Tm.pol, Bool.or_eq_true, beq_iff_eq, e, false_or] at hp
      first
        | exact sle.lfp fun X => ih s _ _ hp (g.bind e X)
        | exact sle.gfp fun X => ih s _ _ hp (g.bind e X)
  | _ => intro s ρ ρ' hp g; exact sle.of_eq (g.congr (by first | simpa [Tm.pol] using hp | simp [Tm.fv]))

/-- `⟦t⟧` is monotone in `X` where `X` occurs only positively. -/
theorem Tm.den_mono {A' B' : Obj} {d : Bool} {t : Tm A' B' d} {k : Nat} (h : t.pol true k = true) {ρ : Val}
    {X Y : Den A B} (hXY : X ⊑ Y) : t.den (ρ.bind k X) ⊑ t.den (ρ.bind k Y) :=
  t.den_pol k true _ _ h (Val.Grow.of_le hXY)

/-- `⟦t⟧` is antitone in `X` where `X` occurs only negatively. -/
theorem Tm.den_anti {A' B' : Obj} {d : Bool} {t : Tm A' B' d} {k : Nat} (h : t.pol false k = true) {ρ : Val}
    {X Y : Den A B} (hXY : X ⊑ Y) : t.den (ρ.bind k Y) ⊑ t.den (ρ.bind k X) :=
  t.den_pol k false _ _ h (Val.Grow.of_le hXY)

#print axioms Tm.den_pol
#print axioms lfp_fix

end LeetQ.Rel.Lang
