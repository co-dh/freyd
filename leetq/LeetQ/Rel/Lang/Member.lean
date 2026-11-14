import Std.Data.HashMap
import Std.Data.HashSet
import LeetQ.Rel.Lang.Elab

/-! # Membership tests: a term asked only "is `(x,y)` in it?"

`K₀ ∩ π₁\(sup(X) X)` needs, for each row `(u,v)` of `K₀`, only whether `(u,v)` is in the division:

```
(u,v) ∈ π₁\(sup(X) X)   ⟺   for every m,  some w  with  (u,m) {sup(X)} w {X} v
```

so the division is never a table: each row is one test, `∀` stopping at the first `m` with no witness and `∃`
at the first witness. A plan (`TP`) keeps the constructors that have a test rule (`≫`, `°`, `∩`, `∪`, `−`, `\`)
and holds every other sub-term as its table (a leaf). All the plan's tables and the tested rows are coded
jointly per object (`Obj.codesC`), so an element is a number, and each leaf is indexed once (`Ix`).

Each rule answers in two modes, in either direction `f` (`true`: `x` to `y`; `false`: the converse):
- test: is `(x,y)` in it;
- image: the `y`s with `x` related to `y`, which a composition enumerates on its cheaper side (`fan`).

`Answers o H` says the ops `o` answer the relation `H` on the codes; each rule's theorem says that the rule
answers the relational operation on what its parts answer: `∃` for `≫`, `∀` for `\`, `∧`, `∨`, `∧¬`, swap. -/

namespace LeetQ.Rel.Lang.Member

open QLean LeetQ.Rel LeetQ.Rel.Alg

/-! ### A table's index over its codes -/

/-- `m` with `p.2` added to the image of `p.1`. -/
def add (m : Std.HashMap Nat (Array Nat)) (p : Nat × Nat) : Std.HashMap Nat (Array Nat) :=
  m.insert p.1 ((m.getD p.1 #[]).push p.2)

theorem mem_foldl_add (l : List (Nat × Nat)) (m : Std.HashMap Nat (Array Nat)) (x y : Nat) :
    y ∈ (l.foldl add m).getD x #[] ↔ y ∈ m.getD x #[] ∨ (x, y) ∈ l := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨a, b⟩ := p
    by_cases h : a = x
    · subst h; simp only [add, Std.HashMap.getD_insert, BEq.rfl, if_true, Array.mem_push, List.mem_cons, Prod.mk.injEq,
        true_and]
      constructor
      · rintro ((h | h) | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]
    · have h' : (a == x) = false := by simpa using h
      simp only [add, Std.HashMap.getD_insert, h', Bool.false_eq_true, if_false, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (h1 | h1) <;> simp [h1]
      · rintro (h1 | ⟨h1, _⟩ | h1)
        · exact .inl h1
        · exact absurd h1.symm h
        · exact .inr h1

/-- Each key's image in `l`. -/
def index (l : List (Nat × Nat)) : Std.HashMap Nat (Array Nat) := l.foldl add {}

theorem mem_index (l : List (Nat × Nat)) (x y : Nat) : y ∈ (index l).getD x #[] ↔ (x, y) ∈ l := by
  simp [index, mem_foldl_add]

theorem contains_foldl (l : List (Nat × Nat)) (s : Std.HashSet (Nat × Nat)) (p : Nat × Nat) :
    (l.foldl (·.insert ·) s).contains p = true ↔ s.contains p = true ∨ p ∈ l := by
  induction l generalizing s with
  | nil => simp
  | cons q l ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl h.symm)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h.symm)
      · exact .inr h

/-- A table of code pairs, indexed once: each key's image (`fwd`), each value's preimage (`bwd`), the pairs as a
    set, and the mean image size each way (`kf`, `kb`, at least `1`), the cost a composition compares. -/
structure Ix where
  ps : Array (Nat × Nat)
  fwd : Std.HashMap Nat (Array Nat)
  bwd : Std.HashMap Nat (Array Nat)
  set : Std.HashSet (Nat × Nat)
  kf : Nat
  kb : Nat

def Ix.of (ps : Array (Nat × Nat)) : Ix :=
  let fwd := index ps.toList; let bwd := index (ps.toList.map Prod.swap)
  ⟨ps, fwd, bwd, ps.toList.foldl (·.insert ·) {}, ps.size / max fwd.size 1 + 1, ps.size / max bwd.size 1 + 1⟩

/-! ### The ops a rule answers with -/

/-- A term's membership test and image in the direction `f`, and its mean image size that way. -/
structure Ops where
  test : Bool → Nat → Nat → Bool
  img : Bool → Nat → Array Nat
  fan : Bool → Nat

/-- `H` in the direction `f`: `H x y` forward, `H y x` backward. -/
def dir (H : Nat → Nat → Prop) : Bool → Nat → Nat → Prop
  | true, x, y => H x y
  | false, x, y => H y x

/-- `o` answers `H`: a test is membership in `H`, an image is the set of `H`-partners, in each direction. -/
def Answers (o : Ops) (H : Nat → Nat → Prop) : Prop :=
  ∀ f x y, (o.test f x y = true ↔ dir H f x y) ∧ (y ∈ o.img f x ↔ dir H f x y)

def Ix.ops (i : Ix) : Ops where
  test f x y := if f then i.set.contains (x, y) else i.set.contains (y, x)
  img f x := (if f then i.fwd else i.bwd).getD x #[]
  fan f := if f then i.kf else i.kb

/-- A table's index answers its pairs: a hash lookup per test, per image. -/
theorem answers_ix (ps : Array (Nat × Nat)) : Answers (Ix.of ps).ops fun x y => (x, y) ∈ ps.toList := by
  intro f x y
  cases f
  · refine ⟨by simp only [Ix.ops, Ix.of, dir, Bool.false_eq_true, if_false, contains_foldl, Std.HashSet.contains_empty, false_or], ?_⟩
    simp only [Ix.ops, Ix.of, dir, Bool.false_eq_true, if_false, mem_index, List.mem_map]
    exact ⟨fun ⟨⟨a, b⟩, h, e⟩ => by cases e; exact h, fun h => ⟨(y, x), h, rfl⟩⟩
  · exact ⟨by simp only [Ix.ops, Ix.of, dir, if_true, contains_foldl, Std.HashSet.contains_empty, Bool.false_eq_true, false_or], by simp [Ix.ops, Ix.of, dir, mem_index]⟩

/-- `R°`: the direction flipped. -/
def conv (r : Ops) : Ops := ⟨fun f => r.test !f, fun f => r.img !f, fun f => r.fan !f⟩

theorem answers_conv {r : Ops} {H : Nat → Nat → Prop} (hr : Answers r H) : Answers (conv r) fun x y => H y x := by
  intro f x y; cases f <;> exact hr _ x y

/-- `R ∩ S`: both tests; the image of the side of smaller fan-out, filtered by the other's test. -/
def meet (r s : Ops) : Ops where
  test f x y := r.test f x y && s.test f x y
  img f x := if r.fan f ≤ s.fan f then (r.img f x).filter (s.test f x ·) else (s.img f x).filter (r.test f x ·)
  fan f := min (r.fan f) (s.fan f)

theorem dir_and (H K : Nat → Nat → Prop) (f : Bool) (x y : Nat) :
    dir (fun x y => H x y ∧ K x y) f x y ↔ dir H f x y ∧ dir K f x y := by cases f <;> exact Iff.rfl

theorem answers_meet {r s : Ops} {H K : Nat → Nat → Prop} (hr : Answers r H) (hs : Answers s K) :
    Answers (meet r s) fun x y => H x y ∧ K x y := by
  intro f x y
  obtain ⟨hr1, hr2⟩ := hr f x y; obtain ⟨hs1, hs2⟩ := hs f x y
  refine ⟨by simp [meet, hr1, hs1, dir_and], ?_⟩
  simp only [meet, dir_and]; split <;> simp [Array.mem_filter, hr2, hs1, hr1, hs2, and_comm]

/-- `R ∪ S`: either test; the two images. -/
def join (r s : Ops) : Ops where
  test f x y := r.test f x y || s.test f x y
  img f x := r.img f x ++ s.img f x
  fan f := r.fan f + s.fan f

theorem answers_join {r s : Ops} {H K : Nat → Nat → Prop} (hr : Answers r H) (hs : Answers s K) :
    Answers (join r s) fun x y => H x y ∨ K x y := by
  intro f x y
  obtain ⟨hr1, hr2⟩ := hr f x y; obtain ⟨hs1, hs2⟩ := hs f x y
  have e : dir (fun x y => H x y ∨ K x y) f x y ↔ dir H f x y ∨ dir K f x y := by cases f <;> exact Iff.rfl
  exact ⟨by simp [join, hr1, hs1, e], by simp [join, hr2, hs2, e]⟩

/-- `R − S`: `R`'s test and not `S`'s; `R`'s image filtered. -/
def diff (r s : Ops) : Ops where
  test f x y := r.test f x y && !s.test f x y
  img f x := (r.img f x).filter (!s.test f x ·)
  fan f := r.fan f

theorem answers_diff {r s : Ops} {H K : Nat → Nat → Prop} (hr : Answers r H) (hs : Answers s K) :
    Answers (diff r s) fun x y => H x y ∧ ¬K x y := by
  intro f x y
  obtain ⟨hr1, hr2⟩ := hr f x y; obtain ⟨hs1, hs2⟩ := hs f x y
  have e : dir (fun x y => H x y ∧ ¬K x y) f x y ↔ dir H f x y ∧ ¬dir K f x y := by cases f <;> exact Iff.rfl
  have hs1' : s.test f x y = false ↔ ¬dir K f x y := by rw [← hs1]; simp
  exact ⟨by simp [diff, hr1, hs1', e], by simp [diff, hr2, hs1', e]⟩

/-- `R S` in the direction `f`, `a` first and `b` second (`R`, `S` forward; `S`, `R` backward): some middle `z`,
    enumerated from the end whose image is smaller — `x`'s under `a`, or `y`'s under `b` backward — and each
    tested against the other side. -/
def compTest (a b : Ops) (f : Bool) (x y : Nat) : Bool :=
  if a.fan f ≤ b.fan !f then (a.img f x).any (b.test f · y) else (b.img (!f) y).any (a.test f x ·)

def comp (r s : Ops) : Ops where
  test f := if f then compTest r s f else compTest s r f
  img f x := if f then (r.img f x).flatMap (s.img f) else (s.img f x).flatMap (r.img f)
  fan f := r.fan f * s.fan f

theorem compTest_iff {a b : Ops} {H K : Nat → Nat → Prop} (f : Bool) (ha : Answers a H) (hb : Answers b K)
    (x y : Nat) : compTest a b f x y = true ↔ ∃ z, dir H f x z ∧ dir K f z y := by
  unfold compTest; split
  · simp only [Array.any_eq_true']
    exact ⟨fun ⟨z, h1, h2⟩ => ⟨z, ((ha f x z).2.1 h1), (hb f z y).1.1 h2⟩,
      fun ⟨z, h1, h2⟩ => ⟨z, (ha f x z).2.2 h1, (hb f z y).1.2 h2⟩⟩
  · simp only [Array.any_eq_true']
    have hb' : ∀ z, z ∈ b.img (!f) y ↔ dir K f z y := fun z => by
      rw [(hb (!f) y z).2]; cases f <;> exact Iff.rfl
    exact ⟨fun ⟨z, h1, h2⟩ => ⟨z, (ha f x z).1.1 h2, (hb' z).1 h1⟩,
      fun ⟨z, h1, h2⟩ => ⟨z, (hb' z).2 h2, (ha f x z).1.2 h1⟩⟩

theorem answers_comp {r s : Ops} {H K : Nat → Nat → Prop} (hr : Answers r H) (hs : Answers s K) :
    Answers (comp r s) fun x y => ∃ z, H x z ∧ K z y := by
  intro f x y
  cases f
  · refine ⟨?_, ?_⟩
    · simp only [comp, Bool.false_eq_true, if_false]
      rw [compTest_iff false hs hr]
      exact ⟨fun ⟨z, h1, h2⟩ => ⟨z, h2, h1⟩, fun ⟨z, h1, h2⟩ => ⟨z, h2, h1⟩⟩
    · simp only [comp, Bool.false_eq_true, if_false, Array.mem_flatMap]
      exact ⟨fun ⟨z, h1, h2⟩ => ⟨z, (hr false z y).2.1 h2, (hs false x z).2.1 h1⟩,
        fun ⟨z, h1, h2⟩ => ⟨z, (hs false x z).2.2 h2, (hr false z y).2.2 h1⟩⟩
  · refine ⟨?_, ?_⟩
    · simp only [comp, if_true]; exact compTest_iff true hr hs x y
    · simp only [comp, if_true, Array.mem_flatMap]
      exact ⟨fun ⟨z, h1, h2⟩ => ⟨z, (hr true x z).2.1 h1, (hs true z y).2.1 h2⟩,
        fun ⟨z, h1, h2⟩ => ⟨z, (hr true x z).2.2 h1, (hs true z y).2.2 h2⟩⟩

/-- Whether `x` is a value of the table `i`: its preimage has an element. -/
def Ix.hasVal (i : Ix) (x : Nat) : Bool := (i.bwd.getD x #[]).any fun _ => true

theorem hasVal_iff (ps : Array (Nat × Nat)) (x : Nat) : (Ix.of ps).hasVal x = true ↔ ∃ k, (k, x) ∈ ps.toList := by
  simp only [Ix.hasVal, Array.any_eq_true', and_true]
  exact ⟨fun ⟨k, h⟩ => by
      obtain ⟨⟨a, b⟩, hm, e⟩ := List.mem_map.1 ((mem_index _ x k).1 h); cases e; exact ⟨_, hm⟩,
    fun ⟨k, h⟩ => ⟨k, (mem_index _ x k).2 (List.mem_map.2 ⟨(k, x), h, rfl⟩)⟩⟩

/-- `R\S` at `(x,y)`, `x` a value of `UB` and `y` of `UC` (the universes `leftDiv` divides over): every `a` with
    `a R x`, enumerated as `x`'s image under `R°`, has `a S y`; the test stops at the first `a` without. -/
def ldivCore (r s : Ops) (B C : Ix) (x y : Nat) : Bool :=
  B.hasVal x && C.hasVal y && (r.img false x).all (s.test true · y)

/-- `R\S`: the test above; an image enumerates the universe of the other end and tests each. -/
def ldiv (r s : Ops) (B C : Ix) : Ops where
  test f x y := if f then ldivCore r s B C x y else ldivCore r s B C y x
  img f x := if f then (C.ps.map (·.2)).filter (ldivCore r s B C x ·) else (B.ps.map (·.2)).filter (ldivCore r s B C · x)
  fan f := if f then C.ps.size else B.ps.size

theorem ldivCore_iff {r s : Ops} {H K : Nat → Nat → Prop} (hr : Answers r H) (hs : Answers s K)
    (B C : Array (Nat × Nat)) (x y : Nat) :
    ldivCore r s (Ix.of B) (Ix.of C) x y = true ↔
      (∃ k, (k, x) ∈ B.toList) ∧ (∃ k, (k, y) ∈ C.toList) ∧ ∀ a, H a x → K a y := by
  simp only [ldivCore, Bool.and_eq_true, hasVal_iff, Array.all_eq_true', and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h a ha => (hs true a y).1.1 (h a ((hr false x a).2.2 ha)),
    fun h a ha => (hs true a y).1.2 (h a ((hr false x a).2.1 ha))⟩)

theorem answers_ldiv {r s : Ops} {H K : Nat → Nat → Prop} (hr : Answers r H) (hs : Answers s K)
    (B C : Array (Nat × Nat)) :
    Answers (ldiv r s (Ix.of B) (Ix.of C))
      fun x y => (∃ k, (k, x) ∈ B.toList) ∧ (∃ k, (k, y) ∈ C.toList) ∧ ∀ a, H a x → K a y := by
  intro f x y
  have mv : ∀ (ps : Array (Nat × Nat)) z, z ∈ ((Ix.of ps).ps.map (·.2)) ↔ ∃ k, (k, z) ∈ ps.toList := fun ps z => by
    simp only [Ix.of, Array.mem_map, Array.mem_toList_iff]
    exact ⟨fun ⟨⟨k, b⟩, h, e⟩ => ⟨k, by cases e; exact h⟩, fun ⟨k, h⟩ => ⟨(k, z), h, rfl⟩⟩
  cases f
  · refine ⟨by simp only [ldiv, Bool.false_eq_true, if_false]; exact ldivCore_iff hr hs B C y x, ?_⟩
    simp only [ldiv, Bool.false_eq_true, if_false, Array.mem_filter, mv, ldivCore_iff hr hs B C, dir]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  · refine ⟨by simp only [ldiv, if_true]; exact ldivCore_iff hr hs B C x y, ?_⟩
    simp only [ldiv, if_true, Array.mem_filter, mv, ldivCore_iff hr hs B C, dir]
    exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩

/-! ### The plan: a term over its tables -/

/-- A closed term with its test-rule constructors kept and every other sub-term a table. -/
inductive TP : Obj → Obj → Type where
  | leaf {A B : Obj} (R : Rel A B) : TP A B
  | comp {A B C : Obj} (R : TP A B) (S : TP B C) : TP A C
  | conv {A B : Obj} (R : TP A B) : TP B A
  | meet {A B : Obj} (R S : TP A B) : TP A B
  | join {A B : Obj} (R S : TP A B) : TP A B
  | diff {A B : Obj} (R S : TP A B) : TP A B
  | ldiv {A B C : Obj} (R : TP A B) (S : TP A C) (UB : Rel B B) (UC : Rel C C) : TP B C

/-- The plan as a table: `Alg`'s op at each node, what `ev` computes for the term. -/
def TP.table : {A B : Obj} → TP A B → Rel A B
  | _, _, .leaf R => R
  | _, _, .comp R S => let r := R.table; if r.n == 0 then zero else r ≫ S.table
  | _, _, .conv R => R.table°
  | _, _, .meet R S => R.table ∩ S.table
  | _, _, .join R S => R.table ∪ S.table
  | _, _, .diff R S => R.table \ S.table
  | _, _, .ldiv R S UB UC => leftDiv R.table S.table UB.val UC.val

/-- A column of some object. -/
abbrev Col := (X : Obj) × Part X

def relCols {A B : Obj} (R : Rel A B) (cs : Array Col) : Array Col := (cs.push ⟨A, ⟨R.n, R.key⟩⟩).push ⟨B, ⟨R.n, R.val⟩⟩

/-- The tables' columns, two per table, in the order `TP.ops` reads them back. -/
def TP.cols : {A B : Obj} → TP A B → Array Col → Array Col
  | _, _, .leaf R, cs => relCols R cs
  | _, _, .comp R S, cs | _, _, .meet R S, cs | _, _, .join R S, cs | _, _, .diff R S, cs => S.cols (R.cols cs)
  | _, _, .conv R, cs => R.cols cs
  | _, _, .ldiv R S UB UC, cs => relCols UC (relCols UB (S.cols (R.cols cs)))

/-- Each column's codes, the columns of one object coded jointly (`Obj.codesC`), so equal elements are equal
    numbers; `none` when a coding did not run within capacity. -/
def codeAll (cs : Array Col) : Option (Array (Array Nat)) := do
  let mut out : Array (Array Nat) := Array.replicate cs.size #[]
  let mut seen : Array Obj := #[]
  for c in cs do
    if seen.contains c.1 then continue
    seen := seen.push c.1
    let A := c.1
    let js := (Array.range cs.size).filter fun j => (cs.getD j c).1 == A
    let parts : Array (Part A) := js.map fun j => match cs.getD j c with
      | ⟨B, p⟩ => if h : B = A then h ▸ p else ⟨0, Vals.empty A⟩
    let (codes, ok) := A.codesC (p := parts.size) ⟨parts, rfl⟩
    guard ok
    for k in [0:js.size] do
      let code := codes.toArray.getD k default
      out := out.set! (js.getD k 0) ((Array.range code.n.toNat).map (Column.idAt code.b code.w ·))
  pure out

/-- The next table's index: its two code columns. -/
def take (ids : Array (Array Nat)) : StateM Nat Ix :=
  modifyGet fun i => (Ix.of ((ids.getD i #[]).zip (ids.getD (i + 1) #[])), i + 2)

/-- The plan's ops, each table indexed once from its codes, read in `TP.cols`' order. -/
def TP.ops (ids : Array (Array Nat)) : {A B : Obj} → TP A B → StateM Nat Ops
  | _, _, .leaf _ => return (← take ids).ops
  | _, _, .comp R S => return Member.comp (← R.ops ids) (← S.ops ids)
  | _, _, .conv R => return Member.conv (← R.ops ids)
  | _, _, .meet R S => return Member.meet (← R.ops ids) (← S.ops ids)
  | _, _, .join R S => return Member.join (← R.ops ids) (← S.ops ids)
  | _, _, .diff R S => return Member.diff (← R.ops ids) (← S.ops ids)
  | _, _, .ldiv R S _ _ => do
    let r ← R.ops ids; let s ← S.ops ids; let b ← take ids; let c ← take ids
    pure (Member.ldiv r s b c)

/-- The rows of `R` whose pair is (`pos`) or is not (`!pos`) in the plan `p`, one test per row, coded jointly with
    the plan's tables; `none` when the coding did not run within capacity. -/
def keep? {A B : Obj} (R : Rel A B) (p : TP A B) (pos : Bool) : Option (Rel A B) := do
  let ids ← codeAll (p.cols #[⟨A, ⟨R.n, R.key⟩⟩, ⟨B, ⟨R.n, R.val⟩⟩])
  let o := Id.run ((p.ops ids).run' 2)
  let ks := ids.getD 0 #[]; let vs := ids.getD 1 #[]
  let idx := (Array.range R.n.toNat).foldl (init := ByteArray.empty) fun b i =>
    if o.test true (ks.getD i 0) (vs.getD i 0) == pos then Column.pushBits b i.toUInt64 8 else b
  pure (R.rows idx)

/-- `R ∩ p` (`pos`) or `R − p`: `keep?`, or the plan's table where the coding did not run within capacity. -/
def keep {A B : Obj} (R : Rel A B) (p : TP A B) (pos : Bool) : Rel A B :=
  match keep? R p pos with
  | some V => V
  | none => if pos then R ∩ p.table else R \ p.table

/-- A plan with a test rule at its root: one a test is worth running on, where a leaf is a table already. -/
def TP.lazy {A B : Obj} : TP A B → Bool
  | .leaf _ => false
  | _ => true

/-- The plan `p`, or the table `t` as a leaf where there is none. -/
def orLeaf {m : Type → Type} [Monad m] {A B : Obj} (p : m (Option (TP A B))) (t : m (Rel A B)) : m (TP A B) := do
  match ← p with
  | some q => pure q
  | none => return .leaf (← t)

/-- A side as a table: its plan's, or `t` where it has none. -/
def tab {m : Type → Type} [Monad m] {A B : Obj} (p : Option (TP A B)) (t : m (Rel A B)) : m (Rel A B) :=
  match p with
  | some q => pure q.table
  | none => t

/-- `R ∩ S` from the sides' plans `pR`, `pS` (or their tables `r`, `s`): a side with a test rule is tested on the
    other's rows, the right one first; two tables meet as tables. -/
def meetM {m : Type → Type} [Monad m] {A B : Obj} (pR pS : Option (TP A B)) (r s : m (Rel A B)) : m (Rel A B) :=
  match pR, pS with
  | _, some p => if p.lazy then return keep (← tab pR r) p true else
    match pR with
    | some q => pure (if q.lazy then keep p.table q true else q.table ∩ p.table)
    | none => return (← r) ∩ p.table
  | some q, none => if q.lazy then return keep (← s) q true else return q.table ∩ (← s)
  | none, none => return (← r) ∩ (← s)

/-- `R − S`: `S` tested on `R`'s rows where it has a test rule, else two tables. -/
def diffM {m : Type → Type} [Monad m] {A B : Obj} (pR pS : Option (TP A B)) (r s : m (Rel A B)) : m (Rel A B) :=
  match pS with
  | some p => if p.lazy then return keep (← tab pR r) p false else return (← tab pR r) \ p.table
  | none => return (← tab pR r) \ (← s)

end LeetQ.Rel.Lang.Member
