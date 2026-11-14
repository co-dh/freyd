/-
  The operators of the relation algebra on the core (RelRep design §2.3): each a pipeline of qlean
  kernels over a `Rel`'s two payloads, with the order, the power side, the list functions and the
  predicates built on them. The codes they compare through are in `LeetQ.Rel.Code`.
-/
import LeetQ.Rel.Code

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel

/-! ## The operators -/

section Gen

variable {A B C : Obj}

/-- `R ⊑ S`: `member` of `|R|` in `|S|`, all set. -/
private def le (R S : Rel A B) : Bool :=
  let c := pairs #v[R, S]
  len (whereBits R.n (c[0].member c[1])) == R.n.toNat

/-- `R ∩ S`: the semi-join on pairs — `member`, `whereBits`, `gatherColumn`. -/
private def inter (R S : Rel A B) : Rel A B :=
  let c := pairs #v[R, S]
  R.rows (whereBits R.n (c[0].member c[1]))

/-- `𝟘`: no pair. -/
def zero : Rel A B := ⟨0, Vals.empty A, Vals.empty B⟩

/-- A stopped run's model relation. -/
instance : Inhabited (Rel A B) := ⟨zero⟩

/-- `R ∪ S`: `razeColumn` of keys and of vals, both at the summed count (`Obj.raze`), the first row of each pair;
    the summed count fits a `USize`. -/
private def union (R S : Rel A B) : Rel A B :=
  need (R.n.toNat + S.n.toNat < USize.size) (fun _ => s!"∪: {R.n} + {S.n} rows do not fit a USize")
    (fun _ => zero) fun h =>
  Rel.nub ⟨_, A.raze #[⟨_, R.key⟩, ⟨_, S.key⟩] (by simpa using h), B.raze #[⟨_, R.val⟩, ⟨_, S.val⟩] (by simpa using h)⟩

/-- `⊤` on the universes `Ua`, `Ub`: `cross`, its two index columns of one length (`cross_len`). -/
def top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  let c := cross ma mb
  longCount "⊤" c.1 fun m h => ⟨m, Vals.pick A Ua c.1 m h, Vals.pick B Ub c.2 m ((cross_len ma mb).trans h)⟩

/-- `𝟙` on `U`: key and val the one column, shared. -/
def idU {t : Obj} {m : USize} (U : Vals t m) : Rel t t := ⟨m, U, U⟩

theorem idU_holds {t : Obj} {m : USize} (U : Vals t m) (x y : t.El) :
    (idU U).Holds x y ↔ x = y ∧ ∃ i, U.row i = x := by
  simp only [Rel.Holds, idU]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨h1 ▸ h2, i, h1⟩, fun ⟨h, i, h1⟩ => ⟨i, h1, h ▸ h1⟩⟩

/-- `R°`: the two fields swap, nothing runs. -/
def convArr {k v : Obj} {n : USize} (key : Vals k n) (val : Vals v n) : Rel v k := ⟨n, val, key⟩

theorem convArr_holds {k v : Obj} {n : USize} (key : Vals k n) (val : Vals v n) (x : k.El) (y : v.El) :
    (convArr key val).Holds y x ↔ (⟨n, key, val⟩ : Rel k v).Holds x y := by
  simp only [Rel.Holds, convArr]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

/-- `R°`: `convArr`. -/
private def conv (R : Rel A B) : Rel B A := convArr R.key R.val

/-- `R ≫ S`: `join` on `R.val = S.key`, the key picked from `R`, the val from `S`. -/
private def comp (R : Rel A B) (S : Rel B C) : Rel A C :=
  let c := B.codes #v[⟨_, R.val⟩, ⟨_, S.key⟩]
  let ij := join c[0] c[1]
  longCount "≫" ij.2 fun m h =>
    ⟨m, Vals.pickN A R.key ij.1 m (h ▸ join_len c[0] c[1]), Vals.pick C S.val ij.2 m h⟩

/-- The coreflexive on the distinct elements of `x`: the first row of each code. -/
def distinctCorefl (t : Obj) {n : USize} (x : Vals t n) : Rel t t :=
  let i := (t.codes #v[⟨n, x⟩])[0].groupIds.2
  longCount "distinct" i fun m h => let d := Vals.pick t x i m h; ⟨m, d, d⟩

/-- `dom R`: the coreflexive on the distinct keys. -/
def dom (R : Rel A B) : Rel A A := distinctCorefl A R.key

/-- `ran R`: the coreflexive on the distinct vals. -/
def ran (R : Rel A B) : Rel B B := distinctCorefl B R.val

/-- `R ≫ corNeg(C)`, the anti-join: the rows of `R` whose value is no value of `C` (`anti` on one joint coding). -/
def antiJoin (R : Rel A B) (C : Rel B B) : Rel A B :=
  let vc := B.codes #v[⟨_, R.val⟩, ⟨_, C.val⟩]
  R.rows (anti vc[0] vc[1])

/-- `R − S`: the rows of `R` whose pair is no pair of `S` — `inter`'s joint pair codes, `anti` in place of `member`. -/
private def diff (R S : Rel A B) : Rel A B :=
  let c := pairs #v[R, S]
  R.rows (anti c[0] c[1])

/-! ## The ops as binary operators: the only way a program writes them -/

instance : Inter (Rel A B) := ⟨inter⟩
instance : Union (Rel A B) := ⟨union⟩
instance : SDiff (Rel A B) := ⟨diff⟩
/-- `R ≫ S`: composition in diagram order, first `R` then `S`. -/
scoped infixl:80 " ≫ " => comp
/-- `R°`: the converse. -/
scoped postfix:max "°" => conv
/-- `R ⊑ S`: inclusion, decided. -/
scoped infix:50 " ⊑ " => le
/-- `R = S` as `R ⊑ S ∧ S ⊑ R`: the same pairs, whatever the row order and multiplicity. -/
instance : BEq (Rel A B) := ⟨fun R S => R ⊑ S && S ⊑ R⟩

/-- The elements of the object `A` in this program: what `𝟙` and `⊤` range over. -/
class Univ (A : Obj) where
  n : USize
  xs : Vals A n

/-- `𝟙 : A ⟶ A`, the identity on the elements of `A`. -/
scoped notation "𝟙" => idU Univ.xs
/-- `⊤ : A ⟶ B`, every pair. -/
scoped notation "⊤" => top Univ.xs Univ.xs
/-- `∼R`: the complement of `R` in `⊤`. -/
scoped notation:max "∼" R:max => ⊤ \ R

/-- `R \ S` (`R : a ⟶ b`, `S : a ⟶ c`), by counting: `join` on the shared key → rows `(y, z)`;
    `cnt(y, z)` against `cnt(R.val)` `at` `y`; the vacuous `y ∉ ran R` with every `z` from the
    universes `Ub`, `Uc`: `⊤` on `anti(Ub, ran R)` and `Uc`. The two parts are disjoint (a counted `y` is in
    `ran R`) and meet by `∪`, whose counts are proved where a `raze` of the parts would need its own. -/
def leftDiv {mb mc : USize} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc) : Rel B C :=
  let r := R.nub; let s := S.nub
  let kc := A.codes #v[⟨_, r.key⟩, ⟨_, s.key⟩]
  let ij := join kc[0] kc[1]
  -- the left index column read at the right's count (`join_len`), as `comp`
  let y : Rel B C := longCount "\\" ij.2 fun m h =>
    ⟨m, Vals.pickN B r.val ij.1 m (h ▸ join_len kc[0] kc[1]), Vals.pick C s.val ij.2 m h⟩
  let ycs := B.codes #v[⟨_, y.key⟩, ⟨_, r.val⟩, ⟨_, Ub⟩]
  let yc := ycs[0]; let rvc := ycs[1]; let ubc := ycs[2]
  let zc := (C.codes #v[⟨_, y.val⟩])[0]
  let (gid, firsts) := tuples.tupleIds yc #[zc]
  let got := classSizes yc.n (gid, firsts)
  let keep := longCount "\\" firsts fun g _ => gather 8 firsts (whereEqV g got (atCnt (cnt rvc) (yc.gather firsts)))
  union (y.rows keep) (top (Vals.pickPart B Ub (anti ubc rvc)).2 Uc)

/-- `R / S = (S° \ R°)°` (`R : a ⟶ c`, `S : b ⟶ c`); its vacuous term is `⊤` on `Ua` and `anti(Ub, dom S)`. -/
def rightDiv {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  conv (leftDiv (conv S) (conv R) Ub Ua)

/-- `R /ₛ S` (`R : a ⟶ c`, `S : b ⟶ c`), equal fibres: the fibres of `R` and of `S` as `segments`
    of one value code space, their `setIds` in one call, `join` on the ids → `(x, y)`, the keys read as
    `comp` reads them (`join_len`); the vacuous term `⊤` on `anti(Ua, dom R)` and `anti(Ub, dom S)`, the
    empty fibres, met by `∪`. -/
def symDiv {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  let vc := C.codes #v[⟨_, R.val⟩, ⟨_, S.val⟩]
  let ac := A.codes #v[⟨_, R.key⟩, ⟨_, Ua⟩]; let rk := ac[0]; let uac := ac[1]
  let bc := B.codes #v[⟨_, S.key⟩, ⟨_, Ub⟩]; let sk := bc[0]; let ubc := bc[1]
  let (pr, orr, fr) := segments rk; let (ps, os, fs) := segments sk
  -- each `segments` offsets end at its code count, so `S`'s starts shifted by `|R|` follow `R`'s
  let ss := os.extract 0 (os.size - 8)
  let ids := longCount "/ₛ" ss fun c _ =>
    setIds (Code.cat #[vc[0].gather pr, vc[1].gather ps]) (concatBytes #[orr.extract 0 (orr.size - 8), addc c ss R.n.toNat])
  let lc := Code.ofLongs (ids.extract 0 (8 * len fr)); let rc := Code.ofLongs (ids.extract (8 * len fr) ids.size)
  let ij := join lc rc
  let rf := Vals.pickPart A R.key fr; let sf := Vals.pickPart B S.key fs
  let hit : Rel A B := longCount "/ₛ" ij.2 fun m h =>
    ⟨m, Vals.pickN A rf.2 ij.1 m (h ▸ join_len lc rc), Vals.pick B sf.2 ij.2 m h⟩
  union hit (top (Vals.pickPart A Ua (anti uac rk)).2 (Vals.pickPart B Ub (anti ubc sk)).2)

/-- `Λ(R) : A ⟶ arr B`: one row per distinct key of `R`, its cell the ARRAY of the key's values, each once,
    in ascending value order (`sortBy`), so two keys with one set of values have one array — across two
    relations too, where `sortBy` orders by value. `Rel.nub`, the values sorted, then the keys' codes
    graded stably: each key one run, whose start and end (`runStarts`) are its row's `lo`, `hi`. -/
def transpose (R : Rel A B) : Rel A (.arr B) :=
  let d := R.nub
  let kc := (A.codes #v[⟨_, d.key⟩])[0]
  let vp := B.sortBy d.val (tilLongs d.n)
  let p := gather 8 vp (kc.gather vp).grade
  let o := (kc.gather p).runStarts
  let lo := o.extract 0 (o.size - 8)
  have h : len (o.extract 8 o.size) = len lo := by simp only [len, lo, ByteArray.size_extract]; omega
  let dk := Vals.pickPart A d.key p; let dv := Vals.pickPart B d.val p
  longCount "Λ" lo fun m hm => ⟨m, Vals.pick A dk.2 lo m hm,
    ⟨dv.1, toUSize_eq hm ▸ longCol lo, toUSize_eq (h.trans hm) ▸ longCol (o.extract 8 o.size), dv.2⟩⟩

/-- `∋ : arr B ⟶ B` on the arrays `X`: each array to each of its elements, one row per element (an array
    holding a value twice relates to it twice). `expand` of the clamped slice counts, each copy's rank
    added to its slice's start; both read at the copies' count `expand` hands on. -/
def mem {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) B :=
  let s := slicesOf X
  expand n s.2 (fun _ => default) fun m i r hi _ =>
    ⟨m, Vals.pick (.arr B) X i m hi, Vals.pick B X.2.2.2 (add m (gather 8 s.1 i) r) m (len_val ..)⟩

/-- `Λ(R) : A ⟶ arr B`, each key of `R` to the array of its values. -/
scoped notation:max "Λ(" R ")" => transpose R
/-- `∋(R) : arr B ⟶ B`, `mem` on the arrays of `Λ(R)`: `Λ(R) ≫ ∋(R) = R`. -/
scoped notation:max "∋(" R ")" => mem (Rel.val (transpose R))

end Gen

variable {A B C : QAtomicType}

/-- `⟨R, S⟩`: `join` on the keys → rows `(x, (y, z))`, both value sides kept under one `n` as the
    columns of one product side; the left index column read at the right's count (`join_len`), as `comp`. -/
def pair {A B C : Obj} (R : Rel A B) (S : Rel A C) : Rel A (.prod B C) :=
  let kc := A.codes #v[⟨_, R.key⟩, ⟨_, S.key⟩]
  let ij := join kc[0] kc[1]
  let h := join_len kc[0] kc[1]
  longCount "⟨R,S⟩" ij.2 fun m hm =>
    ⟨m, Vals.pickN A R.key ij.1 m (hm ▸ h), (Vals.pickN B R.val ij.1 m (hm ▸ h), Vals.pick C S.val ij.2 m hm)⟩

/-- `outl`: the first component's columns, nothing runs. -/
def outl {k v w : Obj} (T : Rel k (.prod v w)) : Rel k v := ⟨T.n, T.key, T.val.1⟩
/-- `outr`: the second component's columns. -/
def outr {k v w : Obj} (T : Rel k (.prod v w)) : Rel k w := ⟨T.n, T.key, T.val.2⟩

/-- The rows of `R` numbered from `k`: row `i` keyed by `k + i`, its value kept — `Ew.val` add on `til`
    at the count `m`, which the row index is too (`Ew.val_size`). Row order enters here, as in `enum`. -/
def num {A B : Obj} (R : Rel A B) (k : USize) : Rel .long B :=
  let m := R.n
  ⟨m, valCol Ew.add Ew.va (tilLongs m) (one k.toUInt64), Vals.pick B R.val (tilLongs m) m (len_tilLongs m)⟩

theorem outl_holds {k v w : Obj} (T : Rel k (.prod v w)) (x : k.El) (y : v.El) :
    (outl T).Holds x y ↔ ∃ z, T.Holds x (y, z) :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨T.val.2.row i, i, h1, by subst h2; rfl⟩, fun ⟨_, i, h1, h2⟩ => ⟨i, h1, congrArg Prod.fst h2⟩⟩

theorem outr_holds {k v w : Obj} (T : Rel k (.prod v w)) (x : k.El) (z : w.El) :
    (outr T).Holds x z ↔ ∃ y, T.Holds x (y, z) :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨T.val.1.row i, i, h1, by subst h2; rfl⟩, fun ⟨_, i, h1, h2⟩ => ⟨i, h1, congrArg Prod.snd h2⟩⟩

/-- `R × S` as a relation of its own, `(x, x') ⟶ (y, y')`: `cross` of the rows of `R` and of `S`.
    `Δ(R)` is `prod R R`. Its two index columns have one length (`cross_len`). -/
def prod {A B D E : Obj} (R : Rel A B) (S : Rel D E) : Rel (.prod A D) (.prod B E) :=
  let c := cross R.n S.n
  longCount "×" c.1 fun m h =>
    ⟨m, (Vals.pick A R.key c.1 m h, Vals.pick D S.key c.2 m ((cross_len R.n S.n).trans h)),
      (Vals.pick B R.val c.1 m h, Vals.pick E S.val c.2 m ((cross_len R.n S.n).trans h))⟩

/-- `n` bits, all `x`: `Ew.cmp` of `til n` against `0`. -/
def bitsOf (x : Bool) (n : USize) : ByteArray :=
  Ew.cmp (if x then Ew.ge else Ew.lt) Ew.i64 Ew.va (tilLongs n) (one 0) n

/-- The tag column of parts `ps`, each `(count, tag)`, `m` the summed count: `concatBits` of constant bit
    columns, of the summed count whatever the parts' payloads hold (`concatBits_wf`). -/
def tags (ps : Array (USize × Bool)) (m : USize) (h : ps.foldl (fun s p => s + p.1.toNat) 0 = m.toNat := by simp) :
    Arr .boolean m :=
  let bs : Array (USize × ByteArray) := ps.map fun p => (p.1, bitsOf p.2 p.1)
  have hb : m.toNat = bs.foldl (fun s p => s + p.1.toNat) 0 := by rw [Array.foldl_map]; exact h.symm
  -- the payload is read off `concatBits_wf`'s statement: `.bits (concatBits (countBytes …) …)`
  Arr.mk _ (KernelWF.concatBits_wf bs hb)

/-- Under the fits bound, `USize` addition is the `Nat` one. -/
theorem toNat_add_fits {n m : USize} (h : n.toNat + m.toNat < USize.size) : (n + m).toNat = n.toNat + m.toNat := by
  rw [USize.toNat_add]; exact Nat.mod_eq_of_lt h

/-- The sum side holding `X` then `Y` as they are: `n` rows tagged `inl`, then `m` tagged `inr` (`tags`), each
    row its own position in its side (`tilCol`); no value copied. `n + m` fits a `USize`. -/
def sumVals {A B : Obj} {n m : USize} (X : Vals A n) (Y : Vals B m) (hN : n.toNat + m.toNat < USize.size) :
    Vals (.sum A B) (n + m) :=
  ⟨n, m, tags #[(n, false), (m, true)] (n + m) (by simp [toNat_add_fits hN]),
    toUSize_eq (toNat_add_fits hN).symm ▸ razeTo .long #[⟨n, tilCol n⟩, ⟨m, tilCol m⟩] (by simp) hN, X, Y⟩

/-- `inl : A ⟶ A + B` on the universe `X`: each `x` to `inl x`, the sum side's left payload `X` itself. -/
def inl {A B : Obj} {n : USize} (X : Vals A n) : Rel A (.sum A B) := ⟨n, X, ⟨n, 0, tags #[(n, false)] n, tilCol n, X, Vals.empty B⟩⟩

/-- `inr : B ⟶ A + B` on the universe `Y`: each `y` to `inr y`. -/
def inr {A B : Obj} {n : USize} (Y : Vals B n) : Rel B (.sum A B) := ⟨n, Y, ⟨0, n, tags #[(n, true)] n, tilCol n, Vals.empty A, Y⟩⟩

/-- `[R, S] : A + B ⟶ C`: `inl x` to what `R` relates `x` to, `inr y` to what `S` relates `y` to. The keys are
    the two key payloads as they are (`sumVals`), the values razed (`Obj.raze`), `R.n + S.n` rows, which fit a
    `USize`. -/
def junc {A B C : Obj} (R : Rel A C) (S : Rel B C) : Rel (.sum A B) C :=
  need (R.n.toNat + S.n.toNat < USize.size) (fun _ => s!"[R,S]: {R.n} + {S.n} rows do not fit a USize")
    (fun _ => zero) fun hN =>
  ⟨R.n + S.n, sumVals R.key S.key hN,
    toUSize_eq (by rw [toNat_add_fits hN]) ▸ C.raze #[⟨_, R.val⟩, ⟨_, S.val⟩] (by simpa using hN)⟩

/-- `R + S ≜ [R inl, S inr] : A + B ⟶ C + D`, built directly: the key and the value sides share one tag and one
    position column over the payloads of `R` and of `S` as they are, where the composites would join each
    relation with an injection and raze the values (the guard below holds it equal to that term). -/
def sum {A B C D : Obj} (R : Rel A C) (S : Rel B D) : Rel (.sum A B) (.sum C D) :=
  need (R.n.toNat + S.n.toNat < USize.size) (fun _ => s!"R + S: {R.n} + {S.n} rows do not fit a USize")
    (fun _ => zero) fun hN =>
  let k := sumVals R.key S.key hN
  ⟨R.n + S.n, k, ⟨R.n, S.n, k.2.2.1, k.2.2.2.1, R.val, S.val⟩⟩

/-- An unfold then a fold: Lean's loop, rounds of `step` until `done`, each round kernels. It ends because
    each round not `done` lowers the measure `μ`: well-founded recursion, no fuel. -/
def hylo {α : Type} (μ : α → Nat) (done : α → Bool) (step : α → α)
    (dec : ∀ x, done x = false → μ (step x) < μ x) (x : α) : α :=
  if h : done x then x else hylo μ done step dec (step x)
termination_by μ x
decreasing_by exact dec x (Bool.eq_false_iff.2 h)

/-- `f` from `a` until `done`, at most `n` rounds: `hylo` with the rounds left as its measure, so a caller
    bounds the iteration by a count instead of proving a measure of its own. -/
def iter {α : Type} (n : Nat) (done : α → Bool) (f : α → α) (a : α) : α :=
  (hylo (·.1) (fun x => x.1 == 0 || done x.2) (fun x => (x.1 - 1, f x.2))
    (fun x h => by simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h; show x.1 - 1 < x.1; omega) (n, a)).2

/-- A fixed point of `φ` from `X₀`: rounds `X ↦ nub(φ(X))`, at most `n`, until a round leaves the row count as
    it was, with the rounds run. On a chain (`φ` monotonic, `X₀ ⊑ φ(X₀)` or `φ(X₀) ⊑ X₀`) an equal count is an
    equal relation, so the stop is the fixed point; `n` bounds the rounds, as the chain's length does. -/
def fixOn {A B : Obj} (n : Nat) (φ : Rel A B → Rel A B) (X₀ : Rel A B) : Rel A B × Nat :=
  let x := X₀.nub
  let r := iter n (fun (p, x, _) => p == x.n.toNat) (fun (_, x, k) => (x.n.toNat, (φ x).nub, k + 1))
    (x.n.toNat + 1, x, 0)
  (r.2.1, r.2.2)

/-- One arc `A\(X C)` of an AC-3 body (`A : V ⟶ V`, `C : D ⟶ D`), with `𝟙(D)` for its division. -/
structure Revise (V D : Obj) where
  A : Rel V V
  C : Rel D D
  UV : Rel V V
  UD : Rel D D

/-- The AC-3 body `s ∩ ⋂ₖ Aₖ\(X Cₖ)`, one naive round: `fixOn` on it is `νX` the naive way. -/
def acRound {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (X : Rel V D) : Rel V D :=
  as.foldl (fun Y a => Y ∩ leftDiv a.A (X ≫ a.C) a.UV.key a.UD.key) s

/-- One delta round of the AC-3 body, from `(X, Δ)`, `Δ ⊑ 𝟙(V)` the variables whose domain shrank last round:
    `X′ = X ∩ ⋂ₖ (Δ Aₖ)\(X Cₖ)` and `Δ′ = dom(X − X′)`. `(Δ A)\…` is `⊤` at every `x ∉ ran(Δ A)`, so each
    division runs only on the rows `ran(Δ A)` (its universe there, so no vacuous row is made) and keeps `X`'s
    other rows; `X − X′` is the anti-join of the pairs. The tie to the naive round, stated, not proved here:
    `Δ`, `Δ′` coreflexive, `Δ ∪ Δ′ = 𝟙`, `Δ′X′ = Δ′X`, `X′ = s ∩ A\(X C)` ⟹ `s ∩ A\(X′ C) = X′ ∩ (Δ A)\(X′ C)`,
    by `(R∪S)\T = R\T ∩ S\T` and `Δ′A\(X′C) = Δ′A\(XC) ⊒ A\(XC) ⊒ X′`. -/
def acDelta {V D : Obj} (as : List (Revise V D)) (p : Rel V D × Rel V V) : Rel V D × Rel V V :=
  let (X, Δ) := p
  let X' := as.foldl (fun Y a =>
    let R := Δ ≫ a.A; let T := ran R
    (antiJoin Y° T)° ∪ (Y ∩ leftDiv R (Δ ≫ X ≫ a.C) T.key a.UD.key)) X
  (X', ran (outl (antiJoin (idU (X.key, X.val)) (idU (X'.key, X'.val)))))

/-- `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` by delta rounds from `(s, 𝟙(V))` — the first the naive round — until `Δ′ = 𝟘`,
    at most `|s| + 1`, with the rounds run. -/
def acFix {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) : Rel V D × Nat :=
  let x := s.nub
  let r := iter (x.n.toNat + 1) (fun (_, Δ, _) => Δ.n == 0)
    (fun (X, Δ, k) => let (X', Δ') := acDelta as (X, Δ); (X', Δ', k + 1)) (x, U, 0)
  (r.1, r.2.2)

/-- The order `Q` as a test of pairs:the pairs of the coreflexive `D` that are pairs of `Q`. Every op that
    takes an order runs it as such a test, on the pairs it compares (`estOn`, …); `Q` closed is this test. -/
def pairsIn {B : Obj} (Q : Rel B B) (D : Rel (.prod B B) (.prod B B)) : Rel (.prod B B) (.prod B B) :=
  D ≫ idU (Q.key, Q.val)

/-- The pairs `(b, c)` of the coreflexive `D` whose swap `(c, b)` passes the test `q`. -/
def swapIn {B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (D : Rel (.prod B B) (.prod B B)) : Rel (.prod B B) (.prod B B) :=
  let s := pair (outr D) (outl D)
  dom (s ≫ q (ran s))

/-- `thin(Q)` per key, `Q` the test `q` run on the pairs `⟨G,G⟩` of values of one key, never on every pair of
    `ran G`: `(a, c)` dropped when some value `b` of `a` passes `(b, c)` and not `(c, b)`. `thin Q` is this at
    `pairsIn Q`. -/
def thinOn {A B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B)) (G : Rel A B) :
    Rel A B :=
  let P := pair G G
  let D := ran P
  G \ P ≫ outr (q D \ swapIn q D)

/-- `est(Q)` per key, `Q` the test `q` run on the pairs `⟨G,G⟩` of values of one key: `(a, b)` dropped when
    some other value `c` of `a` fails `(b, c)`. `est Q` is this at `pairsIn Q`. -/
def estOn {A B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B)) (G : Rel A B) :
    Rel A B :=
  let P := pair G G
  let D := ran P
  let V := ran G
  G \ P ≫ outl ((D \ q D) \ ran (pair V V))

/-- `est(Q)` per key of the family `G : A ⟶ B`, the `Q`-least values, `∋ ∩ (∈ \ Q°)`: the rows `(a, b)` of
    `G` with `b Q c` for every other value `c` of `a`. The pairs `(a, b)` it drops are those with a value `c`
    of `a`, `c ≠ b`, and no `b Q c`, so `est`, as `thin`, reads `Q` up to its reflexive closure, and a strict
    linear order answers as its reflexive one. -/
def est {A B : Obj} (Q : Rel B B) (G : Rel A B) : Rel A B := estOn (pairsIn Q) G

/-- `thin(Q)` per key of the family `G : A ⟶ B`, the `Q`-minimal values: the rows `(a, b)` of `G` with no
    `(a, c)` of `G` where `c` is strictly `Q`-below `b`, the strict part being `Q \ Q°` (`Q` itself when
    strict). -/
def thin {A B : Obj} (Q : Rel B B) (G : Rel A B) : Rel A B := thinOn (pairsIn Q) G

/-- `cons° : arr B ⟶ B × arr B` on the arrays of `X`: each non-empty row to its first element and the rest.
    The rows with a clamped count above `0` (`whereBits`); the rest `lo + 1`, `hi` the clamped end, its payload
    then cut to the cells it refers to (`Vals.compact`), every column at the count of the rows kept. -/
def uncons {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod B (.arr B)) :=
  let s := slicesOf X
  let i := whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one 0) n)
  longCount "cons°" i fun r hr =>
  let l := gather 8 s.1 i
  ⟨r, Vals.pick (.arr B) X i r hr,
    (Vals.pick B X.2.2.2 l r ((gather_len _ _).trans hr),
      Vals.compact (.arr B) ⟨X.1, valCol Ew.add Ew.va l (one 1), valCol Ew.add Ew.vv l (gather 8 s.2 i), X.2.2.2⟩)⟩

/-- `cons : B × arr B ⟶ arr B` on the rows of `P`: each `(y, ys)` to the array `y` then `ys`, under its key.
    The new arrays are laid out one after another (`sums` of the counts plus one); the tails gathered from
    the old payload (`expand` of the clamped counts) and the heads razed after them, then put in place by
    the `grade` of their places. Every row of `P` is kept, at its count; the payload holds the tails' cells
    and one head per row, a count that must fit a `USize`. -/
def cons {K B : Obj} (P : Rel K (.prod B (.arr B))) : Rel K (.arr B) :=
  let n := P.n
  let T := P.val.2
  let s := slicesOf T
  let c1 := addc n s.2 1
  let hi := sums n c1
  let lo := sub n hi c1
  expand n s.2 (fun _ => default) fun k xi xr _ _ =>
  need (k.toNat + n.toNat < USize.size) (fun _ => s!"cons: {k} + {n} cells do not fit a USize") (fun _ => default)
    fun hN =>
  let flat := Obj.raze B #[⟨k, Vals.pick B T.2.2.2 (add k (gather 8 s.1 xi) xr) k (len_val ..)⟩, ⟨n, P.val.1⟩]
    (by simpa using hN)
  let dst := addc k (add k (gather 8 lo xi) xr) 1
  let perm := (Code.ofLongs (concatBytes #[dst, lo])).grade
  longCount "cons" perm fun p hp =>
  ⟨n, Vals.compact K P.key, ⟨p, valCol Ew.sub Ew.vv hi c1, longsN n hi (sums_le (len_val ..)), Vals.pick B flat perm p hp⟩⟩

/-- The rounds of a fold over the rows of `ids : row ⟶ [E]`, from each array's last element to its first:
    the state `pend : row ⟶ V` starts as given, each row from its own values, so two rows of one array may
    start apart; round `k` pairs the rows longer than `k` with their element `k` from the end (`el`) and hands
    both to `step`, and moves the rows not longer to `out`. A row is never longer than the payload, so its
    size plus one rounds end every row (`iter`). The result is keyed by the row ids. -/
def foldRows {E V : Obj} (ids : Rel .long (.arr E)) (pend : Rel .long V)
    (step : Rel .long E → Rel .long V → Rel .long V) : Rel .long V :=
  let X := ids.val
  let n := ids.n
  let s := slicesOf X
  let ends := add n s.1 s.2
  let round : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat := fun (pend, out, k) =>
    let a := whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one k.toUInt64) n)
    let el : Rel .long E := longCount "foldRows" a fun r hr =>
      let pos := Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul (gather 8 ends a) (one (k + 1).toUInt64) r
      ⟨r, Vals.pick .long ids.key a r hr, Vals.pick E X.2.2.2 pos r (len_val ..)⟩
    -- `≫` keeps row multiplicity, so a step reaching a value along two paths doubles its rows: `nub` each round,
    -- or the rows of `pend` grow as the paths do (`2^k` for `π₂ ∪ π₂ succ`), not as the pairs
    ((step el pend).nub, out ∪ (antiJoin pend° (idU el.key))°, k + 1)
  (iter (X.1.toNat + 1) (fun st => st.1.n == 0) round (pend, zero, 0)).2.1

/-- `foldRows` on the arrays of `X`, every row starting from every value of `e`, read back at the arrays by
    `num`'s row ids. -/
def foldBy {E V : Obj} {n m : USize} (X : Vals (.arr E) n) (e : Vals V m)
    (step : Rel .long E → Rel .long V → Rel .long V) : Rel (.arr E) V :=
  let ids := num (idU X) 0
  ids° ≫ foldRows ids (top (A := .long) (B := V) ids.key e) step

/-- A fold step in demand form: `S` runs on the pairs (element, value) the round meets, `S D` for the
    coreflexive `D` on them, so a carrier with no universe folds too. -/
def demandStep {E V : Obj} (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V) (el : Rel .long E)
    (pend : Rel .long V) : Rel .long V :=
  let p := pair el pend; p ≫ S (ran p)

/-- `⦇e, S⦈` on the arrays `X`, the fold of cons-lists, `S` in demand form (`demandStep`). `[]` to each value
    of `e`, `cons(x, xs)` to `w` when `xs` goes to `v` and `(x, v) S(D) w`. -/
def foldOn {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V)
    (X : Vals (.arr E) n) : Rel (.arr E) V :=
  foldBy X e (demandStep S)

/-- `⦇e, S⦈` on the arrays of `X`, `S` one relation: `foldOn` with `S` whatever pairs a round meets. An array
    may have several results or none. -/
def fold {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) V) (X : Vals (.arr E) n) : Rel (.arr E) V :=
  foldOn e (fun _ => S) X

/-- The one-row side holding the empty array. -/
def nilVal (B : Obj) : Vals (.arr B) 1 := ⟨0, col [0], col [0], Vals.empty B⟩

/-- `F(R)`, the list functor on the arrays of `X`: `xs` to every `ys` of its length with `xs[i] R ys[i]` at
    each `i` — `⦇[], (R × 𝟙) ≫ cons⦈`, each round pairing every image of the element with every array so far. -/
def map {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) : Rel (.arr A) (.arr B) :=
  foldBy X (nilVal B) fun el pend => cons (pair (el ≫ R) pend)

/-! ## Order on numbers, the power side, and the note's list functions -/

/-- `<` on the elements of `U` (`leRel`, AOP/A7_2_RelSet.lean:160, strict): the pairs `(U[i], U[j])` with
    `U[i] < U[j]`. `rank` of `U` (`gradeColumn`, ties in position order), `cross` of the positions, `Ew.cmp <`
    of their ranks, less the pairs of one value the ties' order put apart. The domain is the types
    `gradeColumn` orders by value: every atom but a general list, whose witness `decide` discharges. -/
def lt {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (_h : t ≠ .general := by decide) : Rel (.atom t) (.atom t) :=
  let r := longsOf (Ops.rank (t := t) U _h)
  let c := cross n n
  let L : Rel (.atom t) (.atom t) := longCount "<" c.1 fun nn _ =>
    let i := whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 r c.1) (gather 8 r c.2) nn)
    longCount "<" i fun k hk =>
      ⟨k, Vals.pick _ U (gather 8 c.1 i) k ((gather_len _ _).trans hk), Vals.pick _ U (gather 8 c.2 i) k ((gather_len _ _).trans hk)⟩
  L \ idU U

/-- `≤` on the elements of `U` (`leRel`, AOP/A7_2_RelSet.lean:160): `lt U ∪ 𝟙`. -/
def leq {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) : Rel (.atom t) (.atom t) :=
  lt U h ∪ idU U

/-- `succ : long ⟶ long` on `U` (`succ`, AOP/A5_6_ListCombinators.lean:343): each `u` to `u + 1` where `u + 1`
    is in `U`, so the range stays in `U` and the top of `U` goes to nothing. `Ew.val` add, then the rows whose
    sum is a `member` of `U` (`whereBits`), key and sum gathered there. -/
def succ {n : USize} (U : Vals (.atom .long) n) : Rel (.atom .long) (.atom .long) :=
  let s : Arr .long n := valCol Ew.add Ew.va (longsOf U) (one 1)
  let c := codes .long #v[⟨_, s⟩, ⟨_, U⟩]
  let k := whereBits n (c[0].member c[1])
  longCount "succ" k fun r hr => ⟨r, Vals.pick _ U k r hr, Vals.pick (.atom .long) s k r hr⟩

/-- The integral value verb `op` (`Ew.add`, `sub`, `mul`, `idiv`, `imod`) as a relation `long × long ⟶ long` on
    the pairs `W`: each `(u, v)` to `u op v` where that is a `long` other than q's null, and to nothing elsewhere.
    One `Ew.val` over the two columns, then the rows kept (`whereBits`, keyed as `succ`) where the answer is not
    the null — which the kernel answers for a null operand and for `idiv`/`imod` by `0` — and is exact: a
    wrapped `+`/`-` is the one whose order against `u` disagrees with `v`'s sign, a wrapped `*` the one that
    `idiv u` does not take back to `v`. `idiv`/`imod` floor, as q's `div`/`mod`, and cannot wrap on non-null
    operands. So the relation is partial at a zero divisor and at overflow, never a default value. -/
def arith (op : UInt8) {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) :
    Rel (.prod (.atom .long) (.atom .long)) (.atom .long) :=
  let m := n
  let u := longsOf W.1; let v := longsOf W.2
  let s := Kernel.Ew.val op Ew.i64 Ew.vv nul u v m
  let cmp (c : UInt8) (x y : ByteArray) := Ew.cmp c Ew.i64 Ew.vv x y m
  let same (x y : ByteArray) := Ew.bit (Ew.bitCmp + Ew.eq) Ew.vv x y m
  let pos := Ew.cmp Ew.ge Ew.i64 Ew.va v (one 0) m
  let ok := Ew.cmp Ew.ne Ew.i64 Ew.va s (one nul.toUInt64) m
  let exact :=
    if op == Ew.add then same pos (cmp Ew.ge s u)
    else if op == Ew.sub then same pos (cmp Ew.le s u)
    else if op == Ew.mul then
      Ew.bit Ew.greater Ew.vv (cmp Ew.eq (Kernel.Ew.val Ew.idiv Ew.i64 Ew.vv nul s u m) v)
        (Ew.cmp Ew.eq Ew.i64 Ew.va u (one 0) m) m
    else ok
  let k := whereBits m (Ew.bit Ew.lesser Ew.vv ok exact m)
  longCount "arith" k fun r hr =>
    ⟨r, Vals.pick _ W k r hr, longsN r (gather 8 s k) (Nat.le_of_eq ((gather_len _ _).trans hr).symm)⟩

/-- `plus : long × long ⟶ long` on the pairs `W` (`plus`, AOP/A5_6_ListCombinators.lean:339): `u + v`. -/
def plus {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) := arith Ew.add W
/-- `times` on the pairs `W`: `u · v`. -/
def times {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) := arith Ew.mul W
/-- `minus` on the pairs `W`: `u - v`, the converse reading of `plus` (`(u, v) minus w ⟺ (w, v) plus u`). -/
def minus {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) := arith Ew.sub W
/-- `div` on the pairs `W`: `⌊u / v⌋`, q's `div`; no row where `v = 0`. -/
def div {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) := arith Ew.idiv W
/-- `mod` on the pairs `W`: `u - v · ⌊u / v⌋`, q's `mod`, the sign of `v`; no row where `v = 0`. -/
def mod {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) := arith Ew.imod W

/-- `τ : A ⟶ arr A` on `X`, each element to the array holding it alone: `Λ(𝟙)` (`Λ_id_eq_singletonMap`,
    AOP/A5_7_PowerBeads.lean:171, of `singletonMap`, Freyd/S2_40.lean:170; the note's
    `τ≜⟨𝟙,⊸ nil⟩ cons`, diag/aop/07-optimisation.typ:694). -/
def τ {A : Obj} {n : USize} (X : Vals A n) : Rel A (.arr A) := Λ(idU X)

/-- `nil : K ⟶ arr B` on the one-row side `I`: its element to the empty array (`nil`,
    AOP/A1_7_Pointfree.lean:36; the note's `nil ≜ []`, diag/aop/07-optimisation.typ:443). -/
def nil {K B : Obj} (I : Vals K 1) : Rel K (.arr B) := ⟨1, I, nilVal B⟩

/-- `α ≜ [nil, cons] : K + B × arr B ⟶ arr B`, `nil` on the one-row `I`, `cons` on the pairs `P` (the note's
    `α ≜ [nil,cons]`, diag/aop/07-optimisation.typ:449; `alphaR_eq_junc`, AOP/A5_6_ListCombinators.lean:727). -/
def alpha {K B : Obj} {n : USize} (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) :
    Rel (.sum K (.prod B (.arr B))) (.arr B) :=
  junc (nil I) (cons (idU P))

/-- `Λ(R)` total on `U`: each element of `U` that `R` relates to nothing goes to the empty array, which `Λ(R)`,
    one row per key of `R`, has no row for. -/
def lamOn {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Rel A (.arr B) :=
  Λ(R) ∪ top (idU U \ dom R).key (nilVal B)

/-- `E(R) : arr A ⟶ arr B` on the arrays `X`, the existential image, the note's `E(R)≜frac(∋R,∋)`
    (diag/aop/07-optimisation.typ:718), `existsImage R ≜ Λ(∋ ≫ R)` (AOP/A4_6.lean:95): `Λ(∋R)` total on `X`. -/
def E {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) : Rel (.arr A) (.arr B) := lamOn (mem X ≫ R) X

/-- `P(R) : arr A ⟶ arr B` from the arrays `X` to the arrays `Y`, the power relator (`powerRel`,
    AOP/A5_4_PowerRel.lean:34): `((∋)° \ (R ≫ (∋)°)) ∩ ((∋ ≫ R) / ∋)`, every element of `xs` `R`-reaches into `ys`
    and every element of `ys` is reached from `xs`. A relation, not a map, so both ends range over a
    universe: `X` the inputs, `Y` the outputs. -/
def P {A B : Obj} {n m : USize} (R : Rel A B) (X : Vals (.arr A) n) (Y : Vals (.arr B) m) : Rel (.arr A) (.arr B) :=
  leftDiv (mem X)° (R ≫ (mem Y)°) X Y ∩ rightDiv (mem X ≫ R) (mem Y) X Y

/-- `tail ≜ cons° π₂` on the arrays `X` (diag/aop/05-datatypes.typ:561). -/
def tail {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := outr (uncons X)

/-- `length ≜ ⦇[zero,π₂ succ]⦈` on the arrays `X` (diag/aop/09-dynamic.typ:506; `length`,
    AOP/A5_6_ListCombinators.lean:328): `succ` on `0 … X.1`, since no array is longer than the payload `X.1`. -/
def length {E : Obj} {n : USize} (X : Vals (.arr E) n) : Rel (.arr E) (.atom .long) :=
  needSize (X.1.toNat + 1) "length: the payload's count plus one" (fun _ => default) fun c =>
  let sc := succ (tilCol c)
  foldOn (col [0]) (fun D => outr D ≫ sc) X


/-- `suffix : arr E ⟶ arr E` on the arrays `X`, each array to each of its final segments (`suffix`,
    AOP/A5_6_ListCombinators.lean:221): `tail*`, `𝟙 ∪ tail ∪ tail tail ∪ …` by `iter`, each round `tail` on the
    arrays the last one reached; an array is never longer than the payload `X.1`, so `X.1 + 1` rounds end. -/
def suffix {E : Obj} {n : USize} (X : Vals (.arr E) n) : Rel (.arr E) (.arr E) :=
  (iter (X.1.toNat + 1) (fun s => s.2.n == 0) (fun (S, F) => let F' := F ≫ tail (ran F).val; (S ∪ F', F')) (idU X, idU X)).1

/-! ## Arrays of arrays in list order: maps on positions -/

/-- Each array of `X` to the array of its `count + 1` slices `[l k, h k)`, `k = 0 … count`, every one a slice
    of `X`'s own payload, so no cell is copied before `Vals.compact`: `f` maps each row's clamped start and
    count (`slices`) and the `expand` of the `count + 1`s (row, `k`), at the `m` copies, to the slices' starts
    and ends as two columns of `m` rows. -/
private def nest {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (f : (m : USize) → ByteArray × ByteArray → (i r : ByteArray) → len i = m.toNat → Arr .long m × Arr .long m) :
    Rel (.arr B) (.arr (.arr B)) :=
  let s := slicesOf X
  let c := addc n s.2 1
  let hi := sums n c
  expand n c (fun _ => default) fun m i r hi' _ =>
  let b := f m s i r hi'
  ⟨n, Vals.compact (.arr B) X,
    ⟨m, valCol Ew.sub Ew.vv hi c, longsN n hi (sums_le (len_val ..)), Vals.compact (.arr B) ⟨X.1, b.1, b.2, X.2.2.2⟩⟩⟩

/-- `inits : arr B ⟶ arr (arr B)` on the arrays `X`, the prefixes by increasing length, `[]` first (`initsFn`,
    AOP/A5_6_ListCombinators.lean:847; B&dM §5.6 p.130): the `k`-th is `[lo, lo + k)`. -/
def inits {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr (.arr B)) :=
  nest X fun m s i r h => let l := gather 8 s.1 i
    (longsN m l (Nat.le_of_eq ((gather_len _ _).trans h).symm), valCol Ew.add Ew.vv l r)

/-- `tails : arr B ⟶ arr (arr B)` on the arrays `X`, the suffixes by decreasing length, `[]` last (`tailsFn`,
    AOP/A5_6_ListCombinators.lean:857; B&dM §5.6 p.130): the `k`-th is `[lo + k, hi)`. -/
def tails {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr (.arr B)) :=
  nest X fun m s i r h => (valCol Ew.add Ew.vv (gather 8 s.1 i) r,
    longsN m (gather 8 (add n s.1 s.2) i) (Nat.le_of_eq ((gather_len _ _).trans h).symm))

/-- `cat : arr B × arr B ⟶ arr B` on the rows of `P`, each `(xs, ys)` to `xs` then `ys` under its key (`cat`,
    AOP/A5_6_ListCombinators.lean:224, the graph of `cappend`). `cons` with an array for a head: the new arrays
    laid out one after another (`sums` of the two counts), each side's cells gathered by the `expand` of its
    counts and razed, then put in place by the `grade` of their places. -/
def cat {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) :=
  let n := P.n
  let x := P.val.1
  let y := P.val.2
  let a := slicesOf x
  let b := slicesOf y
  let c := add n a.2 b.2
  let hi := sums n c
  let lo := sub n hi c
  expand n a.2 (fun _ => default) fun ka ia ra _ _ =>
  expand n b.2 (fun _ => default) fun kb ib rb _ _ =>
  need (ka.toNat + kb.toNat < USize.size) (fun _ => s!"cat: {ka} + {kb} cells do not fit a USize") (fun _ => default)
    fun hN =>
  let flat := Obj.raze B #[⟨ka, Vals.pick B x.2.2.2 (add ka (gather 8 a.1 ia) ra) ka (len_val ..)⟩,
    ⟨kb, Vals.pick B y.2.2.2 (add kb (gather 8 b.1 ib) rb) kb (len_val ..)⟩] (by simpa using hN)
  let dst := concatBytes #[add ka (gather 8 lo ia) ra, add kb (add kb (gather 8 lo ib) (gather 8 a.2 ib)) rb]
  let perm := (Code.ofLongs dst).grade
  longCount "cat" perm fun p hp =>
  ⟨n, Vals.compact K P.key, ⟨p, valCol Ew.sub Ew.vv hi c, longsN n hi (sums_le (len_val ..)), Vals.pick B flat perm p hp⟩⟩

/-- `zip : arr A × arr B ⟶ arr (A × B)` on the rows of `P`, the two arrays position by position up to the
    shorter (`czip`, AOP/A1_7_Pointfree.lean:27; B&dM p.20): the counts' `Ew.val` lesser, laid out by `sums`,
    each side's cell `k` gathered at its own start plus `k`. -/
def zip {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) : Rel K (.arr (.prod A B)) :=
  let x := P.val.1
  let y := P.val.2
  let n := P.n
  let a := slicesOf x
  let b := slicesOf y
  let c := Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul a.2 b.2 n
  let hi := sums n c
  expand n c (fun _ => default) fun m i r _ _ =>
  ⟨n, Vals.compact K P.key,
    ⟨m, valCol Ew.sub Ew.vv hi c, longsN n hi (sums_le (len_val ..)),
      (Vals.pick A x.2.2.2 (add m (gather 8 a.1 i) r) m (len_val ..),
        Vals.pick B y.2.2.2 (add m (gather 8 b.1 i) r) m (len_val ..))⟩⟩

/-- `snoc° : arr B ⟶ arr B × B` on the arrays of `X`, `uncons` from the other end: each non-empty row to
    all but its last element (`[lo, hi - 1)`, a slice of the same payload) and its last element. -/
def unsnoc {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod (.arr B) B) :=
  let s := slicesOf X
  let i := whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one 0) n)
  longCount "snoc°" i fun r hr =>
  let l := gather 8 s.1 i
  let e := Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul (add r l (gather 8 s.2 i)) (one 1) r
  ⟨r, Vals.pick (.arr B) X i r hr,
    (Vals.compact (.arr B) ⟨X.1, longsN r l (Nat.le_of_eq ((gather_len _ _).trans hr).symm),
      longsN r e (Nat.le_of_eq (len_val ..).symm), X.2.2.2⟩,
      Vals.pick B X.2.2.2 e r (len_val ..))⟩

/-- `at(k) : arr B ⟶ B` on the arrays of `X`, positions from `0`: each row longer than `k` to the cell at
    `lo + k` of the payload, read in place as `uncons` reads the head; a row of `k` or fewer cells has no pair. -/
def atPos {B : Obj} {n : USize} (k : Nat) (X : Vals (.arr B) n) : Rel (.arr B) B :=
  let s := slicesOf X
  let i := whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one k.toUInt64) n)
  longCount "at" i fun r hr =>
  ⟨r, Vals.pick (.arr B) X i r hr, Vals.pick B X.2.2.2 (addc r (gather 8 s.1 i) k) r (len_val ..)⟩

/-- `snoc ≜ (𝟙 × τ) cat` on the rows of `P` (`snoc`, AOP/A9_3_Bracket.lean:933): `(xs, a)` to `xs` then `a`.
    `𝟙 × τ` is `⟨π₁, π₂ τ⟩` on the distinct pairs of `P`, one row each, so `P` keeps its rows. -/
def snoc {K B : Obj} (P : Rel K (.prod (.arr B) B)) : Rel K (.arr B) :=
  let D := ran P
  cat (P ≫ pair (outl D) (outr D ≫ τ (outr D).val))

/-- `cat° : arr B ⟶ arr B × arr B` on the arrays `X`, each array to every way of cutting it in two: the
    `k`-th prefix beside the `k`-th suffix, `⟨inits, tails⟩ zip ∋`. -/
def uncat {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod (.arr B) (.arr B)) :=
  let Z := zip (pair (inits X) (tails X))
  Z ≫ mem Z.val

/-! ## Permutations, sets and order (ch. 6, 8) -/

/-- `perm ≜ ⦇[nil, add]⦈` on the arrays `X` (`perm`, AOP/A5_6_ListCombinators.lean:81; B&dM p.130), `add` putting
    the head anywhere: `(a, xs)` to `ys` then `a` then `zs` for every `(ys, zs)` of `cat°(xs)`. The tuples
    `(a, (ys, zs))` a round meets are distinct keys (`ran`), so `⟨…⟩` on them keeps one row each. -/
def perm {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  foldBy X (nilVal B) fun el pend =>
    let q := pair el (pend ≫ uncat (ran pend).val)
    let D := ran q
    q ≫ cat (pair (outl (outr D)) (cons (pair (outl D) (outr (outr D)))))

/-- `setify : arr B ⟶ P B` on the arrays `X`, each array to the set of its elements (`setify`,
    AOP/A5_6_ListCombinators.lean:49, `Λ(inlist)`; B&dM §7.3 p.177): `Λ(∋)` total on `X`. -/
def setify {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := lamOn (mem X) X

/-- `bagify : arr B ⟶ bag(B)` on the arrays `X` (`bagify`, AOP/A10_3_Tardy.lean:232, the quotient map of
    `perm`). A bag is the `arr` of its elements ascending in `Obj.sortBy`'s order, repeats kept: the one member
    of its `perm` class no type records. Each row's cells gathered contiguous (`expand` of the clamped counts),
    graded by value, then stably by row, so the rows keep their `lo`/`hi`. A per-row grade, not `sort`:
    `sort ≜ perm ordered` enumerates the permutations. -/
def bagify {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  let s := slicesOf X
  let hi := sums n s.2
  expand n s.2 (fun _ => default) fun m i r _ _ =>
  let cells := Vals.pick B X.2.2.2 (add m (gather 8 s.1 i) r) m (len_val ..)
  let v := Obj.sortBy B cells (tilLongs m)
  let p := gather 8 v (Code.ofLongs (gather 8 i v)).grade
  longCount "bagify" p fun q hq =>
  ⟨n, Vals.compact (.arr B) X,
    ⟨q, valCol Ew.sub Ew.vv hi s.2, longsN n hi (sums_le (len_slices ..).2), Vals.pick B cells p q hq⟩⟩

/-- `ordered(Q)`, the coreflexive on the arrays `X` that are `Q`-ordered, each element `Q`-below every later
    one (`orderedP`, AOP/A5_6_ListCombinators.lean:162): the arrays with no non-empty suffix `y :: ys` and `z`
    of `ys` outside `y Q z`. `cons°` of the suffixes, the pairs `(y, z)`, those no pair of `Q` (`antiJoin`). -/
def orderedOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  let T := suffix X ≫ uncons (ran (suffix X)).val
  let D := ran T
  let yz := pair (outl D) (outr D ≫ mem (ran (outr D)).val)
  let bad := antiJoin yz (q (ran yz))
  antiJoin (idU X) (dom (T ≫ dom bad))

/-- `ordered(Q)`, `Q` closed: `orderedOn` at `pairsIn Q`, the test run on the pairs `(y, z)` it compares. -/
def ordered {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := orderedOn (pairsIn Q) X

/-- `sort(Q) ≜ setify° ordered(Q) : P B ⟶ arr B` (`sortRel`, AOP/A8_3.lean:77; B&dM p.201, "sorting sets"):
    a set to its `Q`-ordered listings among the arrays `Y`. A relation into lists has no finite image without
    a universe (`[1, 1, 2]` lists `{1, 2}` under `≤`), so the lists range over `Y`, as `P`'s do. -/
def sortSet {B : Obj} {n : USize} (Q : Rel B B) (Y : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  (setify Y)° ≫ ordered Q Y

/-- `subseq ≜ ⦇[nil, cons ∪ π₂]⦈` on the arrays `X`, each array to each of its subsequences (`subseq`,
    AOP/A5_6_ListCombinators.lean:127): a head kept or dropped. -/
def subseq {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  foldBy X (nilVal B) fun el pend => cons (pair el pend) ∪ pend

/-- `thinL(Q) ≜ setify thin(Q) setify° ∩ subseq` on the arrays `X` (`thinL`, AOP/A8_3.lean:567; B&dM p.200,
    binary thinning), `thin(Q) ≜ ⊇ ∩ (∈ \ Q°∈)` on the sets of `Y`, the subsequences of `X` (`thinRel`,
    AOP/A8_1.lean:71); `thinL ⊑ subseq`, so `Y` holds every target. `⊇` is `∋ / ∋`. -/
def thinL {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  let U := subseq X
  let Y := (ran U).val
  let S := (setify Y).val
  let T := rightDiv (mem S) (mem S) S S ∩ leftDiv (mem S)° (Q° ≫ (mem S)°) S S
  (setify Y ≫ T ≫ (setify Y)°) ∩ U

/-- Binary thinning in one pass, the note's implementation of `thinL(Q)` (`bumpFold_le_thinL`,
    AOP/A8_3.lean:629, `⦇[τ, bump(Q)]⦈ ⊑ thinL(Q)`): each element `a` bumped into the thinned rest `ys` —
    `[a]` when `ys` is empty, else with `b` its head `a` replaces `b` when `a Q b`, `b` stays alone when `b Q a`,
    both stay when neither (`bumpRel_cons`, AOP/A8_3.lean:381). `Q` is the test `q` on the pairs `(a, b)` each
    round meets, so `Q` needs no universe; `thinL Q` is the specification it refines. -/
def thinLOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  foldBy X (nilVal B) fun el pend =>
    let p := pair el pend
    let D := ran p
    let a := outl D
    let ys := outr D
    let u := ys ≫ uncons ys.val
    let ab := pair a (outl u)
    let up := dom (ab ≫ q (ran ab))
    let down := dom (ab ≫ swapIn q (ran ab))
    let lone := D \ dom u ∪ ((dom u \ up) \ down)
    p ≫ (cons lone ∪ cons (pair (up ≫ a) (up ≫ u ≫ outr (ran u))) ∪ down ≫ ys)

/-- `merge(Q) : arr B × arr B ⟶ arr B` on the rows of `P` (`merge`, AOP/A8_3.lean:1147; B&dM p.156): the
    book's equations as rounds of `iter` on the states `((x, y), acc)`, `acc` the output so far: with both
    non-empty the head `a` of `x` goes to `acc` when `a Q b`, `b` the head of `y`, else `b`; with either empty
    the state ends as `acc` then `x` then `y`. A round shortens `x` or `y`, so the cells of both payloads
    plus one bound the rounds. -/
def mergeOn {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) :=
  let round : Rel K (.arr B) × Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B)) →
      Rel K (.arr B) × Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B)) := fun (out, St) =>
    let D := ran St
    let x := outl (outl D)
    let y := outr (outl D)
    let acc := outr D
    let ux := x ≫ uncons x.val
    let uy := y ≫ uncons y.val
    let both := dom (pair ux uy)
    let h := pair (outl ux) (outl uy)
    let l := dom (h ≫ q (ran h))
    let take := l ≫ pair (pair (outr ux) y) (snoc (pair acc (outl ux))) ∪
      antiJoin both l ≫ pair (pair x (outr uy)) (snoc (pair acc (outl uy)))
    (out ∪ St ≫ antiJoin D both ≫ cat (pair (cat (pair acc x)) y), St ≫ take)
  (iter (P.val.1.1.toNat + P.val.2.1.toNat + 1) (fun s => s.2.n == 0) round
    (zero, P ≫ pair (idU (ran P).val) (top (ran P).val (nilVal B)))).1

/-- `merge(Q)`, `Q` closed: `mergeOn` at `pairsIn Q`, the test run on the pairs of heads it compares. -/
def merge {K B : Obj} (Q : Rel B B) (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) := mergeOn (pairsIn Q) P

/-- `loop(F) : X × arr Y ⟶ X` on the rows of `P` (`loop`, AOP/A9_3_Bracket.lean:1686; B&dM Appendix), `F`
    folded along the array from the left, in demand form as `foldOn`'s step: rounds of `iter` taking
    `(c, y :: ys)` to `(c', ys)` with `(c, y) F(D) c'`, `D` the coreflexive on the pairs `(c, y)` the round
    meets, so a state with no universe loops too; a state whose array is empty ends at its `c`. The states
    are `nub`bed each round, as `foldBy`'s, or a value reached along two paths doubles its rows each round
    after. The cells of the arrays' payload plus one bound the rounds. -/
def loopOn {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) :
    Rel K X :=
  let round : Rel K X × Rel K (.prod X (.arr Y)) → Rel K X × Rel K (.prod X (.arr Y)) := fun (out, St) =>
    let D := ran St
    -- `uncons` on the distinct arrays: on `(outr D).val`, an array held by `k` states gives each of them `k`
    -- rows, and `pair` below `k²`, so a round's rows grow as the states sharing a suffix, not as the states
    let u := outr D ≫ uncons (ran (outr D)).val
    let p := pair (outl D) (outl u)
    (out ∪ St ≫ outl (antiJoin D (dom u)), (St ≫ pair (p ≫ F (ran p)) (outr u)).nub)
  (iter (P.val.2.1.toNat + 1) (fun s => s.2.n == 0) round (zero, P)).1

/-- `loop(F)` with `F` one relation: `loopOn` with `F` whatever pairs a round meets. -/
def loop {K X Y : Obj} (F : Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) : Rel K X :=
  loopOn (fun _ => F) P

/-- `tic ≜ cons inits tail : B × arr B ⟶ arr (arr B)` on the rows of `P` (`tic`, AOP/A9_3_Bracket.lean:1845;
    B&dM p.235): the non-empty prefixes of `a :: xs`. -/
def tic {K B : Obj} (P : Rel K (.prod B (.arr B))) : Rel K (.arr (.arr B)) :=
  let C := cons P
  let I := C ≫ inits C.val
  I ≫ tail I.val

namespace Arr

/-- `union : arr (arr A) ⟶ arr A` on the arrays of arrays `X`, the note's `union≜frac(∋∋,∋)`
    (diag/aop/07-optimisation.typ:718; `union ≜ Λ(∋∋)`, AOP/A5_4.lean:337): `Λ(∋∋)` total on `X`. Named
    `Arr.union` because `union` is `∪`'s, which a program must not name. -/
def union {A : Obj} {n : USize} (X : Vals (.arr (.arr A)) n) : Rel (.arr (.arr A)) (.arr A) :=
  lamOn (mem X ≫ mem X.2.2.2) X

/-- `sum ≜ ⦇[zero, plus]⦈` on the arrays of longs `X` (`sum`, AOP/A5_6_ListCombinators.lean:323), each round's
    `plus` on the pairs it meets. Named `Arr.sum` because `sum` is `R + S`'s. -/
def sum {n : USize} (X : Vals (.arr (.atom .long)) n) : Rel (.arr (.atom .long)) (.atom .long) :=
  foldOn (col [0]) (fun D => plus D.val) X

end Arr

/-- `Entire R` on the universe `U`: `𝟙 ⊑ R R°`, written `𝟙 ⊑ dom R` since `dom R = 𝟙 ∩ R R°`. -/
def entire {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Bool := idU U ⊑ dom R

/-- `Simple R`, `R° R ⊑ 𝟙`: in `R` with each pair once, every key distinct (`groupIds` count of the key codes),
    linear where `R° ≫ R` is a join quadratic in a key's values. -/
def simple {A B : Obj} (R : Rel A B) : Bool :=
  let r := R.nub
  len (A.codes #v[⟨_, r.key⟩])[0].groupIds.2 == r.n.toNat

def isMap {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Bool := entire R U && simple R

/-- `Injective R` = `Simple R°`. -/
def injective {A B : Obj} (R : Rel A B) : Bool := simple R°

/-- `Surjective R` = `Entire R°` on the universe `U` of `b`. -/
def surjective {A B : Obj} {m : USize} (R : Rel A B) (U : Vals B m) : Bool := entire R° U

/-- **`R°` swaps the pairs**: the two fields swap (`convArr_holds`). -/
theorem conv_holds {R : Rel A B} (x : El A) (y : El B) : (conv R).Holds y x ↔ R.Holds x y :=
  convArr_holds R.key R.val x y

#print axioms conv_holds
-- the private ops have no operator to name in `AlgTest`, so their axioms are printed where they are visible
#print axioms le
#print axioms inter
#print axioms union
#print axioms conv
#print axioms comp

end LeetQ.Rel.Alg
