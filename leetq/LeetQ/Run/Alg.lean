/-
  The operators of the relation algebra on the core (RelRep design §2.3): each a pipeline of qlean
  kernels over a `Rel`'s two payloads, with the order, the power side, the list functions and the
  predicates built on them. The codes they compare through are in `LeetQ.Rel.Code`.
-/
import LeetQ.Run.Code

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel

/-! ## The operators -/

section Gen

variable {A B C : Obj}

/-- A relation's keys as a part. A function of the relation, not `⟨R.n, R.key⟩`: there `simp` cannot rewrite `R`,
    the `Vals`' count depending on it, so a twin's `_fst` would not reach a part a body codes. -/
def keyPart {k v : Obj} (R : Rel k v) : Part k := ⟨R.n, R.key⟩

/-- A relation's values as a part, as `keyPart`. -/
def valPart {k v : Obj} (R : Rel k v) : Part v := ⟨R.n, R.val⟩

/-- A relation's rows sorted by value, and the bit: `sortByC` at `til`, a function of the relation as `keyPart`. -/
def valSortC {k v : Obj} (R : Rel k v) : ByteArray × Bool := v.sortByC R.val (tilLongs R.n)

/-- A relation's pairs as a part of the product side, as `keyPart`: what `pairs` codes. -/
def pairPart {k v : Obj} (R : Rel k v) : Part (.prod k v) := ⟨R.n, (R.key, R.val)⟩

/-- `R ⊑ S`, `member` of `|R|` in `|S|` on the joint pair codes (`codesC` of the product side), all set, and whether
    it ran within capacity: the codes' bit. -/
def leC (R S : Rel A B) : Bool × Bool :=
  let c := (Obj.prod A B).codesC #v[pairPart R, pairPart S]
  (len (whereBits R.n (c.1[0].member c.1[1])) == R.n.toNat, c.2)

/-- `R ⊑ S`: `leC`'s answer. -/
private def le (R S : Rel A B) : Bool := (leC R S).1

/-- `R ∩ S`, the semi-join on pairs — `member` of the joint pair codes (`codesC` of the product side, which `pairs`
    is), `whereBits`, `gatherColumn` — and whether it ran within capacity: the codes' bit `&&` `R`'s two sides
    fitting at all its rows (`fitsN`), the picks `rows` makes being among them. -/
def interC (R S : Rel A B) : Rel A B × Bool :=
  let c := (Obj.prod A B).codesC #v[pairPart R, pairPart S]
  (R.rows (whereBits R.n (c.1[0].member c.1[1])), c.2 && Vals.fitsN A R.key R.n.toNat && Vals.fitsN B R.val R.n.toNat)

/-- `R ∩ S`: `interC`'s relation. -/
private def inter (R S : Rel A B) : Rel A B := (interC R S).1

/-- `𝟘`: no pair. -/
def zero : Rel A B := ⟨0, Vals.empty A, Vals.empty B⟩

/-- A stopped run's model relation. -/
instance : Inhabited (Rel A B) := ⟨zero⟩

/-- `R ∪ S`: `razeColumn` of keys and of vals, both at the summed count (`Obj.raze`), the first row of each pair;
    the summed count fits a `USize`. Whether it ran within capacity: the summed count's bound (`need`'s guard) and
    the bits of the two razes and of `nub`'s two codes (`razeC`, `codesC`), `&&` the razed sides fitting at all their
    rows (`fitsN`). -/
def unionC (R S : Rel A B) : Rel A B × Bool :=
  need (R.n.toNat + S.n.toNat < USize.size) (fun _ => s!"∪: {R.n} + {S.n} rows do not fit a USize")
    (fun _ => (zero, false)) fun h =>
  let k := A.razeC #[⟨_, R.key⟩, ⟨_, S.key⟩] (by simpa using h)
  let v := B.razeC #[⟨_, R.val⟩, ⟨_, S.val⟩] (by simpa using h)
  let U : Rel A B := ⟨_, k.1, v.1⟩
  let kc := A.codesC #v[⟨_, U.key⟩]; let vc := B.codesC #v[⟨_, U.val⟩]
  (U.rows (tuples.tupleIds kc.1[0] #[vc.1[0]]).2,
    k.2 && v.2 && kc.2 && vc.2 && Vals.fitsN A U.key U.n.toNat && Vals.fitsN B U.val U.n.toNat)

/-- `R ∪ S`: `unionC`'s relation. -/
private def union (R S : Rel A B) : Rel A B := (unionC R S).1

/-- `⊤` on the universes `Ua`, `Ub`: `cross`, its two index columns of one length (`cross_len`). -/
def top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  let c := cross ma mb
  longCount "⊤" c.1 fun m h => ⟨m, Vals.pick A Ua c.1 m h, Vals.pick B Ub c.2 m ((cross_len ma mb).trans h)⟩

/-- `⊤` and whether it ran within capacity: `rep_top`'s pair count decided, `&&` each universe fitting at the
    `ma · mb` rows `cross` picks it at (`fitsN`), the form `rep_top` takes them in; `top` itself runs. -/
def topC {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B × Bool :=
  (top Ua Ub, decide (ma.toNat * mb.toNat < USize.size) && decide (ma.toNat * mb.toNat < 2 ^ 63) &&
    Vals.fitsN A Ua (ma.toNat * mb.toNat) && Vals.fitsN B Ub (ma.toNat * mb.toNat))

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

/-- The joined rows of `op` (`≫`, `\`, `/ₛ`) over the codes `l`, `k`: `join`, the left index column read at the
    right's count (`fit`, `join_len`), `x`'s rows beside `z`'s; the bit is the two picks' (`pickC`). On the codes
    as arguments: inside the picks' proofs a twin's `.1` is rewritten by neither `simp` nor `rw`. -/
def joinC (op : String) (x : Part A) (z : Part C) (l k : Code) : Rel A C × Bool :=
  let ij := join l k
  longCount op ij.2 fun m h =>
    let a := Vals.pickC A x.2 (fit m.toNat ij.1) m (fit_len (h ▸ join_len l k))
    let c := Vals.pickC C z.2 ij.2 m h
    ((⟨m, a.1, c.1⟩ : Rel A C), a.2 && c.2)

/-- `R ≫ S`, `join` on `R.val = S.key` (`joinC`, `R`'s keys beside `S`'s values), and whether it ran within
    capacity: `rep_comp`'s count bounds decided, `&&` the bits of the codes and of the two picks (`codesC`, `joinC`). -/
def compC (R : Rel A B) (S : Rel B C) : Rel A C × Bool :=
  let c := B.codesC #v[⟨_, R.val⟩, ⟨_, S.key⟩]
  let r := joinC "≫" (keyPart R) (valPart S) c.1[0] c.1[1]
  (r.1, c.2 && decide (S.n.toNat < 2 ^ 63) && decide (R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size) && r.2)

/-- `R ≫ S`: `compC`'s relation. -/
private def comp (R : Rel A B) (S : Rel B C) : Rel A C := (compC R S).1

/-- A twin's `.1` through `need` (so through `longCount`, `expand`): each branch's `.1`; a `split` of the test at a
    twin would decide it by evaluating the kernels that produce the count. -/
theorem need_fst {α β : Type} {p : Prop} [Decidable p] (msg : Unit → String) (m : Unit → α × β) (k : p → α × β) :
    (need p msg m k).1 = need p msg (fun u => (m u).1) fun h => (k h).1 := by
  unfold need stop; split <;> rfl

/-- A codes twin's `.1` is `Obj.codes`, at each constructor of the side. -/
theorem _root_.LeetQ.Rel.Obj.codesC_fst (X : Obj) {p : Nat} (cs : Vector (Part X) p) : (X.codesC cs).1 = X.codes cs := by
  cases X <;> rfl

/-- The coreflexive on the distinct elements of `x`, `𝟙` on `x` at the first row of each code, and whether it ran
    within capacity: the one-part code's bit (`codesC`) `&&` `x` fitting at all its rows (`fitsN`), the first rows
    picked being among them. -/
def distinctCoreflC (t : Obj) {n : USize} (x : Vals t n) : Rel t t × Bool :=
  let c := t.codesC #v[⟨n, x⟩]
  ((idU x).rows c.1[0].groupIds.2, c.2 && Vals.fitsN t x n.toNat)

/-- The coreflexive on the distinct elements of `x`: `distinctCoreflC`'s relation. -/
def distinctCorefl (t : Obj) {n : USize} (x : Vals t n) : Rel t t := (distinctCoreflC t x).1

/-- `dom R`: the coreflexive on the distinct keys. -/
def dom (R : Rel A B) : Rel A A := distinctCorefl A R.key

/-- `dom` and whether it ran within capacity: `distinctCoreflC` of the keys. -/
def domC (R : Rel A B) : Rel A A × Bool := distinctCoreflC A R.key

/-- `ran R`: the coreflexive on the distinct vals. -/
def ran (R : Rel A B) : Rel B B := distinctCorefl B R.val

/-- `ran` and whether it ran within capacity: `distinctCoreflC` of the vals. -/
def ranC (R : Rel A B) : Rel B B × Bool := distinctCoreflC B R.val

/-- `R ≫ corNeg(C)`, the anti-join: the rows of `R` whose value is no value of `C` (`anti` on one joint coding), and
    whether it ran within capacity: the joint value codes' bit (`codesC`) `&&` `R`'s two sides fitting at all its rows
    (`fitsN`), the kept rows being among them. -/
def antiJoinC (R : Rel A B) (C : Rel B B) : Rel A B × Bool :=
  let vc := B.codesC #v[⟨_, R.val⟩, ⟨_, C.val⟩]
  (R.rows (anti vc.1[0] vc.1[1]), vc.2 && Vals.fitsN A R.key R.n.toNat && Vals.fitsN B R.val R.n.toNat)

/-- `R ≫ corNeg(C)`: `antiJoinC`'s relation. -/
def antiJoin (R : Rel A B) (C : Rel B B) : Rel A B := (antiJoinC R C).1

/-- `R − S`, the rows of `R` whose pair is no pair of `S` — `interC`'s joint pair codes, `anti` in place of
    `member` — and whether it ran within capacity, as `interC`. -/
def diffC (R S : Rel A B) : Rel A B × Bool :=
  let c := (Obj.prod A B).codesC #v[pairPart R, pairPart S]
  (R.rows (anti c.1[0] c.1[1]), c.2 && Vals.fitsN A R.key R.n.toNat && Vals.fitsN B R.val R.n.toNat)

/-- `R − S`: `diffC`'s relation. -/
private def diff (R S : Rel A B) : Rel A B := (diffC R S).1

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

/-- `R.nub` and whether it ran within capacity: the bits of its two one-part codes (`codesC`) `&&` `R`'s sides
    fitting at all its rows (`fitsN`), `rep_nub`'s premises. -/
def nubC {k v : Obj} (R : Rel k v) : Rel k v × Bool :=
  let kc := k.codesC #v[⟨_, R.key⟩]; let vc := v.codesC #v[⟨_, R.val⟩]
  (R.rows (tuples.tupleIds kc.1[0] #[vc.1[0]]).2,
    kc.2 && vc.2 && Vals.fitsN k R.key R.n.toNat && Vals.fitsN v R.val R.n.toNat)

theorem nubC_fst {k v : Obj} (R : Rel k v) : (nubC R).1 = R.nub := by
  show R.rows (tuples.tupleIds (k.codesC _).1[0] #[(v.codesC _).1[0]]).2 = _
  rw [Obj.codesC_fst, Obj.codesC_fst]; rfl

/-- `\`'s rows from the joined rows `y` on: those whose pair count equals `y`'s count among `R`'s values (`ycs`, the
    codes of `y`'s keys, `R.nub`'s values and `Ub`; `zc`, of `y`'s values), `∪` the vacuous `⊤`; the bit is `⊤`'s and
    `∪`'s. A def of its own, on the codes as arguments: the kept rows' `longCount` binds a proof about the codes, so
    a twin's `.1` inside it is rewritten by neither `simp` (dependent binder) nor `rw` (whose defeq checks then
    evaluate the kernels); as an argument here it is. -/
def divTailC {mb mc : USize} (Ub : Vals B mb) (Uc : Vals C mc) (y : Rel B C) (ycs : Vector Code 3)
    (zc : Vector Code 1) : Rel B C × Bool :=
  -- projected, not matched: `.2` of a `match` would hide the bit from `Bool.and_eq_true`
  let t := tuples.tupleIds ycs[0] #[zc[0]]
  let keep := longCount "\\" t.2 fun g _ =>
    gather 8 t.2 (whereEqV g (classSizes ycs[0].n t) (atCnt (cnt ycs[1]) (ycs[0].gather t.2)))
  let q := topC (Vals.pickPart B Ub (anti ycs[2] ycs[1])).2 Uc
  let u := unionC (y.rows keep) q.1
  (u.1, q.2 && u.2)

/-- `R \ S` (`R : a ⟶ b`, `S : a ⟶ c`), by counting: `join` on the shared key → rows `(y, z)`;
    `cnt(y, z)` against `cnt(R.val)` `at` `y`; the vacuous `y ∉ ran R` with every `z` from the
    universes `Ub`, `Uc`: `⊤` on `anti(Ub, ran R)` and `Uc`. The two parts are disjoint (a counted `y` is in
    `ran R`) and meet by `∪`, whose counts are proved where a `raze` of the parts would need its own. -/
def leftDivC {mb mc : USize} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc) : Rel B C × Bool :=
  let r := nubC R; let s := nubC S
  let kc := A.codesC #v[keyPart r.1, keyPart s.1]
  let y := joinC "\\" (valPart r.1) (valPart s.1) kc.1[0] kc.1[1]
  let ycs := B.codesC #v[keyPart y.1, valPart r.1, ⟨_, Ub⟩]
  let zc := C.codesC #v[valPart y.1]
  let u := divTailC Ub Uc y.1 ycs.1 zc.1
  (u.1, r.2 && s.2 && kc.2 && decide (S.n.toNat < 2 ^ 63) &&
    decide (R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size) && y.2 && ycs.2 && zc.2 && Vals.fitsN B Ub mb.toNat &&
    decide (mb.toNat * mc.toNat < min (2 ^ 63) USize.size) && u.2)

/-- `R \ S`: `leftDivC`'s relation. -/
def leftDiv {mb mc : USize} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc) : Rel B C :=
  (leftDivC R S Ub Uc).1

/-- `R / S = (S° \ R°)°` (`R : a ⟶ c`, `S : b ⟶ c`); its vacuous term is `⊤` on `Ua` and `anti(Ub, dom S)`. The bit
    is `leftDivC`'s. -/
def rightDivC {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B × Bool :=
  let r := leftDivC (conv S) (conv R) Ub Ua
  (conv r.1, r.2)

/-- `R / S`: `rightDivC`'s relation. -/
def rightDiv {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  (rightDivC R S Ua Ub).1

/-! `R /ₛ S` (`R : a ⟶ c`, `S : b ⟶ c`), equal fibres: the fibres of `R` and of `S` as `segments`
    of one value code space, their `setIds` in one call, `join` on the ids → `(x, y)`, the keys read as
    `comp` reads them (`join_len`); the vacuous term `⊤` on `anti(Ua, dom R)` and `anti(Ub, dom S)`, the
    empty fibres, met by `∪`. -/
/-- `/ₛ`'s fibre ids over the value codes `v0`, `v1` and the segments `pr`, `orr` of `R`, `ps`, `os` of `S` (`nR`
    `R`'s count): `setIds` of both fibre families in one call. A def on plain values: its `longCount` binds a proof
    about `os`, under which a twin's `.1` is rewritten by neither `simp` nor `rw`. -/
def symDivIds (v0 v1 : Code) (pr orr ps os : ByteArray) (nR : Nat) : ByteArray :=
  -- each `segments` offsets end at its code count, so `S`'s starts shifted by `|R|` follow `R`'s
  let ss := os.extract 0 (os.size - 8)
  longCount "/ₛ" ss fun c _ =>
    setIds (Code.cat #[v0.gather pr, v1.gather ps]) (concatBytes #[orr.extract 0 (orr.size - 8), addc c ss nR])

/-- `/ₛ`'s rows from the joined rows `hit` on: `∪` the vacuous `⊤` on `anti(Ua, dom R)` and `anti(Ub, dom S)` (`uac`,
    `rk` the codes of `Ua`, `R.key`; `ubc`, `sk` of `Ub`, `S.key`); the bit is `⊤`'s and `∪`'s. A def on the codes as
    arguments, as `divTailC`: the picked parts' counts are types of `⊤`'s arguments. -/
def symDivTailC {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (rk uac sk ubc : Code) (hit : Rel A B) :
    Rel A B × Bool :=
  let q := topC (Vals.pickPart A Ua (anti uac rk)).2 (Vals.pickPart B Ub (anti ubc sk)).2
  let u := unionC hit q.1
  (u.1, q.2 && u.2)

/-- `/ₛ` and whether it ran within capacity: the codes' bits (`codesC`), `rep_symDiv`'s count bounds decided, the
    keys and universes fitting at all their rows (`fitsN`), the join picks' bit (`joinC`), `⊤`'s and `∪`'s. -/
def symDivC {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B × Bool :=
  let vc := C.codesC #v[valPart R, valPart S]
  let ac := A.codesC #v[keyPart R, ⟨_, Ua⟩]; let bc := B.codesC #v[keyPart S, ⟨_, Ub⟩]
  let sr := segments ac.1[0]; let sq := segments bc.1[0]
  let ids := symDivIds vc.1[0] vc.1[1] sr.1 sr.2.1 sq.1 sq.2.1 R.n.toNat
  let lc := Code.ofLongs (ids.extract 0 (8 * len sr.2.2)); let rc := Code.ofLongs (ids.extract (8 * len sr.2.2) ids.size)
  let h := joinC "/ₛ" (Vals.pickPart A R.key sr.2.2) (Vals.pickPart B S.key sq.2.2) lc rc
  let u := symDivTailC Ua Ub ac.1[0] ac.1[1] bc.1[0] bc.1[1] h.1
  (u.1, vc.2 && ac.2 && bc.2 && decide (R.n.toNat + S.n.toNat < USize.size) &&
    decide (R.n.toNat + S.n.toNat + 1 < 2 ^ 63) && Vals.fitsN A R.key R.n.toNat && Vals.fitsN B S.key S.n.toNat &&
    decide (R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size) && h.2 && Vals.fitsN A Ua ma.toNat &&
    Vals.fitsN B Ub mb.toNat && decide (ma.toNat * mb.toNat < min (2 ^ 63) USize.size) && u.2)

/-- `R /ₛ S`: `symDivC`'s relation. -/
def symDiv {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  (symDivC R S Ua Ub).1

/-- `Λ(R) : A ⟶ arr B`: one row per distinct key of `R`, its cell the ARRAY of the key's values, each once,
    in ascending value order (`sortBy`), so two keys with one set of values have one array — across two
    relations too, where `sortBy` orders by value. `Rel.nub`, the values sorted, then the keys' codes
    graded stably: each key one run, whose start and end (`runStarts`) are its row's `lo`, `hi`. `vp` is `d`'s
    rows sorted by value (`sortBy` at `til`), passed in so `transposeC` takes it with its bit from one pass. -/
def transposeRuns (d : Rel A B) (kc : Code) (vp : ByteArray) : Rel A (.arr B) :=
  let p := gather 8 vp (kc.gather vp).grade
  let o := (kc.gather p).runStarts
  let lo := o.extract 0 (o.size - 8)
  have h : len (o.extract 8 o.size) = len lo := by simp only [len, lo, ByteArray.size_extract]; omega
  let dk := Vals.pickPart A d.key p; let dv := Vals.pickPart B d.val p
  longCount "Λ" lo fun m hm => ⟨m, Vals.pick A dk.2 lo m hm,
    ⟨dv.1, toUSize_eq hm ▸ longCol lo, toUSize_eq (h.trans hm) ▸ longCol (o.extract 8 o.size), dv.2⟩⟩

/-- `Λ(R)` and whether it ran within capacity: `transposeRuns` on `nubC`'s relation, its key codes (`codesC`) and
    its values sorted (`sortByC`), the bit `nubC`'s `&&` those codes' `&&` the sort's (the nub values' codes',
    `sortByC_snd`, from the one pass that sorts by them) `&&` `rep_transpose`'s count decided. -/
def transposeC (R : Rel A B) : Rel A (.arr B) × Bool :=
  let d := nubC R
  let kc := A.codesC #v[keyPart d.1]
  let vp := valSortC d.1
  (transposeRuns d.1 kc.1[0] vp.1, d.2 && kc.2 && vp.2 && decide (R.n.toNat < 2 ^ 63))

/-- `Λ(R)`: `transposeC`'s relation. -/
def transpose (R : Rel A B) : Rel A (.arr B) := (transposeC R).1

/-- `Λ(R)` is `transposeRuns` on `R.nub`, its key codes and its values sorted: `nubC`'s and the codes twin's `.1`
    read as their ops. -/
theorem transpose_eq (R : Rel A B) :
    transpose R = transposeRuns R.nub (A.codes #v[⟨_, R.nub.key⟩])[0] (B.sortBy R.nub.val (tilLongs R.nub.n)) := by
  simp only [transpose, transposeC, nubC_fst, Obj.codesC_fst]; simp only [keyPart, valSortC, Obj.sortBy]

/-- `∋ : arr B ⟶ B` on the arrays `X`: each array to each of its elements, one row per element (an array
    holding a value twice relates to it twice). `expand` of the clamped slice counts, each copy's rank
    added to its slice's start; both read at the copies' count `expand` hands on. Whether it ran within capacity:
    the keys' pick bit (`pickC`), at the copies `expand` makes, `&&` `X` fitting at all its rows (`fitsN`), which
    the values' windows are read through. -/
def memC {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) B × Bool :=
  let s := slicesOf X
  let r := expand n s.2 (fun _ => default) fun m i r hi _ =>
    let k := Vals.pickC (.arr B) X i m hi
    ((⟨m, k.1, Vals.pick B X.2.2.2 (add m (gather 8 s.1 i) r) m (len_val ..)⟩ : Rel (.arr B) B), k.2)
  (r.1, r.2 && Vals.fitsN (.arr B) X n.toNat)

/-- `∋` on the arrays `X`: `memC`'s relation. -/
def mem {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) B := (memC X).1

/-- `Λ(R) : A ⟶ arr B`, each key of `R` to the array of its values. -/
scoped notation:max "Λ(" R ")" => transpose R
/-- `∋(R) : arr B ⟶ B`, `mem` on the arrays of `Λ(R)`: `Λ(R) ≫ ∋(R) = R`. -/
scoped notation:max "∋(" R ")" => mem (Rel.val (transpose R))

end Gen

variable {A B C : QAtomicType}

/-- `⟨R, S⟩`'s joined rows over the key codes `l`, `k`, as `joinC`: rows `(x, (y, z))`, `R`'s keys and values
    picked at the left rows, `S`'s values at the right ones; the bit is the three picks' (`pickC`). -/
def pairJoinC {A B C : Obj} (R : Rel A B) (S : Rel A C) (l k : Code) : Rel A (.prod B C) × Bool :=
  let ij := join l k
  longCount "⟨R,S⟩" ij.2 fun m hm =>
    let x := Vals.pickC A R.key (fit m.toNat ij.1) m (fit_len (hm ▸ join_len l k))
    let y := Vals.pickC B R.val (fit m.toNat ij.1) m (fit_len (hm ▸ join_len l k))
    let z := Vals.pickC C S.val ij.2 m hm
    ((⟨m, x.1, (y.1, z.1)⟩ : Rel A (.prod B C)), x.2 && y.2 && z.2)

/-- `⟨R, S⟩`, `join` on the keys (`pairJoinC`), both value sides kept under one `n` as the columns of one product
    side, and whether it ran within capacity: `rep_pair`'s count bounds decided, `&&` the bits of the keys' codes and
    of the three picks (`codesC`, `pairJoinC`), as `compC`. -/
def pairC {A B C : Obj} (R : Rel A B) (S : Rel A C) : Rel A (.prod B C) × Bool :=
  let kc := A.codesC #v[⟨_, R.key⟩, ⟨_, S.key⟩]
  let r := pairJoinC R S kc.1[0] kc.1[1]
  (r.1, kc.2 && decide (S.n.toNat < 2 ^ 63) && decide (R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size) && r.2)

/-- `⟨R, S⟩`: `pairC`'s relation. -/
def pair {A B C : Obj} (R : Rel A B) (S : Rel A C) : Rel A (.prod B C) := (pairC R S).1

/-- `outl`: the first component's columns, nothing runs. -/
def outl {k v w : Obj} (T : Rel k (.prod v w)) : Rel k v := ⟨T.n, T.key, T.val.1⟩
/-- `outr`: the second component's columns. -/
def outr {k v w : Obj} (T : Rel k (.prod v w)) : Rel k w := ⟨T.n, T.key, T.val.2⟩

/-- The rows of `R` numbered from `k`: row `i` keyed by `k + i`, its value kept — `Ew.val` add on `til`
    at the count `m`, which the row index is too (`Ew.val_size`). Row order enters here, as in `enum`. -/
def num {A B : Obj} (R : Rel A B) (k : USize) : Rel .long B :=
  let m := R.n
  ⟨m, valCol Ew.add Ew.va (tilLongs m) (one k.toUInt64), Vals.pick B R.val (tilLongs m) m (len_tilLongs m)⟩

/-- `num` and whether it ran within capacity: `rep_num`'s key bound decided, `&&` the values fitting at all their
    rows (`fitsN`), which `til` picks; `num` itself runs. -/
def numC {A B : Obj} (R : Rel A B) (k : USize) : Rel .long B × Bool :=
  (num R k, decide (k.toNat + R.n.toNat < 2 ^ 63) && Vals.fitsN B R.val R.n.toNat)

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

/-- An interned atom column's dictionary entry count, `0` unencoded. A def, so `Vals.reads` and the bounds on it
    name one constant rather than each module its own `match` auxiliary, which `omega` sees as distinct atoms. -/
def _root_.LeetQ.Rel.Arr.dictSize {t : QAtomicType} {n : USize} (x : Arr t n) : Nat :=
  match x.enc with | .enum _ o _ => o.size | _ => 0

/-- **What reading `x` at the rows `ps` touches**, the one size measure every fit bound is arithmetic on: the
    rows read at each level, an interned atom's dictionary, an array's payload count, a sum's two side counts —
    each clause `Vals.PickFits`'s bounds summed, at the same windows (`w`) and side positions (`side`). A payload
    and a side are read at all their rows as well: `raze` takes them whole (`Vals.RazeFits`), rows no parent row
    reaches included. -/
def _root_.LeetQ.Rel.Vals.reads : (A : Obj) → {n : USize} → Vals A n → List Nat → Nat
  | .atom t, n, x, ps => ps.length + Arr.dictSize (t := t) (n := n) x
  | .prod a b, _, x, ps => Vals.reads a x.1 ps + Vals.reads b x.2 ps
  | .arr b, n, ⟨p, lo, hi, f⟩, ps =>
    let w (k : Nat) : List Nat := if h : k < n.toNat then
      List.range' (min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
        (min (max (hi.get ⟨k, h⟩).toInt 0).toNat p.toNat - min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
      else []
    ps.length + p.toNat + Vals.reads b f (ps.flatMap w ++ List.range p.toNat)
  | .sum a b, n, ⟨l, r, tag, idx, x, y⟩, ps =>
    let side (s : Bool) (c : Nat) : List Nat := ps.filterMap fun k =>
      if h : k < n.toNat then
        (if tag.get ⟨k, h⟩ = s then some (min (max (idx.get ⟨k, h⟩).toInt 0).toNat (c - 1)) else none)
      else if s then none else some c
    ps.length + l.toNat + r.toNat + Vals.reads a x (side false l.toNat ++ List.range l.toNat) +
      Vals.reads b y (side true r.toNat ++ List.range r.toNat)

/-- `R × S` and whether it ran within capacity: `rep_prod`'s bounds decided as it states them, the pair count and
    each column's reads repeated once per row of the other side; `prod` itself runs. -/
def prodC {A B D E : Obj} (R : Rel A B) (S : Rel D E) : Rel (.prod A D) (.prod B E) × Bool :=
  (prod R S, decide (R.n.toNat * S.n.toNat < USize.size) && decide (R.n.toNat * S.n.toNat < 2 ^ 63) &&
    decide ((S.n.toNat + 1) * Vals.reads A R.key (List.range R.n.toNat) < min (2 ^ 63) USize.size) &&
    decide ((S.n.toNat + 1) * Vals.reads B R.val (List.range R.n.toNat) < min (2 ^ 63) USize.size) &&
    decide ((R.n.toNat + 1) * Vals.reads D S.key (List.range S.n.toNat) < min (2 ^ 63) USize.size) &&
    decide ((R.n.toNat + 1) * Vals.reads E S.val (List.range S.n.toNat) < min (2 ^ 63) USize.size))

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

/-- `inl` and whether it ran within capacity: `rep_inl`'s count bound decided; it calls no capacity helper. -/
def inlC {A B : Obj} {n : USize} (X : Vals A n) : Rel A (.sum A B) × Bool := (inl X, decide (n.toNat ≤ 2 ^ 63))

/-- `inr : B ⟶ A + B` on the universe `Y`: each `y` to `inr y`. -/
def inr {A B : Obj} {n : USize} (Y : Vals B n) : Rel B (.sum A B) := ⟨n, Y, ⟨0, n, tags #[(n, true)] n, tilCol n, Vals.empty A, Y⟩⟩

/-- `inr` and whether it ran within capacity: `rep_inr`'s count bound decided. -/
def inrC {A B : Obj} {n : USize} (Y : Vals B n) : Rel B (.sum A B) × Bool := (inr Y, decide (n.toNat ≤ 2 ^ 63))

/-- `[R, S] : A + B ⟶ C`: `inl x` to what `R` relates `x` to, `inr y` to what `S` relates `y` to. The keys are
    the two key payloads as they are (`sumVals`), the values razed (`Obj.raze`), `R.n + S.n` rows, which fit a
    `USize`. Whether it ran within capacity: `need`'s guard, `rep_junc`'s `2^63` bound decided, `&&` the bit of the
    values' raze (`razeC`). -/
def juncC {A B C : Obj} (R : Rel A C) (S : Rel B C) : Rel (.sum A B) C × Bool :=
  need (R.n.toNat + S.n.toNat < USize.size) (fun _ => s!"[R,S]: {R.n} + {S.n} rows do not fit a USize")
    (fun _ => (zero, false)) fun hN =>
  let v := C.razeC #[⟨_, R.val⟩, ⟨_, S.val⟩] (by simpa using hN)
  (⟨R.n + S.n, sumVals R.key S.key hN, toUSize_eq (by rw [toNat_add_fits hN]) ▸ v.1⟩,
    decide (R.n.toNat + S.n.toNat ≤ 2 ^ 63) && v.2)

/-- `[R, S] : A + B ⟶ C`: `juncC`'s relation. -/
def junc {A B C : Obj} (R : Rel A C) (S : Rel B C) : Rel (.sum A B) C := (juncC R S).1

/-- `R + S ≜ [R inl, S inr] : A + B ⟶ C + D`, built directly: the key and the value sides share one tag and one
    position column over the payloads of `R` and of `S` as they are, where the composites would join each
    relation with an injection and raze the values (the guard below holds it equal to that term). -/
def sum {A B C D : Obj} (R : Rel A C) (S : Rel B D) : Rel (.sum A B) (.sum C D) :=
  need (R.n.toNat + S.n.toNat < USize.size) (fun _ => s!"R + S: {R.n} + {S.n} rows do not fit a USize")
    (fun _ => zero) fun hN =>
  let k := sumVals R.key S.key hN
  ⟨R.n + S.n, k, ⟨R.n, S.n, k.2.2.1, k.2.2.2.1, R.val, S.val⟩⟩

/-- `R + S` and whether it ran within capacity: `rep_sum`'s two count bounds decided; it calls no capacity helper. -/
def sumC {A B C D : Obj} (R : Rel A C) (S : Rel B D) : Rel (.sum A B) (.sum C D) × Bool :=
  (sum R S, decide (R.n.toNat + S.n.toNat < USize.size) && decide (R.n.toNat + S.n.toNat ≤ 2 ^ 63))

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

/-- `pairsIn Q D` and whether it ran within capacity: `compC`'s bit. -/
def pairsInC {B : Obj} (Q : Rel B B) (D : Rel (.prod B B) (.prod B B)) : Rel (.prod B B) (.prod B B) × Bool :=
  compC D (idU (Q.key, Q.val))

/-- The order `Q` as a test of pairs:the pairs of the coreflexive `D` that are pairs of `Q`. Every op that
    takes an order runs it as such a test, on the pairs it compares (`estOn`, …); `Q` closed is this test. -/
def pairsIn {B : Obj} (Q : Rel B B) (D : Rel (.prod B B) (.prod B B)) : Rel (.prod B B) (.prod B B) :=
  (pairsInC Q D).1

/-- The pairs `(b, c)` of the coreflexive `D` whose swap `(c, b)` passes the test `qC`, and whether it ran within
    capacity: the `&&` of `pairC`'s, `ranC`'s, the test's, `compC`'s and `domC`'s bits. -/
def swapInC {B : Obj} (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (D : Rel (.prod B B) (.prod B B)) : Rel (.prod B B) (.prod B B) × Bool :=
  let s := pairC (outr D) (outl D)
  let E := ranC s.1
  let t := qC E.1
  let M := compC s.1 t.1
  let d := domC M.1
  (d.1, s.2 && E.2 && t.2 && M.2 && d.2)

/-- The pairs `(b, c)` of the coreflexive `D` whose swap `(c, b)` passes the test `q`: `swapInC`'s relation. -/
def swapIn {B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (D : Rel (.prod B B) (.prod B B)) : Rel (.prod B B) (.prod B B) :=
  (swapInC (fun r => (q r, true)) D).1

/-- **`swapInC`'s relation, written out**: each twin's `.1` is its op, so the body is `dom (s ≫ q (ran s))`. -/
theorem swapInC_fst {B : Obj} (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (D : Rel (.prod B B) (.prod B B)) :
    (swapInC qC D).1 = dom (pair (outr D) (outl D) ≫ (qC (ran (pair (outr D) (outl D)))).1) := rfl

/-- `thin(Q)` per key, `Q` the test `q` run on the pairs `⟨G,G⟩` of values of one key, never on every pair of
    `ran G`: `(a, c)` dropped when some value `b` of `a` passes `(b, c)` and not `(c, b)`. `thin Q` is this at
    `pairsIn Q`. `thinOnC`'s bit is the `&&` of its pieces' and the test's (twice: on `D` and inside `swapInC`). -/
def thinOnC {A B : Obj} (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) (G : Rel A B) :
    Rel A B × Bool :=
  let P := pairC G G
  let D := ranC P.1
  let t := qC D.1
  let S := swapInC qC D.1
  let Y := diffC t.1 S.1
  let M := compC P.1 (outr Y.1)
  let r := diffC G M.1
  (r.1, P.2 && D.2 && t.2 && S.2 && Y.2 && M.2 && r.2)

/-- `thinOn q G`: `thinOnC`'s relation at the test `q` with no bit of its own. -/
def thinOn {A B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B)) (G : Rel A B) :
    Rel A B := (thinOnC (fun r => (q r, true)) G).1

/-- `est(Q)` per key, `Q` the test `q` run on the pairs `⟨G,G⟩` of values of one key: `(a, b)` dropped when
    some other value `c` of `a` fails `(b, c)`. `est Q` is this at `pairsIn Q`. `estOnC`'s bit is the `&&` of its
    pieces' and the test's. -/
def estOnC {A B : Obj} (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) (G : Rel A B) :
    Rel A B × Bool :=
  let P := pairC G G
  let D := ranC P.1
  let V := ranC G
  let t := qC D.1
  let Y := diffC D.1 t.1
  let W := pairC V.1 V.1
  let N := ranC W.1
  let Z := diffC Y.1 N.1
  let M := compC P.1 (outl Z.1)
  let r := diffC G M.1
  (r.1, P.2 && D.2 && V.2 && t.2 && Y.2 && W.2 && N.2 && Z.2 && M.2 && r.2)

/-- `estOn q G`: `estOnC`'s relation at the test `q` with no bit of its own. -/
def estOn {A B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B)) (G : Rel A B) :
    Rel A B := (estOnC (fun r => (q r, true)) G).1

/-- `est Q G` and whether it ran within capacity: `estOnC` at the test `pairsInC Q`. -/
def estC {A B : Obj} (Q : Rel B B) (G : Rel A B) : Rel A B × Bool := estOnC (pairsInC Q) G

/-- `thin Q G` and whether it ran within capacity: `thinOnC` at the test `pairsInC Q`. -/
def thinC {A B : Obj} (Q : Rel B B) (G : Rel A B) : Rel A B × Bool := thinOnC (pairsInC Q) G

/-- `est(Q)` per key of the family `G : A ⟶ B`, the `Q`-least values, `∋ ∩ (∈ \ Q°)`: the rows `(a, b)` of
    `G` with `b Q c` for every other value `c` of `a`. The pairs `(a, b)` it drops are those with a value `c`
    of `a`, `c ≠ b`, and no `b Q c`, so `est`, as `thin`, reads `Q` up to its reflexive closure, and a strict
    linear order answers as its reflexive one. -/
def est {A B : Obj} (Q : Rel B B) (G : Rel A B) : Rel A B := (estC Q G).1

/-- `thin(Q)` per key of the family `G : A ⟶ B`, the `Q`-minimal values: the rows `(a, b)` of `G` with no
    `(a, c)` of `G` where `c` is strictly `Q`-below `b`, the strict part being `Q \ Q°` (`Q` itself when
    strict). -/
def thin {A B : Obj} (Q : Rel B B) (G : Rel A B) : Rel A B := (thinC Q G).1

/-- A pick twin's `.1` is the pick, at each constructor of the side. -/
theorem pickC_fst (A : Obj) {n : USize} (x : Vals A n) (i : ByteArray) (m : USize) (h : len i = m.toNat) :
    (Vals.pickC A x i m h).1 = Vals.pick A x i m h := by
  cases A <;> rfl

/-- A raze twin's `.1` is the raze, at each constructor of the side. -/
theorem razeC_fst (A : Obj) (cs : Array (Part A)) (h) : (Obj.razeC A cs h).1 = Obj.raze A cs h := by
  cases A <;> rfl

/-- `cons° : arr B ⟶ B × arr B` on the arrays of `X`: each non-empty row to its first element and the rest.
    The rows with a clamped count above `0` (`whereBits`); the rest `lo + 1`, `hi` the clamped end, its payload
    then cut to the cells it refers to (`Vals.compact`), every column at the count of the rows kept. The bit is
    the pick of `X` at the non-empty rows (`pickC`), `rep_uncons`'s one fit. -/
def unconsC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod B (.arr B)) × Bool :=
  let s := slicesOf X
  let i := whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one 0) n)
  longCount "cons°" i fun r hr =>
  let l := gather 8 s.1 i
  let x := Vals.pickC (.arr B) X i r hr
  (⟨r, x.1, (Vals.pick B X.2.2.2 l r ((gather_len _ _).trans hr),
      Vals.compact (.arr B) ⟨X.1, valCol Ew.add Ew.va l (one 1), valCol Ew.add Ew.vv l (gather 8 s.2 i), X.2.2.2⟩)⟩,
    x.2)

/-- `cons°`: `unconsC`'s relation. -/
def uncons {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod B (.arr B)) := (unconsC X).1

/-- `cons : B × arr B ⟶ arr B` on the rows of `P`: each `(y, ys)` to the array `y` then `ys`, under its key.
    The new arrays are laid out one after another (`sums` of the counts plus one); the tails gathered from
    the old payload (`expand` of the clamped counts) and the heads razed after them, then put in place by
    the `grade` of their places. Every row of `P` is kept, at its count; the payload holds the tails' cells
    and one head per row, a count that must fit a `USize`. The bit: `P`'s tails and keys fitting at all their
    rows (`fitsN`), `&&`, out of `expand` in the pair, `rep_cons`'s count bound decided on the copies' count `k` plus the rows (`k` is the
    tails' counts summed, `len_expand_slicesOf`; `need` already bounds it by a `USize`) and the bits of the raze
    and of the last pick (`razeC`, `pickC`). -/
def consC {K B : Obj} (P : Rel K (.prod B (.arr B))) : Rel K (.arr B) × Bool :=
  let n := P.n
  let T := P.val.2
  let s := slicesOf T
  let c1 := addc n s.2 1
  let hi := sums n c1
  let lo := sub n hi c1
  let r := expand n s.2 (fun _ => default) fun k xi xr _ _ =>
    need (k.toNat + n.toNat < USize.size) (fun _ => s!"cons: {k} + {n} cells do not fit a USize") (fun _ => default)
      fun hN =>
    let flat := Obj.razeC B #[⟨k, Vals.pick B T.2.2.2 (add k (gather 8 s.1 xi) xr) k (len_val ..)⟩, ⟨n, P.val.1⟩]
      (by simpa using hN)
    let dst := addc k (add k (gather 8 lo xi) xr) 1
    let perm := (Code.ofLongs (concatBytes #[dst, lo])).grade
    longCount "cons" perm fun p hp =>
    let v := Vals.pickC B flat.1 perm p hp
    ((⟨n, Vals.compact K P.key, ⟨p, valCol Ew.sub Ew.vv hi c1, longsN n hi (sums_le (len_val ..)), v.1⟩⟩ :
      Rel K (.arr B)), decide (k.toNat + n.toNat < 2 ^ 63) && flat.2 && v.2)
  (r.1, Vals.fitsN (.arr B) T n.toNat && Vals.fitsN K P.key n.toNat && r.2)

/-- `cons`: `consC`'s relation. -/
def cons {K B : Obj} (P : Rel K (.prod B (.arr B))) : Rel K (.arr B) := (consC P).1

/-- The rounds of a fold over the rows of `ids : row ⟶ [E]`, from each array's last element to its first:
    the state `pend : row ⟶ V` starts as given, each row from its own values, so two rows of one array may
    start apart; round `k` pairs the rows longer than `k` with their element `k` from the end (`el`) and hands
    both to `step`, and moves the rows not longer to `out`. A row is never longer than the payload, so its
    size plus one rounds end every row (`iter`). The result is keyed by the row ids.
    `foldRound` is round `k` on the state `(pend, out, k)`, and whether it ran within capacity: the step's own bit
    `&&` the bits of the round's `nub`, `antiJoin` and `∪` (`nubC`, `antiJoinC`, `unionC`). -/
def foldRound {E V : Obj} (ids : Rel .long (.arr E)) (step : Rel .long E → Rel .long V → Rel .long V × Bool)
    (st : Rel .long V × Rel .long V × Nat) : (Rel .long V × Rel .long V × Nat) × Bool :=
  let s := slicesOf ids.val
  let ends := add ids.n s.1 s.2
  let a := whereBits ids.n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one st.2.2.toUInt64) ids.n)
  let el : Rel .long E := longCount "foldRows" a fun r hr =>
    let pos := Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul (gather 8 ends a) (one (st.2.2 + 1).toUInt64) r
    ⟨r, Vals.pick .long ids.key a r hr, Vals.pick E ids.val.2.2.2 pos r (len_val ..)⟩
  -- `≫` keeps row multiplicity, so a step reaching a value along two paths doubles its rows: `nub` each round,
  -- or the rows of `pend` grow as the paths do (`2^k` for `π₂ ∪ π₂ succ`), not as the pairs
  let S := step el st.1
  let N := nubC S.1
  let J := antiJoinC st.1° (idU el.key)
  let U := unionC st.2.1 J.1°
  ((N.1, U.1, st.2.2 + 1), S.2 && N.2 && J.2 && U.2)

/-- `foldRows` and whether it ran within capacity: the `&&` of the bits of the rounds it ran, carried in the
    loop state from `true`. -/
def foldRowsC {E V : Obj} (ids : Rel .long (.arr E)) (pend : Rel .long V)
    (step : Rel .long E → Rel .long V → Rel .long V × Bool) : Rel .long V × Bool :=
  let r := iter (ids.val.1.toNat + 1) (fun st : (Rel .long V × Rel .long V × Nat) × Bool => st.1.1.n == 0)
    (fun st => let g := foldRound ids step st.1; (g.1, st.2 && g.2)) ((pend, zero, 0), true)
  (r.1.2.1, r.2)

/-- `foldRows`: `foldRowsC`'s relation, the step one with no bit of its own. -/
def foldRows {E V : Obj} (ids : Rel .long (.arr E)) (pend : Rel .long V)
    (step : Rel .long E → Rel .long V → Rel .long V) : Rel .long V :=
  (foldRowsC ids pend fun el p => (step el p, true)).1

/-- `foldRows` on the arrays of `X`, every row starting from every value of `e`, read back at the arrays by
    `num`'s row ids; and whether it ran within capacity: the bits of `num`, `⊤`, the rounds and `≫`. -/
def foldByC {E V : Obj} {n m : USize} (X : Vals (.arr E) n) (e : Vals V m)
    (step : Rel .long E → Rel .long V → Rel .long V × Bool) : Rel (.arr E) V × Bool :=
  let ids := numC (idU X) 0
  let p := topC (A := .long) (B := V) ids.1.key e
  let F := foldRowsC ids.1 p.1 step
  let c := compC ids.1° F.1
  (c.1, ids.2 && p.2 && F.2 && c.2)

/-- `foldBy`: `foldByC`'s relation, the step one with no bit of its own. -/
def foldBy {E V : Obj} {n m : USize} (X : Vals (.arr E) n) (e : Vals V m)
    (step : Rel .long E → Rel .long V → Rel .long V) : Rel (.arr E) V :=
  (foldByC X e fun el p => (step el p, true)).1

/-- A fold step in demand form: `S` runs on the pairs (element, value) the round meets, `S D` for the
    coreflexive `D` on them, so a carrier with no universe folds too. `S` a twin family; the bit the `&&` of
    `pairC`'s, `ranC`'s, `S`'s and `compC`'s. -/
def demandStepC {E V : Obj} (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V × Bool) (el : Rel .long E)
    (pend : Rel .long V) : Rel .long V × Bool :=
  let p := pairC el pend; let d := ranC p.1; let s := S d.1; let c := compC p.1 s.1
  (c.1, p.2 && d.2 && s.2 && c.2)

/-- `demandStep`: `demandStepC`'s relation, the family one with no bit of its own. -/
def demandStep {E V : Obj} (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V) (el : Rel .long E)
    (pend : Rel .long V) : Rel .long V :=
  (demandStepC (fun D => (S D, true)) el pend).1

/-- `⦇e, S⦈` on the arrays `X`, the fold of cons-lists, `S` a twin family in demand form (`demandStepC`), and
    whether it ran within capacity. `[]` to each value of `e`, `cons(x, xs)` to `w` when `xs` goes to `v` and
    `(x, v) S(D) w`. -/
def foldOnC {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V × Bool)
    (X : Vals (.arr E) n) : Rel (.arr E) V × Bool :=
  foldByC X e (demandStepC S)

/-- `foldOn`: `foldOnC`'s relation, the family one with no bit of its own. -/
def foldOn {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V)
    (X : Vals (.arr E) n) : Rel (.arr E) V :=
  (foldOnC e (fun D => (S D, true)) X).1

/-- `⦇e, S⦈` on the arrays of `X`, `S` one relation: `foldOnC` with `S` whatever pairs a round meets, and whether
    it ran within capacity. An array may have several results or none. -/
def foldC {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) V) (X : Vals (.arr E) n) :
    Rel (.arr E) V × Bool :=
  foldOnC e (fun _ => (S, true)) X

/-- `fold`: `foldC`'s relation. -/
def fold {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) V) (X : Vals (.arr E) n) : Rel (.arr E) V :=
  (foldC e S X).1

/-- The one-row side holding the empty array. -/
def nilVal (B : Obj) : Vals (.arr B) 1 := ⟨0, col [0], col [0], Vals.empty B⟩

/-- `F(R)`, the list functor on the arrays of `X`: `xs` to every `ys` of its length with `xs[i] R ys[i]` at
    each `i` — `⦇[], (R × 𝟙) ≫ cons⦈`, each round pairing every image of the element with every array so far. -/
def mapC {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) : Rel (.arr A) (.arr B) × Bool :=
  foldByC X (nilVal B) fun el pend =>
    let q := compC el R; let p := pairC q.1 pend; let c := consC p.1
    (c.1, q.2 && p.2 && c.2)
def map {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) : Rel (.arr A) (.arr B) := (mapC R X).1

/-! ## Order on numbers, the power side, and the note's list functions -/

/-- The rows `<` keeps the pairs of one value from (`ltC`): `rank` of `U` (`gradeColumn`, ties in position order),
    `cross` of the positions, `Ew.cmp <` of their ranks. The domain is the types `gradeColumn` orders by value:
    every atom but a general list, whose witness `decide` discharges. -/
def ltRows {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (_h : t ≠ .general := by decide) :
    Rel (.atom t) (.atom t) :=
  let r := longsOf (Ops.rank (t := t) U _h)
  let c := cross n n
  longCount "<" c.1 fun nn _ =>
    let i := whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 r c.1) (gather 8 r c.2) nn)
    longCount "<" i fun k hk =>
      ⟨k, Vals.pick _ U (gather 8 c.1 i) k ((gather_len _ _).trans hk), Vals.pick _ U (gather 8 c.2 i) k ((gather_len _ _).trans hk)⟩

/-- `<` on the elements of `U` (`leRel`, AOP/A7_2_RelSet.lean:160, strict), the pairs `(U[i], U[j])` with
    `U[i] < U[j]`: `ltRows` less the pairs of one value the ties' order put apart (`diffC` at `idU U`). Whether it
    ran within capacity: `diffC`'s bit `&&` `rep_lt`'s two count bounds decided. The picks of `U` stay plain: an
    atom's rows read back with no fit (`pick_row_atom`). -/
def ltC {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) :
    Rel (.atom t) (.atom t) × Bool :=
  let d := diffC (ltRows U h) (idU U)
  (d.1, d.2 && decide (n.toNat * n.toNat < USize.size) && decide (n.toNat * n.toNat < 2 ^ 63))

/-- `<` on the elements of `U`: `ltC`'s relation. -/
def lt {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (_h : t ≠ .general := by decide) : Rel (.atom t) (.atom t) :=
  (ltC U _h).1

/-- `≤` on the elements of `U` (`leRel`, AOP/A7_2_RelSet.lean:160), `lt U ∪ 𝟙`, and whether it ran within
    capacity: `ltC`'s bit `&&` `unionC`'s. -/
def leqC {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) :
    Rel (.atom t) (.atom t) × Bool :=
  let l := ltC U h; let u := unionC l.1 (idU U); (u.1, l.2 && u.2)

/-- `≤` on the elements of `U`: `leqC`'s relation. -/
def leq {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) : Rel (.atom t) (.atom t) :=
  (leqC U h).1

/-- `succ : long ⟶ long` on `U` (`succ`, AOP/A5_6_ListCombinators.lean:343): each `u` to `u + 1` where `u + 1`
    is in `U`, so the range stays in `U` and the top of `U` goes to nothing. `Ew.val` add, then the rows whose
    sum is a `member` of `U` (`whereBits`), key and sum gathered there. Whether it ran within capacity: the bit of
    its codes (`codesC`); the picks of atoms stay plain. -/
def succC {n : USize} (U : Vals (.atom .long) n) : Rel (.atom .long) (.atom .long) × Bool :=
  let s : Arr .long n := valCol Ew.add Ew.va (longsOf U) (one 1)
  let c := (Obj.atom .long).codesC #v[⟨_, s⟩, ⟨_, U⟩]
  let k := whereBits n (c.1[0].member c.1[1])
  (longCount "succ" k fun r hr => ⟨r, Vals.pick _ U k r hr, Vals.pick (.atom .long) s k r hr⟩, c.2)

/-- `succ : long ⟶ long` on `U`: `succC`'s relation. -/
def succ {n : USize} (U : Vals (.atom .long) n) : Rel (.atom .long) (.atom .long) := (succC U).1

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
    `τ≜⟨𝟙,⊸ nil⟩ cons`, diag/aop/07-optimisation.typ:694), and whether it ran within capacity: `transposeC`'s
    bit at `idU X`. -/
def τC {A : Obj} {n : USize} (X : Vals A n) : Rel A (.arr A) × Bool := transposeC (idU X)

/-- `τ` on `X`: `τC`'s relation. -/
def τ {A : Obj} {n : USize} (X : Vals A n) : Rel A (.arr A) := (τC X).1

/-- `nil : K ⟶ arr B` on the one-row side `I`: its element to the empty array (`nil`,
    AOP/A1_7_Pointfree.lean:36; the note's `nil ≜ []`, diag/aop/07-optimisation.typ:443). -/
def nil {K B : Obj} (I : Vals K 1) : Rel K (.arr B) := ⟨1, I, nilVal B⟩

/-- `α ≜ [nil, cons] : K + B × arr B ⟶ arr B`, `nil` on the one-row `I`, `cons` on the pairs `P` (the note's
    `α ≜ [nil,cons]`, diag/aop/07-optimisation.typ:449; `alphaR_eq_junc`, AOP/A5_6_ListCombinators.lean:727),
    on the twins `juncC`, `consC`; the bit the `&&` of theirs. -/
def alphaC {K B : Obj} {n : USize} (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) :
    Rel (.sum K (.prod B (.arr B))) (.arr B) × Bool :=
  let c := consC (idU P)
  let j := juncC (nil I) c.1
  (j.1, j.2 && c.2)

/-- `α`: `alphaC`'s relation, `junc (nil I) (cons (idU P))` once `juncC`'s `.1` is `junc` (`juncC_fst`). -/
def alpha {K B : Obj} {n : USize} (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) :
    Rel (.sum K (.prod B (.arr B))) (.arr B) :=
  (alphaC I P).1

/-- `Λ(R)` total on `U`: each element of `U` that `R` relates to nothing goes to the empty array, which `Λ(R)`,
    one row per key of `R`, has no row for: `Λ(R) ∪ ⊤` from `(idU U − dom R)`'s keys to `nilVal B`. Whether it ran
    within capacity: the `&&` of the bits of the twins it runs (`transposeC`, `domC`, `diffC`, `topC`, `unionC`). -/
def lamOnC {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Rel A (.arr B) × Bool :=
  let t := transposeC R; let d := domC R
  let D := diffC (idU U) d.1
  let N := topC D.1.key (nilVal B)
  let u := unionC t.1 N.1
  (u.1, t.2 && d.2 && D.2 && N.2 && u.2)

/-- `Λ(R)` total on `U`: `lamOnC`'s relation. -/
def lamOn {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Rel A (.arr B) := (lamOnC R U).1

/-- `E(R) : arr A ⟶ arr B` on the arrays `X`, the existential image, the note's `E(R)≜frac(∋R,∋)`
    (diag/aop/07-optimisation.typ:718), `existsImage R ≜ Λ(∋ ≫ R)` (AOP/A4_6.lean:95): `Λ(∋R)` total on `X`, and
    whether it ran within capacity: the bits of `memC`, `compC`, `lamOnC`. -/
def EC {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) : Rel (.arr A) (.arr B) × Bool :=
  let m := memC X; let c := compC m.1 R; let l := lamOnC c.1 X
  (l.1, m.2 && c.2 && l.2)

/-- `E(R)` on the arrays `X`: `EC`'s relation. -/
def E {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) : Rel (.arr A) (.arr B) := (EC R X).1

/-- `P(R) : arr A ⟶ arr B` from the arrays `X` to the arrays `Y`, the power relator (`powerRel`,
    AOP/A5_4_PowerRel.lean:34): `((∋)° \ (R ≫ (∋)°)) ∩ ((∋ ≫ R) / ∋)`, every element of `xs` `R`-reaches into `ys`
    and every element of `ys` is reached from `xs`. A relation, not a map, so both ends range over a
    universe: `X` the inputs, `Y` the outputs. Whether it ran within capacity: the bits of the twins it runs
    (`memC`, `compC`, `leftDivC`, `rightDivC`, `interC`). -/
def PC {A B : Obj} {n m : USize} (R : Rel A B) (X : Vals (.arr A) n) (Y : Vals (.arr B) m) :
    Rel (.arr A) (.arr B) × Bool :=
  let mx := memC X; let my := memC Y
  let ry := compC R (my.1)°; let xr := compC mx.1 R
  let l := leftDivC (mx.1)° ry.1 X Y; let d := rightDivC xr.1 my.1 X Y
  let i := interC l.1 d.1
  (i.1, mx.2 && my.2 && ry.2 && xr.2 && l.2 && d.2 && i.2)

/-- `P(R)` from `X` to `Y`: `PC`'s relation. -/
def P {A B : Obj} {n m : USize} (R : Rel A B) (X : Vals (.arr A) n) (Y : Vals (.arr B) m) : Rel (.arr A) (.arr B) :=
  (PC R X Y).1

/-- `tail ≜ cons° π₂` on the arrays `X` (diag/aop/05-datatypes.typ:561). -/
def tail {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := outr (uncons X)

/-- `tail` and `unconsC`'s bit, `rep_tail`'s one fit being `rep_uncons`'s. -/
def tailC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  let u := unconsC X; (outr u.1, u.2)

/-- `length ≜ ⦇[zero,π₂ succ]⦈` on the arrays `X` (diag/aop/09-dynamic.typ:506; `length`,
    AOP/A5_6_ListCombinators.lean:328): `succ` on `0 … X.1`, since no array is longer than the payload `X.1`. -/
def lengthC {E : Obj} {n : USize} (X : Vals (.arr E) n) : Rel (.arr E) (.atom .long) × Bool :=
  needSize (X.1.toNat + 1) "length: the payload's count plus one" (fun _ => (default, false)) fun c =>
  let sc := succC (tilCol c)
  let r := foldOnC (col [0]) (fun D => compC (outr D) sc.1) X
  (r.1, sc.2 && r.2 && decide (X.1.toNat + 1 < 2 ^ 63))

/-- `length`: `lengthC`'s relation; the bit `succC`'s, `foldOnC`'s (each round's `compC`'s among them) and the
    count's `+ 1` below `2^63`. -/
def length {E : Obj} {n : USize} (X : Vals (.arr E) n) : Rel (.arr E) (.atom .long) := (lengthC X).1


/-- `suffix : arr E ⟶ arr E` on the arrays `X`, each array to each of its final segments (`suffix`,
    AOP/A5_6_ListCombinators.lean:221): `tail*`, `𝟙 ∪ tail ∪ tail tail ∪ …` by `iter`, each round `tail` on the
    arrays the last one reached; an array is never longer than the payload `X.1`, so `X.1 + 1` rounds end.
    `iterC` is `iter` on a round that also answers a bit, carrying the `&&` of the bits of the rounds it ran. -/
def iterC {α : Type} (n : Nat) (done : α → Bool) (r : α → α × Bool) (a : α) : α × Bool :=
  iter n (fun s => done s.1) (fun s => let g := r s.1; (g.1, s.2 && g.2)) (a, true)

/-- `fixOn` on a step twin `φC` and whether it ran within capacity: `nubC`'s bit at `X₀` `&&` `iterC`'s, each round's
    the step's `&&` `nubC`'s. `fixOn` keeps its own written-out body: `AC3` reads its `iter` rounds by unfolding it;
    `fixOnC_fst` ties the two. -/
def fixOnC {A B : Obj} (n : Nat) (φC : Rel A B → Rel A B × Bool) (X₀ : Rel A B) : (Rel A B × Nat) × Bool :=
  let x := nubC X₀
  let r := iterC n (fun s => s.1 == s.2.1.n.toNat)
    (fun s => let y := φC s.2.1; let z := nubC y.1; ((s.2.1.n.toNat, z.1, s.2.2 + 1), y.2 && z.2))
    (x.1.n.toNat + 1, x.1, 0)
  ((r.1.2.1, r.1.2.2), x.2 && r.2)

/-- One round of `suffix` on `(S, F)`, `S ∪ F tail` beside `F tail`, and its bit: `ranC`'s, `tailC`'s, `compC`'s,
    `unionC`'s. -/
def suffixRound {E : Obj} (st : Rel (.arr E) (.arr E) × Rel (.arr E) (.arr E)) :
    (Rel (.arr E) (.arr E) × Rel (.arr E) (.arr E)) × Bool :=
  let W := ranC st.2
  let t := tailC W.1.val
  let F := compC st.2 t.1
  let U := unionC st.1 F.1
  ((U.1, F.1), W.2 && t.2 && F.2 && U.2)

/-- `suffix` and whether it ran within capacity: the `&&` of the bits of the rounds it ran (`iterC`). -/
def suffixC {E : Obj} {n : USize} (X : Vals (.arr E) n) : Rel (.arr E) (.arr E) × Bool :=
  let r := iterC (X.1.toNat + 1) (fun s => s.2.n == 0) suffixRound (idU X, idU X); (r.1.1, r.2)

/-- `suffix`: `suffixC`'s relation. -/
def suffix {E : Obj} {n : USize} (X : Vals (.arr E) n) : Rel (.arr E) (.arr E) := (suffixC X).1

/-! ## Arrays of arrays in list order: maps on positions -/

/-- Each array of `X` to the array of its `count + 1` slices `[l k, h k)`, `k = 0 … count`, every one a slice
    of `X`'s own payload, so no cell is copied before `Vals.compact`: `f` maps each row's clamped start and
    count (`slices`) and the `expand` of the `count + 1`s (row, `k`), at the `m` copies, to the slices' starts
    and ends as two columns of `m` rows. The bit: `X` fitting at all its rows, its payload count plus one below `2^63`
    (so is every count plus one, which `expand` reads signed), `&&`, out of `expand` in the pair, the copies'
    count `m` below `2^63` (`rep_inits`'s `hS`: `m` is the counts plus one summed; `need` gives `hU`) and the bit of
    the pick that compacts the slices (`pickC`): the slices of one row overlap in `X`'s payload, so their total
    is known only once they are laid out. -/
def nestC {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (f : (m : USize) → ByteArray × ByteArray → (i r : ByteArray) → len i = m.toNat → Arr .long m × Arr .long m) :
    Rel (.arr B) (.arr (.arr B)) × Bool :=
  let s := slicesOf X
  let c := addc n s.2 1
  let hi := sums n c
  let r := expand n c (fun _ => default) fun m i r hi' _ =>
    let b := f m s i r hi'
    let v := Vals.pickC (.arr B) ⟨X.1, b.1, b.2, X.2.2.2⟩ (tilLongs m) m (len_tilLongs m)
    ((⟨n, Vals.compact (.arr B) X, ⟨m, valCol Ew.sub Ew.vv hi c, longsN n hi (sums_le (len_val ..)), v.1⟩⟩ :
      Rel (.arr B) (.arr (.arr B))), decide (m.toNat < 2 ^ 63) && v.2)
  (r.1, decide (X.1.toNat + 1 < 2 ^ 63) && Vals.fitsN (.arr B) X n.toNat && r.2)

/-- `inits : arr B ⟶ arr (arr B)` on the arrays `X`, the prefixes by increasing length, `[]` first (`initsFn`,
    AOP/A5_6_ListCombinators.lean:847; B&dM §5.6 p.130): the `k`-th is `[lo, lo + k)`; the bit `nestC`'s. -/
def initsC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr (.arr B)) × Bool :=
  nestC X fun m s i r h => let l := gather 8 s.1 i
    (longsN m l (Nat.le_of_eq ((gather_len _ _).trans h).symm), valCol Ew.add Ew.vv l r)

/-- `inits`: `initsC`'s relation. -/
def inits {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr (.arr B)) := (initsC X).1

/-- `tails : arr B ⟶ arr (arr B)` on the arrays `X`, the suffixes by decreasing length, `[]` last (`tailsFn`,
    AOP/A5_6_ListCombinators.lean:857; B&dM §5.6 p.130): the `k`-th is `[lo + k, hi)`; the bit `nestC`'s. -/
def tailsC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr (.arr B)) × Bool :=
  nestC X fun m s i r h => (valCol Ew.add Ew.vv (gather 8 s.1 i) r,
    longsN m (gather 8 (add n s.1 s.2) i) (Nat.le_of_eq ((gather_len _ _).trans h).symm))

/-- `tails`: `tailsC`'s relation. -/
def tails {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr (.arr B)) := (tailsC X).1

/-- `cat : arr B × arr B ⟶ arr B` on the rows of `P`, each `(xs, ys)` to `xs` then `ys` under its key (`cat`,
    AOP/A5_6_ListCombinators.lean:224, the graph of `cappend`). `cons` with an array for a head: the new arrays
    laid out one after another (`sums` of the two counts), each side's cells gathered by the `expand` of its
    counts and razed, then put in place by the `grade` of their places. The bit: both sides and the keys fitting
    at all their rows (`fitsN`), `&&`, out of the two `expand`s in the pair, `rep_cat`'s count bound decided on the two copies' counts `ka + kb` (each
    a side's counts summed, `len_expand_slicesOf`; `need` already bounds it by a `USize`) and the bits of the raze
    and of the last pick (`razeC`, `pickC`). -/
def catC {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) × Bool :=
  let n := P.n
  let x := P.val.1
  let y := P.val.2
  let a := slicesOf x
  let b := slicesOf y
  let c := add n a.2 b.2
  let hi := sums n c
  let lo := sub n hi c
  let r := expand n a.2 (fun _ => default) fun ka ia ra _ _ =>
    expand n b.2 (fun _ => default) fun kb ib rb _ _ =>
    need (ka.toNat + kb.toNat < USize.size) (fun _ => s!"cat: {ka} + {kb} cells do not fit a USize") (fun _ => default)
      fun hN =>
    let flat := Obj.razeC B #[⟨ka, Vals.pick B x.2.2.2 (add ka (gather 8 a.1 ia) ra) ka (len_val ..)⟩,
      ⟨kb, Vals.pick B y.2.2.2 (add kb (gather 8 b.1 ib) rb) kb (len_val ..)⟩] (by simpa using hN)
    let dst := concatBytes #[add ka (gather 8 lo ia) ra, add kb (add kb (gather 8 lo ib) (gather 8 a.2 ib)) rb]
    let perm := (Code.ofLongs dst).grade
    longCount "cat" perm fun p hp =>
    let v := Vals.pickC B flat.1 perm p hp
    ((⟨n, Vals.compact K P.key, ⟨p, valCol Ew.sub Ew.vv hi c, longsN n hi (sums_le (len_val ..)), v.1⟩⟩ :
      Rel K (.arr B)), decide (ka.toNat + kb.toNat < 2 ^ 63) && flat.2 && v.2)
  (r.1, Vals.fitsN (.arr B) x n.toNat && Vals.fitsN (.arr B) y n.toNat && Vals.fitsN K P.key n.toNat && r.2)

/-- `cat`: `catC`'s relation. -/
def cat {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) := (catC P).1

/-- `zip : arr A × arr B ⟶ arr (A × B)` on the rows of `P`, the two arrays position by position up to the
    shorter (`czip`, AOP/A1_7_Pointfree.lean:27; B&dM p.20): the counts' `Ew.val` lesser, laid out by `sums`,
    each side's cell `k` gathered at its own start plus `k`. The bit: both sides and the keys fitting at all
    their rows (`fitsN`), `&&`, out of `expand` in the pair, `rep_zip`'s count bound decided on the copies' count `m` (the lesser counts summed,
    `len_expand_sum`; `need` already bounds it by a `USize`); no pick of `zip` needs a bit of its own. -/
def zipC {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) : Rel K (.arr (.prod A B)) × Bool :=
  let x := P.val.1
  let y := P.val.2
  let n := P.n
  let a := slicesOf x
  let b := slicesOf y
  let c := Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul a.2 b.2 n
  let hi := sums n c
  let r := expand n c (fun _ => default) fun m i r _ _ =>
    ((⟨n, Vals.compact K P.key,
      ⟨m, valCol Ew.sub Ew.vv hi c, longsN n hi (sums_le (len_val ..)),
        (Vals.pick A x.2.2.2 (add m (gather 8 a.1 i) r) m (len_val ..),
          Vals.pick B y.2.2.2 (add m (gather 8 b.1 i) r) m (len_val ..))⟩⟩ : Rel K (.arr (.prod A B))),
      decide (m.toNat < 2 ^ 63))
  (r.1, Vals.fitsN (.arr A) x n.toNat && Vals.fitsN (.arr B) y n.toNat && Vals.fitsN K P.key n.toNat && r.2)

/-- `zip`: `zipC`'s relation. -/
def zip {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) : Rel K (.arr (.prod A B)) := (zipC P).1

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

/-- `snoc°` and whether it ran within capacity: `X` fitting at all its rows (`fitsN`), `rep_unsnoc`'s one fit. -/
def unsnocC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod (.arr B) B) × Bool :=
  (unsnoc X, Vals.fitsN (.arr B) X n.toNat)

/-- `at(k) : arr B ⟶ B` on the arrays of `X`, positions from `0`: each row longer than `k` to the cell at
    `lo + k` of the payload, read in place as `uncons` reads the head; a row of `k` or fewer cells has no pair. -/
def atPos {B : Obj} {n : USize} (k : Nat) (X : Vals (.arr B) n) : Rel (.arr B) B :=
  let s := slicesOf X
  let i := whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one k.toUInt64) n)
  longCount "at" i fun r hr =>
  ⟨r, Vals.pick (.arr B) X i r hr, Vals.pick B X.2.2.2 (addc r (gather 8 s.1 i) k) r (len_val ..)⟩

/-- `at(k)` and whether it ran within capacity: `k` below `2^63` and `X` fitting at all its rows (`fitsN`),
    `rep_atPos`'s premises. -/
def atPosC {B : Obj} {n : USize} (k : Nat) (X : Vals (.arr B) n) : Rel (.arr B) B × Bool :=
  (atPos k X, decide (k < 2 ^ 63) && Vals.fitsN (.arr B) X n.toNat)

/-- `snoc ≜ (𝟙 × τ) cat` on the rows of `P` (`snoc`, AOP/A9_3_Bracket.lean:933): `(xs, a)` to `xs` then `a`.
    `𝟙 × τ` is `⟨π₁, π₂ τ⟩` on the distinct pairs of `P`, one row each, so `P` keeps its rows. Written on the twins
    of its pieces (`τ` is `Λ(idU ·)`), the bit the `&&` of theirs. -/
def snocC {K B : Obj} (P : Rel K (.prod (.arr B) B)) : Rel K (.arr B) × Bool :=
  let D := ranC P
  let t := transposeC (idU (outr D.1).val)
  let T := compC (outr D.1) t.1
  let Q := pairC (outl D.1) T.1
  let M := compC P Q.1
  let r := catC M.1
  (r.1, D.2 && t.2 && T.2 && Q.2 && M.2 && r.2)

/-- `snoc`: `snocC`'s relation. -/
def snoc {K B : Obj} (P : Rel K (.prod (.arr B) B)) : Rel K (.arr B) := (snocC P).1

/-- `cat° : arr B ⟶ arr B × arr B` on the arrays `X`, each array to every way of cutting it in two: the
    `k`-th prefix beside the `k`-th suffix, `⟨inits, tails⟩ zip ∋`, on the twins of its pieces, the bit the `&&`
    of theirs. -/
def uncatC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod (.arr B) (.arr B)) × Bool :=
  let i := initsC X
  let t := tailsC X
  let p := pairC i.1 t.1
  let z := zipC p.1
  let v := memC z.1.val
  let r := compC z.1 v.1
  (r.1, i.2 && t.2 && p.2 && z.2 && v.2 && r.2)

/-- `cat°`: `uncatC`'s relation. -/
def uncat {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.prod (.arr B) (.arr B)) := (uncatC X).1

/-! ## Permutations, sets and order (ch. 6, 8) -/

/-- `perm ≜ ⦇[nil, add]⦈` on the arrays `X` (`perm`, AOP/A5_6_ListCombinators.lean:81; B&dM p.130), `add` putting
    the head anywhere: `(a, xs)` to `ys` then `a` then `zs` for every `(ys, zs)` of `cat°(xs)`. The tuples
    `(a, (ys, zs))` a round meets are distinct keys (`ran`), so `⟨…⟩` on them keeps one row each. Whether it ran
    within capacity: `foldByC`'s, each round's the `&&` of its twins' bits. -/
def permC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  foldByC X (nilVal B) fun el pend =>
    let Dp := ranC pend; let un := uncatC Dp.1.val; let U := compC pend un.1; let q := pairC el U.1
    let D := ranC q.1; let W := pairC (outl D.1) (outr (outr D.1)); let Cn := consC W.1
    let V := pairC (outl (outr D.1)) Cn.1; let Ct := catC V.1; let R := compC q.1 Ct.1
    (R.1, Dp.2 && (un.2 && (U.2 && (q.2 && (D.2 && (W.2 && (Cn.2 && (V.2 && (Ct.2 && R.2)))))))))

/-- `perm`: `permC`'s relation. -/
def perm {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (permC X).1

/-- `setify : arr B ⟶ P B` on the arrays `X`, each array to the set of its elements (`setify`,
    AOP/A5_6_ListCombinators.lean:49, `Λ(inlist)`; B&dM §7.3 p.177): `Λ(∋)` total on `X`, and whether it ran
    within capacity: the bits of `memC`, `lamOnC`. -/
def setifyC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  let m := memC X; let l := lamOnC m.1 X
  (l.1, m.2 && l.2)

/-- `setify` on the arrays `X`: `setifyC`'s relation. -/
def setify {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (setifyC X).1

/-- `bagify : arr B ⟶ bag(B)` on the arrays `X` (`bagify`, AOP/A10_3_Tardy.lean:232, the quotient map of
    `perm`). A bag is the `arr` of its elements ascending in `Obj.sortBy`'s order, repeats kept: the one member
    of its `perm` class no type records. Each row's cells gathered contiguous (`expand` of the clamped counts),
    graded by value, then stably by row, so the rows keep their `lo`/`hi`. A per-row grade, not `sort`:
    `sort ≜ perm ordered` enumerates the permutations. Whether it ran within capacity: `rep_bagify`'s count bounds
    decided — the payload, the rows, and, out of `expand` in the pair, the copies' count `m` (the windows' counts
    summed, `len_expand_slicesOf`; `need` already bounds it by a `USize`); the picks' fits follow from those counts,
    so no helper twin is called. -/
def bagifyC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  let s := slicesOf X
  let hi := sums n s.2
  let e := expand n s.2 (fun _ => default) fun m i r _ _ =>
    let cells := Vals.pick B X.2.2.2 (add m (gather 8 s.1 i) r) m (len_val ..)
    let v := Obj.sortBy B cells (tilLongs m)
    let p := gather 8 v (Code.ofLongs (gather 8 i v)).grade
    ((longCount "bagify" p fun q hq => (⟨n, Vals.compact (.arr B) X,
      ⟨q, valCol Ew.sub Ew.vv hi s.2, longsN n hi (sums_le (len_slices ..).2), Vals.pick B cells p q hq⟩⟩ :
        Rel (.arr B) (.arr B))), decide (m.toNat < 2 ^ 63))
  (e.1, decide (X.1.toNat < 2 ^ 63) && decide (n.toNat < 2 ^ 63) && e.2)

/-- `bagify : arr B ⟶ bag(B)` on the arrays `X`: `bagifyC`'s relation. -/
def bagify {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (bagifyC X).1

/-- `ordered(Q)`, the coreflexive on the arrays `X` that are `Q`-ordered, each element `Q`-below every later
    one (`orderedP`, AOP/A5_6_ListCombinators.lean:162): the arrays with no non-empty suffix `y :: ys` and `z`
    of `ys` outside `y Q z`. `cons°` of the suffixes, the pairs `(y, z)`, those no pair of `Q` (`antiJoin`).
    `orderedOnC`'s bit is the `&&` of its pieces' and the test's. -/
def orderedOnC {B : Obj} {n : USize} (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  let S := suffixC X
  let W := ranC S.1
  let u := unconsC W.1.val
  let T := compC S.1 u.1
  let D := ranC T.1
  let V := ranC (outr D.1)
  let m := memC V.1.val
  let M := compC (outr D.1) m.1
  let yz := pairC (outl D.1) M.1
  let E := ranC yz.1
  let t := qC E.1
  let bad := antiJoinC yz.1 t.1
  let db := domC bad.1
  let C := compC T.1 db.1
  let dC := domC C.1
  let r := antiJoinC (idU X) dC.1
  (r.1, S.2 && W.2 && u.2 && T.2 && D.2 && V.2 && m.2 && M.2 && yz.2 && E.2 && t.2 && bad.2 && db.2 && C.2 &&
    dC.2 && r.2)

/-- `orderedOn q X`: `orderedOnC`'s relation at the test `q` with no bit of its own. -/
def orderedOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (orderedOnC (fun r => (q r, true)) X).1

/-- `ordered Q X` and whether it ran within capacity: `orderedOnC` at the test `pairsInC Q`. -/
def orderedC {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  orderedOnC (pairsInC Q) X

/-- `ordered(Q)`, `Q` closed: `orderedOn` at `pairsIn Q`, the test run on the pairs `(y, z)` it compares. -/
def ordered {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (orderedC Q X).1

/-- `sortSet Q Y` and whether it ran within capacity: the `&&` of `setifyC`'s, `orderedC`'s and `compC`'s bits. -/
def sortSetC {B : Obj} {n : USize} (Q : Rel B B) (Y : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  let s := setifyC Y
  let o := orderedC Q Y
  let c := compC (s.1)° o.1
  (c.1, s.2 && o.2 && c.2)

/-- `sort(Q) ≜ setify° ordered(Q) : P B ⟶ arr B` (`sortRel`, AOP/A8_3.lean:77; B&dM p.201, "sorting sets"):
    a set to its `Q`-ordered listings among the arrays `Y`. A relation into lists has no finite image without
    a universe (`[1, 1, 2]` lists `{1, 2}` under `≤`), so the lists range over `Y`, as `P`'s do. -/
def sortSet {B : Obj} {n : USize} (Q : Rel B B) (Y : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (sortSetC Q Y).1

/-- `subseq ≜ ⦇[nil, cons ∪ π₂]⦈` on the arrays `X`, each array to each of its subsequences (`subseq`,
    AOP/A5_6_ListCombinators.lean:127): a head kept or dropped. Whether it ran within capacity: `foldByC`'s, each
    round's the `&&` of `pairC`'s, `consC`'s and `unionC`'s. -/
def subseqC {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  foldByC X (nilVal B) fun el pend =>
    let p := pairC el pend; let c := consC p.1; let u := unionC c.1 pend
    (u.1, p.2 && c.2 && u.2)

/-- `subseq`: `subseqC`'s relation. -/
def subseq {B : Obj} {n : USize} (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (subseqC X).1

/-- `thinL Q X` and whether it ran within capacity: the `&&` of its pieces' twins' bits, `subseqC`'s first. With `Y`
    the subsequences (`ranC`), `S` their sets (`setifyC`), `T = (∋ / ∋) ∩ (∈ \ Q°∈)` on `S`, the result is
    `(setify Y ≫ T ≫ (setify Y)°) ∩ subseq X`. -/
def thinLC {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  let U := subseqC X; let W := ranC U.1; let s := setifyC W.1.val; let m := memC s.1.val
  let QS := compC (Q°) (m.1°)
  let Rd := rightDivC m.1 m.1 s.1.val s.1.val; let Ld := leftDivC (m.1°) QS.1 s.1.val s.1.val
  let T := interC Rd.1 Ld.1; let H := compC s.1 T.1; let G := compC H.1 (s.1°); let r := interC G.1 U.1
  (r.1, U.2 && W.2 && s.2 && m.2 && QS.2 && Rd.2 && Ld.2 && T.2 && H.2 && G.2 && r.2)

/-- `thinL(Q) ≜ setify thin(Q) setify° ∩ subseq` on the arrays `X` (`thinL`, AOP/A8_3.lean:567; B&dM p.200,
    binary thinning), `thin(Q) ≜ ⊇ ∩ (∈ \ Q°∈)` on the sets of `Y`, the subsequences of `X` (`thinRel`,
    AOP/A8_1.lean:71); `thinL ⊑ subseq`, so `Y` holds every target. `⊇` is `∋ / ∋`. -/
def thinL {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) := (thinLC Q X).1

/-- Binary thinning in one pass, the note's implementation of `thinL(Q)` (`bumpFold_le_thinL`,
    AOP/A8_3.lean:629, `⦇[τ, bump(Q)]⦈ ⊑ thinL(Q)`): each element `a` bumped into the thinned rest `ys` —
    `[a]` when `ys` is empty, else with `b` its head `a` replaces `b` when `a Q b`, `b` stays alone when `b Q a`,
    both stay when neither (`bumpRel_cons`, AOP/A8_3.lean:381). `Q` is the test `q` on the pairs `(a, b)` each
    round meets, so `Q` needs no universe; `thinL Q` is the specification it refines. -/
-- `thinLOnC`'s round body on the coreflexive `D` of the round's pairs `(a, ys)`, `q` a twin family: every op by its
-- twin, `swapIn q (ran ab)` as `swapInC q`; the bit the `&&` of every twin's and of `q`'s call
def thinBodyC {B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (D : Rel (.prod B (.arr B)) (.prod B (.arr B))) : Rel (.prod B (.arr B)) (.arr B) × Bool :=
  let a := outl D; let ys := outr D
  let un := unconsC ys.val; let u := compC ys un.1; let ab := pairC a (outl u.1); let rab := ranC ab.1
  let G1 := q rab.1; let q1 := compC ab.1 G1.1; let up := domC q1.1
  let sw := swapInC q rab.1; let q3 := compC ab.1 sw.1; let down := domC q3.1
  let du := domC u.1; let l1 := diffC D du.1; let l2 := diffC du.1 up.1; let l3 := diffC l2.1 down.1
  let lone := unionC l1.1 l3.1; let c1 := consC lone.1
  let ua := compC up.1 a; let uu := compC up.1 u.1; let ru := ranC u.1; let ut := compC uu.1 (outr ru.1)
  let pu := pairC ua.1 ut.1; let c2 := consC pu.1; let dy := compC down.1 ys
  let b1 := unionC c1.1 c2.1; let body := unionC b1.1 dy.1
  (body.1, un.2 && (u.2 && (ab.2 && (rab.2 && (G1.2 && (q1.2 && (up.2 &&
    (sw.2 && (q3.2 && (down.2 && (du.2 && (l1.2 && (l2.2 && (l3.2 && (lone.2 && (c1.2 && (ua.2 && (uu.2 &&
    (ru.2 && (ut.2 && (pu.2 && (c2.2 && (dy.2 && (b1.2 && body.2))))))))))))))))))))))))

/-- `thinLOn` and whether it ran within capacity: `foldOnC` at `thinBodyC q`, `q` a twin family. -/
def thinLOnC {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) × Bool :=
  foldOnC (nilVal B) (thinBodyC q) X

/-- `thinLOn`: `thinLOnC`'s relation, the test one with no bit of its own. -/
def thinLOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) : Rel (.arr B) (.arr B) :=
  (thinLOnC (fun D => (q D, true)) X).1

/-- `merge(Q) : arr B × arr B ⟶ arr B` on the rows of `P` (`merge`, AOP/A8_3.lean:1147; B&dM p.156): the
    book's equations as rounds of `iter` on the states `((x, y), acc)`, `acc` the output so far: with both
    non-empty the head `a` of `x` goes to `acc` when `a Q b`, `b` the head of `y`, else `b`; with either empty
    the state ends as `acc` then `x` then `y`. A round shortens `x` or `y`, so the cells of both payloads
    plus one bound the rounds. A round on `(out, St)` answers `(out ∪ St flushed, St stepped)` and its bit, the
    `&&` of its twins' bits and the test's. -/
def mergeRound {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (st : Rel K (.arr B) × Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B))) :
    (Rel K (.arr B) × Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B))) × Bool :=
  let D := ranC st.2
  let x := outl (outl D.1)
  let y := outr (outl D.1)
  let acc := outr D.1
  let cx := unconsC x.val
  let ux := compC x cx.1
  let cy := unconsC y.val
  let uy := compC y cy.1
  let pu := pairC ux.1 uy.1
  let both := domC pu.1
  let h := pairC (outl ux.1) (outl uy.1)
  let rh := ranC h.1
  let G := q rh.1
  let hq := compC h.1 G.1
  let l := domC hq.1
  let A1 := pairC (outr ux.1) y
  let S1 := pairC acc (outl ux.1)
  let N1 := snocC S1.1
  let P1 := pairC A1.1 N1.1
  let L1 := compC l.1 P1.1
  let nb := antiJoinC both.1 l.1
  let A2 := pairC x (outr uy.1)
  let S2 := pairC acc (outl uy.1)
  let N2 := snocC S2.1
  let P2 := pairC A2.1 N2.1
  let L2 := compC nb.1 P2.1
  let tk := unionC L1.1 L2.1
  let T := compC st.2 tk.1
  let fl := antiJoinC D.1 both.1
  let Sf := compC st.2 fl.1
  let c1 := pairC acc x
  let C1 := catC c1.1
  let c2 := pairC C1.1 y
  let C2 := catC c2.1
  let O := compC Sf.1 C2.1
  let U := unionC st.1 O.1
  ((U.1, T.1), D.2 && cx.2 && ux.2 && cy.2 && uy.2 && pu.2 && both.2 && h.2 && rh.2 && G.2 && hq.2 && l.2 &&
    A1.2 && S1.2 && N1.2 && P1.2 && L1.2 && nb.2 && A2.2 && S2.2 && N2.2 && P2.2 && L2.2 && tk.2 && T.2 && fl.2 &&
    Sf.2 && c1.2 && C1.2 && c2.2 && C2.2 && O.2 && U.2)

/-- `mergeOn`'s first state, each pair of `P` beside the empty `acc`, and its bit: `ranC`'s, `topC`'s, `pairC`'s,
    `compC`'s. -/
def mergeInitC {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) :
    Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B)) × Bool :=
  let R := ranC P
  let T := topC R.1.val (nilVal B)
  let Q := pairC (idU R.1.val) T.1
  let I := compC P Q.1
  (I.1, R.2 && T.2 && Q.2 && I.2)

/-- `mergeOn` on a test answering a bit, and whether it ran within capacity: the first state's bit `&&` the bits
    of the rounds it ran (`iterC`). -/
def mergeOnC {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) × Bool :=
  let I := mergeInitC P
  let r := iterC (P.val.1.1.toNat + P.val.2.1.toNat + 1) (fun s => s.2.n == 0) (mergeRound q) (zero, I.1)
  (r.1.1, I.2 && r.2)

/-- `mergeOn`: `mergeOnC`'s relation, the test one with no bit of its own. -/
def mergeOn {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) :=
  (mergeOnC (fun D => (q D, true)) P).1

/-- `merge(Q)`, `Q` closed, and whether it ran within capacity: `mergeOnC` at `pairsIn Q` run as `compC`, the
    test run on the pairs of heads it compares. -/
def mergeC {K B : Obj} (Q : Rel B B) (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) × Bool :=
  mergeOnC (fun D => compC D (idU (Q.key, Q.val))) P

/-- `merge(Q)`: `mergeC`'s relation. -/
def merge {K B : Obj} (Q : Rel B B) (P : Rel K (.prod (.arr B) (.arr B))) : Rel K (.arr B) := (mergeC Q P).1

/-- `loop(F) : X × arr Y ⟶ X` on the rows of `P` (`loop`, AOP/A9_3_Bracket.lean:1686; B&dM Appendix), `F`
    folded along the array from the left, in demand form as `foldOn`'s step: rounds of `iter` taking
    `(c, y :: ys)` to `(c', ys)` with `(c, y) F(D) c'`, `D` the coreflexive on the pairs `(c, y)` the round
    meets, so a state with no universe loops too; a state whose array is empty ends at its `c`. The states
    are `nub`bed each round, as `foldBy`'s, or a value reached along two paths doubles its rows each round
    after. The cells of the arrays' payload plus one bound the rounds. -/
def loopRound {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X × Bool)
    (st : Rel K X × Rel K (.prod X (.arr Y))) : (Rel K X × Rel K (.prod X (.arr Y))) × Bool :=
  let D := ranC st.2
  let W := ranC (outr D.1)
  -- `uncons` on the distinct arrays: on `(outr D).val`, an array held by `k` states gives each of them `k`
  -- rows, and `pair` below `k²`, so a round's rows grow as the states sharing a suffix, not as the states
  let c := unconsC W.1.val
  let u := compC (outr D.1) c.1
  let p := pairC (outl D.1) (outl u.1)
  let G := F (ran p.1)
  let Q := compC p.1 G.1
  let R := pairC Q.1 (outr u.1)
  let T := compC st.2 R.1
  let N := nubC T.1
  let du := domC u.1
  let A := antiJoinC D.1 du.1
  let O := compC st.2 (outl A.1)
  let U := unionC st.1 O.1
  ((U.1, N.1), D.2 && W.2 && c.2 && u.2 && p.2 && G.2 && Q.2 && R.2 && T.2 && N.2 && du.2 && A.2 && O.2 && U.2)

/-- `loopOn` on a step answering a bit, and whether it ran within capacity: the `&&` of the bits of the rounds it
    ran (`iterC`), each round's the step's and its primitives' (`loopRound`). -/
def loopOnC {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X × Bool)
    (P : Rel K (.prod X (.arr Y))) : Rel K X × Bool :=
  let r := iterC (P.val.2.1.toNat + 1) (fun s => s.2.n == 0) (loopRound F) (zero, P); (r.1.1, r.2)

/-- `loopOn`: `loopOnC`'s relation, the step one with no bit of its own. -/
def loopOn {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) :
    Rel K X :=
  (loopOnC (fun D => (F D, true)) P).1

/-- `loop(F)` with `F` one relation, and whether it ran within capacity: `loopOnC` with `F` whatever pairs a round
    meets, a relation with no bit of its own. -/
def loopC {K X Y : Obj} (F : Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) : Rel K X × Bool :=
  loopOnC (fun _ => (F, true)) P

/-- `loop(F)`: `loopC`'s relation. -/
def loop {K X Y : Obj} (F : Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) : Rel K X := (loopC F P).1

/-- `tic ≜ cons inits tail : B × arr B ⟶ arr (arr B)` on the rows of `P` (`tic`, AOP/A9_3_Bracket.lean:1845;
    B&dM p.235): the non-empty prefixes of `a :: xs`, on the twins of its pieces, the bit the `&&` of theirs. -/
def ticC {K B : Obj} (P : Rel K (.prod B (.arr B))) : Rel K (.arr (.arr B)) × Bool :=
  let C := consC P
  let N := initsC C.1.val
  let I := compC C.1 N.1
  let T := tailC I.1.val
  let r := compC I.1 T.1
  (r.1, C.2 && N.2 && I.2 && T.2 && r.2)

/-- `tic`: `ticC`'s relation. -/
def tic {K B : Obj} (P : Rel K (.prod B (.arr B))) : Rel K (.arr (.arr B)) := (ticC P).1

namespace Arr

/-- `union : arr (arr A) ⟶ arr A` on the arrays of arrays `X`, the note's `union≜frac(∋∋,∋)`
    (diag/aop/07-optimisation.typ:718; `union ≜ Λ(∋∋)`, AOP/A5_4.lean:337): `Λ(∋∋)` total on `X`. Named
    `Arr.union` because `union` is `∪`'s, which a program must not name. `E(∋)` on `X`, `∋` on the payload; whether
    it ran within capacity: the bits of `memC` there and of `EC`. -/
def unionC {A : Obj} {n : USize} (X : Vals (.arr (.arr A)) n) : Rel (.arr (.arr A)) (.arr A) × Bool :=
  let m := memC X.2.2.2; let e := EC m.1 X
  (e.1, m.2 && e.2)

/-- `union` on the arrays of arrays `X`: `unionC`'s relation. -/
def union {A : Obj} {n : USize} (X : Vals (.arr (.arr A)) n) : Rel (.arr (.arr A)) (.arr A) := (unionC X).1

/-- `sum ≜ ⦇[zero, plus]⦈` on the arrays of longs `X` (`sum`, AOP/A5_6_ListCombinators.lean:323), each round's
    `plus` on the pairs it meets. Named `Arr.sum` because `sum` is `R + S`'s. -/
def sumC {n : USize} (X : Vals (.arr (.atom .long)) n) : Rel (.arr (.atom .long)) (.atom .long) × Bool :=
  foldOnC (col [0]) (fun D => (plus D.val, true)) X

/-- `sum`: `sumC`'s relation; `plus` has no capacity of its own, so the bit is `foldOnC`'s. -/
def sum {n : USize} (X : Vals (.arr (.atom .long)) n) : Rel (.arr (.atom .long)) (.atom .long) := (sumC X).1

end Arr

/-- `Entire R` on the universe `U`: `𝟙 ⊑ R R°`, written `𝟙 ⊑ dom R` since `dom R = 𝟙 ∩ R R°`, and whether it ran
    within capacity: `domC`'s bit `&&` `leC`'s. -/
def entireC {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Bool × Bool :=
  let d := domC R; let l := leC (idU U) d.1; (l.1, d.2 && l.2)

/-- `Entire R` on `U`: `entireC`'s answer. -/
def entire {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Bool := (entireC R U).1

/-- `Simple R`, `R° R ⊑ 𝟙`: in `R` with each pair once, every key distinct (`groupIds` count of the key codes),
    linear where `R° ≫ R` is a join quadratic in a key's values; and whether it ran within capacity: `nubC`'s bit
    `&&` the key codes'. -/
def simpleC {A B : Obj} (R : Rel A B) : Bool × Bool :=
  let r := nubC R
  let c := A.codesC #v[⟨_, r.1.key⟩]
  (len c.1[0].groupIds.2 == r.1.n.toNat, r.2 && c.2)

/-- `Simple R`: `simpleC`'s answer. -/
def simple {A B : Obj} (R : Rel A B) : Bool := (simpleC R).1

/-- `R` a map on `U`, entire and simple, and whether it ran within capacity: the `&&` of `entireC`'s and `simpleC`'s
    bits. -/
def isMapC {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Bool × Bool :=
  let e := entireC R U; let s := simpleC R; (e.1 && s.1, e.2 && s.2)

/-- `R` a map on `U`: `isMapC`'s answer. -/
def isMap {A B : Obj} {m : USize} (R : Rel A B) (U : Vals A m) : Bool := (isMapC R U).1

/-- `Injective R` = `Simple R°`, and whether it ran within capacity: `simpleC`'s at `R°`. -/
def injectiveC {A B : Obj} (R : Rel A B) : Bool × Bool := simpleC R°

/-- `Injective R`: `injectiveC`'s answer. -/
def injective {A B : Obj} (R : Rel A B) : Bool := (injectiveC R).1

/-- `Surjective R` = `Entire R°` on the universe `U` of `b`, and whether it ran within capacity: `entireC`'s at
    `R°`. -/
def surjectiveC {A B : Obj} {m : USize} (R : Rel A B) (U : Vals B m) : Bool × Bool := entireC R° U

/-- `Surjective R` on `U`: `surjectiveC`'s answer. -/
def surjective {A B : Obj} {m : USize} (R : Rel A B) (U : Vals B m) : Bool := (surjectiveC R U).1

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
