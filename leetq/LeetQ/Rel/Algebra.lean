/-
  The relation algebra of the RelRep design §2.3 on the core: every operator a pipeline of qlean
  kernels over a `Rel`'s two payloads, never a loop over `Arr.get`, `Column.get` or `Column.atoms`.
  A payload stays in whatever encoding carries it — `bytes`, `foR`, `alp`, `bits`, `syms`, `enum`, or
  a general list — because the three steps that touch one take every encoding: `razeColumn` joins
  them, `findColumn`'s `x?x` codes them, `gatherColumn` picks rows of them. Elements are compared
  through joint CODES — each element's first position in the join of every payload taking part — so
  two columns of one type become comparable longs, and a pair of codes is one long by `rankPair`.
  The spec of each operator is the List-level relation on `toList`; `#guard`s below hold each one
  on small literal relations, and the laws that the kernels' Lean bodies make reachable are proved.
-/
import LeetQ.Rel.Find
import LeetQ.Rel.Ew
import QLean.Kernel.Sort
import QLean.Kernel.Structural
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise
import QLean.Kernel.Coc
import QLean.Eval.Dyad

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel
open LeetQ.Rel.Find (expand one)

/-! ## Long payloads: the index, code and count columns every step passes along -/

/-- Elements of a long payload. -/
def len (b : ByteArray) : Nat := b.size / 8

def nul : Int64 := Int64.minValue

def add (a b : ByteArray) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul a b (len a).toUSize
def sub (a b : ByteArray) : ByteArray := Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul a b (len a).toUSize
def mulc (a : ByteArray) (x : Nat) : ByteArray := Kernel.Ew.val Ew.mul Ew.i64 Ew.va nul a (one x.toUInt64) (len a).toUSize
def sums (b : ByteArray) : ByteArray := Scan.scan .sums .i64 (len b).toUSize b
/-- `src@idx` at element width `w`; a miss reads `0`. -/
def gather (w : Nat) (src idx : ByteArray) : ByteArray := gatherBytes w.toUSize 0 src idx
/-- The positions where `a` equals `b` elementwise. -/
def whereEqV (a b : ByteArray) : ByteArray :=
  whereBits (len a).toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv a b (len a).toUSize)
/-- The positions where `a` equals the long `x`. -/
def whereEq (a : ByteArray) (x : Int64) : ByteArray :=
  whereBits (len a).toUSize (Ew.cmp Ew.eq Ew.i64 Ew.va a (one x.toUInt64) (len a).toUSize)
/-- The first `n` longs and the rest. -/
def split (b : ByteArray) (n : Nat) : ByteArray × ByteArray := (b.extract 0 (8 * n), b.extract (8 * n) b.size)

/-- The elementwise class of a sort layout. -/
def cls : Scan.Kind → UInt8
  | .bit => Ew.bits | .u8 | .c8 => Ew.u8 | .i16 => Ew.i16 | .i32 => Ew.i32 | .i64 => Ew.i64
  | .f32 => Ew.f32 | .f64 => Ew.f64

def isFloat : Scan.Kind → Bool | .f32 | .f64 => true | _ => false

/-! ## Payloads of any encoding: count, pick, join, code -/

/-- Elements in a payload. -/
def count : (t : Ty) → Pay t → Nat
  | .atom a, c => Column.count a c
  | .gen, xs => xs.size

/-- `x@i` for an in-range long payload `i`: `gatherColumn`, which answers every column encoding. A
    general list is picked by position, which is all qlean's own `@` does there (`pickAt`, private). -/
def pick : (t : Ty) → Pay t → ByteArray → Except String (Pay t)
  | .atom a, c, i => match gatherColumn a c (.bytes i) with
    | some (.vector _ out) => pure out
    | _ => throw s!"gatherColumn declines a column of type {a.code} in this encoding"
  | .gen, xs, i => pure ((longRows i).map fun p => xs[p]?.getD (.list #[]))

/-- `raze` of payloads of one type: `razeColumn`, which interns a symbol part to meet an interned one
    and decodes an encoded part to meet a dense one. A general list is `Array.append`. -/
def raze : (t : Ty) → Array (Pay t) → Except String (Pay t)
  | .atom a, cs => if h : cs.size = 1 then pure cs[0] else match razeColumn a cs with
    | some (.vector _ out) => pure out
    | _ => throw s!"razeColumn declines {cs.size} columns of type {a.code}"
  | .gen, cs => pure (cs.foldl (· ++ ·) #[])

/-- No element of `t`: `Column.ofAtoms` of nothing, which picks the type's own constructor. -/
def empty : (t : Ty) → Except String (Pay t)
  | .atom a => match Column.ofAtoms a #[] with
    | some c => pure c
    | none => throw s!"Column.ofAtoms has no empty column of type {a.code}"
  | .gen => pure #[]

/-- Joint codes: equal elements of any of `cols` get one long, below the total length — each
    element's first position in the join, `x?x` (`findColumn`) of the `raze`. A general list is
    matched by identity, `Eval.itemPos`, qlean's own `?` on one. -/
def codes : (t : Ty) → Array (Pay t) → Except String ByteArray
  | .atom a, cs => do
    let all ← raze (.atom a) cs
    match findColumn a false all (.vector a all) with
    | some (.vector .long c) => match Column.bytesOf .long c with
      | some b => pure b
      | none => throw "findColumn answered positions whose payload does not decode"
    | _ => throw s!"findColumn declines x?x on a column of type {a.code} in this encoding"
  | .gen, cs => do
    let all ← raze .gen cs
    pure (all.foldl (init := .empty) fun b y => Column.pushBits b (Eval.itemPos all y).toUInt64 8)

/-- The dense payload an ARITHMETIC kernel (`Ew`, `overGroups`, `grade` by value) reads, at its sort
    layout: a boolean's bits, any other ordered type's `Column.bytesOf` (an encoded one decoded once).
    A symbol, guid or general list has no such payload; equality steps never come here (`codes`). -/
def arrDense {a : QAtomicType} {n : Nat} (x : Arr (.atom a) n) : Except String (Scan.Kind × ByteArray) := do
  let some k := orderKind a | throw s!"type {a.code} has no sort layout: no arithmetic kernel reads it"
  match (x.c : Column) with
  | .bits _ b => pure (k, b)
  | c => match Column.bytesOf a c with
    | some b => pure (k, b)
    | none => throw s!"type {a.code}: Column.bytesOf has no dense payload for this encoding"

/-- A key column's payload: `til` is `tilLongs`, `grp d o` picks `d` at `groupOf o`. -/
def keyPay : {k : Ty} → {n : Nat} → KeyCol k n → Except String (Pay k)
  | _, _, .til n => pure (.bytes (tilLongs n.toUSize))
  | k, n, .grp d o _ => do
    let some ob := Column.bytesOf .long o.c | throw "a grp key's offsets have no dense payload"
    pick k (← keyPay d) (groupOf ob n)
  | _, _, .arr a => pure a.c

/-- A relation's two payloads. -/
structure Cols (k v : Ty) where
  n : Nat
  key : Pay k
  val : Pay v

def cols {k v : Ty} (R : Rel k v) : Except String (Cols k v) := do pure ⟨R.n, ← keyPay R.key, R.val.c⟩

/-- The rows of `d` at the index column `i`. -/
def Cols.rows {k v : Ty} (d : Cols k v) (i : ByteArray) : Except String (Cols k v) := do
  pure ⟨len i, ← pick k d.key i, ← pick v d.val i⟩

/-- Two payloads as a relation keyed by an explicit column. -/
def ofCols (k v : Ty) (kc : Pay k) (vc : Pay v) : Except String (Rel k v) := do
  let n := count k kc
  pure ⟨n, .arr (← Arr.of k n kc "ofCols"), ← Arr.of v n vc "ofCols"⟩

/-! ## The composite steps, named once -/

/-- `rankPair`: two code columns of one length as one code column, `p·N + q` regrouped, where
    every code of `q` is below `N` (so `p·N + q` is injective while `N² < 2⁶³`). qlean's
    `Ew.rankPair` is the rank of two SYMBOL dictionaries, not this; this is `Ew.val` + `groupIds`. -/
def rankPair (p q : ByteArray) (N : Nat) : ByteArray :=
  (Order.groupIds .i64 (len q).toUSize (add (mulc p N) q)).1

/-- `|R|` of tuples: the codes of each column (`codes`, any encoding), folded left by `rankPair`. -/
def tupleCodes (cs : Array ByteArray) : ByteArray :=
  if h : 0 < cs.size then cs.foldl (init := cs[0]) (start := 1) fun acc c => rankPair acc c (len c) else .empty

/-- `|R|` of several relations of one type in one code space, concatenated in order. -/
def pairs {k v : Ty} (ds : Array (Cols k v)) : Except String ByteArray := do
  pure (tupleCodes #[← codes k (ds.map (·.key)), ← codes v (ds.map (·.val))])

/-- `R` with each pair once: the first row of each class of `|R|`. -/
def Cols.nub {k v : Ty} (d : Cols k v) : Except String (Cols k v) := do
  d.rows (Order.groupIds .i64 d.n.toUSize (← pairs #[d])).2

/-- `join(l, r)`: every pair of a left and a right row with equal codes, as two index columns —
    `groupIds`/`groupSizes`/`grade` of the right, `findVec` of the left in its distinct codes,
    `expand` of the matched counts, `gatherBytes` into the grouped right rows. Size `j` = matches. -/
def join (l r : ByteArray) : ByteArray × ByteArray :=
  let (gid, firsts) := Order.groupIds .i64 (len r).toUSize r
  let sizes := Order.groupSizes (len firsts).toUSize gid
  let hit := findVec 8 false (gather 8 r firsts) l
  let (li, w) := expand (gather 8 sizes hit)
  let starts := sub (sums sizes) sizes
  (li, gather 8 (Order.grade .i64 false (len r).toUSize gid) (add (gather 8 starts (gather 8 hit li)) w))

/-- `cnt(c)`: count by `c` — its distinct codes and how many rows hold each. -/
def cnt (c : ByteArray) : ByteArray × ByteArray :=
  let (gid, firsts) := Order.groupIds .i64 (len c).toUSize c
  (gather 8 c firsts, Order.groupSizes (len firsts).toUSize gid)

/-- `at(cnt(c), k)`: the count of each row's `k`, `0` where `k` does not occur. -/
def atCnt (cs : ByteArray × ByteArray) (k : ByteArray) : ByteArray := gather 8 cs.2 (findVec 8 false cs.1 k)

/-- `cross(n, m)`: every pair of `n` left and `m` right rows as two index columns, `p div m` and
    `p mod m` over `til (n·m)` (`Ew.val` in place of the row's `expandBytes`/`cycleIds`). -/
def cross (n m : Nat) : ByteArray × ByteArray :=
  let p := tilLongs (n * m).toUSize
  ( Kernel.Ew.val Ew.idiv Ew.i64 Ew.va nul p (one m.toUInt64) (n * m).toUSize
  , Kernel.Ew.val Ew.imod Ew.i64 Ew.va nul p (one m.toUInt64) (n * m).toUSize)

/-- `anti(x, y)`: the positions of `x` whose code is not in `y` — `memberVec`, `Ew.notBits`, `whereBits`. -/
def anti (x y : ByteArray) : ByteArray := whereBits (len x).toUSize (Ew.notBits (len x) (memberVec 8 false x y))

/-- Dense rank of a payload in value order: `binBytes` into its sorted distinct values. -/
def drank (k : Scan.Kind) (b : ByteArray) : ByteArray :=
  let n := (b.size / k.width).toUSize
  let d := Order.distinct k n b
  binBytes k.width.toUSize (isFloat k) true false (Order.sortValues k false (d.size / k.width).toUSize d) b

/-! ## The operators -/

variable {A B C : Ty}

/-- `R ⊑ S`: `memberVec` of `|R|` in `|S|`, all set. -/
def le (R S : Rel A B) : Except String Bool := do
  let r ← cols R; let s ← cols S
  let (pr, ps) := split (← pairs #[r, s]) r.n
  pure (len (whereBits r.n.toUSize (memberVec 8 false pr ps)) == r.n)

/-- `R ∩ S`: the semi-join on pairs — `memberVec`, `whereBits`, `gatherColumn`. -/
def inter (R S : Rel A B) : Except String (Rel A B) := do
  let r ← cols R; let s ← cols S
  let (pr, ps) := split (← pairs #[r, s]) r.n
  let t ← r.rows (whereBits r.n.toUSize (memberVec 8 false pr ps))
  ofCols A B t.key t.val

/-- `R ∪ S`: `razeColumn` of keys and of vals, the first row of each pair. -/
def union (R S : Rel A B) : Except String (Rel A B) := do
  let r ← cols R; let s ← cols S
  let u ← (Cols.mk (r.n + s.n) (← raze A #[r.key, s.key]) (← raze B #[r.val, s.val])).nub
  ofCols A B u.key u.val

/-- `𝟘`: no pair. -/
def zero : Except String (Rel A B) := do ofCols A B (← empty A) (← empty B)

/-- `⊤` on the universes `Ua`, `Ub`: `cross`. -/
def top {ma mb : Nat} (Ua : Arr A ma) (Ub : Arr B mb) : Except String (Rel A B) := do
  let (i, j) := cross ma mb
  ofCols A B (← pick A Ua.c i) (← pick B Ub.c j)

/-- `𝟙` on `U`: key and val the one column, shared. -/
def idU {t : Ty} {m : Nat} (U : Arr t m) : Rel t t := ⟨m, .arr U, U⟩

theorem idU_holds {t : Ty} {m : Nat} (U : Arr t m) (x y : El t) :
    (idU U).Holds x y ↔ x = y ∧ ∃ i, U.get i = x := by
  simp only [Rel.Holds, idU, KeyCol.get]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨h1 ▸ h2, i, h1⟩, fun ⟨h, i, h1⟩ => ⟨i, h1, h ▸ h1⟩⟩

/-- `R°` of an `arr`-keyed relation: the two fields swap, nothing runs. -/
def convArr {k v : Ty} {n : Nat} (key : Arr k n) (val : Arr v n) : Rel v k := ⟨n, .arr val, key⟩

theorem convArr_holds {k v : Ty} {n : Nat} (key : Arr k n) (val : Arr v n) (x : El k) (y : El v) :
    (convArr key val).Holds y x ↔ (⟨n, .arr key, val⟩ : Rel k v).Holds x y := by
  simp only [Rel.Holds, convArr, KeyCol.get]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

/-- `R°`: a `til`/`grp` key is written only here (`keyPay`); an `arr` key moves. -/
def conv (R : Rel A B) : Except String (Rel B A) :=
  match R with
  | ⟨_, .arr k, v⟩ => pure (convArr k v)
  | R => do let r ← cols R; ofCols B A r.val r.key

/-- `R ≫ S`: `join` on `R.val = S.key`, the key picked from `R`, the val from `S`. -/
def comp (R : Rel A B) (S : Rel B C) : Except String (Rel A C) := do
  let r ← cols R; let s ← cols S
  let (rc, sc) := split (← codes B #[r.val, s.key]) r.n
  let (i, j) := join rc sc
  ofCols A C (← pick A r.key i) (← pick C s.val j)

/-- The coreflexive on the distinct elements of `x`: the first row of each code. -/
def distinctCorefl (t : Ty) (n : Nat) (x : Pay t) : Except String (Rel t t) := do
  let d ← pick t x (Order.groupIds .i64 n.toUSize (← codes t #[x])).2
  ofCols t t d d

/-- `dom R`: the coreflexive on the distinct keys. -/
def dom (R : Rel A B) : Except String (Rel A A) := do let r ← cols R; distinctCorefl A r.n r.key

/-- `ran R`: the coreflexive on the distinct vals. -/
def ran (R : Rel A B) : Except String (Rel B B) := do let r ← cols R; distinctCorefl B r.n r.val

/-- `p?` on `U`, `p x ↔ x op e` for one of `Ew`'s six comparisons: `Ew.cmp`, `whereBits`, `gatherColumn`.
    The comparison is arithmetic, so `U` is an ordered type (`arrDense`). -/
def corefl {a : QAtomicType} {m : Nat} (U : Arr (.atom a) m) (op : UInt8) (e : UInt64) : Except String (Rel (.atom a) (.atom a)) := do
  let (k, u) ← arrDense U
  let d ← pick (.atom a) U.c (whereBits m.toUSize (Ew.cmp op (cls k) Ew.va u (Column.pushBits .empty e k.width) m.toUSize))
  ofCols _ _ d d

/-- `Coreflexive R`, `R ⊑ 𝟙`: every key's code equals its val's. -/
def isCorefl (R : Rel A A) : Except String Bool := do
  let r ← cols R
  let (kc, vc) := split (← codes A #[r.key, r.val]) r.n
  pure (len (whereEqV kc vc) == r.n)

/-- `R \ S` (`R : a ⟶ b`, `S : a ⟶ c`), by counting: `join` on the shared key → rows `(y, z)`;
    `cnt(y, z)` against `cnt(R.val)` `at` `y`; the vacuous `y ∉ ran R` with every `z` from the
    universes `Ub`, `Uc`: `cross(anti(Ub, ran R), Uc)`. -/
def leftDiv {mb mc : Nat} (R : Rel A B) (S : Rel A C) (Ub : Arr B mb) (Uc : Arr C mc) : Except String (Rel B C) := do
  let r ← (← cols R).nub; let s ← (← cols S).nub
  let (rk, sk) := split (← codes A #[r.key, s.key]) r.n
  let (i, j) := join rk sk
  let y ← pick B r.val i; let z ← pick C s.val j
  let (yc, rest) := split (← codes B #[y, r.val, Ub.c]) (len i)
  let (rvc, ubc) := split rest r.n
  let zc ← codes C #[z]
  let (gid, firsts) := Order.groupIds .i64 (len i).toUSize (rankPair yc zc (len zc))
  let got := Order.groupSizes (len firsts).toUSize gid
  let keep := gather 8 firsts (whereEqV got (atCnt (cnt rvc) (gather 8 yc firsts)))
  let miss := anti ubc rvc
  let (p, q) := cross (len miss) mc
  ofCols B C (← raze B #[← pick B y keep, ← pick B Ub.c (gather 8 miss p)])
    (← raze C #[← pick C z keep, ← pick C Uc.c q])

/-- `R / S = (S° \ R°)°` (`R : a ⟶ c`, `S : b ⟶ c`); its vacuous term is `cross(Ua, anti(Ub, dom S))`. -/
def rightDiv {ma mb : Nat} (R : Rel A C) (S : Rel B C) (Ua : Arr A ma) (Ub : Arr B mb) : Except String (Rel A B) := do
  conv (← leftDiv (← conv S) (← conv R) Ub Ua)

/-- `R /ₛ S` (`R : a ⟶ c`, `S : b ⟶ c`), equal fibres by counting: `join` on `z` → `(x, y)`;
    `cnt(x, y)` equal to both `cnt(R.key)` `at` `x` and `cnt(S.key)` `at` `y`; the vacuous term
    `cross(anti(Ua, dom R), anti(Ub, dom S))`, the empty fibres. -/
def symDiv {ma mb : Nat} (R : Rel A C) (S : Rel B C) (Ua : Arr A ma) (Ub : Arr B mb) : Except String (Rel A B) := do
  let r ← (← cols R).nub; let s ← (← cols S).nub
  let (rv, sv) := split (← codes C #[r.val, s.val]) r.n
  let (i, j) := join rv sv
  let x ← pick A r.key i; let y ← pick B s.key j
  let xa ← codes A #[x, r.key, Ua.c]; let ya ← codes B #[y, s.key, Ub.c]
  let (xc, xr) := split xa (len i); let (rkc, uac) := split xr r.n
  let (yc, yr) := split ya (len j); let (skc, ubc) := split yr s.n
  let (gid, firsts) := Order.groupIds .i64 (len i).toUSize (rankPair xc yc (len ya))
  let got := Order.groupSizes (len firsts).toUSize gid
  let nx := atCnt (cnt rkc) (gather 8 xc firsts); let ny := atCnt (cnt skc) (gather 8 yc firsts)
  let keep := gather 8 firsts (whereEq (add (sub nx got) (sub ny got)) 0)
  let ex := anti uac rkc; let ey := anti ubc skc
  let (p, q) := cross (len ex) (len ey)
  ofCols A B (← raze A #[← pick A x keep, ← pick A Ua.c (gather 8 ex p)])
    (← raze B #[← pick B y keep, ← pick B Ub.c (gather 8 ey q)])

/-- `grp (arr ds) o` over `val`: the keys `ds` of the groups and the offsets `o` a kernel wrote (`runStarts`,
    which ends with the count), the cuts decided by `KeyCol.grp?`. -/
def grouped {v : Ty} {n : Nat} (t : Ty) (ds : Pay t) (o : ByteArray) (val : Arr v n) : Except String (Rel t v) := do
  let g := count t ds
  let some key := KeyCol.grp? (.arr (← Arr.of t g ds "grouped")) (← Arr.of (.atom .long) (g + 1) (.bytes o) "grouped") n
    | throw s!"grp: the offsets are not ascending cuts of {n} rows"
  pure ⟨n, key, val⟩

/-- The groups of a column whose equal elements are contiguous: `grp (arr ds) o` with `o` the run starts
    of its codes and the count (`runStarts`) and `ds` the element at each start. -/
def runs {v : Ty} {n : Nat} (t : Ty) (key : Pay t) (val : Arr v n) : Except String (Rel t v) := do
  let st := runStarts 8 false (← codes t #[key])
  grouped t (← pick t key (st.extract 0 (st.size - 8))) st val

/-- A family stored as its pairs `(X, x)` sorted key-major, each pair once: the set `X` IS the
    contiguous run of its key, so the key is `grp (arr ds) o` (`runs`). `Order.grade` on the
    key-major `kc·N + vc`, `gatherColumn`. -/
def family (d : Cols A B) : Except String (Rel A B) := do
  let d ← d.nub
  let vc ← codes B #[d.val]
  let s ← d.rows (Order.grade .i64 false d.n.toUSize (add (mulc (← codes A #[d.key]) (len vc)) vc))
  runs A s.key (← Arr.of B s.n s.val "family")

/-- `Λ(R)`: `x Λ(R) X ↔ X = {z | x R z}` — the family of `R`'s fibres, one segment per `x ∈ dom R`. -/
def transpose (R : Rel A B) : Except String (Rel A B) := do family (← cols R)

/-- q's `=x` of a list: each distinct value against the positions holding it — `Order.group`'s flattened
    indices of the codes as `val`, the key `grp (arr ds) o` of the values they hold (`runs`). -/
def group (R : Rel (.atom .long) B) : Except String (Rel B (.atom .long)) := do
  let r ← cols R
  let (_, idx, _) := Order.group .i64 r.n.toUSize (← codes B #[r.val])
  runs B (← pick B r.val idx) (← Arr.of (.atom .long) (len idx) (← pick (.atom .long) r.key idx) "group")

/-- `∋` of a `grp`-keyed family: the pairs `(set id, element)`, the key's offsets reused, no kernel. -/
def mem {k v : Ty} (G : Rel k v) : Except String (Rel (.atom .long) v) :=
  match G with
  | ⟨n, .grp (g := g) _ o wf, val⟩ => pure ⟨n, .grp (.til g) o wf, val⟩
  | _ => throw "∋ reads a grp-keyed family; an arr-keyed family is its own ∋"

/-- `E(R)` of a stored family `G` (pairs `(X, x)`): `Λ(∋ ≫ R)` = the family of `G ≫ R`. -/
def existsImage (G : Rel A B) (R : Rel B C) : Except String (Rel A C) := do
  family (← cols (← comp G R))

/-- A table of one key and two value columns: the product `⟨R, S⟩`, `x ⟨R,S⟩ (y, z)`. -/
structure Tab (k v w : Ty) where
  n : Nat
  key : KeyCol k n
  fst : Arr v n
  snd : Arr w n

def Tab.Holds {k v w : Ty} (T : Tab k v w) (x : El k) (y : El v) (z : El w) : Prop :=
  ∃ i, T.key.get i = x ∧ T.fst.get i = y ∧ T.snd.get i = z

def Tab.toList {k v w : Ty} (T : Tab k v w) : List (El k × El v × El w) :=
  List.ofFn fun i => (T.key.get i, T.fst.get i, T.snd.get i)

/-- `⟨R, S⟩`: `join` on the keys → rows `(x, y, z)`, both value columns kept under one `n`. -/
def pair (R : Rel A B) (S : Rel A C) : Except String (Tab A B C) := do
  let r ← cols R; let s ← cols S
  let (rk, sk) := split (← codes A #[r.key, s.key]) r.n
  let (i, j) := join rk sk
  let t ← ofCols A B (← pick A r.key i) (← pick B r.val i)
  pure ⟨t.n, t.key, t.val, ← Arr.of C t.n (← pick C s.val j) "pair"⟩

/-- `outl`: the first component column, nothing runs. -/
def outl {k v w : Ty} (T : Tab k v w) : Rel k v := ⟨T.n, T.key, T.fst⟩
/-- `outr`: the second component column. -/
def outr {k v w : Ty} (T : Tab k v w) : Rel k w := ⟨T.n, T.key, T.snd⟩

theorem outl_holds {k v w : Ty} (T : Tab k v w) (x : El k) (y : El v) : (outl T).Holds x y ↔ ∃ z, T.Holds x y z :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨_, i, h1, h2, rfl⟩, fun ⟨_, i, h1, h2, _⟩ => ⟨i, h1, h2⟩⟩

theorem outr_holds {k v w : Ty} (T : Tab k v w) (x : El k) (z : El w) : (outr T).Holds x z ↔ ∃ y, T.Holds x y z :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨_, i, h1, rfl, h2⟩, fun ⟨_, i, h1, _, h2⟩ => ⟨i, h1, h2⟩⟩

/-- A relation between pairs, `(x, y) ⟶ (x', y')`, as four columns of one `n`. -/
structure Rel2 (k₁ k₂ v₁ v₂ : Ty) where
  n : Nat
  k₁ : Arr k₁ n
  k₂ : Arr k₂ n
  v₁ : Arr v₁ n
  v₂ : Arr v₂ n

def Rel2.toList {k₁ k₂ v₁ v₂ : Ty} (T : Rel2 k₁ k₂ v₁ v₂) : List ((El k₁ × El k₂) × (El v₁ × El v₂)) :=
  List.ofFn fun i => ((T.k₁.get i, T.k₂.get i), (T.v₁.get i, T.v₂.get i))

/-- `R × S` as a relation of its own: `cross` of the rows of `R` and of `S`. `Δ(R)` is `prod R R`. -/
def prod {D E : Ty} (R : Rel A B) (S : Rel D E) : Except String (Rel2 A D B E) := do
  let r ← cols R; let s ← cols S
  let (i, j) := cross r.n s.n
  let m := r.n * s.n
  pure ⟨m, ← Arr.of A m (← pick A r.key i) "prod", ← Arr.of D m (← pick D s.key j) "prod",
    ← Arr.of B m (← pick B r.val i) "prod", ← Arr.of E m (← pick E s.val j) "prod"⟩

/-- A relation out of a sum `a + a`: a tag bit beside each key, `false` for `inl`. Read with the
    value tagged by the key's own tag it is `R + S` as well as `[R, S]`. -/
structure SumRel (k v : Ty) where
  n : Nat
  tag : Arr (.atom .boolean) n
  key : Arr k n
  val : Arr v n

def SumRel.toList {k v : Ty} (T : SumRel k v) : List ((Bool × El k) × El v) :=
  List.ofFn fun i => ((T.tag.get i, T.key.get i), T.val.get i)

/-- `n` bits, all `x`: `Ew.cmp` of `til n` against `0`. -/
def bitsOf (x : Bool) (n : Nat) : ByteArray :=
  Ew.cmp (if x then Ew.ge else Ew.lt) Ew.i64 Ew.va (tilLongs n.toUSize) (one 0) n.toUSize

/-- `[R, S]`: the rows of `R` tagged `inl`, of `S` tagged `inr` — `concatBits` of constant bit columns. -/
def junc (R : Rel A C) (S : Rel A C) : Except String (SumRel A C) := do
  let r ← cols R; let s ← cols S
  let m := r.n + s.n
  pure ⟨m, ← Arr.of (.atom .boolean) m (.bits m (concatBits #[r.n, s.n] #[bitsOf false r.n, bitsOf true s.n])) "junc",
    ← Arr.of A m (← raze A #[r.key, s.key]) "junc", ← Arr.of C m (← raze C #[r.val, s.val]) "junc"⟩

/-- `inl°` on `U`: `inl x ↦ x`, the tag set to `false`; `inr°` with `true`. -/
def injConv {m : Nat} (tag : Bool) (U : Arr A m) : Except String (SumRel A A) := do
  pure ⟨m, ← Arr.of (.atom .boolean) m (.bits m (bitsOf tag m)) "injConv", U, U⟩

/-- `F(f)` on a map `f` given as an `Ew` monad: the functor on values, key kept (a `grp` key too). -/
def mapVal {k : Ty} {a : QAtomicType} (op : UInt8) (R : Rel k (.atom a)) : Except String (Rel k (.atom a)) := do
  let (vk, v) ← arrDense R.val
  let some nb := nullBits a | throw "a type with no null"
  pure ⟨R.n, R.key, ← Arr.of (.atom a) R.n (.bytes (Kernel.Ew.mon op (cls vk) nb.toInt64 v R.n.toUSize)) "mapVal"⟩

/-- `⦇e, f⦈` of a list when `f` is one of `Coc.Over`'s reductions: `overBytes`. -/
def foldOver {k : Ty} (op : Coc.Over) (R : Rel k (.atom .long)) : Except String Int64 := do
  let (_, v) ← arrDense R.val
  pure (overBytes op Ew.i64 nul v)

/-- The same per key: `overGroups` over the key codes' `groupIds`, one row per distinct key. -/
def foldGroups (op : Coc.Over) (R : Rel A (.atom .long)) : Except String (Rel A (.atom .long)) := do
  let r ← cols R; let (_, v) ← arrDense R.val
  let (gid, firsts) := Order.groupIds .i64 r.n.toUSize (← codes A #[r.key])
  let ng := len firsts
  ofCols A (.atom .long) (← pick A r.key firsts) (.bytes ((overGroups op Ew.i64 nul ng.toUSize gid v).extract 0 (8 * ng)))

/-- `α⁻¹` of a list, `uncons`: its first element and the rest, two picks (`gatherColumn`). -/
def uncons (R : Rel (.atom .long) B) : Except String (Rel (.atom .long) B × Rel (.atom .long) B) := do
  let r ← cols R
  if r.n = 0 then throw "uncons of an empty list"
  let m := r.n - 1
  let rest := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul (tilLongs m.toUSize) (one 1) m.toUSize
  pure (⟨1, .til 1, ← Arr.of B 1 (← pick B r.val (one 0)) "uncons"⟩, ⟨m, .til m, ← Arr.of B m (← pick B r.val rest) "uncons"⟩)

/-- An unfold then a fold: Lean's loop, at most `fuel` rounds of `step` until `done`, each round kernels. -/
def hylo {α : Type} (done : α → Except String Bool) (step : α → Except String α) : Nat → α → Except String α
  | 0, _ => throw "hylo: out of fuel"
  | fuel + 1, x => do if ← done x then pure x else hylo done step fuel (← step x)

/-- `est(≤)` (`desc`: `est(≥)`) of a family of longs: `overGroups` lesser/greater per key. -/
def est (desc : Bool) (G : Rel A (.atom .long)) : Except String (Rel A (.atom .long)) :=
  foldGroups (if desc then .greater else .lesser) G

/-- The rows of `G` in the order key ascending, then each of `ks` in turn (`desc`), by stable grades
    from the last key to the first; answers the permutation. -/
def gradeBy (gid : ByteArray) (ks : List (Scan.Kind × Bool × ByteArray)) : ByteArray :=
  let n := (len gid).toUSize
  let p := ks.foldr (init := tilLongs n) fun (k, desc, b) p =>
    gather 8 p (Order.grade k desc n (gather k.width b p))
  gather 8 p (Order.grade .i64 false n (gather 8 gid p))

/-- `thin(Q)` for `Q` the key order "`f y ≥ f x`", `f` the value itself: per set its maximal
    elements — `Order.grade` on `(group, f)`, `groupLasts` = the max per group, `Ew.cmp eq`, `whereBits`. -/
def thinMax (G : Rel A (.atom .long)) : Except String (Rel A (.atom .long)) := do
  let r ← cols G; let (_, v) ← arrDense G.val
  let (gid, firsts) := Order.groupIds .i64 r.n.toUSize (← codes A #[r.key])
  let p := gradeBy gid [(.i64, false, v)]
  let top := gather 8 v (gather 8 p (Order.groupLasts (len firsts).toUSize (gather 8 gid p)))
  let t ← r.rows (whereEqV v (gather 8 top gid))
  ofCols A (.atom .long) t.key t.val

/-- `thin(Q)` for the two-key Pareto order `(k₁ ≤, k₂ ≤)` on a family with two value columns: the
    rows in key order with `k₁` then `k₂` descending, `Scan.scan maxs` of the group-major rank
    `group·N + rank(k₂)`, a row kept where it beats the prior running max (`Ew.cmp gt`). -/
def thinPareto (T : Tab A (.atom .long) (.atom .long)) : Except String (Tab A (.atom .long) (.atom .long)) := do
  let key ← keyPay T.key
  let (_, k₁) ← arrDense T.fst; let (_, k₂) ← arrDense T.snd
  let n := T.n
  let gid := (Order.groupIds .i64 n.toUSize (← codes A #[key])).1
  let p := gradeBy gid [(.i64, true, k₁), (.i64, true, k₂)]
  let c := add (mulc (gather 8 gid p) n) (gather 8 (drank .i64 k₂) p)
  let prior := concatBytes #[one nul.toUInt64, (Scan.scan .maxs .i64 n.toUSize c).extract 0 (8 * (n - 1))]
  let keep := gather 8 p (whereBits n.toUSize (Ew.cmp Ew.gt Ew.i64 Ew.vv c prior n.toUSize))
  let m := len keep
  pure ⟨m, .arr (← Arr.of A m (← pick A key keep) "thinPareto"), ← Arr.of (.atom .long) m (.bytes (gather 8 k₁ keep)) "thinPareto",
    ← Arr.of (.atom .long) m (.bytes (gather 8 k₂ keep)) "thinPareto"⟩

/-- `Entire R` on the universe `U`: `memberVec` of `U`'s codes in the keys', all set. -/
def entire {m : Nat} (R : Rel A B) (U : Arr A m) : Except String Bool := do
  let r ← cols R
  let (uc, kc) := split (← codes A #[U.c, r.key]) m
  pure (len (whereBits m.toUSize (memberVec 8 false uc kc)) == m)

/-- `Simple R`: in `R` with each pair once, every key distinct (`groupIds` count of the key codes). -/
def simple (R : Rel A B) : Except String Bool := do
  let r ← (← cols R).nub
  pure (len (Order.groupIds .i64 r.n.toUSize (← codes A #[r.key])).2 == r.n)

def isMap {m : Nat} (R : Rel A B) (U : Arr A m) : Except String Bool := do
  pure ((← entire R U) && (← simple R))

/-- `Injective R` = `Simple R°`. -/
def injective (R : Rel A B) : Except String Bool := do simple (← conv R)

/-- `Surjective R` = `Entire R°` on the universe `U` of `b`. -/
def surjective {m : Nat} (R : Rel A B) (U : Arr B m) : Except String Bool := do
  entire (← conv R) U

/-! ## Checks against the `toList` specs, on small literal relations -/

section Checks

private abbrev L := Ty.atom .long
private abbrev LL := Rel (.atom .long) (.atom .long)

private def seteq {α : Type} [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains
private def ok {α : Type} (x : Except String α) (p : α → Bool) : Bool := match x with | .ok v => p v | .error _ => false

-- R = {1↦10, 1↦20, 2↦10, 3↦30}, S = {1↦10, 2↦10, 2↦20, 4↦40}
private def R : LL := ⟨4, .arr { c := .bytes <| packLongs [1, 1, 2, 3], wf := by decide }, { c := .bytes <| packLongs [10, 20, 10, 30], wf := by decide }⟩
private def S : LL := ⟨4, .arr { c := .bytes <| packLongs [1, 2, 2, 4], wf := by decide }, { c := .bytes <| packLongs [10, 10, 20, 40], wf := by decide }⟩
-- T : b ⟶ c, {10↦7, 20↦8, 20↦9}
private def T : LL := ⟨3, .arr { c := .bytes <| packLongs [10, 20, 20], wf := by decide }, { c := .bytes <| packLongs [7, 8, 9], wf := by decide }⟩
-- a list (key `til`), with a repeat: (5 3 5 9)
private def Ls : LL := ⟨4, .til 4, { c := .bytes <| packLongs [5, 3, 5, 9], wf := by decide }⟩
private def Ua : Arr L 4 := { c := .bytes <| packLongs [1, 2, 3, 4], wf := by decide }
private def Ub : Arr L 4 := { c := .bytes <| packLongs [10, 20, 30, 40], wf := by decide }
private def Uc : Arr L 3 := { c := .bytes <| packLongs [7, 8, 9], wf := by decide }

#guard ok (le R S) (· == false)
#guard ok (inter R S) fun X => ok (le X R) id && ok (le X S) id
#guard ok (inter R S) fun X => seteq X.toList (R.toList.filter S.toList.contains)
#guard ok (union R S) fun X => seteq X.toList (R.toList ++ S.toList) && X.n == 6
#guard ok (zero (A := L) (B := L)) (·.n == 0)
#guard ok (top Ua Uc) fun X => seteq X.toList (Ua.toList.flatMap fun x => Uc.toList.map (x, ·))
#guard (idU Ua).toList == Ua.toList.map fun x => (x, x)
#guard ok (conv R) fun X => seteq X.toList (R.toList.map fun (x, y) => (y, x))
#guard ok (conv Ls) fun X => seteq X.toList (Ls.toList.map fun (x, y) => (y, x))
#guard ok (comp R T) fun X =>
  seteq X.toList (R.toList.flatMap fun (x, y) => T.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard ok (comp Ls Ls) fun X =>
  seteq X.toList (Ls.toList.flatMap fun (x, y) => Ls.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard ok (dom R) fun X => seteq X.toList [(1, 1), (2, 2), (3, 3)] && X.n == 3
#guard ok (ran S) fun X => seteq X.toList [(10, 10), (20, 20), (40, 40)] && X.n == 3
#guard ok (corefl Ua Ew.gt 2) fun X => X.toList == [(3, 3), (4, 4)]
#guard ok (isCorefl (idU Ua)) id && ok (isCorefl R) (· == false)

-- `R \ S` over `Ub × Ub`: `y (R\S) z ↔ ∀ x, x R y → x S z`
private def leftSpec (R S : LL) (Ub Uc : List Int64) : List (Int64 × Int64) :=
  Ub.flatMap fun y => (Uc.filter fun z => R.toList.all fun (x, y') => y' != y || S.toList.contains (x, z)).map (y, ·)
#guard ok (leftDiv R S Ub Ub) fun X => seteq X.toList (leftSpec R S Ub.toList Ub.toList)
#guard ok (leftDiv R R Ub Ub) fun X => seteq X.toList (leftSpec R R Ub.toList Ub.toList)
-- `R / S` (`R : a ⟶ c`, `S : b ⟶ c`): `x (R/S) y ↔ ∀ z, y S z → x R z`
#guard ok (rightDiv R S Ua Ua) fun X => seteq X.toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => S.toList.all fun (y', z) => y' != y || R.toList.contains (x, z)).map (x, ·))
-- `R /ₛ S`: equal fibres
private def fib (R : LL) (x : Int64) : List Int64 := R.toList.filterMap fun (x', z) => if x == x' then some z else none
#guard ok (symDiv R S Ua Ua) fun X => seteq X.toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib S y)).map (x, ·))
#guard ok (symDiv R R Ua Ua) fun X => seteq X.toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib R y)).map (x, ·))

-- `Λ(R)`: the same pairs, each set one contiguous run of its key
#guard ok (do transpose (← union R R)) fun X => seteq X.toList R.toList && X.n == 4 &&
  (X.toList.map (·.1)) == [1, 1, 2, 3]
#guard ok (group Ls) fun X => X.toList == [(5, 0), (5, 2), (3, 1), (9, 3)]
#guard ok (group Ls) fun X => X.key matches .grp ..
private def Lf : LL := ⟨4, .til 4, { c := .foR 4 (Coc.encode 8 (packLongs [5, 3, 5, 9])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9])).2, wf := ⟨rfl, rfl⟩ }⟩
#guard ok (group Lf) fun X => X.toList == [(5, 0), (5, 2), (3, 1), (9, 3)]
#guard ok (do transpose (← union R R)) fun X => X.key matches .grp ..
#guard ok (do mem (← transpose R)) fun X => X.toList.map (·.2) == [10, 20, 10, 30] && (X.toList.map (·.1)) == [0, 0, 1, 2]
#guard ok (do transpose (← zero (A := L) (B := L))) (·.n == 0)
-- `anti`: the positions of `x` not in `y`
#guard anti (packLongs [3, 1, 4, 1]) (packLongs [1, 5]) == packLongs [0, 2]
-- `∋` of a grp-keyed family: the parted list `(10 20; 30)` from the core
private def o2 : Arr L 3 := { c := .bytes <| packLongs [0, 2, 3], wf := by decide }
private def parted : LL := ⟨3, .grp (.til 2) o2 (by decide), { c := .bytes <| packLongs [10, 20, 30], wf := by decide }⟩
#guard ok (mem parted) fun X => X.toList == [(0, 10), (0, 20), (1, 30)]
#guard ok (keyPay parted.key) fun c => Column.bytesOf .long c == some (packLongs [0, 0, 1])
-- `E(R)` of the family `G = {X₁ = {1, 2}, X₂ = {3}}`
private def G : LL := ⟨3, .arr { c := .bytes <| packLongs [1, 1, 2], wf := by decide }, { c := .bytes <| packLongs [1, 2, 3], wf := by decide }⟩
#guard ok (existsImage G R) fun X => seteq X.toList
  (G.toList.flatMap fun (s, x) => R.toList.filterMap fun (x', y) => if x == x' then some (s, y) else none)

#guard ok (pair R S) fun P => seteq P.toList
  (R.toList.flatMap fun (x, y) => S.toList.filterMap fun (x', z) => if x == x' then some (x, y, z) else none)
#guard ok (pair R S) fun P => seteq (outl P).toList (R.toList.filter fun (x, _) => S.toList.any (·.1 == x))
#guard ok (pair R S) fun P => seteq (outr P).toList (S.toList.filter fun (x, _) => R.toList.any (·.1 == x))
#guard ok (prod R T) fun P => seteq P.toList
  (R.toList.flatMap fun (x, x') => T.toList.map fun (y, y') => ((x, y), (x', y')))
#guard ok (junc R S) fun J => seteq J.toList (R.toList.map (fun (x, y) => ((false, x), y)) ++ S.toList.map fun (x, y) => ((true, x), y))
#guard ok (injConv true Ua) fun J => J.toList == Ua.toList.map fun x => ((true, x), x)

#guard ok (mapVal Ew.neg Ls) fun X => X.toList == [(0, -5), (1, -3), (2, -5), (3, -9)]
#guard ok (foldOver .add Ls) (· == 22)
#guard ok (foldGroups .add R) fun X => X.toList == [(1, 30), (2, 10), (3, 30)]
#guard ok (uncons Ls) fun (h, t) => h.toList == [(0, 5)] && t.toList == [(0, 3), (1, 5), (2, 9)]
-- an unfold then a fold: uncons to the end, summing the heads
#guard ok (hylo (fun (xs, _) => pure (xs.n == 0))
    (fun ((xs : LL), (acc : Int64)) => do let (h, t) ← uncons xs; pure (t, acc + (← foldOver .add h))) 10 (Ls, 0))
  fun (_, s) => s == 22
#guard ok (est false R) fun X => X.toList == [(1, 10), (2, 10), (3, 30)]
#guard ok (est true R) fun X => X.toList == [(1, 20), (2, 10), (3, 30)]
#guard ok (thinMax R) fun X => seteq X.toList [(1, 20), (2, 10), (3, 30)]
-- Pareto: set 1 holds (1,5) (3,2) (2,2) (3,1) (1,5): keep (1,5) and (3,2), one copy each
private def P : Tab L L L := ⟨5, .arr { c := .bytes <| packLongs [1, 1, 1, 1, 1], wf := by decide },
  { c := .bytes <| packLongs [1, 3, 2, 3, 1], wf := by decide }, { c := .bytes <| packLongs [5, 2, 2, 1, 5], wf := by decide }⟩
#guard ok (thinPareto P) fun X => seteq X.toList [(1, 3, 2), (1, 1, 5)] && X.n == 2

private def Ua3 : Arr L 3 := { c := .bytes <| packLongs [3, 1, 2], wf := by decide }
#guard ok (entire R Ua) (· == false) && ok (entire R Ua3) id
#guard ok (simple R) (· == false) && ok (simple (idU Ua)) id && ok (simple Ls) id
#guard ok (isMap (idU Ua) Ua) id
#guard ok (injective Ls) (· == false) && ok (injective T) id
#guard ok (surjective R Ub) (· == false) && ok (surjective (idU Ub) Ub) id

/-! ### Every other encoding: the list `i ↦ x i` of four elements in each, against its own spec -/

/-- A list over the payload `c`: key `til`. -/
private def lst (t : Ty) (c : Pay t) : Except String (Rel L t) := do
  let n := count t c
  pure ⟨n, .til n, ← Arr.of t n c "lst"⟩
/-- `L ≫ L°`: the pairs of positions holding one element. -/
private def same {t : Ty} (X Y : Rel L t) : Except String LL := do comp X (← conv Y)
private def U4 : Arr L 4 := { c := .bytes <| packLongs [0, 1, 2, 3], wf := by decide }
-- the positions of `(p q p r)` paired with equal elements: `(0 2)` share, `1` and `3` alone
private def pqpr : List (Int64 × Int64) := [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (3, 3)]

-- boolean, `bits`: `1010b`, whose positions pair `(0 2)` and `(1 3)`
private abbrev Bo := Ty.atom .boolean
private def bitsC : Column := .bits 4 (ByteArray.mk #[0b0101])
#guard ok (do same (← lst Bo bitsC) (← lst Bo bitsC)) fun X =>
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)] && X.n == 8
#guard ok (do group (← lst Bo bitsC)) fun X => X.toList == [(true, 0), (true, 2), (false, 1), (false, 3)]
#guard ok (do ran (← lst Bo bitsC)) fun X => seteq X.toList [(true, true), (false, false)] && X.n == 2
#guard ok (do union (← lst Bo bitsC) (← lst Bo bitsC)) fun X => X.n == 4
#guard ok (do symDiv (← lst Bo bitsC) (← lst Bo bitsC) U4 U4) fun X =>
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)]

-- symbol, `syms` and `enum`: `` `bc`a`bc`d `` in both, compared across the two
private abbrev Sy := Ty.atom .symbol
private def symsC : Column := .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0, 100, 0]) #[0, 3, 5, 8, 10]
private def enumC : Column :=
  .enum 4 (ByteArray.mk #[97, 0, 98, 99, 0, 100, 0]) #[0, 2, 5, 7] (Column.packIds (Column.idWidth #[0, 2, 5, 7]) 4 fun i => [1, 0, 1, 2][i]!)
#guard ok (lst Sy enumC) fun X => X.toList == [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
#guard ok (do same (← lst Sy symsC) (← lst Sy enumC)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do same (← lst Sy enumC) (← lst Sy enumC)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do union (← lst Sy symsC) (← lst Sy enumC)) fun X => X.n == 4 &&
  seteq X.toList [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
#guard ok (do group (← lst Sy enumC)) fun X => X.toList == [("bc", 0), ("bc", 2), ("a", 1), ("d", 3)]
#guard ok (do group (← lst Sy symsC)) fun X => X.toList == [("bc", 0), ("bc", 2), ("a", 1), ("d", 3)]
#guard ok (do symDiv (← lst Sy symsC) (← lst Sy enumC) U4 U4) fun X => seteq X.toList pqpr
#guard ok (do leftDiv (← lst Sy enumC) (← lst Sy symsC) (← Arr.of Sy 4 symsC "U") (← Arr.of Sy 4 enumC "U")) fun X =>
  seteq X.toList [("bc", "bc"), ("a", "a"), ("d", "d")]
#guard ok (do top (← Arr.of Sy 4 enumC "U") (← Arr.of Bo 4 bitsC "U")) (·.n == 16)
#guard ok (do transpose (← conv (← lst Sy enumC))) fun X => X.key matches .grp .. && X.n == 4

-- float through ALP: `1.5 2.25 1.5 0.1`, and the same as dense bytes
private abbrev Fl := Ty.atom .float
private def fs : List Float := [1.5, 2.25, 1.5, 0.1]
private def fb : ByteArray := packLongs (fs.map (·.toBits.toInt64))
-- `alpOf` and not `Column.answer`, which keeps a column this short dense
private def alpC : Column := (Column.alpOf .float (.bytes fb)).getD (.bytes fb)
#guard alpC matches .alp ..
#guard ok (do same (← lst Fl alpC) (← lst Fl alpC)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do same (← lst Fl alpC) (← lst Fl (.bytes fb))) fun X => seteq X.toList pqpr && X.n == 6
-- a float element is its IEEE bits
#guard ok (do group (← lst Fl alpC)) fun X =>
  X.toList.map (·.2) == [0, 2, 1, 3] && X.toList.map (·.1) == [1.5, 1.5, 2.25, 0.1].map Float.toBits
#guard ok (do union (← lst Fl alpC) (← lst Fl (.bytes fb))) fun X => X.n == 4
#guard ok (do symDiv (← lst Fl alpC) (← lst Fl alpC) U4 U4) fun X => seteq X.toList pqpr

-- a general list, `(1; (); 1; ,2)`, elements matched by identity
private def gs : Array QValue := #[.atom (.long 1), .list #[], .atom (.long 1), .list #[.atom (.long 2)]]
#guard ok (do same (← lst .gen gs) (← lst .gen gs)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do group (← lst .gen gs)) fun X => X.toList.map (·.2) == [0, 2, 1, 3] && X.n == 4
#guard ok (do union (← lst .gen gs) (← lst .gen gs)) fun X => X.n == 4
#guard ok (do dom (← conv (← lst .gen gs))) (·.n == 3)
#guard ok (do symDiv (← lst .gen gs) (← lst .gen gs) U4 U4) fun X => seteq X.toList pqpr
#guard ok (do uncons (← lst .gen gs)) fun (h, t) => h.n == 1 && t.n == 3
#guard ok (do zero (A := .gen) (B := Sy)) (·.n == 0)

end Checks

#print axioms idU_holds
#print axioms convArr_holds
#print axioms outl_holds
#print axioms outr_holds
#print axioms le
#print axioms inter
#print axioms union
#print axioms zero
#print axioms top
#print axioms conv
#print axioms comp
#print axioms dom
#print axioms ran
#print axioms corefl
#print axioms isCorefl
#print axioms leftDiv
#print axioms rightDiv
#print axioms symDiv
#print axioms transpose
#print axioms group
#print axioms existsImage
#print axioms pair
#print axioms prod
#print axioms junc
#print axioms injConv
#print axioms mapVal
#print axioms foldGroups
#print axioms uncons
#print axioms thinMax
#print axioms thinPareto
#print axioms entire
#print axioms simple
#print axioms injective
#print axioms surjective

end LeetQ.Rel.Alg
