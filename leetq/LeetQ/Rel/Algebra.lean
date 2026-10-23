/-
  The relation algebra of the RelRep design §2.3 on the core: every operator a pipeline of qlean
  kernels over the dense payloads of a `Rel`'s two columns, never a loop over `Arr.get`,
  `Column.get` or `Column.atoms`. Elements are compared through joint CODES — the first-occurrence
  group of each element across every column taking part (`Order.groupIds` of a `concatBytes`) — so
  two columns of one type become comparable longs, and a pair of codes is one long by `rankPair`.
  The spec of each operator is the List-level relation on `toList`; `#guard`s below hold each one
  on small literal relations, and the laws that the kernels' Lean bodies make reachable are proved.
-/
import LeetQ.Rel.Core
import QLean.Kernel.Sort
import QLean.Kernel.Structural
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel

/-! ## Long payloads: the index, code and count columns every step passes along -/

/-- One long, the `av` operand of an elementwise kernel. -/
def long1 (x : Int64) : ByteArray := Column.pushBits .empty x.toUInt64 8

/-- Elements of a long payload. -/
def len (b : ByteArray) : Nat := b.size / 8

def nul : Int64 := Int64.minValue

def add (a b : ByteArray) : ByteArray := Ew.val Ew.add Ew.i64 Ew.vv nul a b (len a).toUSize
def sub (a b : ByteArray) : ByteArray := Ew.val Ew.sub Ew.i64 Ew.vv nul a b (len a).toUSize
def mulc (a : ByteArray) (x : Nat) : ByteArray := Ew.val Ew.mul Ew.i64 Ew.va nul a (long1 (.ofNat x)) (len a).toUSize
def sums (b : ByteArray) : ByteArray := Scan.scan .sums .i64 (len b).toUSize b
/-- `src@idx` at element width `w`; a miss reads `0`. -/
def gather (w : Nat) (src idx : ByteArray) : ByteArray := gatherBytes w.toUSize 0 src idx
/-- The positions where `a` equals `b` elementwise. -/
def whereEqV (a b : ByteArray) : ByteArray :=
  whereBits (len a).toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv a b (len a).toUSize)
/-- The positions where `a` equals the long `x`. -/
def whereEq (a : ByteArray) (x : Int64) : ByteArray :=
  whereBits (len a).toUSize (Ew.cmp Ew.eq Ew.i64 Ew.va a (long1 x) (len a).toUSize)
/-- The first `n` longs and the rest. -/
def split (b : ByteArray) (n : Nat) : ByteArray × ByteArray := (b.extract 0 (8 * n), b.extract (8 * n) b.size)

/-- The elementwise class of a sort layout. -/
def cls : Scan.Kind → UInt8
  | .bit => Ew.bits | .u8 | .c8 => Ew.u8 | .i16 => Ew.i16 | .i32 => Ew.i32 | .i64 => Ew.i64
  | .f32 => Ew.f32 | .f64 => Ew.f64

def isFloat : Scan.Kind → Bool | .f32 | .f64 => true | _ => false

/-! ## Dense payloads of the core's columns, and back -/

/-- A column's dense payload and the layout the sort kernels read it at; an encoded column is
    decoded once (`Coc.decode`, the design's mark for a kernel that exists on `bytes` only). -/
def arrDense : {t : Ty} → {n : Nat} → Arr t n → Except String (Scan.Kind × ByteArray)
  | .gen, _, _ => throw "a general (type 0) column has no fixed-width payload"
  | .atom a, _, x => do
    let some k := orderKind a | throw "an atom type with no sort layout (guid, symbol): no dense kernel path"
    match (x.c : Column) with
    | .bytes b => pure (k, b)
    | .foR m md pk => pure (k, Coc.decode k.width.toUSize md pk m.toUSize)
    | _ => throw "a bits, syms, enum or ALP column: no dense kernel path in this layer"

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it (`bin`). -/
def groupOf (o : ByteArray) (n : Nat) : ByteArray := binBytes 8 false true false o (tilLongs n.toUSize)

/-- A key column's dense payload: `til` is `tilLongs`, `grp d o` gathers `d` at `groupOf o`. -/
def keyDense : {k : Ty} → {n : Nat} → KeyCol k n → Except String (Scan.Kind × ByteArray)
  | _, _, .til n => pure (.i64, tilLongs n.toUSize)
  | _, n, .grp d o _ => do
    let (k, b) ← keyDense d
    let (_, ob) ← arrDense o
    pure (k, gather k.width b (groupOf ob n))
  | _, _, .arr a => arrDense a

/-- A relation's two columns as dense payloads. -/
structure Dense where
  kk : Scan.Kind
  key : ByteArray
  vk : Scan.Kind
  val : ByteArray
  deriving Inhabited

def Dense.n (d : Dense) : Nat := d.key.size / d.kk.width

def dense {k v : Ty} (R : Rel k v) : Except String Dense := do
  let (kk, key) ← keyDense R.key
  let (vk, val) ← arrDense R.val
  pure ⟨kk, key, vk, val⟩

/-- The rows of `d` at the index column `i`. -/
def Dense.rows (d : Dense) (i : ByteArray) : Dense :=
  { d with key := gather d.kk.width d.key i, val := gather d.vk.width d.val i }

/-- A dense payload as an `Arr`, its length checked once against the type's count. -/
def Arr.ofDense (a : QAtomicType) (n : Nat) (b : ByteArray) : Except String (Arr (.atom a) n) :=
  let c : Pay (.atom a) := .bytes b
  if h : (Ty.atom a).WF n c then pure ⟨c, h, 0, none⟩
  else throw s!"a payload of {b.size} bytes is not {n} elements of its type"

/-- A boolean column of `n` bits. -/
def Arr.ofBits (n : Nat) (b : ByteArray) : Except String (Arr (.atom .boolean) n) :=
  let c : Pay (.atom .boolean) := .bits n b
  if h : (Ty.atom .boolean).WF n c then pure ⟨c, h, 0, none⟩ else throw s!"{b.size} bytes do not hold {n} bits"

/-- Two dense payloads as a relation keyed by an explicit column. -/
def ofDense (a b : QAtomicType) (kb vb : ByteArray) : Except String (Rel (.atom a) (.atom b)) := do
  let n := Column.count a (.bytes kb)
  pure ⟨n, .arr (← Arr.ofDense a n kb), ← Arr.ofDense b n vb⟩

/-! ## The composite steps, named once -/

/-- Joint codes: equal elements of any of `cols` get one long, below the total length — the
    first-occurrence group of the concatenation (`concatBytes`, `Order.groupIds`). -/
def codes (k : Scan.Kind) (cols : Array ByteArray) : ByteArray :=
  let all := concatBytes cols
  (Order.groupIds k (all.size / k.width).toUSize all).1

/-- `rankPair`: two code columns of one length as one code column, `p·N + q` regrouped, where
    every code of `q` is below `N` (so `p·N + q` is injective while `N² < 2⁶³`). qlean's
    `Ew.rankPair` is the rank of two SYMBOL dictionaries, not this; this is `Ew.val` + `groupIds`. -/
def rankPair (p q : ByteArray) (N : Nat) : ByteArray :=
  (Order.groupIds .i64 (len q).toUSize (add (mulc p N) q)).1

/-- `|R|` of several relations of one type in one code space, concatenated in order. -/
def pairs (ds : Array Dense) : ByteArray :=
  let vc := codes ds[0]!.vk (ds.map (·.val))
  rankPair (codes ds[0]!.kk (ds.map (·.key))) vc (len vc)

/-- `R` with each pair once: the first row of each class of `|R|`. -/
def Dense.nub (d : Dense) : Dense := d.rows (Order.groupIds .i64 d.n.toUSize (pairs #[d])).2

/-- q's `where` on a count column: row `i` repeated `cnt[i]` times, and each copy's rank in its run
    (`Scan.scan sums`, `overBytes add`, `tilLongs`, `binBytes` of the outputs into the run starts). -/
def expand (cnt : ByteArray) : ByteArray × ByteArray :=
  let rs := sub (sums cnt) cnt
  let p := tilLongs (overBytes .add Ew.i64 nul cnt).toInt.toNat.toUSize
  let i := binBytes 8 false true false rs p
  (i, sub p (gather 8 rs i))

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
  ( Ew.val Ew.idiv Ew.i64 Ew.va nul p (long1 (.ofNat m)) (n * m).toUSize
  , Ew.val Ew.imod Ew.i64 Ew.va nul p (long1 (.ofNat m)) (n * m).toUSize)

/-- `anti(x, y)`: the positions of `x` whose code is not in `y` — `findVec`'s miss, `Ew.cmp eq`, `whereBits`. -/
def anti (x y : ByteArray) : ByteArray := whereEq (findVec 8 false y x) (.ofNat (len y))

/-- Dense rank of a payload in value order: `binBytes` into its sorted distinct values. -/
def drank (k : Scan.Kind) (b : ByteArray) : ByteArray :=
  let n := (b.size / k.width).toUSize
  let d := Order.distinct k n b
  binBytes k.width.toUSize (isFloat k) true false (Order.sortValues k false (d.size / k.width).toUSize d) b

/-! ## The operators -/

variable {a b c : QAtomicType}

/-- `R ⊑ S`: `memberVec` of `|R|` in `|S|`, all set. -/
def le (R S : Rel (.atom a) (.atom b)) : Except String Bool := do
  let r ← dense R; let s ← dense S
  let (pr, ps) := split (pairs #[r, s]) r.n
  pure (len (whereBits r.n.toUSize (memberVec 8 false pr ps)) == r.n)

/-- `R ∩ S`: the semi-join on pairs — `memberVec`, `whereBits`, `gatherBytes`. -/
def inter (R S : Rel (.atom a) (.atom b)) : Except String (Rel (.atom a) (.atom b)) := do
  let r ← dense R; let s ← dense S
  let (pr, ps) := split (pairs #[r, s]) r.n
  let t := r.rows (whereBits r.n.toUSize (memberVec 8 false pr ps))
  ofDense a b t.key t.val

/-- `R ∪ S`: `concatBytes` of keys and of vals, the first row of each pair. -/
def union (R S : Rel (.atom a) (.atom b)) : Except String (Rel (.atom a) (.atom b)) := do
  let r ← dense R; let s ← dense S
  let u : Dense := { r with key := concatBytes #[r.key, s.key], val := concatBytes #[r.val, s.val] }
  ofDense a b u.nub.key u.nub.val

/-- `𝟘`: no pair. -/
def zero : Except String (Rel (.atom a) (.atom b)) := ofDense a b .empty .empty

/-- `⊤` on the universes `Ua`, `Ub`: `cross`. -/
def top {ma mb : Nat} (Ua : Arr (.atom a) ma) (Ub : Arr (.atom b) mb) : Except String (Rel (.atom a) (.atom b)) := do
  let (ka, ua) ← arrDense Ua; let (kb, ub) ← arrDense Ub
  let (i, j) := cross ma mb
  ofDense a b (gather ka.width ua i) (gather kb.width ub j)

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

/-- `R°`: a `til`/`grp` key is written only here (`keyDense`); an `arr` key moves. -/
def conv (R : Rel (.atom a) (.atom b)) : Except String (Rel (.atom b) (.atom a)) :=
  match R with
  | ⟨_, .arr k, v⟩ => pure (convArr k v)
  | R => do let r ← dense R; ofDense b a r.val r.key

/-- `R ≫ S`: `join` on `R.val = S.key`, the key gathered from `R`, the val from `S`. -/
def comp (R : Rel (.atom a) (.atom b)) (S : Rel (.atom b) (.atom c)) : Except String (Rel (.atom a) (.atom c)) := do
  let r ← dense R; let s ← dense S
  let (rc, sc) := split (codes r.vk #[r.val, s.key]) r.n
  let (i, j) := join rc sc
  ofDense a c (gather r.kk.width r.key i) (gather s.vk.width s.val j)

/-- `dom R`: the coreflexive on the distinct keys. -/
def dom (R : Rel (.atom a) (.atom b)) : Except String (Rel (.atom a) (.atom a)) := do
  let r ← dense R
  let d := gather r.kk.width r.key (Order.groupIds r.kk r.n.toUSize r.key).2
  ofDense a a d d

/-- `ran R`: the coreflexive on the distinct vals. -/
def ran (R : Rel (.atom a) (.atom b)) : Except String (Rel (.atom b) (.atom b)) := do
  let r ← dense R
  let d := gather r.vk.width r.val (Order.groupIds r.vk r.n.toUSize r.val).2
  ofDense b b d d

/-- `p?` on `U`, `p x ↔ x op e` for one of `Ew`'s six comparisons: `Ew.cmp`, `whereBits`, `gatherBytes`. -/
def corefl {m : Nat} (U : Arr (.atom a) m) (op : UInt8) (e : UInt64) : Except String (Rel (.atom a) (.atom a)) := do
  let (k, u) ← arrDense U
  let d := gather k.width u (whereBits m.toUSize (Ew.cmp op (cls k) Ew.va u (Column.pushBits .empty e k.width) m.toUSize))
  ofDense a a d d

/-- `Coreflexive R`, `R ⊑ 𝟙`: `matchBytes` of key against val. -/
def isCorefl (R : Rel (.atom a) (.atom a)) : Except String Bool := do
  let r ← dense R
  pure (matchBytes r.kk.width.toUSize (isFloat r.kk) r.key r.val)

/-- `R \ S` (`R : a ⟶ b`, `S : a ⟶ c`), by counting: `join` on the shared key → rows `(y, z)`;
    `cnt(y, z)` against `cnt(R.val)` `at` `y`; the vacuous `y ∉ ran R` with every `z` from the
    universes `Ub`, `Uc`: `cross(anti(Ub, ran R), Uc)`. -/
def leftDiv {mb mc : Nat} (R : Rel (.atom a) (.atom b)) (S : Rel (.atom a) (.atom c))
    (Ub : Arr (.atom b) mb) (Uc : Arr (.atom c) mc) : Except String (Rel (.atom b) (.atom c)) := do
  let r := (← dense R).nub; let s := (← dense S).nub
  let (_, ub) ← arrDense Ub; let (_, uc) ← arrDense Uc
  let (rk, sk) := split (codes r.kk #[r.key, s.key]) r.n
  let (i, j) := join rk sk
  let y := gather r.vk.width r.val i; let z := gather s.vk.width s.val j
  let (yc, rest) := split (codes r.vk #[y, r.val, ub]) (len i)
  let (rvc, ubc) := split rest r.n
  let zc := codes s.vk #[z]
  let (gid, firsts) := Order.groupIds .i64 (len i).toUSize (rankPair yc zc (len zc))
  let got := Order.groupSizes (len firsts).toUSize gid
  let keep := gather 8 firsts (whereEqV got (atCnt (cnt rvc) (gather 8 yc firsts)))
  let miss := anti ubc rvc
  let (p, q) := cross (len miss) mc
  ofDense b c (concatBytes #[gather r.vk.width y keep, gather r.vk.width ub (gather 8 miss p)])
    (concatBytes #[gather s.vk.width z keep, gather s.vk.width uc q])

/-- `R / S = (S° \ R°)°` (`R : a ⟶ c`, `S : b ⟶ c`); its vacuous term is `cross(Ua, anti(Ub, dom S))`. -/
def rightDiv {ma mb : Nat} (R : Rel (.atom a) (.atom c)) (S : Rel (.atom b) (.atom c))
    (Ua : Arr (.atom a) ma) (Ub : Arr (.atom b) mb) : Except String (Rel (.atom a) (.atom b)) := do
  conv (← leftDiv (← conv S) (← conv R) Ub Ua)

/-- `R /ₛ S` (`R : a ⟶ c`, `S : b ⟶ c`), equal fibres by counting: `join` on `z` → `(x, y)`;
    `cnt(x, y)` equal to both `cnt(R.key)` `at` `x` and `cnt(S.key)` `at` `y`; the vacuous term
    `cross(anti(Ua, dom R), anti(Ub, dom S))`, the empty fibres. -/
def symDiv {ma mb : Nat} (R : Rel (.atom a) (.atom c)) (S : Rel (.atom b) (.atom c))
    (Ua : Arr (.atom a) ma) (Ub : Arr (.atom b) mb) : Except String (Rel (.atom a) (.atom b)) := do
  let r := (← dense R).nub; let s := (← dense S).nub
  let (_, ua) ← arrDense Ua; let (_, ub) ← arrDense Ub
  let (rv, sv) := split (codes r.vk #[r.val, s.val]) r.n
  let (i, j) := join rv sv
  let x := gather r.kk.width r.key i; let y := gather s.kk.width s.key j
  let xa := codes r.kk #[x, r.key, ua]; let ya := codes s.kk #[y, s.key, ub]
  let (xc, xr) := split xa (len i); let (rkc, uac) := split xr r.n
  let (yc, yr) := split ya (len j); let (skc, ubc) := split yr s.n
  let (gid, firsts) := Order.groupIds .i64 (len i).toUSize (rankPair xc yc (len ya))
  let got := Order.groupSizes (len firsts).toUSize gid
  let nx := atCnt (cnt rkc) (gather 8 xc firsts); let ny := atCnt (cnt skc) (gather 8 yc firsts)
  let keep := gather 8 firsts (whereEq (add (sub nx got) (sub ny got)) 0)
  let ex := anti uac rkc; let ey := anti ubc skc
  let (p, q) := cross (len ex) (len ey)
  ofDense a b (concatBytes #[gather r.kk.width x keep, gather r.kk.width ua (gather 8 ex p)])
    (concatBytes #[gather s.kk.width y keep, gather s.kk.width ub (gather 8 ey q)])

/-- A family stored as its pairs `(X, x)` sorted key-major, each pair once: the set `X` IS the
    contiguous run of its key, so the key carries q's parted attribute (3). `Order.grade` on the
    key-major `kc·N + vc`, `gatherBytes`. -/
def family (d : Dense) (a b : QAtomicType) : Except String (Rel (.atom a) (.atom b)) := do
  let d := d.nub
  let vc := codes d.vk #[d.val]
  let s := d.rows (Order.grade .i64 false d.n.toUSize (add (mulc (codes d.kk #[d.key]) (len vc)) vc))
  let key ← Arr.ofDense a s.n s.key
  pure ⟨s.n, .arr { key with attr := 3 }, ← Arr.ofDense b s.n s.val⟩

/-- `Λ(R)`: `x Λ(R) X ↔ X = {z | x R z}` — the family of `R`'s fibres, one segment per `x ∈ dom R`. -/
def transpose (R : Rel (.atom a) (.atom b)) : Except String (Rel (.atom a) (.atom b)) := do
  family (← dense R) a b

/-- q's `=x` of a list: each distinct value against the positions holding it, `Order.group`'s
    distinct values and flattened indices, the value key parted. -/
def group (R : Rel (.atom .long) (.atom b)) : Except String (Rel (.atom b) (.atom .long)) := do
  let r ← dense R
  let (_, idx, _) := Order.group r.vk r.n.toUSize r.val
  let key ← Arr.ofDense b (len idx) (gather r.vk.width r.val idx)
  pure ⟨len idx, .arr { key with attr := 3 }, ← Arr.ofDense .long (len idx) (gather 8 r.key idx)⟩

/-- `∋` of a `grp`-keyed family: the pairs `(set id, element)`, the key's offsets reused, no kernel. -/
def mem {k v : Ty} (G : Rel k v) : Except String (Rel (.atom .long) v) :=
  match G with
  | ⟨n, .grp (g := g) _ o wf, val⟩ => pure ⟨n, .grp (.til g) o wf, val⟩
  | _ => throw "∋ reads a grp-keyed family; an arr-keyed family is its own ∋"

/-- `E(R)` of a stored family `G` (pairs `(X, x)`): `Λ(∋ ≫ R)` = the family of `G ≫ R`. -/
def existsImage (G : Rel (.atom a) (.atom b)) (R : Rel (.atom b) (.atom c)) : Except String (Rel (.atom a) (.atom c)) := do
  family (← dense (← comp G R)) a c

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
def pair (R : Rel (.atom a) (.atom b)) (S : Rel (.atom a) (.atom c)) : Except String (Tab (.atom a) (.atom b) (.atom c)) := do
  let r ← dense R; let s ← dense S
  let (rk, sk) := split (codes r.kk #[r.key, s.key]) r.n
  let (i, j) := join rk sk
  let t ← ofDense a b (gather r.kk.width r.key i) (gather r.vk.width r.val i)
  pure ⟨t.n, t.key, t.val, ← Arr.ofDense c t.n (gather s.vk.width s.val j)⟩

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
def prod {d e : QAtomicType} (R : Rel (.atom a) (.atom b)) (S : Rel (.atom d) (.atom e)) :
    Except String (Rel2 (.atom a) (.atom d) (.atom b) (.atom e)) := do
  let r ← dense R; let s ← dense S
  let (i, j) := cross r.n s.n
  let m := r.n * s.n
  pure ⟨m, ← Arr.ofDense a m (gather r.kk.width r.key i), ← Arr.ofDense d m (gather s.kk.width s.key j),
    ← Arr.ofDense b m (gather r.vk.width r.val i), ← Arr.ofDense e m (gather s.vk.width s.val j)⟩

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
  Ew.cmp (if x then Ew.ge else Ew.lt) Ew.i64 Ew.va (tilLongs n.toUSize) (long1 0) n.toUSize

/-- `[R, S]`: the rows of `R` tagged `inl`, of `S` tagged `inr` — `concatBits` of constant bit columns. -/
def junc (R : Rel (.atom a) (.atom c)) (S : Rel (.atom a) (.atom c)) : Except String (SumRel (.atom a) (.atom c)) := do
  let r ← dense R; let s ← dense S
  let m := r.n + s.n
  pure ⟨m, ← Arr.ofBits m (concatBits #[r.n, s.n] #[bitsOf false r.n, bitsOf true s.n]),
    ← Arr.ofDense a m (concatBytes #[r.key, s.key]), ← Arr.ofDense c m (concatBytes #[r.val, s.val])⟩

/-- `inl°` on `U`: `inl x ↦ x`, the tag set to `false`; `inr°` with `true`. -/
def injConv {m : Nat} (tag : Bool) (U : Arr (.atom a) m) : Except String (SumRel (.atom a) (.atom a)) := do
  pure ⟨m, ← Arr.ofBits m (bitsOf tag m), U, U⟩

/-- `F(f)` on a map `f` given as an `Ew` monad: the functor on values, key kept (a `grp` key too). -/
def mapVal {k : Ty} (op : UInt8) (R : Rel k (.atom a)) : Except String (Rel k (.atom a)) := do
  let (vk, v) ← arrDense R.val
  let some nb := nullBits a | throw "a type with no null"
  pure ⟨R.n, R.key, ← Arr.ofDense a R.n (Ew.mon op (cls vk) nb.toInt64 v R.n.toUSize)⟩

/-- `⦇e, f⦈` of a list when `f` is one of `Coc.Over`'s reductions: `overBytes`. -/
def foldOver {k : Ty} (op : Coc.Over) (R : Rel k (.atom .long)) : Except String Int64 := do
  let (_, v) ← arrDense R.val
  pure (overBytes op Ew.i64 nul v)

/-- The same per key: `overGroups` over the key's `groupIds`, one row per distinct key. -/
def foldGroups (op : Coc.Over) (R : Rel (.atom a) (.atom .long)) : Except String (Rel (.atom a) (.atom .long)) := do
  let r ← dense R
  let (gid, firsts) := Order.groupIds r.kk r.n.toUSize r.key
  let ng := len firsts
  ofDense a .long (gather r.kk.width r.key firsts) ((overGroups op Ew.i64 nul ng.toUSize gid r.val).extract 0 (8 * ng))

/-- `α⁻¹` of a list, `uncons`: its first element and the rest, two views (`gatherBytes`, `extract`). -/
def uncons (R : Rel (.atom .long) (.atom a)) : Except String (Rel (.atom .long) (.atom a) × Rel (.atom .long) (.atom a)) := do
  let r ← dense R
  if r.n = 0 then throw "uncons of an empty list"
  let w := r.vk.width
  let m := r.n - 1
  pure (⟨1, .til 1, ← Arr.ofDense a 1 (r.val.extract 0 w)⟩, ⟨m, .til m, ← Arr.ofDense a m (r.val.extract w r.val.size)⟩)

/-- An unfold then a fold: Lean's loop, at most `fuel` rounds of `step` until `done`, each round kernels. -/
def hylo {α : Type} (done : α → Except String Bool) (step : α → Except String α) : Nat → α → Except String α
  | 0, _ => throw "hylo: out of fuel"
  | fuel + 1, x => do if ← done x then pure x else hylo done step fuel (← step x)

/-- `est(≤)` (`desc`: `est(≥)`) of a family of longs: `overGroups` lesser/greater per key. -/
def est (desc : Bool) (G : Rel (.atom a) (.atom .long)) : Except String (Rel (.atom a) (.atom .long)) :=
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
def thinMax (G : Rel (.atom a) (.atom .long)) : Except String (Rel (.atom a) (.atom .long)) := do
  let r ← dense G
  let (gid, firsts) := Order.groupIds r.kk r.n.toUSize r.key
  let p := gradeBy gid [(.i64, false, r.val)]
  let top := gather 8 r.val (gather 8 p (Order.groupLasts (len firsts).toUSize (gather 8 gid p)))
  let t := r.rows (whereEqV r.val (gather 8 top gid))
  ofDense a .long t.key t.val

/-- `thin(Q)` for the two-key Pareto order `(k₁ ≤, k₂ ≤)` on a family with two value columns: the
    rows in key order with `k₁` then `k₂` descending, `Scan.scan maxs` of the group-major rank
    `group·N + rank(k₂)`, a row kept where it beats the prior running max (`Ew.cmp gt`). -/
def thinPareto (T : Tab (.atom a) (.atom .long) (.atom .long)) : Except String (Tab (.atom a) (.atom .long) (.atom .long)) := do
  let (kk, key) ← keyDense T.key
  let (_, k₁) ← arrDense T.fst; let (_, k₂) ← arrDense T.snd
  let n := T.n
  let gid := (Order.groupIds kk n.toUSize key).1
  let p := gradeBy gid [(.i64, true, k₁), (.i64, true, k₂)]
  let c := add (mulc (gather 8 gid p) n) (gather 8 (drank .i64 k₂) p)
  let prior := concatBytes #[long1 nul, (Scan.scan .maxs .i64 n.toUSize c).extract 0 (8 * (n - 1))]
  let keep := gather 8 p (whereBits n.toUSize (Ew.cmp Ew.gt Ew.i64 Ew.vv c prior n.toUSize))
  let m := len keep
  pure ⟨m, .arr (← Arr.ofDense a m (gather kk.width key keep)), ← Arr.ofDense .long m (gather 8 k₁ keep),
    ← Arr.ofDense .long m (gather 8 k₂ keep)⟩

/-- `Entire R` on the universe `U`: `memberVec` of `U` in the keys, all set. -/
def entire {m : Nat} (R : Rel (.atom a) (.atom b)) (U : Arr (.atom a) m) : Except String Bool := do
  let r ← dense R; let (_, u) ← arrDense U
  let (uc, kc) := split (codes r.kk #[u, r.key]) m
  pure (len (whereBits m.toUSize (memberVec 8 false uc kc)) == m)

/-- `Simple R`: in `R` with each pair once, every key distinct (`Order.distinct` count). -/
def simple (R : Rel (.atom a) (.atom b)) : Except String Bool := do
  let r := (← dense R).nub
  pure (len (Order.groupIds r.kk r.n.toUSize r.key).2 == r.n)

def isMap {m : Nat} (R : Rel (.atom a) (.atom b)) (U : Arr (.atom a) m) : Except String Bool := do
  pure ((← entire R U) && (← simple R))

/-- `Injective R` = `Simple R°`. -/
def injective (R : Rel (.atom a) (.atom b)) : Except String Bool := do simple (← conv R)

/-- `Surjective R` = `Entire R°` on the universe `U` of `b`. -/
def surjective {m : Nat} (R : Rel (.atom a) (.atom b)) (U : Arr (.atom b) m) : Except String Bool := do
  entire (← conv R) U

/-! ## Checks against the `toList` specs, on small literal relations -/

section Checks

private def pack (xs : List Int64) : Column := .bytes (xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty)
private abbrev L := Ty.atom .long
private abbrev LL := Rel (.atom .long) (.atom .long)

private def seteq {α : Type} [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains
private def ok {α : Type} (x : Except String α) (p : α → Bool) : Bool := match x with | .ok v => p v | .error _ => false

-- R = {1↦10, 1↦20, 2↦10, 3↦30}, S = {1↦10, 2↦10, 2↦20, 4↦40}
private def R : LL := ⟨4, .arr { c := pack [1, 1, 2, 3], wf := by decide }, { c := pack [10, 20, 10, 30], wf := by decide }⟩
private def S : LL := ⟨4, .arr { c := pack [1, 2, 2, 4], wf := by decide }, { c := pack [10, 10, 20, 40], wf := by decide }⟩
-- T : b ⟶ c, {10↦7, 20↦8, 20↦9}
private def T : LL := ⟨3, .arr { c := pack [10, 20, 20], wf := by decide }, { c := pack [7, 8, 9], wf := by decide }⟩
-- a list (key `til`), with a repeat: (5 3 5 9)
private def Ls : LL := ⟨4, .til 4, { c := pack [5, 3, 5, 9], wf := by decide }⟩
private def Ua : Arr L 4 := { c := pack [1, 2, 3, 4], wf := by decide }
private def Ub : Arr L 4 := { c := pack [10, 20, 30, 40], wf := by decide }
private def Uc : Arr L 3 := { c := pack [7, 8, 9], wf := by decide }

#guard ok (le R S) (· == false)
#guard ok (inter R S) fun X => ok (le X R) id && ok (le X S) id
#guard ok (inter R S) fun X => seteq X.toList (R.toList.filter S.toList.contains)
#guard ok (union R S) fun X => seteq X.toList (R.toList ++ S.toList) && X.n == 6
#guard ok (zero (a := .long) (b := .long)) (·.n == 0)
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
-- `∋` of a grp-keyed family: the parted list `(10 20; 30)` from the core
private def o2 : Arr L 3 := { c := pack [0, 2, 3], wf := by decide }
private def parted : LL := ⟨3, .grp (.til 2) o2 (by decide), { c := pack [10, 20, 30], wf := by decide }⟩
#guard ok (mem parted) fun X => X.toList == [(0, 10), (0, 20), (1, 30)]
#guard ok (keyDense parted.key) fun (_, b) => b == (pack [0, 0, 1] |> fun | .bytes b => b | _ => .empty)
-- `E(R)` of the family `G = {X₁ = {1, 2}, X₂ = {3}}`
private def G : LL := ⟨3, .arr { c := pack [1, 1, 2], wf := by decide }, { c := pack [1, 2, 3], wf := by decide }⟩
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
private def P : Tab L L L := ⟨5, .arr { c := pack [1, 1, 1, 1, 1], wf := by decide },
  { c := pack [1, 3, 2, 3, 1], wf := by decide }, { c := pack [5, 2, 2, 1, 5], wf := by decide }⟩
#guard ok (thinPareto P) fun X => seteq X.toList [(1, 3, 2), (1, 1, 5)] && X.n == 2

private def Ua3 : Arr L 3 := { c := pack [3, 1, 2], wf := by decide }
#guard ok (entire R Ua) (· == false) && ok (entire R Ua3) id
#guard ok (simple R) (· == false) && ok (simple (idU Ua)) id && ok (simple Ls) id
#guard ok (isMap (idU Ua) Ua) id
#guard ok (injective Ls) (· == false) && ok (injective T) id
#guard ok (surjective R Ub) (· == false) && ok (surjective (idU Ub) Ub) id

end Checks

#print axioms idU_holds
#print axioms convArr_holds
#print axioms outl_holds
#print axioms outr_holds

end LeetQ.Rel.Alg
