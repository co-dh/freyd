/-
  Timing of leetq's RelRep q operators against real q (`q/bench.q`, the same data and the same checksum).

  `bench <op> <n> <n> …` runs one operator at each size, ascending: one warm-up, then the median of 5
  runs, printed as `op n ms checksum`. A warm-up over 10 s is printed alone (`1run`) and the larger sizes
  are skipped, since a size ten times larger cannot fit the 60 s budget.

  The data is MINSTD (`x ↦ 48271x mod (2³¹-1)`), one stream per column, seeded by the column's number,
  exactly as `gen` in `q/bench.q`. Each run reads its input from an `IO.Ref` after the first clock read and
  stores its checksum before the second, so the work can be neither hoisted out of the loop nor dropped.
-/
import LeetQ.Q.Table
import LeetQ.QRel
import LeetQ.Compressed
import LeetQ.Long
import LeetQ.Rel.Scan
import LeetQ.Rel.Struct
import LeetQ.Rel.Find
import LeetQ.Rel.Norm

open Freyd.Alg.RelSet LeetQ LeetQ.Q

namespace Bench

def M : Nat := 2147483647

/-- `cnt` MINSTD values after `seed`: q's `1_ cnt {(48271*x) mod M}\ seed`. -/
def gen (cnt seed : Nat) : Array Nat := Id.run do
  let mut x := seed
  let mut a := Array.mkEmpty cnt
  for _ in [0:cnt] do
    x := 48271 * x % M
    a := a.push x
  return a

/-- q's `gen[cnt;seed] mod m`. -/
def ints (cnt seed m : Nat) : Array Int := (gen cnt seed).map fun x => ((x % m : Nat) : Int)

/-- Through `Array.zip`: the compiled `List.zip` takes one stack frame per pair. -/
def zipL {β : Type} (a : Array Int) (b : Array β) : List (Int × β) := (a.zip b).toList

/-- q's `a!b`. -/
def fin (a b : Array Int) : FinRel Int Int := FinRel.ofList (zipL a b)

/-- Wrapping 64-bit sum, like q's long `sum`: a bignum `Int` accumulator would allocate once past 2^31. -/
@[inline] def sumBy {α : Type} (f : α → Int64) (xs : Array α) : Int64 := xs.foldl (fun s x => s + f x) 0

/-- One timed run of `f` on `d`: nanoseconds and the checksum; an `error` from `f` is thrown. -/
def timedE {α : Type} (name : String) (d : α) (f : α → Except String Int64) : IO (IO (Nat × Int64)) := do
  let r ← IO.mkRef d
  let out ← IO.mkRef (none : Option (Except String Int64))
  pure do
    let t0 ← IO.monoNanosNow
    let x ← r.get
    out.set (some (f x))
    let t1 ← IO.monoNanosNow
    match ← out.get with
    | some (.ok c) => pure (t1 - t0, c)
    | some (.error e) => throw (IO.userError s!"{name}: {e}")
    | none => throw (IO.userError s!"{name}: no answer was stored")

/-- `timedE` for an `f` that answers `none` when the result is not held as pairs. -/
def timed {α : Type} (name : String) (d : α) (f : α → Option Int64) : IO (IO (Nat × Int64)) :=
  timedE name d fun x => match f x with
    | some c => .ok c
    | none => .error "the answer is not held as pairs (fin? answered none)"

/-- An `Except` input built before the clock starts, thrown as an `IO` error. -/
def io {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-! ## The operators, each with q's expression and checksum -/

/-- A dense `long` column, built before the clock starts. -/
def col (a : Array Int) : ByteArray := enc 8 (a.toList.map Int64.ofInt)

/-- q's `sum` of a dense `long` column, `0N` skipped: `overBytes .add`. -/
def colSum (b : ByteArray) : Int64 := Compressed.Col.sum Compressed.nul (.dense 8 b)

/-- `d@ks` by `Long.getAll`, `findVec` then `gatherBytes`; `sum d@ks` (q's `sum` skips `0N`). -/
def getAllOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "getAll" (col (ints n 1 n), col (ints n 2 1000000), col (ints n 3 (2 * n)))
    fun (k, v, ks) => some (colSum (Long.getAll k v ks))

/-- `d+e` by `Long.zipD`, `findVec`, `gatherBytes`, `Ew.val`, `memberVec`, `whereBits`; `(sum key r)+sum value r`,
`d`'s keys being `r`'s first rows. -/
def zipDOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let dk := col (ints n 1 n)
  timed "zipD" (dk, col (ints n 2 1000000), col (ints n 4 n), col (ints n 5 1000000), colSum dk)
    fun (dk, dv, ek, ev, sk) => let z := Long.zipD dk dv ek ev
      some (sk + colSum z.1 + colSum z.2.1 + colSum z.2.2)

/-- `select sum v by k from t` by `Compressed.selbySum`, `groupIds` then `overGroups`; `exec sum k+v`. -/
def selbyOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "selby" (Keys.ofList false ((ints n 6 1000).toList.map Int64.ofInt),
      Keys.ofList false ((ints n 7 1000000).toList.map Int64.ofInt))
    fun (k, v) => some ((Compressed.selbySum Compressed.nul k v).foldl (fun s p => s + p.1 + p.2) 0)

/-- `t ij kt` by `Long.ij`, `memberVec`, `whereBits`, `findVec`, `gatherBytes`; `kt` of `n/10` keys;
`exec sum v+w`, `v` read at the kept rows by `Long.aIdx`. -/
def ijOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let m := max 1 (n / 10)
  timed "ij" (col (ints n 8 m), col (ints n 11 1000000), col (ints m 9 m), col (ints m 10 1000000))
    fun (tk, tv, kk, kv) => let p := Long.ij tk kk kv; some (colSum (Long.aIdx tv p.1) + colSum p.2)

/-- ``aj[`s`tm;tr;qr]``, `qr` sorted by time (stably, as `` `tm xasc``); `exec sum p` (`0N` skipped). -/
def ajOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let qr := (zipL (ints n 14 100) ((ints n 15 1000000).zip (ints n 16 1000000))).mergeSort
    fun a b => decide (a.2.1 ≤ b.2.1)
  timed "aj" (tab ((ints n 12 100).zip (ints n 13 1000000)), tab qr.toArray)
    fun (T, U) => ((aj Prod.fst Prod.snd Prod.fst Prod.snd T U).bind rows).map (sumBy (fun p => Int64.ofInt (p.2.getD 0)))

/-- `wj` over `aj`'s tables, the window `(tm-100, tm]` and the row prevailing at `tm-100`. -/
def wjOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let qr := (zipL (ints n 14 100) ((ints n 15 1000000).zip (ints n 16 1000000))).mergeSort
    fun a b => decide (a.2.1 ≤ b.2.1)
  timed "wj" (tab ((ints n 12 100).zip (ints n 13 1000000)), tab qr.toArray)
    fun (T, U) => ((wj (-100) 0 Prod.fst Prod.snd Prod.fst Prod.snd T U).bind rows).map (sumBy (fun p => Int64.ofInt p.2))

/-- Key `gen 17 mod n`, value `gen 18 mod 1e6`, sorted by key stably (q's `iasc`). -/
def sortedPairs (n : Nat) : List (Int64 × Int64) :=
  (((gen n 17).zip (gen n 18)).toList.map fun (a, b) => (Int64.ofNat (a % n), Int64.ofNat (b % 1000000))).mergeSort
    QSortedRel.keyLE

def needles (n : Nat) : Array Int64 := (gen n 19).map fun x => Int64.ofNat (x % n)

/-- Every needle's run, `v raze lo+til each 1+hi-lo` with `lo:k binr xs; hi:k bin xs`; `sum`. -/
def lookups (s : QSortedRel Int64) (xs : Array Int64) : Option Int64 :=
  some (xs.foldl (fun a k => (s.lookup k).foldl (fun a x => a + x) a) 0)

/-- `QSortedRel.lookup` on a dense `long` key column. -/
def lookupDenseOp (n : Nat) : IO (IO (Nat × Int64)) := do
  let l := sortedPairs n
  let some s := QSortedRel.ofBytes? (enc 8 (l.map Prod.fst)) (enc 8 (l.map Prod.snd))
    | throw (IO.userError s!"lookupDense {n}: ofBytes? refused the sorted key column")
  timed "lookupDense" (s, needles n) fun (s, xs) => lookups s xs

/-- `QSortedRel.lookup` on the same keys Frame-of-Reference encoded; q has no in-memory FoR, so its
    side is the dense lookup again. -/
def lookupFoROp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "lookupFoR" (QSortedRel.ofList (sortedPairs n) dense true, needles n) fun (s, xs) => lookups s xs

/-! ## Compute on compressed columns

`LeetQ.Compressed` on a value column `v` (column 21, `mod 1000`: dense at 2 bytes, or FoR with small
residuals), a bit column `b` (column 23, `mod 2`) and a key column `k` (column 22, `mod 1000`); q's side
is `sum v`, `sum v where b`, `select sum v by k from t` in `q/bench.q`. -/

def nul : Int64 := Int64.minValue

def vcol (n : Nat) (seed : Nat) : List Int64 := (gen n seed).toList.map fun x => Int64.ofNat (x % 1000)

/-- q's `1=gen[n;23] mod 2`, one bit per row, least significant bit first. -/
def bitsOf (n : Nat) : ByteArray := Id.run do
  let g := gen n 23
  let mut b := ByteArray.emptyWithCapacity ((n + 7) / 8)
  for j in [0:(n + 7) / 8] do
    let mut byte : UInt8 := 0
    for t in [0:8] do
      if 8 * j + t < n && g[8 * j + t]! % 2 == 1 then byte := byte ||| (1 <<< t.toUInt8)
    b := b.push byte
  return b

def sumColOp (name : String) (foR : Bool) (n : Nat) : IO (IO (Nat × Int64)) :=
  timed name (Keys.ofList foR (vcol n 21)) fun v => some (Compressed.Col.sum nul v)

def sumDenseOp := sumColOp "sumDense" false
def sumFoROp := sumColOp "sumFoR" true

/-- The `.pairs` path: `Q.Agg.sum` of `ql(vs)`. -/
def sumPairsOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "sumPairs" (Q.Agg.ql ((vcol n 21).map Int64.toInt).toArray) fun D => (Q.Agg.sum D).bind (·.head?.map Int64.ofInt)

def sumWhereDenseOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "sumWhereDense" (bitsOf n, Keys.ofList false (vcol n 21))
    fun (b, v) => some (Compressed.sumWhere nul n.toUSize b v)

def selbySumColOp (name : String) (foR : Bool) (n : Nat) : IO (IO (Nat × Int64)) :=
  timed name (Keys.ofList foR (vcol n 22), Keys.ofList foR (vcol n 21))
    fun (k, v) => some ((Compressed.selbySum nul k v).foldl (fun s p => s + p.1 + p.2) 0)

def selbySumDenseOp := selbySumColOp "selbySumDense" false
def selbySumFoROp := selbySumColOp "selbySumFoR" true

/-- `a@ks` by `Long.aIdx`, `gatherBytes`; `sum a@ks`. -/
def aIdxOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "aIdx" (col (ints n 24 1000000), col ((gen n 25).map fun x => ((x % n : Nat) : Int)))
    fun (a, ks) => some (colSum (Long.aIdx a ks))

/-! ## The RelRep layer (`LeetQ.Rel`): a relation is a key and a value column -/

/-- The list `x` of longs. -/
def listR (n : Nat) (a : Array Int) : Except String (LeetQ.Rel.Arr .long n) :=
  LeetQ.Rel.Arr.ofPart .long n (LeetQ.Rel.Alg.longs (col a)) "listR"

/-- `sum` of a list: `Ops.over .add`. -/
def sumR (what : String) {t : QLean.QAtomicType} {m : Nat} (r : LeetQ.Rel.Arr t m) : Except String Int64 :=
  match LeetQ.Rel.Ops.over .add r with
  | some c => .ok c
  | none => .error s!"{what}: Ops.over .add answered none"

/-- `scan` of `x`, then its sum. -/
def scanOp (name : String) (f : QLean.Prim.Dyadic) (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io name (listR n (ints n 26 1000))
  timedE name x fun x => do
    let some r := LeetQ.Rel.Ops.scan f .long x | .error s!"{name}: Ops.scan answered none"
    sumR name r

/-- `sums x` by `Ops.scan .add`; `sum sums x`. -/
def sumsOp := scanOp "sums" .add

/-- `mins x` by `Ops.scan .lesser`; `sum mins x`. -/
def minsOp := scanOp "mins" .lesser

/-- `w mop x` by `Ops.mwin`; `sum w mop x`. -/
def mwinOp (name : String) (op : QLean.Kernel.Scan.MOp) (w n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io name (listR n (ints n 26 1000))
  timedE name x fun x => do
    let some r := LeetQ.Rel.Ops.mwin op w .long x | .error s!"{name}: Ops.mwin answered none"
    sumR name r

/-- `10 msum x`; `sum 10 msum x`. -/
def msumOp := mwinOp "msum" .msum 10

/-- `w mmin x`; `sum w mmin x`. -/
def mminOp (w : Nat) := mwinOp "mmin" .mmin w

/-- `x + y` pointwise by `Ew.zip .add` on two lists: one `Ew.val`; `sum x + y`. -/
def relEach2Op (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "relEach2" (listR n (ints n 26 1000))
  let y ← io "relEach2" (listR n (ints n 27 1000))
  timedE "relEach2" (x, y) fun (x, y) => do sumR "relEach2" (← LeetQ.Rel.Ew.zip .add .long x y)

/-- `d + e` on keys by `Ew.dyadic .add` over explicit key columns, the key sets overlapping by half: `Ew.align`;
    `sum d + e`. -/
def relZipDOp (n : Nat) : IO (IO (Nat × Int64)) := do
  let d ← io "relZipD" (LeetQ.Rel.Alg.ofCols .long .long (LeetQ.Rel.Alg.longs <| col ((Array.range n).map Int.ofNat)) (LeetQ.Rel.Alg.longs <| col (ints n 26 1000)))
  let e ← io "relZipD" (LeetQ.Rel.Alg.ofCols .long .long (LeetQ.Rel.Alg.longs <| col ((Array.range n).map fun i => ((i + n / 2 : Nat) : Int)))
    (LeetQ.Rel.Alg.longs <| col (ints n 27 1000)))
  timedE "relZipD" (d, e) fun (d, e) => do let r ← LeetQ.Rel.Ew.dyadic .add .long d e; sumR "relZipD" r.val

/-- The list `x` of longs `foR`-encoded: the haystack `Find.direct` admits. -/
def foRR (n : Nat) (a : Array Int) : Except String (LeetQ.Rel.Arr .long n) := do
  let (md, pk) := QLean.Kernel.Coc.encode 8 (col a)
  LeetQ.Rel.Arr.of .long n (.vector .long n (.foR md pk) none) "foRR"

/-- `x?y`, `x` a `foR` haystack and `y` dense needles, both below 1000; `sum x?y`. -/
def findFoROp (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "findFoR" (foRR n (ints n 26 1000))
  let y ← io "findFoR" (listR n (ints n 27 1000))
  timedE "findFoR" (x, y) fun (x, y) => do sumR "findFoR" (← LeetQ.Rel.Find.find x y)

/-- `y in x`, the same operands; `sum y in x`. -/
def inFoROp (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "inFoR" (foRR n (ints n 26 1000))
  let y ← io "inFoR" (listR n (ints n 27 1000))
  timedE "inFoR" (x, y) fun (x, y) => do sumR "inFoR" (← LeetQ.Rel.Find.«in» y x)

/-- `?x`, `x` a `foR` column below 1000; `sum ?x`. -/
def distinctFoROp (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "distinctFoR" (foRR n (ints n 26 1000))
  timedE "distinctFoR" x fun x => do sumR "distinctFoR" (← LeetQ.Rel.Find.distinct x).2

/-! ## The relation algebra's codes: `|R|` and `ej` on keys of each encoding -/

/-- One bit per element of `a`, `1` where it is odd, least significant bit first. -/
def oddBits (a : Array Int) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity ((a.size + 7) / 8)
  for j in [0:(a.size + 7) / 8] do
    let mut byte : UInt8 := 0
    for t in [0:8] do
      if 8 * j + t < a.size && a[8 * j + t]! % 2 == 1 then byte := byte ||| (1 <<< t.toUInt8)
    b := b.push byte
  return b

/-- The values `a` (each below `m`) as a key column in the encoding `enc`: `bits` (their parity), `enum` over
    the dictionary `s0 … s(m-1)`, `foR` and dense `long`. -/
def encCol (enc : String) (m : Nat) (a : Array Int) : Except String LeetQ.Rel.Struct.KCol := do
  match enc with
  | "bits" => pure (.boolean, (a.size, .bits (oddBits a)))
  | "enum" =>
    let (blob, dof) := (Array.range m).foldl (init := (ByteArray.empty, #[0])) fun (b, o) i =>
      let b := (b ++ s!"s{i}".toUTF8).push 0
      (b, o.push b.size)
    let w := QLean.Column.idWidth dof
    let (ids, bad) := QLean.Kernel.enumIds a.size.toUSize m.toUSize 0 w.toUSize (col a)
    if bad.toNat != a.size then throw s!"encCol enum: value at {bad} is outside 0..{m}"
    pure (.symbol, (a.size, .enum blob dof ids))
  | "foR" => let (md, pk) := QLean.Kernel.Coc.encode 8 (col a); pure (.long, (a.size, .foR md pk))
  | "dense" => pure ⟨.long, LeetQ.Rel.Alg.longs (col a)⟩
  | e => throw s!"encCol: no encoding {e}"

/-- The key range each encoding is benched at: two bits, a hundred symbols, a thousand-wide FoR range, a
    million dense longs. -/
def encRange : String → Nat | "bits" => 2 | "enum" => 100 | "foR" => 1000 | _ => 1000000

/-- `|R|` of `R` whose key and value are both in `enc`: the distinct pairs (`Cols.nub`); their count. -/
def relCardOp (enc : String) (n : Nat) : IO (IO (Nat × Int64)) := do
  let m := encRange enc
  let ⟨t, k⟩ ← io "relCard" (encCol enc m (ints n 28 m))
  let ⟨u, v⟩ ← io "relCard" (encCol enc m (ints n 29 m))
  if u = t then
    let R ← io "relCard" (LeetQ.Rel.Alg.ofCols t t k v)
    timedE s!"relCard {enc}" R fun R => do pure (Int64.ofNat (← (← LeetQ.Rel.Alg.cols R).nub).n)
  else throw (IO.userError "relCard: key and value differ in type")

/-- `ej` of `n` left keys in `enc` against the `m` keys `til m`, each once: `n` matches; the sum of the right rows. -/
def relJoinOp (enc : String) (n : Nat) : IO (IO (Nat × Int64)) := do
  let m := encRange enc
  let l ← io "relJoin" (encCol enc m (ints n 30 m))
  let r ← io "relJoin" (encCol enc m ((Array.range m).map Int.ofNat))
  timedE s!"relJoin {enc}" (l, r) fun (l, r) => do let j ← LeetQ.Rel.Struct.ej #[l] #[r]; sumR "relJoin" j.val

/-- `ej` on a two-column key tuple in `enc`: `n` left tuples against `m` right ones, both drawn from the
    range; the sum of the right rows. -/
def relJoin2Op (enc : String) (n : Nat) : IO (IO (Nat × Int64)) := do
  let m := encRange enc
  let l₁ ← io "relJoin2" (encCol enc m (ints n 30 m))
  let l₂ ← io "relJoin2" (encCol enc m (ints n 31 m))
  let r₁ ← io "relJoin2" (encCol enc m ((Array.range m).map Int.ofNat))
  let r₂ ← io "relJoin2" (encCol enc m (ints m 32 m))
  timedE s!"relJoin2 {enc}" (l₁, l₂, r₁, r₂) fun (l₁, l₂, r₁, r₂) => do
    let j ← LeetQ.Rel.Struct.ej #[l₁, l₂] #[r₁, r₂]; sumR "relJoin2" j.val

/-- `aj`/`wj` input: `n` left rows (key below 1000, time below 1e6) and `n` right rows sorted by key then time
    (q's `` `p#s `` quote layout, which `wj` requires): left keys, left times, right keys, right times. -/
def asofData (n : Nat) : Array Int × Array Int × Array Int × Array Int :=
  let r := ((ints n 14 1000).zip (ints n 15 1000000)).toList.mergeSort fun a b => decide (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2)
  (ints n 12 1000, ints n 13 1000000, (r.map (·.1)).toArray, (r.map (·.2)).toArray)

/-- A dense `long` key column. -/
def longKey (a : Array Int) : LeetQ.Rel.Struct.KCol := ⟨.long, LeetQ.Rel.Alg.longs (col a)⟩

/-- ``aj[`s`tm;t;q]`` by `Struct.aj` over `asofData`, 1e3 key groups; the sum of the matched right rows. -/
def relAjOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let (lk, lt, rk, rt) := asofData n
  timedE "relAj" (longKey lk, longKey lt, longKey rk, longKey rt) fun (lk, lt, rk, rt) => do
    sumR "relAj" (← LeetQ.Rel.Struct.aj #[lk] #[rk] lt rt).2

/-- `aj` as a `Prog` term executed through `norm` (`Prog.exec`), its order join rewritten to `ajJ` (R7) and its
    `miss` to that one `ajJ` (`missRule`), over `relAj`'s data; the checksum must be `relAj`'s. -/
def progAjOp (n : Nat) : IO (IO (Nat × Int64)) := do
  let (lk, lt, rk, rt) := asofData n
  let arr (a : Array Int) : IO (LeetQ.Rel.Arr .long n) :=
    io "progAj" (LeetQ.Rel.Arr.ofPart .long n (LeetQ.Rel.Alg.longs (col a)) "progAj")
  timedE "progAj" (← arr lk, ← arr lt, ← arr rk, ← arr rt) fun (lk, lt, rk, rt) => do
    sumR "progAj" (← LeetQ.Rel.Prog.exec (LeetQ.Rel.Prog.aj lk lt rk rt)).val

/-- `wj` by `Struct.wj` over `asofData`, the window `[tm-100, tm]` with the prevailing row; the sum of the rows. -/
def relWjOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let (lk, lt, rk, rt) := asofData n
  timedE "relWj" (longKey (lt.map (· - 100)), longKey lt, longKey lk, longKey rk, longKey rt,
      longKey ((Array.range rt.size).map Int.ofNat)) fun (w, lt, lk, rk, rt, c) => do
    let ⟨_, _, s⟩ ← LeetQ.Rel.Struct.wjBy .add true w lt #[lk] #[rk] rt c
    sumR "relWj" s

def ops : List (String × (Nat → IO (IO (Nat × Int64)))) :=
  ["bits", "enum", "foR", "dense"].flatMap (fun e =>
    [(s!"relCard-{e}", relCardOp e), (s!"relJoin-{e}", relJoinOp e), (s!"relJoin2-{e}", relJoin2Op e)]) ++
  [("getAll", getAllOp), ("zipD", zipDOp), ("selby", selbyOp), ("ij", ijOp), ("aj", ajOp), ("wj", wjOp), ("relAj", relAjOp), ("progAj", progAjOp), ("relWj", relWjOp),
   ("lookupDense", lookupDenseOp), ("lookupFoR", lookupFoROp),
   ("sumDense", sumDenseOp), ("sumFoR", sumFoROp), ("sumPairs", sumPairsOp), ("sumWhereDense", sumWhereDenseOp),
   ("selbySumDense", selbySumDenseOp), ("selbySumFoR", selbySumFoROp), ("aIdx", aIdxOp), ("sums", sumsOp),
   ("mins", minsOp), ("msum", msumOp), ("mmin", mminOp 10), ("mmin1000", mminOp 1000),
   ("relEach2", relEach2Op), ("relZipD", relZipDOp),
   ("findFoR", findFoROp), ("inFoR", inFoROp), ("distinctFoR", distinctFoROp)]

/-- Nanoseconds as milliseconds with three decimals. -/
def ms (t : Nat) : String :=
  let f := toString (t % 1000000 / 1000)
  s!"{t / 1000000}.{"".pushn '0' (3 - f.length)}{f}"

def median (ts : List Nat) : Nat := (ts.mergeSort (· ≤ ·))[ts.length / 2]!

end Bench

open Bench in
def main (args : List String) : IO UInt32 := do
  let name :: sizes := args
    | throw (IO.userError s!"usage: bench <op> <n>…; ops: {ops.map (·.1)}")
  let some (_, op) := ops.find? (·.1 == name)
    | throw (IO.userError s!"unknown op {name}; ops: {ops.map (·.1)}")
  for s in sizes do
    let some n := s.toNat? | throw (IO.userError s!"size {s} is not a natural number")
    let run ← op n
    let (w, c0) ← run
    if w > 10000000000 then
      IO.println s!"{name} {n} {ms w} {c0.toInt} 1run; larger sizes skipped"
      return 0
    let mut ts := []
    for _ in [0:5] do
      let (t, c) ← run
      if c != c0 then throw (IO.userError s!"{name} {n}: checksum {c.toInt} differs from the warm-up's {c0.toInt}")
      ts := t :: ts
    IO.println s!"{name} {n} {ms (median ts)} {c0.toInt}"
    (← IO.getStdout).flush
  return 0
