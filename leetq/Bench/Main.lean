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

/-- One timed run of `f` on `d`: nanoseconds and the checksum; `none` from `f` is an error. -/
def timed {α : Type} (name : String) (d : α) (f : α → Option Int64) : IO (IO (Nat × Int64)) := do
  let r ← IO.mkRef d
  let out ← IO.mkRef (none : Option Int64)
  pure do
    let t0 ← IO.monoNanosNow
    let x ← r.get
    out.set (f x)
    let t1 ← IO.monoNanosNow
    let some c ← out.get | throw (IO.userError s!"{name}: the answer is not held as pairs (fin? answered none)")
    pure (t1 - t0, c)

/-! ## The operators, each with q's expression and checksum -/

/-- `d@ks`; `sum d@ks` (q's `sum` skips `0N`). -/
def getAllOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "getAll" (RelRep.pairs (fin (ints n 1 n) (ints n 2 1000000)), ints n 3 (2 * n))
    fun (D, ks) => (fin? (getAll D ks)).map fun r => r.vals.foldl (fun s x => s + Int64.ofInt (x.getD 0)) 0

/-- `d+e`; `(sum key r)+sum value r`. -/
def zipDOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "zipD" (fin (ints n 1 n) (ints n 2 1000000), fin (ints n 4 n) (ints n 5 1000000))
    fun (r, s) => (ps (zipD (· + ·) 0 r s)).map (sumBy fun p => Int64.ofInt p.1 + Int64.ofInt p.2)

/-- `select sum v by k from t`; `exec sum k+v`. -/
def selbyOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "selby" (tab ((ints n 6 1000).zip (ints n 7 1000000)))
    fun T => ((selby List.sum Prod.fst Prod.snd T).bind ps).map (sumBy fun p => Int64.ofInt p.1 + Int64.ofInt p.2)

/-- `t ij kt`, `kt` of `n/10` keys; `exec sum v+w`. -/
def ijOp (n : Nat) : IO (IO (Nat × Int64)) :=
  let m := max 1 (n / 10)
  timed "ij" (tab ((ints n 8 m).zip (ints n 11 1000000)), RelRep.pairs (fin (ints m 9 m) (ints m 10 1000000)))
    fun (T, KT) => (rows (ij Prod.fst T KT)).map (sumBy fun p => Int64.ofInt p.1.2 + Int64.ofInt p.2)

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

/-- `a@ks`, a `vec` then a `vec`: every index in range, so the composite is a `vec`; `sum a@ks`. -/
def aIdxOp (n : Nat) : IO (IO (Nat × Int64)) :=
  timed "aIdx" (ints n 24 1000000, (gen n 25).map (· % n))
    fun (a, ks) => (rows (RelRep.comp (RelRep.vec ks rfl) (RelRep.vec a rfl))).map (sumBy Int64.ofInt)

def ops : List (String × (Nat → IO (IO (Nat × Int64)))) :=
  [("getAll", getAllOp), ("zipD", zipDOp), ("selby", selbyOp), ("ij", ijOp), ("aj", ajOp), ("wj", wjOp),
   ("lookupDense", lookupDenseOp), ("lookupFoR", lookupFoROp),
   ("sumDense", sumDenseOp), ("sumFoR", sumFoROp), ("sumPairs", sumPairsOp), ("sumWhereDense", sumWhereDenseOp),
   ("selbySumDense", selbySumDenseOp), ("selbySumFoR", selbySumFoROp), ("aIdx", aIdxOp)]

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
