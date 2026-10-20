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

def zipL {β : Type} (a : Array Int) (b : Array β) : List (Int × β) := a.toList.zip b.toList

/-- q's `a!b`. -/
def fin (a b : Array Int) : FinRel Int Int := FinRel.ofList (zipL a b)

def sumBy {α : Type} (f : α → Int) (xs : List α) : Int := xs.foldl (fun s x => s + f x) 0

/-- One timed run of `f` on `d`: nanoseconds and the checksum; `none` from `f` is an error. -/
def timed {α : Type} (name : String) (d : α) (f : α → Option Int) : IO (IO (Nat × Int)) := do
  let r ← IO.mkRef d
  let out ← IO.mkRef (none : Option Int)
  pure do
    let t0 ← IO.monoNanosNow
    let x ← r.get
    out.set (f x)
    let t1 ← IO.monoNanosNow
    let some c ← out.get | throw (IO.userError s!"{name}: the operator answered none (a test where pairs were expected)")
    pure (t1 - t0, c)

/-! ## The operators, each with q's expression and checksum -/

/-- `d@ks`; `sum d@ks` (q's `sum` skips `0N`). -/
def getAllOp (n : Nat) : IO (IO (Nat × Int)) :=
  timed "getAll" (RelRep.pairs (fin (ints n 1 n) (ints n 2 1000000)), (ints n 3 (2 * n)).toList)
    fun (D, ks) => (rows (getAll D ks)).map (sumBy (·.getD 0))

/-- `d+e`; `(sum key r)+sum value r`. -/
def zipDOp (n : Nat) : IO (IO (Nat × Int)) :=
  timed "zipD" (fin (ints n 1 n) (ints n 2 1000000), fin (ints n 4 n) (ints n 5 1000000))
    fun (r, s) => (ps (zipD (· + ·) 0 r s)).map (sumBy fun p => p.1 + p.2)

/-- `select sum v by k from t`; `exec sum k+v`. -/
def selbyOp (n : Nat) : IO (IO (Nat × Int)) :=
  timed "selby" (tab (zipL (ints n 6 1000) (ints n 7 1000000)))
    fun T => (ps (selby List.sum Prod.fst Prod.snd T)).map (sumBy fun p => p.1 + p.2)

/-- `t ij kt`, `kt` of `n/10` keys; `exec sum v+w`. -/
def ijOp (n : Nat) : IO (IO (Nat × Int)) :=
  let m := max 1 (n / 10)
  timed "ij" (tab (zipL (ints n 8 m) (ints n 11 1000000)), RelRep.pairs (fin (ints m 9 m) (ints m 10 1000000)))
    fun (T, KT) => (rows (ij Prod.fst T KT)).map (sumBy fun p => p.1.2 + p.2)

/-- ``aj[`s`tm;tr;qr]``, `qr` sorted by time (stably, as `` `tm xasc``); `exec sum p` (`0N` skipped). -/
def ajOp (n : Nat) : IO (IO (Nat × Int)) :=
  let qr := (zipL (ints n 14 100) ((ints n 15 1000000).zip (ints n 16 1000000))).mergeSort
    fun a b => decide (a.2.1 ≤ b.2.1)
  timed "aj" (tab (zipL (ints n 12 100) (ints n 13 1000000)), tab qr)
    fun (T, U) => (rows (aj Prod.fst Prod.snd Prod.fst Prod.snd T U)).map (sumBy (·.2.getD 0))

/-- Key `gen 17 mod n`, value `gen 18 mod 1e6`, sorted by key stably (q's `iasc`). -/
def sortedPairs (n : Nat) : List (Int64 × Int64) :=
  ((gen n 17).toList.zip (gen n 18).toList |>.map fun (a, b) => (Int64.ofNat (a % n), Int64.ofNat (b % 1000000))).mergeSort
    QSortedRel.keyLE

def needles (n : Nat) : Array Int64 := (gen n 19).map fun x => Int64.ofNat (x % n)

/-- Every needle's run, `v raze lo+til each 1+hi-lo` with `lo:k binr xs; hi:k bin xs`; `sum`. -/
def lookups (s : QSortedRel Int64) (xs : Array Int64) : Option Int :=
  some (xs.foldl (fun a k => a + sumBy Int64.toInt (s.lookup k)) 0)

/-- `QSortedRel.lookup` on a dense `long` key column. -/
def lookupDenseOp (n : Nat) : IO (IO (Nat × Int)) := do
  let l := sortedPairs n
  let some s := QSortedRel.ofBytes? (enc 8 (l.map Prod.fst)) (enc 8 (l.map Prod.snd))
    | throw (IO.userError s!"lookupDense {n}: ofBytes? refused the sorted key column")
  timed "lookupDense" (s, needles n) fun (s, xs) => lookups s xs

/-- `QSortedRel.lookup` on the same keys Frame-of-Reference encoded; q has no in-memory FoR, so its
    side is the dense lookup again. -/
def lookupFoROp (n : Nat) : IO (IO (Nat × Int)) :=
  timed "lookupFoR" (QSortedRel.ofList (sortedPairs n) dense true, needles n) fun (s, xs) => lookups s xs

/-! ## Compute on compressed columns

Placeholder for `LeetQ.Compressed` (sum on dense/FoR columns, `where` on bits, sum-where, select sum by),
added once that module is merged. Each op goes into `ops` below with the same shape, and its q side into
`q/bench.q`'s matching section: `sum v`, `sum v where b`, `select sum v by k from t`. -/

def ops : List (String × (Nat → IO (IO (Nat × Int)))) :=
  [("getAll", getAllOp), ("zipD", zipDOp), ("selby", selbyOp), ("ij", ijOp), ("aj", ajOp),
   ("lookupDense", lookupDenseOp), ("lookupFoR", lookupFoROp)]

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
      IO.println s!"{name} {n} {ms w} {c0} 1run; larger sizes skipped"
      return 0
    let mut ts := []
    for _ in [0:5] do
      let (t, c) ← run
      if c != c0 then throw (IO.userError s!"{name} {n}: checksum {c} differs from the warm-up's {c0}")
      ts := t :: ts
    IO.println s!"{name} {n} {ms (median ts)} {c0}"
    (← IO.getStdout).flush
  return 0
