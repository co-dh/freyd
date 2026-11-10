/-
  Timing of leetq's Rel operators.

  `bench <op> <n> <n> …` runs one operator at each size, ascending: one warm-up, then the median of 5
  runs, printed as `op n ms checksum`. A warm-up over 10 s is printed alone (`1run`) and the larger sizes
  are skipped, since a size ten times larger cannot fit the 60 s budget.

  The data is MINSTD (`x ↦ 48271x mod (2³¹-1)`), one stream per column, seeded by the column's number.
  Each run reads its input from an `IO.Ref` after the first clock read and
  stores its checksum before the second, so the work can be neither hoisted out of the loop nor dropped.
-/
import LeetQ.Rel.Scan
import LeetQ.Rel.Struct
import LeetQ.Rel.Find
import LeetQ.Rel.Norm

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

/-- An `Except` input built before the clock starts, thrown as an `IO` error. -/
def io {α : Type} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-! ## The operators, each with q's expression and checksum -/

/-- A dense `long` column, built before the clock starts. -/
def col (a : Array Int) : ByteArray := LeetQ.Rel.packLongs (a.toList.map Int64.ofInt)

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
  let d ← io "relZipD" do
    let a ← LeetQ.Rel.Alg.longsP (col ((Array.range n).map Int.ofNat)) "relZipD"
    let b ← LeetQ.Rel.Alg.longsP (col (ints n 26 1000)) "relZipD"
    LeetQ.Rel.Alg.ofCols .long .long a b
  let e ← io "relZipD" do
    let a ← LeetQ.Rel.Alg.longsP (col ((Array.range n).map fun i => ((i + n / 2 : Nat) : Int))) "relZipD"
    let b ← LeetQ.Rel.Alg.longsP (col (ints n 27 1000)) "relZipD"
    LeetQ.Rel.Alg.ofCols .long .long a b
  timedE "relZipD" (d, e) fun (d, e) => do let r ← LeetQ.Rel.Ew.dyadic .add .long d e; sumR "relZipD" r.val

/-- The list `x` of longs `foR`-encoded: the haystack `Find.direct` admits. -/
def foRR (n : Nat) (a : Array Int) : Except String (LeetQ.Rel.Arr .long n) := do
  let (md, pk) := QLean.Kernel.Coc.encode 8 (col a)
  LeetQ.Rel.Arr.of .long n (.vector .long n (.foR md pk) none) "foRR"

/-- `x?y`, `x` a `foR` haystack and `y` dense needles, both below 1000; `sum x?y`. -/
def findFoROp (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "findFoR" (foRR n (ints n 26 1000))
  let y ← io "findFoR" (listR n (ints n 27 1000))
  timedE "findFoR" (x, y) fun (x, y) => do sumR "findFoR" (LeetQ.Rel.Find.find x y)

/-- `y in x`, the same operands; `sum y in x`. -/
def inFoROp (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "inFoR" (foRR n (ints n 26 1000))
  let y ← io "inFoR" (listR n (ints n 27 1000))
  timedE "inFoR" (x, y) fun (x, y) => do sumR "inFoR" (LeetQ.Rel.Find.«in» y x)

/-- `?x`, `x` a `foR` column below 1000; `sum ?x`. -/
def distinctFoROp (n : Nat) : IO (IO (Nat × Int64)) := do
  let x ← io "distinctFoR" (foRR n (ints n 26 1000))
  timedE "distinctFoR" x fun x => do sumR "distinctFoR" (LeetQ.Rel.Find.distinct x).2

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

/-- A dense `long` key column. -/
def longKey (a : Array Int) : LeetQ.Rel.Struct.KCol := ⟨.long, _, LeetQ.Rel.Alg.col (a.toList.map Int64.ofInt)⟩

/-- The values `a` (each below `m`) as a key column in the encoding `enc`: `bits` (their parity), `enum` over
    the dictionary `s0 … s(m-1)`, `foR` and dense `long`. -/
def encCol (enc : String) (m : Nat) (a : Array Int) : Except String LeetQ.Rel.Struct.KCol := do
  match enc with
  | "bits" => pure ⟨.boolean, a.size, ← LeetQ.Rel.Arr.of .boolean a.size (.vector .boolean a.size (.bits (oddBits a)) none) "encCol"⟩
  | "enum" =>
    let (blob, dof) := (Array.range m).foldl (init := (ByteArray.empty, #[0])) fun (b, o) i =>
      let b := (b ++ s!"s{i}".toUTF8).push 0
      (b, o.push b.size)
    let w := QLean.Column.idWidth dof
    let (ids, bad) := QLean.Kernel.enumIds a.size.toUSize m.toUSize 0 w.toUSize (col a)
    if bad.toNat != a.size then throw s!"encCol enum: value at {bad} is outside 0..{m}"
    pure ⟨.symbol, a.size, ← LeetQ.Rel.Arr.of .symbol a.size (.vector .symbol a.size (.enum blob dof ids) none) "encCol"⟩
  | "foR" => let (md, pk) := QLean.Kernel.Coc.encode 8 (col a); pure ⟨.long, a.size, ← LeetQ.Rel.Arr.of .long a.size (.vector .long a.size (.foR md pk) none) "encCol"⟩
  | "dense" => pure (longKey a)
  | e => throw s!"encCol: no encoding {e}"

/-- The key range each encoding is benched at: two bits, a hundred symbols, a thousand-wide FoR range, a
    million dense longs. -/
def encRange : String → Nat | "bits" => 2 | "enum" => 100 | "foR" => 1000 | _ => 1000000

/-- `|R|` of `R` whose key and value are both in `enc`: the distinct pairs (`Cols.nub`); their count. -/
def relCardOp (enc : String) (n : Nat) : IO (IO (Nat × Int64)) := do
  let m := encRange enc
  let ⟨t, k⟩ ← io "relCard" (encCol enc m (ints n 28 m))
  let ⟨u, v⟩ ← io "relCard" (encCol enc m (ints n 29 m))
  if h : u = t then
    let R ← io "relCard" (LeetQ.Rel.Alg.ofCols t t k (h ▸ v))
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

open LeetQ.Rel.Prog in
/-- `progAj` with the miss branch's `E` over a second copy of the four lists, loaded again so the copies are distinct
    objects: `missRule`'s `sameArr` runs its index loop (`eqAt`), not the pointer test. Checksum as `progAj`'s. -/
def progAjCopyOp (n : Nat) : IO (IO (Nat × Int64)) := do
  let (lk, lt, rk, rt) := asofData n
  let ld (a : Array Int) : IO (LeetQ.Rel.Arr .long n) :=
    io "progAjCopy" (LeetQ.Rel.Arr.ofPart .long n (LeetQ.Rel.Alg.longs (col a)) "progAjCopy")
  timedE "progAjCopy" (← ld lk, ← ld lt, ← ld rk, ← ld rt, ← ld lk, ← ld lt, ← ld rk, ← ld rt)
    fun (lk, lt, rk, rt, lk', lt', rk', rt') => do
    let E (lk lt rk rt : LeetQ.Rel.Arr .long n) : LeetQ.Rel.Prog .long .long :=
      extr true (inter (comp (arr lk) (conv (arr rk))) (ojoin .ge (arr lt) (arr rt)))
    let P : LeetQ.Rel.Prog .long .long := union (comp (til n) (E lk lt rk rt))
      (comp (anti (til n) (dom (E lk' lt' rk' rt'))) (fn (.cst (u := .long) Int64.minValue)))
    sumR "progAjCopy" (← exec P).val

/-- A key and a value column for `progSel`/`relSel`: `n` longs below 1e6, half the keys past the cut `5e5`. -/
def selData (what : String) (n : Nat) : IO (LeetQ.Rel.Arr .long n × LeetQ.Rel.Arr .long n) := do
  let arr (a : Array Int) : IO (LeetQ.Rel.Arr .long n) := io what (LeetQ.Rel.Arr.ofPart .long n (LeetQ.Rel.Alg.longs (col a)) what)
  pure (← arr (ints n 12 1000000), ← arr (ints n 13 1000000))

/-- `(>a)? R` as a `Prog` term through `Prog.exec`: the key column tested, key and value picked. Checksum: the
    picked values' sum, as `relSel`'s. -/
def progSelOp (n : Nat) : IO (IO (Nat × Int64)) := do
  timedE "progSel" (← selData "progSel" n) fun (k, v) => do
    let R : LeetQ.Rel.Rel .long .long := ⟨n, k, v⟩
    sumR "progSel" (← LeetQ.Rel.Prog.exec (LeetQ.Rel.Prog.selKey (B := .long) 500000 (.rel R))).val

/-- `(×2)° (×2) R` through `Prog.exec`: the even keys by the `lowZero` kernel, key and value picked. Checksum: the
    picked values' sum. -/
def progEvenOp (n : Nat) : IO (IO (Nat × Int64)) := do
  timedE "progEven" (← selData "progEven" n) fun (k, v) => do
    let R : LeetQ.Rel.Rel .long .long := ⟨n, k, v⟩
    sumR "progEven" (← LeetQ.Rel.Prog.exec (LeetQ.Rel.Prog.evens (B := .long) (.rel R))).val

/-- `(>a)? R` by hand: `Ew.atomVal`, `Find.where`, two picks, q's `(where k>a)` on key and value. -/
def relSelOp (n : Nat) : IO (IO (Nat × Int64)) := do
  timedE "relSel" (← selData "relSel" n) fun (k, v) => do
    let w := LeetQ.Rel.Find.where (← LeetQ.Rel.Ew.atomVal (t := .long) .lt .boolean (500000 : Int64) k)
    let (_, i) ← LeetQ.Rel.Alg.arrDense w.2
    let _ ← LeetQ.Rel.Vals.ofParts (.atom .long) w.1 (LeetQ.Rel.Alg.pick .long ⟨_, k⟩ i) "relSel"
    sumR "relSel" (← LeetQ.Rel.Vals.ofParts (.atom .long) w.1 (LeetQ.Rel.Alg.pick .long ⟨_, v⟩ i) "relSel")

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
  [("relAj", relAjOp), ("progAj", progAjOp), ("progAjCopy", progAjCopyOp),("progSel", progSelOp), ("progEven", progEvenOp), ("relSel", relSelOp), ("relWj", relWjOp),
   ("sums", sumsOp),
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
