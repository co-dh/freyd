/-
  The structural verbs, raze and the symbol verbs on the RelRep core. Each hands its operand columns
  to the qlean dispatcher that owns the encoding: `razeColumn` (`concatBytes`/`concatBits`/
  `concatSyms`/`concatEnum`/`concatFoR`), `takeColumn`/`dropColumn`/`rotateColumn` (one `sliceColumn`
  over `cycleBytes`/`cycleBits`/`cycleIds`/`cycleFoR`), `reverseColumn`, `gatherColumn`, the amend
  pair `amendRounds` + `scatterPacked`, and `likeSyms`/`maskByIds`/`fixedHits` for symbols and chars.
  A list answer is keyed `til m`; an answer per element of an operand keeps that operand's key.
  The specs are List-level, on `toList`.
-/
import LeetQ.Rel.Algebra

namespace LeetQ.Rel.Struct

open QLean QLean.Kernel
open LeetQ.Rel.Find (list onKey vec dense one expand)

/-! ## Concat, take, drop, reverse, rotate: a new list -/

/-- `x,y`: `razeColumn` over the two payloads; a `syms` part meets an `enum` one by interning. -/
def concat {k k' : Ty} {a : QAtomicType} (x : Rel k (.atom a)) (y : Rel k' (.atom a)) :
    Except String (Rel (.atom .long) (.atom a)) := do
  list a (← vec "x,y" a (razeColumn a #[x.val.c, y.val.c]))

/-- `n#x`: `|n|` elements cycling from `takeFrom n (count x)`. -/
def take {k : Ty} {a : QAtomicType} (n : Int) (x : Rel k (.atom a)) : Except String (Rel (.atom .long) (.atom a)) := do
  list a (← vec "n#x" a (takeColumn a x.val.c n))

/-- `n_x`: `|n|` elements off the front (`n ≥ 0`) or the back, clamped. -/
def drop {k : Ty} {a : QAtomicType} (n : Int) (x : Rel k (.atom a)) : Except String (Rel (.atom .long) (.atom a)) := do
  list a (← vec "n_x" a (dropColumn a x.val.c n))

/-- `|x`: `reverseColumn`; a `syms` blob, which it declines (reversing a blob rebuilds it), is
    `x@` the reversed `til n`, `gatherSyms`. -/
def reverse {k : Ty} {a : QAtomicType} (x : Rel k (.atom a)) : Except String (Rel (.atom .long) (.atom a)) := do
  let r := match a, x.val.c with
    | .symbol, .syms .. => gatherColumn a x.val.c (.bytes (reverseBytes 8 (tilLongs x.n.toUSize)))
    | _, _ => reverseColumn a x.val.c
  list a (← vec "|x" a r)

/-- `n rotate x`: a left rotation by `n mod count x`. -/
def rotate {k : Ty} {a : QAtomicType} (n : Int) (x : Rel k (.atom a)) : Except String (Rel (.atom .long) (.atom a)) := do
  list a (← vec "n rotate x" a (rotateColumn a n x.val.c))

/-! ## Index and amend: an answer per element of an operand -/

/-- `x@y` = `y ; x`: `gatherColumn`, the type's null at a miss; on `y`'s key. -/
def index {k k' : Ty} {a : QAtomicType} (x : Rel k (.atom a)) (y : Rel k' (.atom .long)) :
    Except String (Rel k' (.atom a)) := do
  onKey y.key a (← vec "x@y" a (gatherColumn a x.val.c y.val.c)) "x@y"

/-- A column as `scatterPacked` writes it, with its element width in bits: `bits` as it is at `1`, any
    other fixed-width encoding dense (`Find.dense`) at `8·width`. A symbol column has no such payload. -/
def packed (verb : String) (a : QAtomicType) : Column → Except String (ByteArray × Nat)
  | .bits _ b => pure (b, 1)
  | c => do
    let some w := a.width | throw s!"{verb}: a {repr a} column has no fixed-width payload to scatter into"
    pure (← dense verb a c, 8 * w)

/-- `@[x;i;f;y]`, `f` a dyadic verb, or `:` at `none`; on `x`'s key. `amendRounds` checks every index
    against `count x` and, for a verb, splits the indices into rounds holding each index at most once,
    so a round is one `gatherColumn` of the current `x`, one `Ew.dyad` and one `scatterPacked` (q's
    index-by-index application). `Ew.dyad` is `dyadColumn`, so the verb runs at every type pair it is
    defined on whose answer is `x`'s type, nulls by its own rule. Under `:` the scatter keeps the last
    write, so one round is q's answer, and `y` must have `x`'s type (q's 'type otherwise). -/
def amend {k k' k'' : Ty} {a u : QAtomicType} (x : Rel k (.atom a)) (i : Rel k' (.atom .long))
    (op : Option Prim.Dyadic) (y : Rel k'' (.atom u)) : Except String (Rel k (.atom a)) := do
  let verb := "@[x;i;f;y]"
  if i.n ≠ y.n then throw s!"{verb}: {i.n} indices against {y.n} values (q's 'length)"
  let (xb, wb) ← packed verb a x.val.c
  -- the payload back as a column of `x`'s form: `packed` answers width `1` exactly on `bits`
  let col (b : ByteArray) : Column := if wb = 1 then .bits x.n b else .bytes b
  let ib ← dense verb .long i.val.c
  let r := amendRounds x.n.toUSize 8 op.isSome ib
  let word (j : Nat) := Column.bitsAt r (j * 8) 8
  if word 0 == ~~~0 then throw s!"{verb}: index {(word 1).toInt64} outside 0..{x.n} (q's 'length)"
  let step (acc ix : ByteArray) (yv : Column) : Except String ByteArray := do
    let v ← match op with
      | none => if u = a then pure (← packed verb u yv).1 else throw s!"{verb}: `:` of a {repr u} into a {repr a} list (q's 'type)"
      | some v => do
        let cur ← vec verb a (gatherColumn a (col acc) (.bytes ix))
        pure (← packed verb a (← Ew.dyad v Ew.vv a u a cur yv (ix.size / 8)).c).1
    pure (scatterPacked wb.toUSize acc ix v 0 false)
  let rounds := (word 0).toNat
  -- words `2 … 2+rounds-1` count the indices up to each round; the grouped positions follow
  let out ← if rounds ≤ 1 then step xb ib y.val.c else
    rounds.foldM (fun rr _ acc => do
      let lo := if rr == 0 then 0 else (word (1 + rr)).toNat
      let ks := r.extract ((2 + rounds + lo) * 8) ((2 + rounds + (word (2 + rr)).toNat) * 8)
      step acc (gatherBytes 8 0 ib ks) (← vec verb u (gatherColumn u y.val.c (.bytes ks)))) xb
  onKey x.key a (Column.answer a (col out)) verb

/-! ## Parted lists: a key `grp (til g) o` -/

/-- `b + x` on longs. -/
def plus (b : ByteArray) (x : Int64) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.va Alg.nul b (one x.toUInt64) (Alg.len b).toUSize

/-- A parted list over `val`: its `n` rows cut by the long payload `o` (`g+1` offsets) through `KeyCol.grp?`. -/
def parted {v : Ty} {n : Nat} (verb : String) (o : ByteArray) (val : Arr v n) : Except String (Rel (.atom .long) v) := do
  let g := o.size / 8 - 1
  let some key := KeyCol.grp? (.til g) (← Arr.of (.atom .long) (g + 1) (.bytes o) verb) n
    | throw s!"{verb}: the offsets are not ascending cuts of {n} rows (q's 'domain)"
  pure ⟨n, key, val⟩

/-- `o cut x`: the key `grp (til g) (o, n)` over `val`. A first offset `o₀ = 0` leaves `val` untouched (zero
    copy); above `0`, q drops the rows before it: `dropColumn` of `x` and the offsets lowered by `o₀` (`plus`).
    Offsets that are negative or do not ascend within `n` are refused (`KeyCol.grp?`). -/
def cut {k k' : Ty} {a : QAtomicType} (o : Rel k (.atom .long)) (x : Rel k' (.atom a)) :
    Except String (Rel (.atom .long) (.atom a)) := do
  let ob ← dense "o cut x" .long o.val.c
  let o₀ : Int64 := if o.n = 0 then 0 else (Column.bitsAt ob 0 8).toInt64
  if o₀ < 0 || x.n < o₀.toNatClampNeg then throw s!"o cut x: the first offset {o₀} is outside 0..{x.n} (q's 'domain)"
  if o₀ = 0 then return (← parted "o cut x" (concatBytes #[ob, one x.n.toUInt64]) x.val)
  let m := x.n - o₀.toNatClampNeg
  let c ← vec "o cut x" a (dropColumn a x.val.c o₀.toInt)
  parted "o cut x" (concatBytes #[plus ob (-o₀), one m.toUInt64]) (← Arr.of (.atom a) m c "o cut x")

/-- `x f/: y`: `m` runs of `n`, run `j` is `x f y[j]` — `Alg.cross` of the positions, two gathers and ONE
    `Ew.dyad` over all `m·n` pairs, no call per right element; `o := j·n` for `j ≤ m`. -/
def eachRight {k k' : Ty} {t u : QAtomicType} (v : Prim.Dyadic) (rt : QAtomicType) (x : Rel k (.atom t))
    (y : Rel k' (.atom u)) : Except String (Rel (.atom .long) (.atom rt)) := do
  let (j, i) := Alg.cross y.n x.n
  let xs ← vec "x f/:y" t (gatherColumn t x.val.c (.bytes i))
  let ys ← vec "x f/:y" u (gatherColumn u y.val.c (.bytes j))
  parted "x f/:y" (Alg.mulc (tilLongs (y.n + 1).toUSize) x.n) (← Ew.dyad v Ew.vv t u rt xs ys (y.n * x.n))

/-- `+x` of a parted list of `g` runs of one length `m`: `m` runs of `g`. The equal lengths are one
    `matchBytes` of `o` against `j·m`; position `p` of the answer reads `(p mod g)·m + p div g`
    (`Alg.cross`, `Ew.val`, one gather); `o' := j·g`. -/
def flip {a : QAtomicType} (x : Rel (.atom .long) (.atom a)) : Except String (Rel (.atom .long) (.atom a)) :=
  match x with
  | ⟨n, .grp (g := g) _ o _, xv⟩ => do
    let m := if g = 0 then 0 else n / g
    let some ob := KeyCol.longBytes o.c | throw "+x: the offsets have no long payload"
    unless matchBytes 8 false ob (Alg.mulc (tilLongs (g + 1).toUSize) m) do
      throw "+x: the runs differ in length (q's 'length)"
    let (q, r) := Alg.cross m g
    let c ← vec "+x" a (gatherColumn a xv.c (.bytes (Alg.add (Alg.mulc r m) q)))
    parted "+x" (Alg.mulc (tilLongs (m + 1).toUSize) g) (← Arr.of (.atom a) (m * g) c "+x")
  | _ => throw "+x: the operand is not a parted list (q's 'type)"

/-- `x@y` on a parted `x`: the runs `y` selects, a parted list — the run lengths `o[1..] − o[..g]` gathered at
    `y` (`0` outside `0 … g-1`), `Find.expand` of them, one gather of `val` at `o[y[i]] + w`; `o' := 0, sums`. -/
def indexParted {k' : Ty} {a : QAtomicType} (x : Rel (.atom .long) (.atom a)) (y : Rel k' (.atom .long)) :
    Except String (Rel (.atom .long) (.atom a)) :=
  match x with
  | ⟨_, .grp _ o _, xv⟩ => do
    let some ob := KeyCol.longBytes o.c | throw "x@y: the offsets have no long payload"
    let yb ← dense "x@y" .long y.val.c
    let lens := Alg.gather 8 (Alg.sub (ob.extract 8 ob.size) (ob.extract 0 (ob.size - 8))) yb
    let (i, w) := expand lens
    let src := Alg.add (Alg.gather 8 (Alg.gather 8 ob yb) i) w
    let c ← vec "x@y" a (gatherColumn a xv.c (.bytes src))
    parted "x@y" (concatBytes #[one 0, Alg.sums lens]) (← Arr.of (.atom a) (Alg.len src) c "x@y")
  | _ => throw "x@y: the operand is not parted; `index` reads a list"

/-! ## Joins on columns: `|R|` of the key tuples (`Alg.tupleCodes`), then gathers -/

/-- A dense column and the layout it is compared at, as `Alg.arrDense` answers it. -/
abbrev Col := Scan.Kind × ByteArray

/-- A key column in any encoding: its element type and payload, compared only by `Alg.codes`. -/
abbrev KCol := (t : Ty) × Pay t

/-- The key tuples of both sides in one code space (`Alg.codes` per column pair, `Alg.tupleCodes`),
    split at the left's count; both counts. -/
def keyCodes (verb : String) (l r : Array KCol) : Except String (ByteArray × ByteArray × Nat × Nat) := do
  match l[0]?, r[0]? with
  | some (⟨t, a⟩ : KCol), some (⟨u, b⟩ : KCol) =>
    unless l.size == r.size do throw s!"{verb}: {l.size} left key columns against {r.size} right (q's 'length)"
    let cs ← (l.zip r).mapM fun ((p : KCol), (q : KCol)) =>
      if h : q.1 = p.1 then Alg.codes p.1 #[p.2, h ▸ q.2] else throw s!"{verb}: the two sides' key columns differ in type (q's 'type)"
    let nl := Alg.count t a
    let (lc, rc) := Alg.split (Alg.tupleCodes cs) nl
    pure (lc, rc, nl, Alg.count u b)
  | _, _ => throw s!"{verb}: no key column"

/-- `ej`: every pair of a left and a right row with equal key tuples, left row ↦ right row (`Alg.join`). -/
def ej (l r : Array KCol) : Except String (Rel (.atom .long) (.atom .long)) := do
  let (lc, rc, _, _) ← keyCodes "ej" l r
  let (li, ri) := Alg.join lc rc
  Alg.ofCols (.atom .long) (.atom .long) (.bytes li) (.bytes ri)

/-- `ij` against a keyed right side: each left row ↦ the first right row of its key tuple, unmatched rows
    dropped — `findVec`, `Ew.cmp lt` against the miss, `whereBits`, a gather. -/
def ij (l r : Array KCol) : Except String (Rel (.atom .long) (.atom .long)) := do
  let (lc, rc, nl, nr) ← keyCodes "ij" l r
  let hit := findVec 8 false rc lc
  let li := whereBits nl.toUSize (Ew.cmp Ew.lt Ew.i64 Ew.va hit (one nr.toUInt64) nl.toUSize)
  Alg.ofCols (.atom .long) (.atom .long) (.bytes li) (.bytes (Alg.gather 8 hit li))

/-- The right rows graded by `code·T + rank(time)` and the left's tuples' bases `code·T`: the `aj`/`wj` sort.
    `T` bounds both the codes and the joint ranks `rk` (`Alg.drank` of every time column, right's last). -/
def timeGrade (rc lc rr : ByteArray) (T : Nat) : ByteArray × ByteArray × ByteArray :=
  let rk := Alg.add (Alg.mulc rc T) rr
  let p := Order.grade .i64 false (Alg.len rk).toUSize rk
  (p, Alg.gather 8 rk p, Alg.mulc lc T)

/-- `acc` with `vals` written at the positions where `hi > lo` (`Ew.cmp gt`, `whereBits`, `scatterPacked`). -/
def writeWhere (acc lo hi vals : ByteArray) : ByteArray :=
  let n := Alg.len acc
  let ks := whereBits n.toUSize (Ew.cmp Ew.gt Ew.i64 Ew.vv hi lo n.toUSize)
  scatterPacked 64 acc ks (Alg.gather 8 vals ks) 0 false

/-- `aj`: each left row ↦ the right row of its key tuple with the last time at or before its own, `0N` at
    none — `timeGrade`, `binBytes` of the left's `code·T + rank(time)`, kept where it lies above the last
    right row of a lower code (a second `binBytes`), written over `0N` by `writeWhere`. -/
def aj (l r : Array KCol) (lt rt : Col) : Except String (Rel (.atom .long) (.atom .long)) := do
  let (lc, rc, nl, _) ← keyCodes "aj" l r
  unless lt.1 == rt.1 do throw "aj: the two time columns differ in type (q's 'type)"
  let (lr, rr) := Alg.split (Alg.drank lt.1 (concatBytes #[lt.2, rt.2])) nl
  let (p, srt, base) := timeGrade rc lc rr (Alg.len (concatBytes #[lc, rc]))
  let bin := binBytes 8 false true false srt
  let pos := bin (Alg.add base lr)
  let ri := writeWhere (expandBytes 8 0 (one Alg.nul.toUInt64) (one nl.toUInt64)) (bin (plus base (-1))) pos (Alg.gather 8 p pos)
  pure ⟨nl, .til nl, ← Arr.of (.atom .long) nl (.bytes ri) "aj"⟩

/-- `wj`: each left row ↦ the right rows of its key tuple with a time in `[w₀, w₁]`, in time order, a parted
    list — `timeGrade`, `binBytes` of each window's ends, `Find.expand` of the lengths. `prevailing` (q's
    `wj`; `false` is `wj1`) also takes the last right row before `w₀` that has the key tuple: the start
    lowered by one where it stays above the last row of a lower code (`writeWhere`). -/
def wj (prevailing : Bool) (w₀ w₁ : Col) (l r : Array KCol) (rt : Col) : Except String (Rel (.atom .long) (.atom .long)) := do
  let (lc, rc, nl, _) ← keyCodes "wj" l r
  unless w₀.1 == rt.1 && w₁.1 == rt.1 do throw "wj: the window and time columns differ in type (q's 'type)"
  let ranks := Alg.drank rt.1 (concatBytes #[w₀.2, w₁.2, rt.2])
  let (r₀, rest) := Alg.split ranks nl
  let (r₁, rr) := Alg.split rest nl
  let (p, srt, base) := timeGrade rc lc rr (Alg.len ranks)
  let bin := binBytes 8 false true false srt
  let before := bin (plus (Alg.add base r₀) (-1))
  let last := bin (Alg.add base r₁)
  let start := if prevailing then writeWhere (plus before 1) (bin (plus base (-1))) before before else plus before 1
  let lens := Alg.sub (plus last 1) start
  let neg := whereBits nl.toUSize (Ew.cmp Ew.lt Ew.i64 Ew.va lens (one 0) nl.toUSize)
  if neg.size > 0 then throw "wj: a window ends before it starts (q's 'domain)"
  let (i, w) := expand lens
  let rows := Alg.gather 8 p (Alg.add (Alg.gather 8 start i) w)
  parted "wj" (concatBytes #[one 0, Alg.sums lens]) (← Arr.of (.atom .long) (Alg.len rows) (.bytes rows) "wj")

/-! ## Raze -/

/-- `raze`: the key becomes `til n`, the values untouched — zero copy whatever the key was. -/
def raze {k v : Ty} (R : Rel k v) : Rel (.atom .long) v := ⟨R.n, .til R.n, R.val⟩

theorem raze_val_toList {k v : Ty} (R : Rel k v) : (raze R).val.toList = R.val.toList := rfl

/-- `raze R` relates position `i` to the value at `i`. -/
theorem raze_holds {k v : Ty} (R : Rel k v) (i : Int64) (y : El v) :
    (raze R).Holds i y ↔ ∃ j : Fin R.n, Int64.ofNat j = i ∧ R.val.get j = y := Iff.rfl

/-! ## Symbols and chars -/

/-- `x like p` on a symbol column: `likeSyms` over a `syms` blob; over an `enum` dictionary, then
    `maskByIds` carries the dictionary's bits to the elements. On `x`'s key. -/
def like {k : Ty} (x : Rel k (.atom .symbol)) (p : String) : Except String (Rel k (.atom .boolean)) := do
  let pb := p.toUTF8
  let bits ← match x.val.c with
    | .syms b o => pure (likeSyms pb b o)
    | .enum n d dof ids =>
      pure ((likeSyms pb d dof).map fun m => maskByIds m (dof.size - 1).toUSize n.toUSize (Column.idWidth dof).toUSize ids)
    | _ => throw "x like p: the operand is neither a syms nor an enum column"
  let some bs := bits | throw s!"x like p: the pattern {p} does not parse (q's 'length or 'nyi)"
  onKey x.key .boolean (.bits x.n bs) "x like p"

/-- `x ss p` on a char list: the starts of the non-overlapping matches, `fixedHits`. -/
def ss {k : Ty} (x : Rel k (.atom .char)) (p : String) : Except String (Rel (.atom .long) (.atom .long)) := do
  let some hs := fixedHits p.toUTF8 (← dense "x ss p" .char x.val.c)
    | throw s!"x ss p: the pattern {p} is not fixed-width (q's 'nyi)"
  list .long (.bytes hs)

/-! ## The List-level spec -/

/-- `n#xs` on a non-empty `xs`: `|n|` elements from `takeFrom n |xs|`, cycling. -/
def takeSpec {α : Type} [Inhabited α] (n : Int) (xs : List α) : List α :=
  (List.range n.natAbs).map fun j => xs[(takeFrom n xs.length + j) % xs.length]!

/-- `n_xs`. -/
def dropSpec {α : Type} (n : Int) (xs : List α) : List α :=
  if 0 ≤ n then xs.drop n.toNat else xs.take (xs.length - n.natAbs)

/-- `n rotate xs`. -/
def rotateSpec {α : Type} (n : Int) (xs : List α) : List α :=
  if xs.isEmpty then xs else xs.rotateLeft (n.emod xs.length).toNat

/-- `xs@is`, `d` at a miss. -/
def indexSpec {α : Type} (d : α) (xs : List α) (is : List Int64) : List α :=
  is.map fun i => if 0 ≤ i then xs.getD i.toInt.toNat d else d

/-- `@[xs;is;f;ys]`: index by index, left to right. -/
def amendSpec {α : Type} [Inhabited α] (f : α → α → α) (xs : List α) (is : List Int64) (ys : List α) : List α :=
  (is.zip ys).foldl (fun acc (i, y) => acc.set i.toInt.toNat (f acc[i.toInt.toNat]! y)) xs

/-- `o cut xs`: run `i` is `xs[o[i] .. o[i+1])`, `o[g] = |xs|`. -/
def cutSpec {α : Type} (os : List Int64) (xs : List α) : List (Int64 × α) :=
  let o := os.map (·.toInt.toNat) ++ [xs.length]
  (List.range os.length).flatMap fun i => ((xs.drop o[i]!).take (o[i+1]! - o[i]!)).map (Int64.ofNat i, ·)

/-- A parted list's pairs from its runs. -/
def runsSpec {α : Type} (rs : List (List α)) : List (Int64 × α) :=
  (List.range rs.length).flatMap fun i => (rs.getD i []).map (Int64.ofNat i, ·)

/-- `xs f/: ys`: run `j` is `xs f ys[j]`. -/
def eachRightSpec {α β γ : Type} [Inhabited β] (f : α → β → γ) (xs : List α) (ys : List β) : List (Int64 × γ) :=
  runsSpec (ys.map fun y => xs.map (f · y))

/-- `ej` over key tuples: every `(i, j)` with equal tuples, `i` then `j` ascending. -/
def ejSpec (l r : List (List Int64)) : List (Int64 × Int64) :=
  (List.range l.length).flatMap fun i => ((List.range r.length).filter (r[·]! == l[i]!)).map fun j => (Int64.ofNat i, Int64.ofNat j)

/-- The right rows of the key `k` with a time in `[a, b]`, in time order (stable: right order among ties). -/
def window (rk rt : List Int64) (k a b : Int64) : List Nat :=
  ((List.range rk.length).filter fun j => rk[j]! == k && a ≤ rt[j]! && rt[j]! ≤ b).mergeSort fun i j => decide (rt[i]! ≤ rt[j]!)

/-- `aj`: the last row of `window` up to the left's time, `0N` at none. -/
def ajSpec (lk lt rk rt : List Int64) : List Int64 :=
  (lk.zip lt).map fun (k, t) => ((window rk rt k Int64.minValue t).getLast?.map Int64.ofNat).getD Int64.minValue

/-- `wj1` / `wj`: the rows of `window` in `[w₀, w₁]`, and for `wj` the last one before `w₀` first. -/
def wjSpec (prevailing : Bool) (lk w₀ w₁ rk rt : List Int64) : List (Int64 × Int64) :=
  runsSpec ((List.range lk.length).map fun i =>
    let pre := if prevailing then ((window rk rt lk[i]! Int64.minValue (w₀[i]! - 1)).getLast?).toList else []
    (pre ++ window rk rt lk[i]! w₀[i]! w₁[i]!).map Int64.ofNat)

/-! ## Checks against the spec on small literal Rels -/

section Checks

open QLean.Column

private def ans {α : Type} {k v : Ty} (f : Rel k v → α) : Except String (Rel k v) → Option α
  | .ok r => some (f r)
  | .error _ => none
private def lv (xs : List Int64) (h : Ty.WF (.atom .long) xs.length (.bytes (packLongs xs)) := by decide) :
    Rel (.atom .long) (.atom .long) := ⟨xs.length, .til _, { c := .bytes (packLongs xs), wf := h }⟩

private def xs := lv [5, 3, 5, 9, 3]
private def ys := lv [7, 8]
-- the five longs Frame-of-Reference encoded
private def xf : Rel (.atom .long) (.atom .long) :=
  ⟨5, .til 5, { c := .foR 5 (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).2, wf := ⟨rfl, rfl⟩ }⟩
private def bs : Rel (.atom .long) (.atom .boolean) := ⟨5, .til 5, { c := .bits 5 (ByteArray.mk #[0b10110]), wf := by decide }⟩
-- one symbol column `bc a bc` as `syms` and as `enum` over the dictionary `a, bc`
private def sy : Rel (.atom .long) (.atom .symbol) :=
  ⟨3, .til 3, { c := .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8], wf := by decide }⟩
private def se : Rel (.atom .long) (.atom .symbol) :=
  ⟨3, .til 3, { c := .enum 3 (ByteArray.mk #[97, 0, 98, 99, 0]) #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!), wf := by decide }⟩
private def cs : Rel (.atom .long) (.atom .char) := ⟨6, .til 6, { c := .bytes "aaabaa".toUTF8, wf := by decide }⟩
-- the parted list `(10 20; 30)`, keys `0 0 1`
private def o2 : Arr (.atom .long) 3 := { c := .bytes (packLongs [0, 2, 3]), wf := by decide }
private def pl : Rel (.atom .long) (.atom .long) := ⟨3, .grp (.til 2) o2 (by decide), (lv [10, 20, 30]).val⟩

#guard [xs, xf].all fun x => ans (·.val.toList) (concat x ys) == some (x.val.toList ++ ys.val.toList)
#guard ans (·.val.toList) (concat bs bs) == some (bs.val.toList ++ bs.val.toList)
#guard [sy, se].all fun x => [sy, se].all fun y => ans (·.val.toList) (concat x y) == some (x.val.toList ++ y.val.toList)
#guard [xs, xf].all fun x => [7, -7, 2, -2, 0].all fun n => ans (·.val.toList) (take n x) == some (takeSpec n x.val.toList)
#guard ans (·.val.toList) (take (-7) xs) == some [9, 3, 5, 3, 5, 9, 3]
#guard [sy, se].all fun x => [4, -2].all fun n => ans (·.val.toList) (take n x) == some (takeSpec n x.val.toList)
#guard [xs, xf].all fun x => [2, -2, 9, -9, 0].all fun n => ans (·.val.toList) (drop n x) == some (dropSpec n x.val.toList)
#guard [sy, se].all fun x => ans (·.val.toList) (drop 1 x) == some (dropSpec 1 x.val.toList)
#guard [xs, xf].all fun x => ans (·.val.toList) (reverse x) == some x.val.toList.reverse
#guard [sy, se].all fun x => ans (·.val.toList) (reverse x) == some x.val.toList.reverse
#guard ans (·.val.toList) (reverse bs) == some bs.val.toList.reverse
#guard [xs, xf].all fun x => [2, -2, 7, 0].all fun n => ans (·.val.toList) (rotate n x) == some (rotateSpec n x.val.toList)
#guard ans (·.val.toList) (rotate 2 xs) == some [5, 9, 3, 5, 3]
#guard [sy, se].all fun x => ans (·.val.toList) (rotate (-1) x) == some (rotateSpec (-1) x.val.toList)
#guard [xs, xf].all fun x =>
  ans (·.val.toList) (index x (lv [4, 0, 7, -1])) == some (indexSpec Int64.minValue x.val.toList [4, 0, 7, -1])
#guard [sy, se].all fun x => ans (·.val.toList) (index x (lv [2, 1])) == some (indexSpec "" x.val.toList [2, 1])
#guard ans (·.toList.map Prod.fst) (index xs (lv [4, 0])) == some (lv [4, 0]).key.toList
#guard ans (·.val.toList) (amend xs (lv [1, 3, 1]) none (lv [0, 7, 2])) == some (amendSpec (fun _ y => y) xs.val.toList [1, 3, 1] [0, 7, 2])
#guard ans (·.val.toList) (amend xs (lv [1, 3, 1]) none (lv [0, 7, 2])) == some [5, 2, 5, 7, 3]
#guard [xs, xf].all fun x =>
  ans (·.val.toList) (amend x (lv [0, 0, 4, 0]) (some .add) (lv [1, 2, 3, 4])) == some (amendSpec (· + ·) x.val.toList [0, 0, 4, 0] [1, 2, 3, 4])
#guard ans (·.val.toList) (amend xs (lv [0, 0, 4, 0]) (some .add) (lv [1, 2, 3, 4])) == some [12, 3, 5, 9, 6]
#guard (amend xs (lv [5]) none (lv [0])).toOption.isNone
-- the other value types: `bits` (width 1), `float` with a `float` or a `long` `y`, `int` (width 4)
private def bs3 : Rel (.atom .long) (.atom .boolean) := ⟨3, .til 3, { c := .bits 3 (ByteArray.mk #[0b101]), wf := by decide }⟩
private def fv (xs : List Float) : Rel (.atom .long) (.atom .float) :=
  match Arr.of (.atom .float) xs.length (.bytes (xs.foldl (fun b x => pushBits b x.toBits 8) .empty)) "fv" with
  | .ok a => ⟨xs.length, .til _, a⟩ | .error _ => ⟨0, .til 0, { c := .bytes .empty, wf := by decide }⟩
private def iv (xs : List Int32) : Rel (.atom .long) (.atom .int) :=
  match Arr.of (.atom .int) xs.length (.bytes (xs.foldl (fun b x => pushBits b x.toUInt32.toUInt64 4) .empty)) "iv" with
  | .ok a => ⟨xs.length, .til _, a⟩ | .error _ => ⟨0, .til 0, { c := .bytes .empty, wf := by decide }⟩
#guard [(Prim.Dyadic.greater, (· || ·)), (.lesser, (· && ·)), (.eq, (· == ·))].all fun (v, f) =>
  ans (·.val.toList) (amend bs (lv [0, 0, 4]) (some v) bs3) == some (amendSpec f bs.val.toList [0, 0, 4] bs3.val.toList)
#guard ans (·.val.toList) (amend bs (lv [0, 0, 4]) (some .greater) bs3) == some [true, true, true, false, true]
#guard ans (·.val.toList) (amend bs (lv [3, 0, 3]) none bs3) == some [false, true, true, true, true]
-- a float element is its IEEE bits (`Carrier .float`), read as a `Float` by `Float.ofBits`
private def fl {k : Ty} (r : Rel k (.atom .float)) : List Float := r.val.toList.map Float.ofBits
#guard ans fl (amend (fv [1.5, 2.5, 4]) (lv [0, 2, 0]) (some .add) (fv [1, 2, 3])) == some (amendSpec (· + ·) [1.5, 2.5, 4] [0, 2, 0] [1, 2, 3])
#guard ans fl (amend (fv [1.5, 2.5, 4]) (lv [0, 2, 0]) (some .add) (fv [1, 2, 3])) == some [5.5, 2.5, 6]
#guard ans fl (amend (fv [1.5, 2.5, 4]) (lv [0, 2]) (some .add) (lv [1, 2])) == some [2.5, 2.5, 6]
#guard ans fl (amend (fv [1.5, 2.5, 4]) (lv [1, 1]) (some .lesser) (fv [2, 0.5])) == some [1.5, 0.5, 4]
#guard ans (·.val.toList) (amend (iv [1, 2, 3]) (lv [1, 1, 2]) (some .add) (iv [10, 20, 5])) ==
  some (amendSpec (· + ·) [1, 2, 3] [1, 1, 2] [10, 20, 5])
#guard ans (·.val.toList) (amend (iv [1, 2, 3]) (lv [1, 1, 2]) (some .add) (iv [10, 20, 5])) == some [1, 32, 8]
-- `:` keeps `x`'s type: a `long` `y` into a `float` list is q's 'type
#guard (amend (fv [1.5]) (lv [0]) none (lv [1])).toOption.isNone
#guard (raze pl).toList == [(0, 10), (1, 20), (2, 30)]
#guard (raze pl).val.toList == pl.val.toList
#guard [sy, se].all fun x => ans (·.val.toList) (like x "b*") == some [true, false, true]
#guard [sy, se].all fun x => ans (·.val.toList) (like x "?") == some [false, true, false]
#guard ans (·.val.toList) (ss cs "aa") == some [0, 4]

-- parted lists, on `bytes` and on `foR` payloads
private def x6 := lv [1, 2, 3, 4, 5, 6]
private def x6f : Rel (.atom .long) (.atom .long) :=
  ⟨6, .til 6, { c := .foR 6 (Coc.encode 8 (packLongs [1, 2, 3, 4, 5, 6])).1 (Coc.encode 8 (packLongs [1, 2, 3, 4, 5, 6])).2, wf := ⟨rfl, rfl⟩ }⟩
#guard [xs, xf].all fun x => ans (·.toList) (cut (lv [0, 2, 2]) x) == some (cutSpec [0, 2, 2] x.val.toList)
#guard ans (·.toList) (cut (lv [0, 2]) xf) == some [(0, 5), (0, 3), (1, 5), (1, 9), (1, 3)]
-- q: `2 4 _ til 6` is `(2 3;4 5)`; the rows before the first offset are dropped
#guard [x6, x6f].all fun x => ans (·.toList) (cut (lv [2, 4]) x) == some (runsSpec [[3, 4], [5, 6]])
#guard [x6, x6f].all fun x => ans (·.toList) (cut (lv [0, 2, 4]) x) == some (runsSpec [[1, 2], [3, 4], [5, 6]])
#guard [xs, xf].all fun x => ans (·.toList) (cut (lv [1, 2]) x) == some (cutSpec [1, 2] x.val.toList) &&
  ans (·.toList) (cut (lv [1, 1, 4]) x) == some (cutSpec [1, 1, 4] x.val.toList) && ans (·.toList) (cut (lv [5]) x) == some (cutSpec [5] x.val.toList)
#guard [(cut (lv [-1, 2]) xs), (cut (lv [0, 3, 2]) xs), (cut (lv [0, 9]) xs), (cut (lv [6]) xs)].all (·.toOption.isNone)
#guard [sy, se].all fun x => ans (·.toList) (cut (lv [0, 1]) x) == some (cutSpec [0, 1] x.val.toList)
#guard [xs, xf].all fun x => ans (·.toList) (eachRight .add .long x ys) == some (eachRightSpec (· + ·) x.val.toList ys.val.toList)
#guard ans (·.toList) (eachRight .lt .boolean xf (lv [5, 4])) == some (eachRightSpec (fun a b => decide (a < b)) xf.val.toList [5, 4])
#guard [x6, x6f].all fun x => ans (·.toList) (do flip (← cut (lv [0, 2, 4]) x)) == some (runsSpec [[1, 3, 5], [2, 4, 6]])
#guard [x6, x6f].all fun x => ans (·.toList) (do flip (← flip (← cut (lv [0, 2, 4]) x))) == some (cutSpec [0, 2, 4] x6.val.toList)
#guard (do flip (← cut (lv [0, 1, 4]) x6)).toOption.isNone
#guard [xs, xf].all fun x => ans (·.toList) (do indexParted (← cut (lv [0, 2, 3]) x) (lv [2, 0, 5, -1, 3])) ==
  some (runsSpec [[9, 3], [5, 3], [], [], []])
#guard [sy, se].all fun x => ans (·.toList) (do indexParted (← cut (lv [0, 1]) x) (lv [1, 1])) ==
  some (runsSpec [x.val.toList.drop 1, x.val.toList.drop 1])

-- joins: left keys `lk` (and `lk₂`), times `lt`; right keys `rk` (and `rk₂`), times `rt`
private def col (xs : List Int64) : Struct.Col := (.i64, packLongs xs)
private def key (xs : List Int64) : Struct.KCol := ⟨.atom .long, .bytes (packLongs xs)⟩
-- keys of any encoding: `bits` `101b` against `01b`, and `syms` `` `a`b `` against its interned self
#guard ans (·.toList) (ej #[⟨.atom .boolean, .bits 3 (ByteArray.mk #[0b101])⟩] #[⟨.atom .boolean, .bits 2 (ByteArray.mk #[0b10])⟩]) == some [(0, 1), (1, 0), (2, 1)]
#guard ans (·.toList) (ej #[⟨.atom .symbol, .syms (ByteArray.mk #[97, 0, 98, 0]) #[0, 2, 4]⟩] #[⟨.atom .symbol, Column.intern (.syms (ByteArray.mk #[98, 0, 97, 0]) #[0, 2, 4])⟩]) == some [(0, 1), (1, 0)]
#guard (ej #[key [1]] #[⟨.atom .boolean, .bits 1 (ByteArray.mk #[1])⟩]).toOption.isNone
private def lk : List Int64 := [1, 1, 2, 3]
private def lk₂ : List Int64 := [0, 1, 0, 0]
private def lt : List Int64 := [5, 10, 3, 4]
private def rk : List Int64 := [1, 2, 1, 2, 9]
private def rk₂ : List Int64 := [0, 0, 1, 0, 0]
private def rt : List Int64 := [3, 1, 7, 4, 0]
-- the right times as a `foR` column, through `Alg.arrDense`
private def rtf : Arr (.atom .long) 5 := { c := .foR 5 (Coc.encode 8 (packLongs rt)).1 (Coc.encode 8 (packLongs rt)).2, wf := ⟨rfl, rfl⟩ }
private def rtc : Struct.Col := match Alg.arrDense rtf with | .ok c => c | .error _ => (.i64, .empty)
#guard rtc.2 == packLongs rt
#guard ans (·.toList) (ej #[key lk] #[key rk]) == some (ejSpec (lk.map ([·])) (rk.map ([·])))
#guard ans (·.toList) (ej #[key lk] #[key rk]) == some [(0, 0), (0, 2), (1, 0), (1, 2), (2, 1), (2, 3)]
#guard ans (·.toList) (ej #[key lk, key lk₂] #[key rk, key rk₂]) == some (ejSpec (lk.zipWith (fun a b => [a, b]) lk₂) (rk.zipWith (fun a b => [a, b]) rk₂))
#guard ans (·.toList) (ij #[key lk] #[key rk]) == some [(0, 0), (1, 0), (2, 1)]
#guard [col rt, rtc].all fun c => ans (·.val.toList) (aj #[key lk] #[key rk] (col lt) c) == some (ajSpec lk lt rk rt)
#guard ans (·.val.toList) (aj #[key lk] #[key rk] (col lt) (col rt)) == some [0, 2, 1, Int64.minValue]
private def w₀ : List Int64 := lt.map (· - 3)
#guard [false, true].all fun p => [col rt, rtc].all fun c =>
  ans (·.toList) (wj p (col w₀) (col lt) #[key lk] #[key rk] c) == some (wjSpec p lk w₀ lt rk rt)
#guard ans (·.toList) (wj true (col w₀) (col lt) #[key lk] #[key rk] (col rt)) == some [(0, 0), (1, 0), (1, 2), (2, 1)]
#guard (ej #[key lk] #[]).toOption.isNone

end Checks

#print axioms concat
#print axioms take
#print axioms drop
#print axioms reverse
#print axioms rotate
#print axioms index
#print axioms amend
#print axioms raze_holds
#print axioms like
#print axioms ss
#print axioms cut
#print axioms flip
#print axioms indexParted
#print axioms aj
#print axioms wj

end LeetQ.Rel.Struct
