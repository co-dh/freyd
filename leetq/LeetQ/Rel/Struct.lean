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
import QLean.Verify.Group

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
    other fixed-width encoding dense (`Find.dense`) at `8·width`. A symbol column has no such payload;
    `scatter` writes it by `assignSyms`. -/
def packed (verb : String) (a : QAtomicType) : Column → Except String (ByteArray × Nat)
  | .bits _ b => pure (b, 1)
  | c => do
    let some w := a.width | throw s!"{verb}: a {repr a} column has no fixed-width payload to scatter into"
    pure (← dense verb a c, 8 * w)

/-- The `n`-element column `acc` with `v`'s elements written at the long positions `ix`, in order, so the
    last write to a repeated position stays. A symbol column has no fixed-width payload: `assignSyms`
    writes it in the encodings it holds (`scatterSyms` on two blobs, `scatterIds` into an interned
    column, `,`'s policy where the two differ). Every other type is `packed` and `scatterPacked`. -/
def scatter (verb : String) (a : QAtomicType) (n : Nat) (acc v : Column) (ix : ByteArray) : Except String Column :=
  match a with
  | .symbol => match assignSyms n acc v ix false with
    | some c => pure c
    | none => throw s!"{verb}: assignSyms refused a payload that is no symbol column"
  | _ => do
    let (xb, wb) ← packed verb a acc
    let out := scatterPacked wb.toUSize xb ix (← packed verb a v).1 0 false
    -- the payload back as a column of `acc`'s form: `packed` answers width `1` exactly on `bits`
    pure (if wb = 1 then .bits n out else .bytes out)

/-- `@[x;i;f;y]`, `f` a dyadic verb, or `:` at `none`; on `x`'s key. `amendRounds` checks every index
    against `count x` and, for a verb, splits the indices into rounds holding each index at most once,
    so a round is one `gatherColumn` of the current `x`, one `Ew.dyad` and one `scatter` (q's
    index-by-index application). `Ew.dyad` is `dyadColumn`, so the verb runs at every type pair it is
    defined on whose answer is `x`'s type, nulls by its own rule. Under `:` the scatter keeps the last
    write, so one round is q's answer, and `y` must have `x`'s type (q's 'type otherwise). -/
def amend {k k' k'' : Ty} {a u : QAtomicType} (x : Rel k (.atom a)) (i : Rel k' (.atom .long))
    (op : Option Prim.Dyadic) (y : Rel k'' (.atom u)) : Except String (Rel k (.atom a)) := do
  let verb := "@[x;i;f;y]"
  if i.n ≠ y.n then throw s!"{verb}: {i.n} indices against {y.n} values (q's 'length)"
  let ib ← dense verb .long i.val.c
  let r := amendRounds x.n.toUSize 8 op.isSome ib
  let word (j : Nat) := Column.bitsAt r (j * 8) 8
  if word 0 == ~~~0 then throw s!"{verb}: index {(word 1).toInt64} outside 0..{x.n} (q's 'length)"
  let step (acc : Column) (ix : ByteArray) (yv : Column) : Except String Column := do
    let v ← match op with
      | none => if u = a then pure yv else throw s!"{verb}: `:` of a {repr u} into a {repr a} list (q's 'type)"
      | some v => do
        let cur ← vec verb a (gatherColumn a acc (.bytes ix))
        pure (← Ew.dyad v Ew.vv a u a cur yv (ix.size / 8)).c
    scatter verb a x.n acc v ix
  let rounds := (word 0).toNat
  -- words `2 … 2+rounds-1` count the indices up to each round; the grouped positions follow
  let out ← if rounds ≤ 1 then step x.val.c ib y.val.c else
    rounds.foldM (fun rr _ acc => do
      let lo := if rr == 0 then 0 else (word (1 + rr)).toNat
      let ks := r.extract ((2 + rounds + lo) * 8) ((2 + rounds + (word (2 + rr)).toNat) * 8)
      step acc (gatherBytes 8 0 ib ks) (← vec verb u (gatherColumn u y.val.c (.bytes ks)))) x.val.c
  onKey x.key a (Column.answer a out) verb

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

/-! ## Joins on columns: `|R|` of the key tuples (`Alg.tuples`), then gathers -/

/-- A dense column and the layout it is compared at, as `Alg.arrDense` answers it. -/
abbrev Col := Scan.Kind × ByteArray

/-- A key column in any encoding: its element type and payload, compared only by `Alg.codes`. -/
abbrev KCol := (t : Ty) × Pay t

/-- The key tuples of both sides in one code space (`Alg.codes` per column pair, `Alg.tuples`), left
    then right, each at the narrowest layout its columns allow. -/
def keyCodes (verb : String) (l r : Array KCol) : Except String (Alg.Code × Alg.Code) := do
  if l.size == 0 then throw s!"{verb}: no key column"
  unless l.size == r.size do throw s!"{verb}: {l.size} left key columns against {r.size} right (q's 'length)"
  let cs ← (l.zip r).mapM fun ((p : KCol), (q : KCol)) =>
    if h : q.1 = p.1 then Alg.codes p.1 #[p.2, h ▸ q.2] else throw s!"{verb}: the two sides' key columns differ in type (q's 'type)"
  Alg.two (← Alg.tuples cs)

/-- `keyCodes` as long ids, split at the left's count, and that count. `timeGrade`'s `code·T + rank` is
    long arithmetic (missing kernel: a grade and `binBytes` over the pair (code, rank) at the code's own
    layout), so the joint codes go through their long ids (`Code.longs`). -/
def longKeyCodes (verb : String) (l r : Array KCol) : Except String (ByteArray × ByteArray × Nat) := do
  let (lc, rc) ← keyCodes verb l r
  let (a, b) := Alg.split (Alg.Code.cat #[lc, rc]).longs lc.n
  pure (a, b, lc.n)

/-- `ej`: every pair of a left and a right row with equal key tuples, left row ↦ right row (`Alg.join`). -/
def ej (l r : Array KCol) : Except String (Rel (.atom .long) (.atom .long)) := do
  let (lc, rc) ← keyCodes "ej" l r
  let (li, ri) := Alg.join lc rc
  Alg.ofCols (.atom .long) (.atom .long) (.bytes li) (.bytes ri)

/-- `ij` against a keyed right side: each left row ↦ the first right row of its key tuple, unmatched rows
    dropped — `findVec`, `Ew.cmp lt` against the miss, `whereBits`, a gather. -/
def ij (l r : Array KCol) : Except String (Rel (.atom .long) (.atom .long)) := do
  let (lc, rc) ← keyCodes "ij" l r
  let hit := rc.find lc
  let li := whereBits lc.n.toUSize (Ew.cmp Ew.lt Ew.i64 Ew.va hit (one rc.n.toUInt64) lc.n.toUSize)
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
  let (lc, rc, nl) ← longKeyCodes "aj" l r
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
  let (lc, rc, nl) ← longKeyCodes "wj" l r
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

/-! ## Value laws of the moves on long columns

  Each law reads the answer through `Arr.toList_long` and the operand through `longWords`. The payload
  lemmas are width-generic (`w`-byte words, `Verify.elemsW w`); the laws are stated at `long` because
  `longWords`/`toList_long` is the only bridge from `Arr.toList` to payload words. The operand `x` is a
  `bytes` payload: at `foR` the kernels move encoded blocks (`cycleFoR`, `reverseFoR`, `gatherFoR`,
  `concatFoR`), none of which has a law. -/

section MoveLaws

/-- A `bytes` payload of whole eight-byte words: what `cycleBytes` and `concatBytes` need wherever a
    whole payload is copied after another (a lap of `n#x`, `rotate`, the left part of `x,y`); a ragged
    tail would be copied into the middle of the answer. -/
def Words : Column → Prop
  | .bytes b => b.size % 8 = 0
  | _ => False

theorem words_bytes {c : Column} (h : Words c) : ∃ b, c = .bytes b ∧ b.size % 8 = 0 := by
  cases c with
  | bytes b => exact ⟨b, rfl, h⟩
  | _ => exact h.elim

theorem elemsW_empty (w : Nat) : Verify.elemsW w ByteArray.empty = [] := by simp [Verify.elemsW]

/-- Reading `w`-byte words is local: past `a`'s whole words, `a ++ b` reads `b`'s. -/
theorem elemsW_append (w : Nat) (hw : 0 < w) (a b : ByteArray) (ha : a.size % w = 0) :
    Verify.elemsW w (a ++ b) = Verify.elemsW w a ++ Verify.elemsW w b := by
  obtain ⟨q, hq⟩ : ∃ q, a.size = w * q := ⟨a.size / w, by have := Nat.div_add_mod a.size w; omega⟩
  have hqa : a.size / w = q := by rw [hq, Nat.mul_div_cancel_left q hw]
  have hs : (a ++ b).size / w = q + b.size / w := by rw [ByteArray.size_append, hq, Nat.mul_add_div hw]
  apply List.ext_getElem (by simp [Verify.elemsW, hs, hqa])
  intro i h1 h2
  simp only [Verify.elemsW, List.getElem_map, List.getElem_range, List.getElem_append, List.length_map,
    List.length_range, hqa]
  split
  · rename_i hi
    have : (i + 1) * w ≤ q * w := Nat.mul_le_mul_right w hi
    rw [Nat.succ_mul] at this
    exact Verify.bitsAt_shift _ _ _ _ _ fun k hk => Verify.ba_append_left a b _ (by rw [hq, Nat.mul_comm w q]; omega)
  · rename_i hi
    refine Verify.bitsAt_shift _ _ _ _ _ fun k hk => ?_
    have e : i * w + k = a.size + ((i - q) * w + k) := by
      rw [hq, Nat.mul_comm w q, Nat.sub_mul]; have := Nat.mul_le_mul_right w (Nat.le_of_not_lt hi); omega
    rw [e, Verify.ba_append_right]

/-- A fold of `++` over parts of whole words reads the parts' words in order. -/
theorem elemsW_foldl_append (w : Nat) (hw : 0 < w) :
    ∀ (ps : List ByteArray) (acc : ByteArray), acc.size % w = 0 → (∀ p ∈ ps, p.size % w = 0) →
      Verify.elemsW w (ps.foldl (· ++ ·) acc) = Verify.elemsW w acc ++ ps.flatMap (Verify.elemsW w)
  | [], _, _, _ => by simp
  | p :: ps, acc, ha, hp => by
    rw [List.foldl_cons, elemsW_foldl_append w hw ps _ (by rw [ByteArray.size_append]; have := hp p (by simp); omega)
      (fun q hq => hp q (by simp [hq])), elemsW_append w hw _ _ ha]
    simp

/-- `concatBytes` over parts of whole words reads the parts' words in order. -/
theorem elemsW_concatBytes (w : Nat) (hw : 0 < w) (ps : Array ByteArray) (hp : ∀ p ∈ ps.toList, p.size % w = 0) :
    Verify.elemsW w (concatBytes ps) = ps.toList.flatMap (Verify.elemsW w) := by
  rw [concatBytes, ← Array.foldl_toList, elemsW_foldl_append w hw _ _ (by rfl) hp, elemsW_empty, List.nil_append]

/-- A whole-word range of a payload reads the range of its words. -/
theorem elemsW_extract (w : Nat) (hw : 0 < w) (b : ByteArray) {s e : Nat} (he : e ≤ b.size / w) :
    Verify.elemsW w (b.extract (s * w) (e * w)) = ((Verify.elemsW w b).drop s).take (e - s) := by
  have hle : e * w ≤ b.size := by have := Nat.mul_le_mul_right w he; have := Nat.div_mul_le_self b.size w; omega
  have hsz : (b.extract (s * w) (e * w)).size / w = e - s := by
    rw [ByteArray.size_extract, Nat.min_eq_left hle, ← Nat.sub_mul, Nat.mul_div_cancel _ hw]
  apply List.ext_getElem (by simp [Verify.elemsW, hsz]; omega)
  intro i h1 h2
  simp only [Verify.elemsW, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  have hi : i < e - s := by simpa [Verify.elemsW, hsz] using h1
  rw [Verify.bitsAt_extract b (by have := Nat.mul_le_mul_right w (show s + i + 1 ≤ e by omega)
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at this; omega), Nat.add_mul]

/-- The flattened laps of `E` at position `i` read `E` at `i mod |E|`. -/
theorem getElem_flatten_replicate {α : Type} (E : List α) :
    ∀ (q i : Nat) (h : i < ((List.replicate q E).flatten).length),
      ((List.replicate q E).flatten)[i] = E[i % E.length]'(Nat.mod_lt _ (by
        cases E with
        | nil => simp at h
        | cons _ _ => simp))
  | 0, i, h => by simp at h
  | q + 1, i, h => by
    simp only [List.replicate_succ, List.flatten_cons, List.getElem_append]
    split
    · rename_i hi; simp only [Nat.mod_eq_of_lt hi]
    · rename_i hi
      rw [getElem_flatten_replicate E q]
      congr 1
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hi)]

/-- `cycleBytes`' three pieces, read as words: `m` words of `E` from `off`, cycling. -/
theorem cycle_list {α : Type} [Inhabited α] (E : List α) (off m : Nat) (h : off < E.length ∨ m = 0) :
    (if off + m ≤ E.length then (E.drop off).take (off + m - off) else
      E.drop off ++ (List.replicate ((m - (E.length - off)) / E.length) E).flatten ++
        E.take ((m - (E.length - off)) % E.length)) =
    (List.range m).map fun j => E[(off + j) % E.length]! := by
  split
  · rename_i hle
    apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    have hj : j < m := by simpa using h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [Nat.mod_eq_of_lt (by omega), getElem!_pos E _ (by omega)]
  · rename_i hlt
    have hoff : off < E.length := by omega
    have hL : 0 < E.length := by omega
    have hq := Nat.div_add_mod (m - (E.length - off)) E.length
    apply List.ext_getElem (by
      simp [List.length_flatten, List.sum_replicate]
      rw [Nat.mul_comm]; have := Nat.mod_lt (m - (E.length - off)) hL; omega)
    intro j h1 h2
    have hj : j < m := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_append]
    split
    · rename_i ha
      split
      · rename_i hb
        simp only [List.length_drop] at hb
        rw [List.getElem_drop, Nat.mod_eq_of_lt (by omega), getElem!_pos E _ (by omega)]
      · rename_i hb
        simp only [List.length_drop] at hb
        rw [getElem_flatten_replicate, getElem!_pos E _ (Nat.mod_lt _ hL)]
        congr 1
        rw [show off + j = (j - (E.length - off)) + E.length by omega, Nat.add_mod_right]
    · rename_i ha
      simp only [List.length_append, List.length_drop, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul] at ha
      rw [List.getElem_take, getElem!_pos E _ (Nat.mod_lt _ hL)]
      simp only [List.length_append, List.length_drop, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul]
      congr 1
      have hr := Nat.mod_lt (m - (E.length - off)) hL
      rw [show off + j = (j - (E.length - off + (m - (E.length - off)) / E.length * E.length)) +
          E.length * ((m - (E.length - off)) / E.length + 1) by rw [Nat.mul_succ, Nat.mul_comm]; omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [Nat.mul_comm] at hq; omega)]

/-- **`cycleBytes` at a dense payload of `w`-byte words** reads `m` words from `off`, cycling: word `j` is
    word `(off + j) mod n`. A lap copies the whole payload, so it holds whole words unless no lap is run. -/
theorem elemsW_cycleBytes (w : Nat) (hw : 0 < w) (b : ByteArray) (off m : Nat)
    (h : off < b.size / w ∨ m = 0) (hb : off + m ≤ b.size / w ∨ b.size % w = 0) :
    Verify.elemsW w (cycleBytes (· * w) (b.size / w) off m b) =
      (List.range m).map fun j => (Verify.elemsW w b)[(off + j) % (b.size / w)]! := by
  have hE : (Verify.elemsW w b).length = b.size / w := by simp [Verify.elemsW]
  rw [← hE, ← cycle_list _ off m (by rw [hE]; exact h), hE]
  unfold cycleBytes
  split
  · rename_i hle; rw [if_pos hle, elemsW_extract w hw b hle]
  · rename_i hlt
    rw [if_neg hlt]
    have hoff : off < b.size / w := by omega
    have hbw : b.size % w = 0 := by omega
    have hsz : b.size = b.size / w * w := by have := Nat.div_add_mod b.size w; rw [Nat.mul_comm] at this; omega
    have hr := Nat.mod_lt (m - (b.size / w - off)) (show 0 < b.size / w by omega)
    have whole : ∀ s e, e ≤ b.size / w → (b.extract (s * w) (e * w)).size % w = 0 := fun s e he => by
      rw [ByteArray.size_extract, Nat.min_eq_left (by rw [hsz]; exact Nat.mul_le_mul_right w he), ← Nat.sub_mul,
        Nat.mul_mod_left]
    rw [elemsW_concatBytes w hw _ (by
      intro p hp
      simp only [Array.toList_append, List.mem_append, Array.toList_replicate, List.mem_replicate] at hp
      rcases hp with (hp | ⟨-, rfl⟩) | hp
      · simp at hp; subst hp; exact whole _ _ (Nat.le_refl _)
      · exact hbw
      · simp at hp; subst hp; rw [← Nat.zero_mul w]; exact whole _ _ (Nat.le_of_lt hr))]
    simp only [Array.toList_append, Array.toList_replicate, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.flatMap_replicate]
    rw [elemsW_extract w hw b (Nat.le_refl _), ← Nat.zero_mul w, elemsW_extract w hw b (Nat.le_of_lt hr),
      List.drop_zero, Nat.sub_zero, hE]
    rw [Nat.min_eq_left (by omega : b.size / w - off ≤ b.size / w - off)] at *
    simp [hE, List.take_of_length_le]

/-- A dense long answer handed back through `Column.answer` lists the same words: kept dense, or encoded
    by `Coc.encode`, whose round trip is `foRBits_encode_bits`. -/
theorem longWords_answer (C : ByteArray) : longWords (Column.answer .long (.bytes C)) = some (Verify.elemsW 8 C) := by
  by_cases hs : C.size < 8 * Column.encodeMin
  · simp [Column.answer, QAtomicType.width, hs, longWords]
  · cases he : Coc.encodeBelow (8 : Nat).toUSize C with
    | none => simp [Column.answer, QAtomicType.width, hs, he, longWords, Column.alpEncodes, Column.encodes]
    | some mp =>
      obtain ⟨md, pk⟩ := mp
      have hmp : (md, pk) = Coc.encode (8 : Nat).toUSize C := by
        revert he; unfold Coc.encodeBelow; split; intro he; split at he <;> simp_all
      simp only [Column.answer, QAtomicType.width, hs, he, longWords, Column.alpEncodes, Column.encodes]
      simp only [Prod.ext_iff] at hmp
      obtain ⟨rfl, rfl⟩ := hmp
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Verify.elemsW]
      apply List.map_congr_left
      intro i hi
      apply UInt64.toNat_inj.1
      rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _),
        Verify.foRBits_encode_bits 8 (by decide) (by decide) C i (List.mem_range.1 hi)]

/-- `sliceColumn` at a long `bytes` column: the dense arm, over the column or, empty, over its null. -/
theorem sliceColumn_long (b : ByteArray) (off m : Nat) :
    sliceColumn .long (.bytes b) off m = some (.vector .long (Column.answer .long (.bytes
      (if b.size / 8 = 0 then cycleBytes (· * 8) 1 off m (Column.pushBits .empty 0x8000000000000000 8)
       else cycleBytes (· * 8) (b.size / 8) off m b)))) := by
  by_cases h : b.size / 8 = 0 <;>
    simp [sliceColumn, Column.count, QAtomicType.width, h, nullColumn, foRColumn, Column.bytesOf, nullBits,
      Column.pushBits_size]

/-- The words of a long `bytes` column, read as longs, are its `toList`. -/
theorem toList_bytes {m : Nat} (x : Arr (.atom .long) m) {b : ByteArray} (hc : x.c = .bytes b) :
    x.toList = (Verify.elemsW 8 b).map UInt64.toInt64 := Arr.toList_long x (by rw [hc]; rfl)

/-- A word list's `!` read under `toInt64` at an index in range. -/
theorem getElem!_map_toInt64 (E : List UInt64) (i : Nat) (h : i < E.length) :
    (E.map UInt64.toInt64)[i]! = E[i]!.toInt64 := by
  rw [getElem!_pos _ _ (by simpa using h), getElem!_pos _ _ h, List.getElem_map]

/-- A slice of a long `bytes` column, as `list` wraps it: `m` words from `off`, cycling. The column holds
    whole words unless no lap is run; `off < n` unless nothing is read. -/
theorem slice_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {b : ByteArray}
    {verb : String} {off m : Nat} (hc : x.val.c = .bytes b) (h0 : 0 < x.n)
    (h : off < x.n ∨ m = 0) (hb : off + m ≤ x.n ∨ b.size % 8 = 0)
    (hr : (do list .long (← vec verb .long (sliceColumn .long x.val.c off m))) = .ok r) :
    r.val.toList = (List.range m).map fun j => x.val.toList[(off + j) % x.n]! := by
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  rw [hc, sliceColumn_long, if_neg (by omega)] at hr
  simp only [vec, bind, Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at hr
  rw [Arr.toList_long r.val (by rw [Find.list_c hr]; exact longWords_answer _),
    elemsW_cycleBytes 8 (by decide) b off m (by omega) (by omega), toList_bytes x.val hc, List.map_map, hn]
  refine List.map_congr_left fun j _ => ?_
  rw [Function.comp, getElem!_map_toInt64 _ _ (by simp [Verify.elemsW, hn]; exact Nat.mod_lt _ h0)]

/-- **`n#x` is `takeSpec`** on a non-empty long column of whole words: `takeSpec`'s default element
    reads an empty `xs`, where q pads with nulls, so `x.n ≠ 0`; a lap copies the payload, so `Words`. -/
theorem take_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {n : Int}
    (hx : Words x.val.c) (h0 : 0 < x.n) (h : take n x = .ok r) : r.val.toList = takeSpec n x.val.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  have hl : x.val.toList.length = x.n := Arr.length_toList _
  unfold take takeColumn at h
  rw [hc, show Column.count .long (.bytes b) = x.n by simp [Column.count, QAtomicType.width, hn], ← hc] at h
  rw [slice_toList hc h0 (.inl (by unfold takeFrom; split <;> [omega; exact Nat.mod_lt _ h0])) (.inr hb) h,
    takeSpec, hl]

/-- **`n_x` is `dropSpec`** on a long `bytes` column: no lap is run, so any `bytes` payload. -/
theorem drop_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {n : Int} {b : ByteArray}
    (hc : x.val.c = .bytes b) (h : drop n x = .ok r) : r.val.toList = dropSpec n x.val.toList := by
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  have hl : x.val.toList.length = x.n := Arr.length_toList _
  unfold drop dropColumn at h
  rw [hc, show Column.count .long (.bytes b) = x.n by simp [Column.count, QAtomicType.width, hn], ← hc] at h
  by_cases h0 : x.n = 0
  · rw [hc, sliceColumn_long, if_pos (by omega)] at h
    simp only [vec, bind, Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
    rw [Arr.toList_long r.val (by rw [Find.list_c h]; exact longWords_answer _), h0, Nat.min_eq_right (Nat.zero_le _),
      Nat.sub_zero, show (Column.pushBits .empty 0x8000000000000000 8).size / 8 = 1 by simp [Column.pushBits_size]]
    rw [← show (Column.pushBits .empty 0x8000000000000000 8).size / 8 = 1 by simp [Column.pushBits_size],
      elemsW_cycleBytes 8 (by decide) _ _ 0 (.inr rfl) (.inl (by simp [Column.pushBits_size]; split <;> omega))]
    rw [List.eq_nil_of_length_eq_zero (hl.trans h0)]; simp [dropSpec]
  rw [slice_toList hc (by omega) (by split <;> omega) (.inl (by split <;> omega)) h]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, dropSpec]; split <;> simp [hl] <;> omega
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    rw [getElem!_pos _ _ (by rw [hl]; exact Nat.mod_lt _ (by omega))]
    unfold dropSpec
    split
    · rename_i hp
      rw [if_pos hp]; simp only [List.getElem_drop]
      congr 1; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rename_i hp
      rw [if_neg hp]; simp only [List.getElem_take]
      congr 1; rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `rotateLeft` by `i < |xs|` reads `xs` at `(i + j) mod |xs|`. -/
theorem rotateLeft_eq {α : Type} [Inhabited α] (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.rotateLeft i = (List.range xs.length).map fun j => xs[(i + j) % xs.length]! := by
  unfold List.rotateLeft
  split
  · rename_i h1
    apply List.ext_getElem (by simp)
    intro j h1' h2
    have : j = 0 ∧ i = 0 := by simp at h2; omega
    obtain ⟨rfl, rfl⟩ := this
    simp [getElem!_pos xs 0 (by omega)]
  · rw [Nat.mod_eq_of_lt hi]
    have := cycle_list xs i xs.length (.inl hi)
    rw [if_neg (by omega), Nat.sub_sub_self (Nat.le_of_lt hi), show (xs.length - (xs.length - i)) = i by omega,
      Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] at this
    simpa using this

/-- **`n rotate x` is `rotateSpec`** on a long column of whole words (a rotation by a non-zero count runs
    a lap). -/
theorem rotate_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {n : Int}
    (hx : Words x.val.c) (h : rotate n x = .ok r) : r.val.toList = rotateSpec n x.val.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  have hl : x.val.toList.length = x.n := Arr.length_toList _
  unfold rotate rotateColumn at h
  rw [hc, show Column.count .long (.bytes b) = x.n by simp [Column.count, QAtomicType.width, hn], ← hc] at h
  by_cases h0 : x.n = 0
  · rw [hc, sliceColumn_long, if_pos (by omega)] at h
    simp only [vec, bind, Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
    rw [Arr.toList_long r.val (by rw [Find.list_c h]; exact longWords_answer _), h0]
    rw [← show (Column.pushBits .empty 0x8000000000000000 8).size / 8 = 1 by simp [Column.pushBits_size],
      elemsW_cycleBytes 8 (by decide) _ _ 0 (.inr rfl) (.inl (by simp [Column.pushBits_size]))]
    rw [List.eq_nil_of_length_eq_zero (hl.trans h0)]; simp [rotateSpec]
  have hlt : (n.emod x.n).toNat < x.n := by
    have := Int.emod_lt_of_pos n (show (0 : Int) < x.n by omega); have := Int.emod_nonneg n (show (x.n : Int) ≠ 0 by omega); omega
  rw [show (x.n == 0) = false by simpa using h0] at h
  rw [slice_toList hc (by omega) (.inl hlt) (.inr hb) h, rotateSpec, if_neg (by simp [← List.length_eq_zero_iff, hl, h0]),
    rotateLeft_eq _ _ (by rw [hl]; exact hlt), hl]

/-- **`|x` is `List.reverse`** on a long `bytes` column, from `reverseBytes_spec`. -/
theorem reverse_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {b : ByteArray}
    (hc : x.val.c = .bytes b) (h : reverse x = .ok r) : r.val.toList = x.val.toList.reverse := by
  unfold reverse at h
  simp only [hc, reverseColumn, foRColumn, rowWidth, denseWidth, QAtomicType.width, Column.bytesOf, vec, bind,
    Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
  rw [Arr.toList_long r.val (show longWords r.val.c = some (Verify.elemsW 8 (reverseBytes (8 : Nat).toUSize b)) by
    rw [Find.list_c h]; rfl), toList_bytes x.val hc]
  have := Verify.reverseBytes_spec (8 : Nat).toUSize (by decide) (by decide) b
  rw [show (8 : Nat).toUSize.toNat = 8 from rfl] at this
  rw [this, List.map_reverse]

/-- **`x,y` is `++`** on long `bytes` columns, `x` of whole words: `concatBytes` copies `x`'s payload whole. -/
theorem concat_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel (.atom .long) (.atom .long)}
    {c : ByteArray} (hx : Words x.val.c) (hc' : y.val.c = .bytes c) (h : concat x y = .ok r) :
    r.val.toList = x.val.toList ++ y.val.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  unfold concat at h
  simp only [hc, hc', razeColumn, encodedParts, Column.alpEncodes, Column.encodes, Column.bytesOf, vec, bind,
    Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
  rw [Arr.toList_long r.val (show longWords r.val.c = some (Verify.elemsW 8 (concatBytes #[b, c])) by
    rw [Find.list_c h]; rfl), toList_bytes x.val hc, toList_bytes y.val hc',
    show concatBytes #[b, c] = (ByteArray.empty ++ b) ++ c from rfl,
    elemsW_append 8 (by decide) _ _ (by rw [ByteArray.size_append]; simpa using hb),
    elemsW_append 8 (by decide) _ _ (by rfl), elemsW_empty, List.nil_append, List.map_append]

end MoveLaws

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
-- `:` on symbols, every pair of encodings: `y` is `d a e` (`d`, `e` in neither `x` dictionary), the index
-- `2` repeated so the last write stays
private def sy3 : Rel (.atom .long) (.atom .symbol) :=
  ⟨3, .til 3, { c := .syms (ByteArray.mk #[100, 0, 97, 0, 101, 0]) #[0, 2, 4, 6], wf := by decide }⟩
private def se3 : Rel (.atom .long) (.atom .symbol) :=
  ⟨3, .til 3, { c := .enum 3 (ByteArray.mk #[97, 0, 100, 0, 101, 0]) #[0, 2, 4, 6] (packIds (idWidth #[0, 2, 4, 6]) 3 fun i => [1, 0, 2][i]!), wf := by decide }⟩
#guard [sy, se].all fun x => [sy3, se3].all fun y =>
  ans (·.val.toList) (amend x (lv [2, 0, 2]) none y) == some (amendSpec (fun _ y => y) x.val.toList [2, 0, 2] y.val.toList)
#guard [sy, se].all fun x => [sy3, se3].all fun y => ans (·.val.toList) (amend x (lv [2, 0, 2]) none y) == some ["a", "a", "e"]
-- the encoding kept: a blob stays a blob only against a blob, an interned `x` stays interned
#guard ans (fun (r : Rel (.atom .long) (.atom .symbol)) => r.val.c matches Column.syms ..) (amend sy (lv [0, 1, 2]) none sy3) == some true
#guard [sy3, se3].all fun y => ans (fun (r : Rel (.atom .long) (.atom .symbol)) => r.val.c matches Column.enum ..) (amend se (lv [0, 1, 2]) none y) == some true
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
