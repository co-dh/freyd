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

/-- A key or time column as the `QValue` qlean's join passes read: the payload where it lies, no copy. -/
def colValue : KCol → QValue
  | ⟨.atom a, c⟩ => .vector a c
  | ⟨.gen, xs⟩ => .list xs

/-- The rows of a key or time column. -/
def colRows : KCol → Nat
  | ⟨.atom a, c⟩ => Column.count a c
  | ⟨.gen, xs⟩ => xs.size

/-- `Eval.keyMatch`, q's `?` of the key tuples (`q.k` line 42): the right's `nr` rows grouped by key tuple
    **as they lie**, and each of the left's `nl` rows' group, `none` at a miss. -/
def keyGroups (verb : String) (l r : Array KCol) (nl nr : Nat) : Except String (Eval.Groups × Array (Option Nat)) := do
  if l.size == 0 then throw s!"{verb}: no key column"
  unless l.size == r.size do throw s!"{verb}: {l.size} left key columns against {r.size} right (q's 'length)"
  unless (l.zip r).all fun (p, q) => p.1 == q.1 do throw s!"{verb}: the two sides' key columns differ in type (q's 'type)"
  unless l.all (colRows · == nl) && r.all (colRows · == nr) do throw s!"{verb}: a key column's length differs from its time column's (q's 'length)"
  pure (Eval.keyMatch (r.map colValue) nr (l.map colValue) nl)

/-- `aj`: each left row ↦ the right row q's `bin` names inside its key tuple's group, `0N` at none —
    `keyGroups`, then `Eval.groupEdge` (`q.k` line 46's `(x#z) bin x#y`): one C bisection per left row over
    the right's time column at its own encoding. q sorts nothing: an unsorted group is bisected as its rows lie.
    A miss is `nr`, which the gather from `til nr` reads as `0N`. -/
def aj (l r : Array KCol) (lt rt : KCol) : Except String (Rel (.atom .long) (.atom .long)) := do
  unless lt.1 == rt.1 do throw "aj: the two time columns differ in type (q's 'type)"
  let (nl, nr) := (colRows lt, colRows rt)
  let (gs, at?) ← keyGroups "aj" l r nl nr
  let hit := Kernel.longColumn (Eval.groupEdge gs at? (colValue rt) (colValue lt) nr)
  pure ⟨nl, .til nl, ← Arr.of (.atom .long) nl (← vec "aj" .long (gatherColumn .long (.bytes (tilLongs nr.toUSize)) hit)) "aj"⟩

/-- `wj` (`prevailing`) and `wj1`: each left row ↦ the right rows `[lo, hi)`, a parted list — q's `ww`
    (`q.k` line 54) as qlean's `windowJoin` runs it: `wj` is `ww[0 1;w]`, `lo` the row `bin` names at `w₀`
    (the prevailing row at or before it); `wj1` is `ww[1;w-1 0]`, one past the row at `w₀-1`; `hi` one past
    the row at `w₁`. A bound `bin` misses clamps to the group's first row, an inverted run is empty. The
    rows are a range of the right table, so a right side not laid out by key (q's `` `p# ``) mixes keys. -/
def wj (prevailing : Bool) (w₀ w₁ : KCol) (l r : Array KCol) (rt : KCol) : Except String (Rel (.atom .long) (.atom .long)) := do
  unless w₀.1 == rt.1 && w₁.1 == rt.1 do throw "wj: the window and time columns differ in type (q's 'type)"
  let (nl, nr) := (colRows w₀, colRows rt)
  let (gs, at?) ← keyGroups "wj" l r nl nr
  -- `wj1`'s `w-1` at q's own type rule for `-`, as qlean's interpreter subtracts it
  let lo ← if prevailing then pure (colValue w₀) else match w₀ with
    | ⟨.atom t, c⟩ => match dyadColumn .sub Ew.va t .long c (.bytes (one 1)) with
      | some (u, d) => pure (QValue.vector u d)
      | none => throw s!"wj1: no kernel subtracts 1 from a {repr t} window"
    | ⟨.gen, _⟩ => throw "wj1: a general list window (q's 'type)"
  let firsts := gs.firsts
  let edges (bound : QValue) (off : Nat) : Array Nat :=
    (Eval.groupEdge gs at? (colValue rt) bound nr).mapIdx fun i e => match at?[i]! with
      | none => 0
      | some g => let s := firsts[g]!; if e == nr then s else min nr (max s (e + off))
  let los := edges lo (if prevailing then 0 else 1)
  let lens ← dense "wj" .long (Kernel.longColumn ((los.zip (edges (colValue w₁) 1)).map fun (a, b) => b - a))
  let (i, w) := expand lens
  let rows := Alg.add (Alg.gather 8 (← dense "wj" .long (Kernel.longColumn los)) i) w
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
  apply List.ext_getElem (by simp only [Verify.elemsW, List.length_map, List.length_range, List.length_append, hs, hqa])
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
    rw [List.foldl_cons, elemsW_foldl_append w hw ps _ (by rw [ByteArray.size_append, Nat.add_mod, ha, hp p (by simp)] <;> simp)
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
  apply List.ext_getElem (by simp only [Verify.elemsW, List.length_map, List.length_range, List.length_take, List.length_drop, hsz]; omega)
  intro i h1 h2
  simp only [Verify.elemsW, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  have hi : i < e - s := by
    have := h1; simp only [Verify.elemsW, List.length_map, List.length_range] at this; rwa [hsz] at this
  have hb : s * w + i * w + w ≤ e * w := by
    have := Nat.mul_le_mul_right w (show s + i + 1 ≤ e by omega)
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at this; omega
  rw [Verify.bitsAt_extract b hb, Nat.add_mul]

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

theorem length_flatten_replicate {α : Type} (E : List α) (q : Nat) :
    (List.replicate q E).flatten.length = q * E.length := by
  induction q with
  | zero => simp
  | succ q ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

/-- `cycleBytes`' three pieces, read as words: `m` words of `E` from `off`, cycling. -/
theorem cycle_list {α : Type} [Inhabited α] (E : List α) (off m : Nat) (h : off < E.length ∨ off + m ≤ E.length) :
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
    rw [Nat.mul_comm] at hq
    apply List.ext_getElem (by
      simp; have := Nat.mod_lt (m - (E.length - off)) hL; omega)
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
        rw [show off + j = (j - (E.length - off)) + E.length by omega, Nat.add_mod_right, List.length_drop]
    · rename_i ha
      simp only [List.length_append, List.length_drop, length_flatten_replicate] at ha
      rw [List.getElem_take, getElem!_pos E _ (Nat.mod_lt _ hL)]
      simp only [List.length_append, List.length_drop, length_flatten_replicate]
      congr 1
      have hr := Nat.mod_lt (m - (E.length - off)) hL
      generalize (m - (E.length - off)) / E.length = Q at *
      generalize (m - (E.length - off)) % E.length = R at *
      have e : off + j = (j - (E.length - off + Q * E.length)) + E.length * (Q + 1) := by
        rw [Nat.mul_succ, Nat.mul_comm E.length Q]; omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **`cycleBytes` at a dense payload of `w`-byte words** reads `m` words from `off`, cycling: word `j` is
    word `(off + j) mod n`. A lap copies the whole payload, so it holds whole words unless no lap is run. -/
theorem elemsW_cycleBytes (w : Nat) (hw : 0 < w) (b : ByteArray) (off m : Nat)
    (h : off < b.size / w ∨ off + m ≤ b.size / w) (hb : off + m ≤ b.size / w ∨ b.size % w = 0) :
    Verify.elemsW w (cycleBytes (· * w) (b.size / w) off m b) =
      (List.range m).map fun j => (Verify.elemsW w b)[(off + j) % (b.size / w)]! := by
  have hE : (Verify.elemsW w b).length = b.size / w := by simp [Verify.elemsW]
  rw [← hE, ← cycle_list _ off m (by rw [hE]; exact h), hE]
  unfold cycleBytes
  split
  · rename_i hle; exact elemsW_extract w hw b hle
  · rename_i hlt
    simp only []
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
      · simp at hp; subst hp; simpa using whole 0 _ (Nat.le_of_lt hr))]
    simp only [Array.toList_append, Array.toList_replicate, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.flatMap_replicate]
    rw [elemsW_extract w hw b (Nat.le_refl _), ← Nat.zero_mul w, elemsW_extract w hw b (Nat.le_of_lt hr),
      List.drop_zero, Nat.sub_zero, List.take_of_length_le (by simp [hE])]

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
  rw [getElem!_pos (E.map UInt64.toInt64) i (by simpa using h), getElem!_pos E i h, List.getElem_map]

/-- A slice of a long `bytes` column, as `list` wraps it: `m` words from `off`, cycling. The column holds
    whole words and `off < n` unless no lap is run; an empty column is sliced only to nothing. -/
theorem slice_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {b : ByteArray}
    {verb : String} {off m : Nat} (hc : x.val.c = .bytes b) (h0 : 0 < x.n ∨ m = 0)
    (h : off < x.n ∨ off + m ≤ x.n) (hb : off + m ≤ x.n ∨ b.size % 8 = 0)
    (hr : (do list .long (← vec verb .long (sliceColumn .long x.val.c off m))) = .ok r) :
    r.val.toList = (List.range m).map fun j => x.val.toList[(off + j) % x.val.toList.length]! := by
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  rw [hc, sliceColumn_long] at hr
  simp only [vec, bind, Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at hr
  rw [Arr.toList_long r.val (by rw [Find.list_c hr]; exact longWords_answer _)]
  by_cases hz : x.n = 0
  · obtain rfl : m = 0 := by omega
    obtain rfl : off = 0 := by omega
    simp [cycleBytes, Verify.elemsW]
  have hE : (Verify.elemsW 8 b).length = x.n := by simp [Verify.elemsW, hn]
  rw [if_neg (by omega), elemsW_cycleBytes 8 (by decide) b off m (by omega) (by omega), toList_bytes x.val hc,
    List.map_map, List.length_map, hn]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp]
  rw [getElem!_map_toInt64 _ _ (by rw [hE]; exact Nat.mod_lt _ (by omega)), hE]

/-- `m` words of `xs` from `off`, cycling, with no lap run: the window `xs[off .. off + m)`. -/
theorem range_map_window {α : Type} [Inhabited α] (xs : List α) (off m : Nat) (h : off + m ≤ xs.length) :
    (List.range m).map (fun j => xs[(off + j) % xs.length]!) = (xs.drop off).take m := by
  rw [← cycle_list xs off m (.inr h), if_pos h, Nat.add_sub_cancel_left]

/-- **`n#x` is `takeSpec`** on a non-empty long column of whole words: `takeSpec`'s default element
    reads an empty `xs`, where q pads with nulls, so `x.n ≠ 0`; a lap copies the payload, so `Words`. -/
theorem take_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {n : Int}
    (hx : Words x.val.c) (h0 : 0 < x.n) (h : take n x = .ok r) : r.val.toList = takeSpec n x.val.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  have hl : x.val.toList.length = x.n := Arr.length_toList _
  unfold take takeColumn at h
  rw [hc, show Column.count .long (.bytes b) = x.n by simp [Column.count, QAtomicType.width, hn], ← hc] at h
  rw [slice_toList hc (.inl h0) (.inl (by unfold takeFrom; split; omega; exact Nat.mod_lt _ h0)) (.inr hb) h,
    takeSpec, hl]

/-- **`n_x` is `dropSpec`** on a long `bytes` column: no lap is run, so any `bytes` payload. -/
theorem drop_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {n : Int} {b : ByteArray}
    (hc : x.val.c = .bytes b) (h : drop n x = .ok r) : r.val.toList = dropSpec n x.val.toList := by
  have hn : b.size / 8 = x.n := Arr.n_long_bytes x.val hc
  have hl : x.val.toList.length = x.n := Arr.length_toList _
  unfold drop dropColumn at h
  rw [hc, show Column.count .long (.bytes b) = x.n by simp [Column.count, QAtomicType.width, hn], ← hc] at h
  rw [slice_toList hc (by omega) (.inr (by split <;> omega)) (.inl (by split <;> omega)) h,
    range_map_window _ _ _ (by rw [hl]; split <;> omega)]
  unfold dropSpec
  by_cases hp : 0 ≤ n
  · simp only [hp, ↓reduceIte]
    rw [List.take_of_length_le (by simp [hl])]
    by_cases hk : n.toNat ≤ x.n
    · congr 1; omega
    · rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.drop_eq_nil_of_le (by rw [hl]; omega)]
  · simp only [hp, ↓reduceIte, List.drop_zero]
    congr 1; omega

/-- `rotateLeft` by `i < |xs|` reads `xs` at `(i + j) mod |xs|`. -/
theorem rotateLeft_eq {α : Type} [Inhabited α] (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.rotateLeft i = (List.range xs.length).map fun j => xs[(i + j) % xs.length]! := by
  unfold List.rotateLeft
  simp only []
  split
  · rename_i h1
    apply List.ext_getElem (by simp)
    intro j h1' h2
    have : j = 0 ∧ i = 0 := by simp at h2; omega
    obtain ⟨rfl, rfl⟩ := this
    simp [List.getElem?_eq_getElem hi]
  · rw [Nat.mod_eq_of_lt hi]
    by_cases hi0 : i = 0
    · subst hi0; rw [range_map_window xs 0 xs.length (by omega)]; simp
    have := cycle_list xs i xs.length (.inl hi)
    rw [if_neg (by omega), Nat.sub_sub_self (Nat.le_of_lt hi), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] at this
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
  simp only [] at h
  by_cases h0 : x.n = 0
  · rw [slice_toList hc (.inr h0) (.inr (by simp [h0])) (.inl (by simp [h0])) h,
      List.eq_nil_of_length_eq_zero (hl.trans h0)]
    simp [h0, rotateSpec]
  have hlt : (n.emod x.n).toNat < x.n := by
    have := Int.emod_lt_of_pos n (show (0 : Int) < x.n by omega)
    have := Int.emod_nonneg n (show (x.n : Int) ≠ 0 by omega)
    change (n % (x.n : Int)).toNat < x.n; omega
  simp only [show (x.n == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte] at h
  have hne : ¬ x.val.toList.isEmpty = true := by
    rw [List.isEmpty_iff]; intro he; rw [he] at hl; simp at hl; omega
  rw [slice_toList hc (.inl (by omega)) (.inl hlt) (.inr hb) h, rotateSpec, if_neg hne,
    rotateLeft_eq _ _ (by rw [hl]; exact hlt), hl]

/-- **`|x` is `List.reverse`** on a long `bytes` column, from `reverseBytes_spec`. -/
theorem reverse_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {b : ByteArray}
    (hc : x.val.c = .bytes b) (h : reverse x = .ok r) : r.val.toList = x.val.toList.reverse := by
  unfold reverse at h
  simp only [hc, reverseColumn, foRColumn, rowWidth, denseWidth, QAtomicType.width, Column.bytesOf, vec, bind,
    Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
  rw [Arr.toList_long r.val (show longWords r.val.c = some (Verify.elemsW 8 (reverseBytes (8 : Nat).toUSize b)) by
    rw [Find.list_c h]; rfl), toList_bytes x.val hc]
  have e8 : (8 : Nat).toUSize.toNat = 8 := Find.usize_eight
  have := Verify.reverseBytes_spec (8 : Nat).toUSize (by rw [e8]; decide) (by rw [e8]; decide) b
  rw [e8] at this
  rw [this, List.map_reverse]

/-- Two dense long payloads meet densely: no part is encoded, so `encodedParts` has nothing to meet. -/
theorem razeColumn_bytes (b c : ByteArray) :
    razeColumn .long #[.bytes b, .bytes c] = some (.vector .long (.bytes (concatBytes #[b, c]))) := by
  have he : encodedParts .long #[.bytes b, .bytes c] = none := by
    first
    | rfl
    | (simp [encodedParts, Column.alpEncodes, Column.encodes]; done)
    | (simp [encodedParts, Column.alpEncodes, Column.encodes, ← Array.any_toList]; done)
  first
  | (simp [razeColumn, he, Column.bytesOf]; done)
  | (simp [razeColumn, he, Column.bytesOf, ← Array.mapM_toList]; done)
  | (simp only [razeColumn, he]; rfl)

/-- **`x,y` is `++`** on long `bytes` columns, `x` of whole words: `concatBytes` copies `x`'s payload whole. -/
theorem concat_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel (.atom .long) (.atom .long)}
    {c : ByteArray} (hx : Words x.val.c) (hc' : y.val.c = .bytes c) (h : concat x y = .ok r) :
    r.val.toList = x.val.toList ++ y.val.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  unfold concat at h
  rw [hc, hc', razeColumn_bytes] at h
  simp only [vec, bind, Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
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

/-- The right rows of the key `k`, in row order. -/
def group {κ : Type} [BEq κ] [Inhabited κ] (rk : List κ) (k : κ) : List Nat := (List.range rk.length).filter (rk[·]! == k)

/-- q's `x bin` inside the group `g`, the times as its rows lie (q sorts nothing): the bisection
    `Eval.partitionAt` of `rt ≤ x`, and the row before its point, `none` at the group's start. -/
def binSpec (rt : List Int64) (g : List Nat) (x : Int64) : Option Nat :=
  match Id.run (Eval.partitionAt (fun j => pure (rt[g[j]!]! ≤ x)) g.length) with
  | 0 => none
  | p => some g[p - 1]!

/-- `aj`: `binSpec` of the left's time in its key's group, `0N` at none. -/
def ajSpec {κ : Type} [BEq κ] [Inhabited κ] (lk : List κ) (lt : List Int64) (rk : List κ) (rt : List Int64) : List Int64 :=
  (lk.zip lt).map fun (k, t) => ((binSpec rt (group rk k) t).map Int64.ofNat).getD Int64.minValue

/-- `wj` / `wj1`: the right rows `[lo, hi)`, `hi` one past `binSpec` at `w₁`; `lo` the row at `w₀` (`wj`) or one
    past the row at `w₀-1` (`wj1`); a miss is the group's first row `s`, nothing below `s`. -/
def wjSpec {κ : Type} [BEq κ] [Inhabited κ] (prevailing : Bool) (lk : List κ) (w₀ w₁ : List Int64) (rk : List κ) (rt : List Int64) :
    List (Int64 × Int64) :=
  runsSpec ((List.range lk.length).map fun i =>
    let g := group rk lk[i]!
    match g.head? with
    | none => []
    | some s =>
      let edge (x : Int64) (off : Nat) := ((binSpec rt g x).map (max s <| · + off)).getD s
      let lo := if prevailing then edge w₀[i]! 0 else edge (w₀[i]! - 1) 1
      (List.range (edge w₁[i]! 1 - lo)).map fun j => Int64.ofNat (lo + j))

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
-- the right times also as a `foR` column, which `groupEdge` bisects where it lies
private def rtf : Struct.KCol := ⟨.atom .long, .foR 5 (Coc.encode 8 (packLongs rt)).1 (Coc.encode 8 (packLongs rt)).2⟩
#guard ans (·.toList) (ej #[key lk] #[key rk]) == some (ejSpec (lk.map ([·])) (rk.map ([·])))
#guard ans (·.toList) (ej #[key lk] #[key rk]) == some [(0, 0), (0, 2), (1, 0), (1, 2), (2, 1), (2, 3)]
#guard ans (·.toList) (ej #[key lk, key lk₂] #[key rk, key rk₂]) == some (ejSpec (lk.zipWith (fun a b => [a, b]) lk₂) (rk.zipWith (fun a b => [a, b]) rk₂))
#guard ans (·.toList) (ij #[key lk] #[key rk]) == some [(0, 0), (1, 0), (2, 1)]
-- `aj` over keys interleaved in the right table (the hashed grouping), dense and `foR` times; key `3` is missing
#guard [key rt, rtf].all fun c => ans (·.val.toList) (aj #[key lk] #[key rk] (key lt) c) == some (ajSpec lk lt rk rt)
#guard ans (·.val.toList) (aj #[key lk] #[key rk] (key lt) (key rt)) == some [0, 2, 1, Int64.minValue]
-- two key columns
#guard ans (·.val.toList) (aj #[key lk, key lk₂] #[key rk, key rk₂] (key lt) (key rt)) ==
  some (ajSpec (lk.zip lk₂) lt (rk.zip rk₂) rt)
#guard ans (·.val.toList) (aj #[key lk, key lk₂] #[key rk, key rk₂] (key lt) (key rt)) == some [0, 2, 1, Int64.minValue]
-- q 4.1, ``aj[`s`t;flip `s`t!(`a`b;3 8);([]s:`a`a`a`a`b`b`b`b;t:5 1 9 2 5 1 9 2;v:10+10*til 8)]``: the groups
-- bisected as they lie answer `v` `20 60` (rows 1 5); `` `s`t xasc `` of the same rows answers `40 50` (rows 1 6)
private def sk : List Int64 := [0, 0, 0, 0, 1, 1, 1, 1]
#guard ans (·.val.toList) (aj #[key [0, 1]] #[key sk] (key [3, 8]) (key [5, 1, 9, 2, 5, 1, 9, 2])) == some [1, 5]
#guard ajSpec [0, 1] [3, 8] sk [5, 1, 9, 2, 5, 1, 9, 2] == [1, 5]
#guard ans (·.val.toList) (aj #[key [0, 1]] #[key sk] (key [3, 8]) (key [1, 2, 5, 9, 1, 2, 5, 9])) == some [1, 6]
#guard (aj #[key lk] #[key rk] (key lt) ⟨.atom .int, .bytes (packLongs rt)⟩).toOption.isNone
private def w₀ : List Int64 := lt.map (· - 3)
#guard [false, true].all fun p => [key rt, rtf].all fun c =>
  ans (·.toList) (wj p (key w₀) (key lt) #[key lk] #[key rk] c) == some (wjSpec p lk w₀ lt rk rt)
-- q's `wj` reads a range of the right table: on interleaved keys `wj1`'s run for row 1 takes row 1 of key `2`
#guard ans (·.toList) (wj true (key w₀) (key lt) #[key lk] #[key rk] (key rt)) == some [(0, 0), (1, 2), (2, 1)]
#guard ans (·.toList) (wj false (key w₀) (key lt) #[key lk] #[key rk] (key rt)) == some [(0, 0), (1, 1), (1, 2), (2, 1)]
-- qlean's measured case: window `[4;6]` over the times `1 3 5` — `wj` takes the quote at `3`, prevailing on
-- entry, `wj1` does not; key `2` has only its prevailing row `3`, key `4` is missing
private def qk : List Int64 := [1, 1, 1, 2, 2]
private def qt : List Int64 := [1, 3, 5, 2, 8]
#guard [false, true].all fun p =>
  ans (·.toList) (wj p (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt)) == some (wjSpec p [1, 2, 4] [4, 4, 4] [6, 6, 6] qk qt)
#guard ans (·.toList) (wj true (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt)) == some [(0, 1), (0, 2), (1, 3)]
#guard ans (·.toList) (wj false (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt)) == some [(0, 2)]
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
