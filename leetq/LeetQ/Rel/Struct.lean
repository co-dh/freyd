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
import LeetQ.Rel.Scan
import QLean.Verify.Group
import QLean.Verify.Gather
import QLean.Verify.Dyad
import QLean.Verify.EwEnc

namespace LeetQ.Rel.Struct

open QLean QLean.Dep QLean.Kernel
open LeetQ.Rel.Find (list onKey vec dense one expand)

/-! ## Concat, take, drop, reverse, rotate: a new list -/

/-- `x,y`: `razeColumn` over the two payloads; a `syms` part meets an `enum` one by interning. -/
def concat {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr a ny) :
    Except String (Arr a (nx + ny)) := do
  onKey (nx + ny) a (← vec "x,y" a (razeColumn a #[x.c, y.c])) "x,y"

/-- `n#x`: `|n|` elements cycling from `takeFrom n (count x)`. -/
def take {a : QAtomicType} {nx : Nat} (n : Int) (x : Arr a nx) : Except String (Arr a n.natAbs) := do
  onKey n.natAbs a (← vec "n#x" a (takeColumn a x.c n)) "n#x"

/-- `n_x`: `|n|` elements off the front (`n ≥ 0`) or the back, clamped. -/
def drop {a : QAtomicType} {nx : Nat} (n : Int) (x : Arr a nx) : Except String (Arr a (nx - n.natAbs)) := do
  onKey (nx - n.natAbs) a (← vec "n_x" a (dropColumn a x.c n)) "n_x"

/-- `|x`: `reverseColumn`; a `syms` blob, which it declines (reversing a blob rebuilds it), is
    `x@` the reversed `til n`, `gatherSyms`. -/
def reverse {a : QAtomicType} {nx : Nat} (x : Arr a nx) : Except String (Arr a nx) := do
  let r := match a, x.c.enc with
    | .symbol, .syms .. => gatherColumn a x.c (Alg.longs (reverseBytes 8 (tilLongs nx.toUSize)))
    | _, _ => reverseColumn a x.c
  onKey nx a (← vec "|x" a r) "|x"

/-- `n rotate x`: a left rotation by `n mod count x`. -/
def rotate {a : QAtomicType} {nx : Nat} (n : Int) (x : Arr a nx) : Except String (Arr a nx) := do
  onKey nx a (← vec "n rotate x" a (rotateColumn a n x.c)) "n rotate x"

/-! ## Index and amend: an answer per element of an operand -/

/-- `x@y` = `y ; x`: `gatherColumn`, the type's null at a miss; one element per `y`. -/
def index {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr .long ny) :
    Except String (Arr a ny) := do
  onKey ny a (← vec "x@y" a (gatherColumn a x.c y.c)) "x@y"

/-- A column as `scatterPacked` writes it, with its element width in bits: `bits` as it is at `1`, any
    other fixed-width encoding dense (`Find.dense`) at `8·width`. A symbol column has no such payload;
    `scatter` writes it by `assignSyms`. -/
def packed (verb : String) (a : QAtomicType) (c : Column) : Except String (ByteArray × Nat) :=
  match c.enc with
  | .bits b => pure (b, 1)
  | _ => do
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
    pure (if wb = 1 then ⟨a, n, .bits out, none⟩ else ⟨a, n, .bytes out, none⟩)

/-- `@[x;i;f;y]`, `f` a dyadic verb, or `:` at `none`; on `x`'s key. `amendRounds` checks every index
    against `count x` and, for a verb, splits the indices into rounds holding each index at most once,
    so a round is one `gatherColumn` of the current `x`, one `Ew.dyad` and one `scatter` (q's
    index-by-index application). `Ew.dyad` is `dyadColumn`, so the verb runs at every type pair it is
    defined on whose answer is `x`'s type, nulls by its own rule. Under `:` the scatter keeps the last
    write, so one round is q's answer, and `y` must have `x`'s type (q's 'type otherwise). -/
def amend {a u : QAtomicType} {nx ni ny : Nat} (x : Arr a nx) (i : Arr .long ni)
    (op : Option Prim.Dyadic) (y : Arr u ny) : Except String (Arr a nx) := do
  let verb := "@[x;i;f;y]"
  if ni ≠ ny then throw s!"{verb}: {ni} indices against {ny} values (q's 'length)"
  let ib ← dense verb .long i.c
  let r := amendRounds nx.toUSize 8 op.isSome ib
  let word (j : Nat) := Column.bitsAt r (j * 8) 8
  if word 0 == ~~~0 then throw s!"{verb}: index {(word 1).toInt64} outside 0..{nx} (q's 'length)"
  let step (acc : Column) (ix : ByteArray) (yv : Column) : Except String Column := do
    let v ← match op with
      | none => if u = a then pure yv else throw s!"{verb}: `:` of a {repr u} into a {repr a} list (q's 'type)"
      | some v => do
        let cur ← vec verb a (gatherColumn a acc (Alg.longs ix))
        pure (← Ew.dyad v Ew.vv a u a cur yv (ix.size / 8)).c
    scatter verb a nx acc v ix
  let rounds := (word 0).toNat
  -- words `2 … 2+rounds-1` count the indices up to each round; the grouped positions follow
  let out ← if rounds ≤ 1 then step x.c ib y.c else
    rounds.foldM (fun rr _ acc => do
      let lo := if rr == 0 then 0 else (word (1 + rr)).toNat
      let ks := r.extract ((2 + rounds + lo) * 8) ((2 + rounds + (word (2 + rr)).toNat) * 8)
      step acc (gatherBytes 8 0 ib ks) (← vec verb u (gatherColumn u y.c (Alg.longs ks)))) x.c
  onKey nx a (Column.answer out) verb

/-! ## Parted lists: q's nested list, one boxed vector per run; `Parted` its flat working form -/

/-- `b + x` on longs. -/
def plus (b : ByteArray) (x : Int64) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.va Alg.nul b (one x.toUInt64) (Alg.len b).toUSize

/-- The flat form over `val`: its `n` rows cut by the long payload `o` (`g+1` offsets), decided by `Parted.of?`. -/
def partedP {v : QAtomicType} {n : Nat} (verb : String) (o : ByteArray) (val : Arr v n) : Except String (Parted v) := do
  let g := o.size / 8 - 1
  let some P := Parted.of? (← Arr.of .long (g + 1) (Alg.longs o) verb) val
    | throw s!"{verb}: the offsets are not ascending cuts of {n} rows (q's 'domain)"
  pure P

/-- q's nested list of a flat form: one boxed vector per run (`Parted.box`). -/
def boxed {v : QAtomicType} (P : Parted v) : Except String ((g : Nat) × Arr .general g) := do pure ⟨P.g, ← P.box⟩

/-- `partedP`, boxed. -/
def parted {v : QAtomicType} {n : Nat} (verb : String) (o : ByteArray) (val : Arr v n) : Except String ((g : Nat) × Arr .general g) := do
  boxed (← partedP verb o val)

/-- `o cut x` in its flat form: `x` cut at `(o, n)`. A first offset `o₀ = 0` leaves `val` untouched (zero
    copy); above `0`, q drops the rows before it: `dropColumn` of `x` and the offsets lowered by `o₀` (`plus`).
    Offsets that are negative or do not ascend within `n` are refused (`Parted.of?`). -/
def cutP {a : QAtomicType} {no nx : Nat} (o : Arr .long no) (x : Arr a nx) : Except String (Parted a) := do
  let ob ← dense "o cut x" .long o.c
  let o₀ : Int64 := if no = 0 then 0 else (Column.bitsAt ob 0 8).toInt64
  if o₀ < 0 || nx < o₀.toNatClampNeg then throw s!"o cut x: the first offset {o₀} is outside 0..{nx} (q's 'domain)"
  if o₀ = 0 then return (← partedP "o cut x" (concatBytes #[ob, one nx.toUInt64]) x)
  let m := nx - o₀.toNatClampNeg
  let c ← vec "o cut x" a (dropColumn a x.c o₀.toInt)
  partedP "o cut x" (concatBytes #[plus ob (-o₀), one m.toUInt64]) (← Arr.of a m c "o cut x")

/-- `o cut x`: `cutP`, boxed. -/
def cut {a : QAtomicType} {no nx : Nat} (o : Arr .long no) (x : Arr a nx) : Except String ((g : Nat) × Arr .general g) := do
  boxed (← cutP o x)

/-- `x f/: y`: `m` runs of `n`, run `j` is `x f y[j]` — `Alg.cross` of the positions, two gathers and ONE
    `Ew.dyad` over all `m·n` pairs, no call per right element; `o := j·n` for `j ≤ m`. -/
def eachRightP {t u : QAtomicType} (v : Prim.Dyadic) (rt : QAtomicType) {nx ny : Nat} (x : Arr t nx)
    (y : Arr u ny) : Except String (Parted rt) := do
  let (j, i) := Alg.cross ny nx
  let xs ← vec "x f/:y" t (gatherColumn t x.c (Alg.longs i))
  let ys ← vec "x f/:y" u (gatherColumn u y.c (Alg.longs j))
  partedP "x f/:y" (Alg.mulc (tilLongs (ny + 1).toUSize) nx) (← Ew.dyad v Ew.vv t u rt xs ys (ny * nx))

/-- `x f/: y`: `eachRightP`, boxed. -/
def eachRight {t u : QAtomicType} (v : Prim.Dyadic) (rt : QAtomicType) {nx ny : Nat} (x : Arr t nx)
    (y : Arr u ny) : Except String ((g : Nat) × Arr .general g) := do
  boxed (← eachRightP v rt x y)

/-- `+x` of a nested list of `g` runs of `a`s of one length `m`: `m` runs of `g`. The equal lengths are one
    `matchBytes` of `o` against `j·m`; position `p` of the answer reads `(p mod g)·m + p div g`
    (`Alg.cross`, `Ew.val`, one gather); `o' := j·g`. -/
def flipP {a : QAtomicType} (P : Parted a) : Except String (Parted a) := do
  let g := P.g
  let m := if g = 0 then 0 else P.n / g
  let some ob := longBytes P.o.c | throw "+x: the offsets have no long payload"
  unless matchBytes 8 false ob (Alg.mulc (tilLongs (g + 1).toUSize) m) do
    throw "+x: the runs differ in length (q's 'length)"
  let (q, r) := Alg.cross m g
  let c ← vec "+x" a (gatherColumn a P.val.c (Alg.longs (Alg.add (Alg.mulc r m) q)))
  partedP "+x" (Alg.mulc (tilLongs (m + 1).toUSize) g) (← Arr.of a (m * g) c "+x")

/-- `+x`: `flipP` of the flat form, boxed. -/
def flip (a : QAtomicType) {nx : Nat} (x : Arr .general nx) : Except String ((g : Nat) × Arr .general g) := do
  boxed (← flipP (← Parted.ofBoxes a x))

/-- `x@y` on a nested list of `a`s: the runs `y` selects — the run lengths `o[1..] − o[..g]` gathered at
    `y` (`0` outside `0 … g-1`), `Find.expand` of them, one gather of `val` at `o[y[i]] + w`; `o' := 0, sums`. -/
def indexPartedP {a : QAtomicType} {ny : Nat} (P : Parted a) (y : Arr .long ny) : Except String (Parted a) := do
  let some ob := longBytes P.o.c | throw "x@y: the offsets have no long payload"
  let yb ← dense "x@y" .long y.c
  let lens := Alg.gather 8 (Alg.sub (ob.extract 8 ob.size) (ob.extract 0 (ob.size - 8))) yb
  let (i, w) := expand lens
  let src := Alg.add (Alg.gather 8 (Alg.gather 8 ob yb) i) w
  let c ← vec "x@y" a (gatherColumn a P.val.c (Alg.longs src))
  partedP "x@y" (concatBytes #[one 0, Alg.sums lens]) (← Arr.of a (Alg.len src) c "x@y")

/-- `x@y` on a nested list: `indexPartedP` of the flat form, boxed. -/
def indexParted (a : QAtomicType) {nx ny : Nat} (x : Arr .general nx) (y : Arr .long ny) : Except String ((g : Nat) × Arr .general g) := do
  boxed (← indexPartedP (← Parted.ofBoxes a x) y)

/-! ## Joins on columns: `|R|` of the key tuples (`Alg.tuples`), then gathers -/

/-- A key column in any encoding: its element type and payload, compared only by `Alg.codes`. -/
abbrev KCol := (t : QAtomicType) × Column

/-- The key tuples of both sides in one code space (`Alg.codes` per column pair, `Alg.tuples`), left
    then right, each at the narrowest layout its columns allow. -/
def keyCodes (verb : String) (l r : Array KCol) : Except String (Alg.Code × Alg.Code) := do
  if l.size == 0 then throw s!"{verb}: no key column"
  unless l.size == r.size do throw s!"{verb}: {l.size} left key columns against {r.size} right (q's 'length)"
  let cs ← (l.zip r).mapM fun ((p : KCol), (q : KCol)) =>
    if q.1 = p.1 then Alg.codes p.1 #[p.2, q.2] else throw s!"{verb}: the two sides' key columns differ in type (q's 'type)"
  Alg.two (← Alg.tuples cs)

/-- `ej`: every pair of a left and a right row with equal key tuples, left row ↦ right row (`Alg.join`). -/
def ej (l r : Array KCol) : Except String (Rel .long .long) := do
  let (lc, rc) ← keyCodes "ej" l r
  let (li, ri) := Alg.join lc rc
  Alg.ofCols .long .long (Alg.longs li) (Alg.longs ri)

/-- `ij` against a keyed right side: each left row ↦ the first right row of its key tuple, unmatched rows
    dropped — `findVec`, `Ew.cmp lt` against the miss, `whereBits`, a gather. -/
def ij (l r : Array KCol) : Except String (Rel .long .long) := do
  let (lc, rc) ← keyCodes "ij" l r
  let hit := rc.find lc
  let li := whereBits lc.n.toUSize (Ew.cmp Ew.lt Ew.i64 Ew.va hit (one rc.n.toUInt64) lc.n.toUSize)
  Alg.ofCols .long .long (Alg.longs li) (Alg.longs (Alg.gather 8 hit li))

/-- A key or time column as the `QValue` qlean's join passes read: the payload where it lies, no copy. -/
def colValue (p : KCol) : QValue :=
  match p.1 with
  | .general => QValue.general (match p.2.enc with | .gen xs => xs | _ => #[])
  | _ => .vector p.2

/-- The rows of a key or time column. -/
def colRows (p : KCol) : Nat := p.2.n

/-- `Eval.keyMatch`, q's `?` of the key tuples (`q.k` line 42): the right's `nr` rows grouped by key tuple
    **as they lie**, and each of the left's `nl` rows' group as a `long` column, the group count at a miss. -/
def keyGroups (verb : String) (l r : Array KCol) (nl nr : Nat) : Except String (Eval.Groups × Column) := do
  if l.size == 0 then throw s!"{verb}: no key column"
  unless l.size == r.size do throw s!"{verb}: {l.size} left key columns against {r.size} right (q's 'length)"
  unless (l.zip r).all fun (p, q) => p.1 == q.1 do throw s!"{verb}: the two sides' key columns differ in type (q's 'type)"
  unless l.all (colRows · == nl) && r.all (colRows · == nr) do throw s!"{verb}: a key column's length differs from its time column's (q's 'length)"
  pure (Eval.keyMatch (r.map colValue) nr (l.map colValue) nl)

/-- `aj`: each left row ↦ the right row q's `bin` names inside its key tuple's group, `0N` at none —
    `keyGroups`, then `Eval.groupEdge` (`q.k` line 46's `(x#z) bin x#y`): one C bisection per left row over
    the right's time column at its own encoding. q sorts nothing: an unsorted group is bisected as its rows lie.
    A miss is `nr`: one `^` pass reading `nr` as its null fills it with `0N`. -/
def aj (l r : Array KCol) (lt rt : KCol) : Except String ((m : Nat) × Arr .long m) := do
  unless lt.1 == rt.1 do throw "aj: the two time columns differ in type (q's 'type)"
  let (nl, nr) := (colRows lt, colRows rt)
  let (gs, ids) ← keyGroups "aj" l r nl nr
  let e ← dense "aj" .long (Eval.groupEdge gs ids (colValue rt) (colValue lt) nr)
  let hit := Kernel.Ew.val Ew.fill Ew.i64 Ew.av (Int64.ofNat nr) (one Int64.minValue.toUInt64) e nl.toUSize
  pure ⟨nl, ← Arr.of .long nl (Alg.longs hit) "aj"⟩

/-- `wj` (`prevailing`) and `wj1`: each left row ↦ the right rows `[lo, hi)`, a parted list — q's `ww`
    (`q.k` line 54) as qlean's `windowJoin` runs it: `wj` is `ww[0 1;w]`, `lo` the row `bin` names at `w₀`
    (the prevailing row at or before it); `wj1` is `ww[1;w-1 0]`, one past the row at `w₀-1`; `hi` one past
    the row at `w₁`. A bound `bin` misses clamps to the group's first row, an inverted run is empty. The
    rows are a range of the right table, so a right side not laid out by key (q's `` `p# ``) mixes keys. -/
def wjP (prevailing : Bool) (w₀ w₁ : KCol) (l r : Array KCol) (rt : KCol) : Except String (Parted .long) := do
  unless w₀.1 == rt.1 && w₁.1 == rt.1 do throw "wj: the window and time columns differ in type (q's 'type)"
  let (nl, nr) := (colRows w₀, colRows rt)
  let (gs, ids) ← keyGroups "wj" l r nl nr
  -- `wj1`'s `w-1` at q's own type rule for `-`, as qlean's interpreter subtracts it
  let lo ← if prevailing then pure (colValue w₀) else match w₀.1 with
    | .general => throw "wj1: a general list window (q's 'type)"
    | t => match dyadColumn .sub Ew.va t .long w₀.2 (Alg.longs (one 1)) with
      | some (_, d) => pure (QValue.vector d)
      | none => throw s!"wj1: no kernel subtracts 1 from a {repr t} window"
  -- each left row's group start, `0` at a key miss: `firsts` gathered at the ids, whose miss is `firsts`' size
  let starts := Alg.gather 8 (← dense "wj" .long (Kernel.longColumn (gs.firsts.push 0))) (← dense "wj" .long ids)
  let n := nl.toUSize
  let mn := Int64.minValue
  -- an edge `max s (e + off)`, `s` where `bin` misses: the miss `nr` (read as the `^` pass's null) becomes
  -- `-1`, whose `+ off` is at most `0 ≤ s`; a hit is `e < nr`, so `e + 1 ≤ nr` needs no clamp
  let edges (bound : QValue) (off : Nat) : Except String ByteArray := do
    let e := Kernel.Ew.val Ew.fill Ew.i64 Ew.av (Int64.ofNat nr) (one (-1 : Int64).toUInt64)
      (← dense "wj" .long (Eval.groupEdge gs ids (colValue rt) bound nr)) n
    let e := if off == 0 then e else Kernel.Ew.val Ew.add Ew.i64 Ew.va mn e (one off.toUInt64) n
    pure (Kernel.Ew.val Ew.greater Ew.i64 Ew.vv mn starts e n)
  let los ← edges lo (if prevailing then 0 else 1)
  -- an inverted run is empty: `0 | hi - lo`
  let lens := Kernel.Ew.val Ew.greater Ew.i64 Ew.av mn (one 0)
    (Kernel.Ew.val Ew.sub Ew.i64 Ew.vv mn (← edges (colValue w₁) 1) los n) n
  let (i, w) := expand lens
  let rows := Alg.add (Alg.gather 8 los i) w
  partedP "wj" (concatBytes #[one 0, Alg.sums lens]) (← Arr.of .long (Alg.len rows) (Alg.longs rows) "wj")

/-- `wj` with the aggregate `::`: the windows `wjP` as q's nested list, one boxed row list per left row. -/
def wj (prevailing : Bool) (w₀ w₁ : KCol) (l r : Array KCol) (rt : KCol) : Except String ((g : Nat) × Arr .general g) := do
  boxed (← wjP prevailing w₀ w₁ l r rt)

/-- `wj[w;c;t;(q;(f;c))]` with `f` one of `Coc.Over`'s folds, as q runs it: one `f/` per window, one atom per
    left row, no window boxed — the right column `c` gathered at `wjP`'s flat rows, then `Ops.overBy` over
    `wjP`'s own offsets. Answered at `Coc.Over.resultType`'s type, which comes with the answer. -/
def wjBy (op : Coc.Over) (prevailing : Bool) (w₀ w₁ : KCol) (l r : Array KCol) (rt c : KCol) :
    Except String ((u : QAtomicType) × (m : Nat) × Arr u m) := do
  let ⟨a, cc⟩ := c
  if a = .general then throw "wj: a general list aggregated column (q's 'type)"
  unless colRows c == colRows rt do throw s!"wj: {colRows c} values against {colRows rt} right rows (q's 'length)"
  let P ← wjP prevailing w₀ w₁ l r rt
  let x ← vec "wj" a (gatherColumn a cc (Alg.longs (← dense "wj" .long P.val.c)))
  let Q : Parted a := ⟨P.g, P.n, P.o, P.co, ← Arr.of a P.n x "wj"⟩
  let some ⟨u, s⟩ := Ops.overBy op Q | throw s!"wj: no grouped {repr op}/ over {repr a}"
  pure ⟨u, Q.g, s⟩

/-! ## Raze -/

/-- `raze` of a nested list of `v`s: the flat form's values (`Parted.ofBoxes`). -/
def raze (v : QAtomicType) {nx : Nat} (x : Arr .general nx) : Except String ((m : Nat) × Arr v m) := do
  let P ← Parted.ofBoxes v x
  pure ⟨P.n, P.val⟩

/-! ## Symbols and chars -/

/-- `x like p` on a symbol column: `likeSyms` over a `syms` blob; over an `enum` dictionary, then
    `maskByIds` carries the dictionary's bits to the elements. On `x`'s key. -/
def like {nx : Nat} (x : Arr .symbol nx) (p : String) : Except String (Arr .boolean nx) := do
  let pb := p.toUTF8
  let bits ← match x.c.enc with
    | .syms b o => pure (likeSyms pb b o)
    | .enum d dof ids =>
      pure ((likeSyms pb d dof).map fun m => maskByIds m (dof.size - 1).toUSize x.c.n.toUSize (Column.idWidth dof).toUSize ids)
    | _ => throw "x like p: the operand is neither a syms nor an enum column"
  let some bs := bits | throw s!"x like p: the pattern {p} does not parse (q's 'length or 'nyi)"
  onKey nx .boolean ⟨.boolean, nx, .bits bs, none⟩ "x like p"

/-- `x ss p` on a char list: the starts of the non-overlapping matches, `fixedHits`. -/
def ss {nx : Nat} (x : Arr .char nx) (p : String) : Except String ((m : Nat) × Arr .long m) := do
  let some hs := fixedHits p.toUTF8 (← dense "x ss p" .char x.c)
    | throw s!"x ss p: the pattern {p} is not fixed-width (q's 'nyi)"
  list .long (Alg.longs hs)

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
def Words (c : Column) : Prop :=
  match c.enc with
  | .bytes b => b.size % 8 = 0
  | _ => False

theorem words_bytes {c : Column} (h : Words c) : ∃ b, c.enc = .bytes b ∧ b.size % 8 = 0 := by
  unfold Words at h
  split at h
  · rename_i b hb; exact ⟨b, hb, h⟩
  · exact h.elim

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

/-- `sliceColumn` at a long `bytes` column: the dense arm, over the column or, empty, over its null. -/
theorem sliceColumn_long (n : Nat) (b : ByteArray) (off m : Nat) {a : Option (UInt8 × IndexCell)} :
    sliceColumn .long ⟨.long, n, .bytes b, a⟩ off m = some (.vector (Column.answer ⟨.long, m, .bytes
      (if n = 0 then cycleBytes (· * 8) 1 off m (Column.pushBits .empty 0x8000000000000000 8)
       else cycleBytes (· * 8) (b.size / 8) off m b), none⟩)) := by
  by_cases h : n = 0 <;>
    simp [sliceColumn, QAtomicType.width, h, nullColumn, foRColumn, Column.bytesOf, nullBits,
      Column.pushBits_size]

/-- `answer` keeps the header's count: every arm is `c` or `c` with its `enc` replaced. -/
theorem answer_n (c : Column) : (Column.answer c).n = c.n := by
  unfold Column.answer; repeat' split
  all_goals rfl

/-- The words of a long `bytes` column, read as longs, are its `toList`. -/
theorem toList_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.c.enc = .bytes b) :
    x.toList = (Verify.elemsW 8 b).map UInt64.toInt64 := Arr.toList_long x (by simp only [longWords, hc])

/-- A word list's `!` read under `toInt64` at an index in range. -/
theorem getElem!_map_toInt64 (E : List UInt64) (i : Nat) (h : i < E.length) :
    (E.map UInt64.toInt64)[i]! = E[i]!.toInt64 := by
  rw [getElem!_pos (E.map UInt64.toInt64) i (by simpa using h), getElem!_pos E i h, List.getElem_map]

/-- An `onKey` over a `vec` answer holds the `vec` payload. -/
theorem onKey_vec {verb s : String} {a : QAtomicType} {o : Option QValue} {m : Nat} {r : Arr a m}
    (h : (do onKey m a (← vec verb a o) s) = .ok r) : vec verb a o = .ok r.c := by
  cases hv : vec verb a o with
  | error e => simp [hv, bind, Except.bind] at h
  | ok c => simp only [hv, bind, Except.bind] at h; exact congrArg Except.ok (Find.onKey_c h).symm

/-- A slice of a long `bytes` column, in any `Arr` holding `vec`'s payload: `m` words from `off`, cycling. The
    column holds whole words and `off < n` unless no lap is run; an empty column is sliced only to nothing. -/
theorem slice_toList {nx : Nat} {x : Arr .long nx} {m' : Nat} {a : Arr .long m'} {b : ByteArray}
    {verb : String} {off m : Nat} (hc : x.c.enc = .bytes b) (h0 : 0 < nx ∨ m = 0)
    (h : off < nx ∨ off + m ≤ nx) (hb : off + m ≤ nx ∨ b.size % 8 = 0)
    (hv : vec verb .long (sliceColumn .long x.c off m) = .ok a.c) :
    a.toList = (List.range m).map fun j => x.toList[(off + j) % x.toList.length]! := by
  have hn : b.size / 8 = nx := Arr.n_long_bytes x hc
  rw [x.c_eq hc, sliceColumn_long] at hv
  simp only [vec, Column.answer_ty, beq_self_eq_true, ↓reduceIte, Except.ok.injEq] at hv
  by_cases hz : nx = 0
  · obtain rfl : m = 0 := by omega
    have hm : m' = 0 := by rw [← a.wf.2.1, ← hv, answer_n]
    subst hm
    simp only [List.range_zero, List.map_nil]; exact List.eq_nil_of_length_eq_zero (Arr.length_toList a)
  have hE : (Verify.elemsW 8 b).length = nx := by simp [Verify.elemsW, hn]
  have hW := elemsW_cycleBytes 8 (by decide) b off m (by omega) (by omega)
  have hs : (cycleBytes (· * 8) (b.size / 8) off m b).size / 8 = m := by
    have := congrArg List.length hW; simpa [Verify.elemsW] using this
  have hv' : a.c = Column.answer ⟨.long, (cycleBytes (· * 8) (b.size / 8) off m b).size / 8,
      .bytes (cycleBytes (· * 8) (b.size / 8) off m b), none⟩ := by rw [hs, ← hv, if_neg hz]
  rw [Arr.toList_long a (by rw [hv']; exact longWords_answer _), hW, toList_bytes x hc,
    List.map_map, List.length_map, hn]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp]
  rw [getElem!_map_toInt64 _ _ (by rw [hE]; exact Nat.mod_lt _ (by omega)), hE]

/-- `m` words of `xs` from `off`, cycling, with no lap run: the window `xs[off .. off + m)`. -/
theorem range_map_window {α : Type} [Inhabited α] (xs : List α) (off m : Nat) (h : off + m ≤ xs.length) :
    (List.range m).map (fun j => xs[(off + j) % xs.length]!) = (xs.drop off).take m := by
  rw [← cycle_list xs off m (.inr h), if_pos h, Nat.add_sub_cancel_left]

/-- **`n#x` is `takeSpec`** on a non-empty long column of whole words: `takeSpec`'s default element
    reads an empty `xs`, where q pads with nulls, so `nx ≠ 0`; a lap copies the payload, so `Words`. -/
theorem take_toList {n : Int} {nx : Nat} {x : Arr .long nx} {r : Arr .long n.natAbs}
    (hx : Words x.c) (h0 : 0 < nx) (h : take n x = .ok r) : r.toList = takeSpec n x.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  have hn : b.size / 8 = nx := Arr.n_long_bytes x hc
  have hl : x.toList.length = nx := Arr.length_toList _
  unfold take takeColumn at h
  rw [x.wf.2.1] at h
  rw [slice_toList hc (.inl h0) (.inl (by unfold takeFrom; split; omega; exact Nat.mod_lt _ h0)) (.inr hb) (onKey_vec h),
    takeSpec, hl]

/-- `dropColumn` of a long `bytes` column, in any `Arr` holding `vec`'s payload, is `dropSpec`: no lap is run, so
    any `bytes` payload. -/
theorem dropColumn_toList {nx : Nat} {x : Arr .long nx} {m' : Nat} {a : Arr .long m'} {verb : String}
    {n : Int} {b : ByteArray} (hc : x.c.enc = .bytes b) (hv : vec verb .long (dropColumn .long x.c n) = .ok a.c) :
    a.toList = dropSpec n x.toList := by
  have hl : x.toList.length = nx := Arr.length_toList _
  unfold dropColumn at hv
  simp only [x.wf.2.1] at hv
  rw [slice_toList hc (by omega) (.inr (by split <;> omega)) (.inl (by split <;> omega)) hv,
    range_map_window _ _ _ (by rw [hl]; split <;> omega)]
  unfold dropSpec
  by_cases hp : 0 ≤ n
  · simp only [hp, ↓reduceIte]
    rw [List.take_of_length_le (by simp [hl])]
    by_cases hk : n.toNat ≤ nx
    · congr 1; omega
    · rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.drop_eq_nil_of_le (by rw [hl]; omega)]
  · simp only [hp, ↓reduceIte, List.drop_zero]
    congr 1; omega

/-- **`n_x` is `dropSpec`** on a long `bytes` column. -/
theorem drop_toList {n : Int} {nx : Nat} {x : Arr .long nx} {r : Arr .long (nx - n.natAbs)} {b : ByteArray}
    (hc : x.c.enc = .bytes b) (h : drop n x = .ok r) : r.toList = dropSpec n x.toList :=
  dropColumn_toList hc (onKey_vec h)

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
theorem rotate_toList {n : Int} {nx : Nat} {x r : Arr .long nx}
    (hx : Words x.c) (h : rotate n x = .ok r) : r.toList = rotateSpec n x.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  have hn : b.size / 8 = nx := Arr.n_long_bytes x hc
  have hl : x.toList.length = nx := Arr.length_toList _
  unfold rotate rotateColumn at h
  simp only [x.wf.2.1] at h
  by_cases h0 : nx = 0
  · rw [slice_toList hc (.inr h0) (.inr (by simp [h0])) (.inl (by simp [h0])) (onKey_vec h),
      List.eq_nil_of_length_eq_zero (hl.trans h0)]
    simp [h0, rotateSpec]
  have hlt : (n.emod nx).toNat < nx := by
    have := Int.emod_lt_of_pos n (show (0 : Int) < nx by omega)
    have := Int.emod_nonneg n (show (nx : Int) ≠ 0 by omega)
    change (n % (nx : Int)).toNat < nx; omega
  simp only [show (nx == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte] at h
  have hne : ¬ x.toList.isEmpty = true := by
    rw [List.isEmpty_iff]; intro he; rw [he] at hl; simp at hl; omega
  rw [slice_toList hc (.inl (by omega)) (.inl hlt) (.inr hb) (onKey_vec h), rotateSpec, if_neg hne,
    rotateLeft_eq _ _ (by rw [hl]; exact hlt), hl]

/-- **`|x` is `List.reverse`** on a long `bytes` column, from `reverseBytes_spec`. -/
theorem reverse_toList {nx : Nat} {x r : Arr .long nx} {b : ByteArray}
    (hc : x.c.enc = .bytes b) (h : reverse x = .ok r) : r.toList = x.toList.reverse := by
  unfold reverse at h
  simp only [hc, x.c_eq hc, reverseColumn, foRColumn, rowWidth, denseWidth, QAtomicType.width, Column.bytesOf, vec, bind,
    Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
  rw [Arr.toList_long r (show longWords r.c = some (Verify.elemsW 8 (reverseBytes (8 : Nat).toUSize b)) by
    rw [Find.onKey_c h]; rfl), toList_bytes x hc]
  have e8 : (8 : Nat).toUSize.toNat = 8 := Find.usize_eight
  have := Verify.reverseBytes_spec (8 : Nat).toUSize (by rw [e8]; decide) (by rw [e8]; decide) b
  rw [e8] at this
  rw [this, List.map_reverse]

/-- Two dense long payloads meet densely: no part is encoded, so `encodedParts` has nothing to meet. -/
theorem razeColumn_bytes (n k : Nat) (b c : ByteArray) {a a' : Option (UInt8 × IndexCell)} :
    razeColumn .long #[⟨.long, n, .bytes b, a⟩, ⟨.long, k, .bytes c, a'⟩] =
      some (.vector ⟨.long, n + k, .bytes (concatBytes #[b, c]), none⟩) := by
  have he : encodedParts .long #[⟨.long, n, .bytes b, a⟩, ⟨.long, k, .bytes c, a'⟩] = none := by
    first
    | rfl
    | (simp [encodedParts, Column.alpEncodes, Column.encodes]; done)
    | (simp [encodedParts, Column.alpEncodes, Column.encodes, ← Array.any_toList]; done)
  first
  | (simp [razeColumn, he, Column.bytesOf]; done)
  | (simp [razeColumn, he, Column.bytesOf, ← Array.mapM_toList]; done)
  | (simp only [razeColumn, he]; rfl)

/-- **`x,y` is `++`** on long `bytes` columns, `x` of whole words: `concatBytes` copies `x`'s payload whole. -/
theorem concat_toList {nx ny : Nat} {x : Arr .long nx} {y : Arr .long ny} {r : Arr .long (nx + ny)}
    {c : ByteArray} (hx : Words x.c) (hc' : y.c.enc = .bytes c) (h : concat x y = .ok r) :
    r.toList = x.toList ++ y.toList := by
  obtain ⟨b, hc, hb⟩ := words_bytes hx
  unfold concat at h
  rw [x.c_eq hc, y.c_eq hc', razeColumn_bytes] at h
  simp only [vec, bind, Except.bind, show (QAtomicType.long == QAtomicType.long) = true from rfl, ↓reduceIte] at h
  rw [Arr.toList_long r (show longWords r.c = some (Verify.elemsW 8 (concatBytes #[b, c])) by
    rw [Find.onKey_c h]; rfl), toList_bytes x hc, toList_bytes y hc',
    show concatBytes #[b, c] = (ByteArray.empty ++ b) ++ c from rfl,
    elemsW_append 8 (by decide) _ _ (by rw [ByteArray.size_append]; simpa using hb),
    elemsW_append 8 (by decide) _ _ (by rfl), elemsW_empty, List.nil_append, List.map_append]

/-- A long column's words are its fixed-width reads, `Column.raw`. -/
theorem raw_long {c : Column} {ws : List UInt64} (ht : c.ty = .long) (hw : c.WF) (h : longWords c = some ws) :
    (Column.raw c).toList = ws := by
  obtain ⟨t, n, e⟩ := c
  simp only at ht; subst ht
  cases e with
  | bytes b =>
    simp only [longWords, Option.some.injEq] at h; subst h
    have hn : b.size / 8 = n := Arr.n_long_bytes (m := n) { c := ⟨.long, n, .bytes b, none⟩, wf := ⟨rfl, rfl, hw⟩ } rfl
    rw [Verify.raw_bytes .long 8 rfl (by decide) (by decide), Array.toList_map, Array.toList_range]
    simp only [Verify.elemsW, hn]
  | foR md pk =>
    simp only [longWords, Option.some.injEq] at h; subst h
    rw [Verify.raw_foR .long 8 rfl (by decide) (by decide), Array.toList_map, Array.toList_range]
  | _ => cases h

/-- A long column's encoded count is its row count, which the kernels take as a `USize`. -/
theorem countFits_long {m : Nat} (x : Arr .long m) {ws : List UInt64} (h : longWords x.c = some ws)
    (hm : m < USize.size) : Verify.countFits x.c := by
  obtain ⟨B, hc, -⟩ := Arr.dense_long x h hm
  rcases hc with hc | ⟨md, pk, hc, -⟩
  · simp only [Verify.countFits, hc]
  · simp only [Verify.countFits, hc, x.wf.2.1]; exact hm

/-- `vec` answers a payload only from a vector of its own type. -/
theorem vec_ok {verb : String} {a : QAtomicType} {o : Option QValue} {c : Column} (h : vec verb a o = .ok c) :
    o = some (.vector c) ∧ c.ty = a := by
  match o, h with
  | some (.vector c'), h =>
    simp only [vec] at h
    split at h
    · rename_i hb; cases h; exact ⟨rfl, beq_iff_eq.1 hb⟩
    · cases h

/-- A word read as a long: itself below `2^63`, wrapped past it. -/
theorem toInt_toInt64 (u : UInt64) :
    u.toInt64.toInt = if u.toNat < 2 ^ 63 then (u.toNat : Int) else u.toNat - 2 ^ 64 := by
  have : u.toInt64.toInt = u.toBitVec.toInt := rfl
  rw [this, BitVec.toInt_eq_toNat_cond]
  change (if 2 * u.toNat < 2 ^ 64 then (u.toNat : Int) else (u.toNat : Int) - 2 ^ 64) = _
  split <;> split <;> omega

/-- q's `x@i` at one index word `u`, read unsigned as `gatherAt` does with `0N` the fill, is `indexSpec`'s
    signed read while `|E| < 2^63`: a word at or past `2^63` is a negative long or `0N`, and misses as it
    misses `E`. -/
theorem index_word (E : List UInt64) (u : UInt64) (hn : E.length < 2 ^ 63) :
    (E.getD u.toNat 0x8000000000000000).toInt64 =
      if 0 ≤ u.toInt64 then (E.map UInt64.toInt64).getD u.toInt64.toInt.toNat Int64.minValue
      else Int64.minValue := by
  have hu := toInt_toInt64 u
  have hle : (0 : Int64) ≤ u.toInt64 ↔ 0 ≤ u.toInt64.toInt := by simp [Int64.le_iff_toInt_le]
  have hlt := UInt64.toNat_lt u
  by_cases h63 : u.toNat < 2 ^ 63
  · rw [if_pos h63] at hu
    rw [if_pos (hle.2 (by omega)), hu, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases E[u.toNat]? <;> rfl
  · rw [if_neg h63] at hu
    rw [if_neg (fun h => by have := hle.1 h; omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- **`x@y` is `indexSpec 0N`** on long columns, each `bytes` or `foR` (`longWords`), from
    `gatherColumn_raw`: the kernel reads an index unsigned (`gatherAt`), q signed, and the two agree
    while `nx < 2^63`; the `USize` bounds are `countFits`, the kernels counting in `USize`. -/
theorem index_toList {nx ny : Nat} {x : Arr .long nx} {y r : Arr .long ny}
    {xs ws : List UInt64} (hx : longWords x.c = some xs) (hy : longWords y.c = some ws)
    (hxU : nx < USize.size) (hyU : ny < USize.size) (hn : nx < 2 ^ 63) (h : index x y = .ok r) :
    r.toList = indexSpec Int64.minValue x.toList y.toList := by
  unfold index at h
  cases hv : vec "x@y" .long (gatherColumn .long x.c y.c) with
  | error e => rw [hv] at h; cases h
  | ok c =>
    rw [hv] at h
    simp only [bind, Except.bind] at h
    have rc : r.c = c := Find.onKey_c h
    have hg := (vec_ok hv).1
    have hA : ∀ M P a, x.c.enc = .alp M P a → Column.alpF32 a = (8 == 4) := fun _ _ _ he => by
      simp [longWords, he] at hx
    obtain ⟨_, _, -, -, hcB⟩ := Verify.gatherColumn_fixed_shape (t := .long) (w := 8) rfl _ _ c x.wf.1 y.wf.1
      (countFits_long y hy hyU) hA hg
    have hraw := Verify.gatherColumn_raw (t := .long) (w := 8) rfl _ _ c x.wf.1 x.wf.2.2 y.wf.1 y.wf.2.2
      (countFits_long x hx hxU) (countFits_long y hy hyU) hA hg
    have hcw : c.ty = .long ∧ c.WF := by rw [← rc]; exact ⟨r.wf.1, r.wf.2.2⟩
    have hw : longWords c = some (Column.raw c).toList := by
      cases hl : longWords c with
      | none => rw [hcB] at hl; cases hl
      | some ws => rw [raw_long hcw.1 hcw.2 hl]
    have hlen : xs.length < 2 ^ 63 := by
      have := Arr.length_toList x; rw [Arr.toList_long x hx, List.length_map] at this; omega
    rw [Arr.toList_long r (show longWords r.c = _ by rw [rc]; exact hw), hraw, raw_long x.wf.1 x.wf.2.2 hx,
      raw_long y.wf.1 y.wf.2.2 hy, Arr.toList_long x hx,
      Arr.toList_long y hy, indexSpec, List.map_map, List.map_map]
    refine List.map_congr_left fun u _ => ?_
    exact (congrArg UInt64.toInt64 (Verify.ofNat_toNat_mod64 _)).trans (index_word xs u hlen)

/-- Positions `[0, c g)`, each labelled `f` of how many of the cuts `c 1 … c g` lie at or below it, are `g`
    runs, run `r` being `c (r+1) − c r` copies of `f r`, for cuts ascending from `c 0 = 0`. -/
theorem runs_countP {α : Type} (f : Nat → α) (c : Nat → Nat) (h0 : c 0 = 0) :
    ∀ g, (∀ r, r < g → c r ≤ c (r+1)) →
      (List.range (c g)).map (fun i => f ((List.range g).countP fun r => decide (c (r+1) ≤ i))) =
        (List.range g).flatMap fun r => List.replicate (c (r+1) - c r) (f r)
  | 0, _ => by simp [h0]
  | g + 1, hm => by
    have mono : ∀ d r, r + d = g → c r ≤ c g := by
      intro d; induction d with
      | zero => intro r h; rw [← h, Nat.add_zero]; exact Nat.le_refl _
      | succ d ih => intro r h; exact Nat.le_trans (hm r (by omega)) (ih (r+1) (by omega))
    obtain ⟨d, hd⟩ : ∃ d, c (g+1) = c g + d := ⟨_, (Nat.add_sub_cancel' (hm g (by omega))).symm⟩
    rw [List.range_succ, List.flatMap_append, ← runs_countP f c h0 g (fun r hr => hm r (by omega)),
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hd, Nat.add_sub_cancel_left, List.range_add,
      List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.1 hi
      have : ¬ c (g + 1) ≤ i := by omega
      simp [List.countP_append, this]
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, fun a ha => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
      have hj := List.mem_range.1 hj
      simp only [Function.comp]
      rw [List.countP_append, List.countP_eq_length.2 (fun r hr => decide_eq_true (by
        have := mono (g - (r+1)) (r+1) (by have := List.mem_range.1 hr; omega); omega))]
      have : ¬ c (g + 1) ≤ c g + j := by omega
      simp [this]

/-- Under `Cuts o n`, the offsets read as naturals start at `0`, end at `n` and ascend. -/
theorem cuts_nat {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) :
    (o.toList[0]!).toNatClampNeg = 0 ∧ (o.toList[g]!).toNatClampNeg = n ∧
      ∀ r, r < g → (o.toList[r]!).toNatClampNeg ≤ (o.toList[r+1]!).toNatClampNeg := by
  have hc : ∀ r, r ≤ g → ((o.toList[r]!).toNatClampNeg : Int) = (o.toList[r]!).toInt := fun r hr => by
    rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg (cuts_get co (Nat.le_refl r) hr).1
  have e : ∀ m (hm : m ≤ g), o.toList[m]! = o.get ⟨m, by omega⟩ := fun m hm => by
    rw [getElem!_pos _ m (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
  refine ⟨by rw [e 0 (by omega)]; exact congrArg Int64.toNatClampNeg co.2.1, ?_, fun r hr => ?_⟩
  · have := hc g (Nat.le_refl g); rw [e g (Nat.le_refl g)] at this
    have h2 := co.2.2; simp only [Fin.last] at h2; rw [e g (Nat.le_refl g)]; omega
  · have := (cuts_get co (i := r) (j := r + 1) (by omega) hr).2.1; have := hc r (by omega); have := hc (r+1) hr; omega

/-- **A flat form's groups are its runs**: under `Cuts o n`, the group of `i` is the run `r` with
    `o[r] ≤ i < o[r+1]` (`Parted.group`), so the groups are `o[r+1] − o[r]` copies of each `r` in turn. -/
theorem keys_toList {v : QAtomicType} (P : Parted v) :
    (List.ofFn fun i : Fin P.n => Int64.ofNat (P.key i)) = (List.range P.g).flatMap fun r =>
      List.replicate ((P.o.toList[r+1]!).toNatClampNeg - (P.o.toList[r]!).toNatClampNeg) (Int64.ofNat r) := by
  obtain ⟨g, n, o, co, val⟩ := P
  dsimp only
  have hc : ∀ r, r ≤ g → ((o.toList[r]!).toNatClampNeg : Int) = (o.toList[r]!).toInt := fun r hr => by
    rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg (cuts_get co (Nat.le_refl r) hr).1
  have e : ∀ m (hm : m ≤ g), o.toList[m]! = o.get ⟨m, by omega⟩ := fun m hm => by
    rw [getElem!_pos _ m (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
  obtain ⟨h0, cg, mono⟩ := cuts_nat co
  rw [← runs_countP Int64.ofNat (fun r => (o.toList[r]!).toNatClampNeg) h0 g mono]
  apply List.ext_getElem (by simp only [List.length_ofFn, List.length_map, List.length_range, cg])
  intro i h1 h2
  have hi : i < n := by simpa using h1
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · rw [h0] at cg; omega
    · exact h
  have hgrp : Parted.group o i = (List.range g).countP fun r => decide ((o.toList[r+1]!).toNatClampNeg ≤ i) := by
    unfold Parted.group
    rw [show List.range g = (List.finRange g).map Fin.val from List.ext_getElem (by simp) (fun j _ _ => by simp),
      List.countP_map]
    congr 1; funext r
    have := hc (r.val+1) (by omega)
    have e' : o.get r.succ = o.toList[r.val+1]! := (e (r.val+1) (by omega)).symm
    simp only [Function.comp, e']
    exact decide_eq_decide.2 (by omega)
  have hlt : ((List.range g).countP fun r => decide ((o.toList[r+1]!).toNatClampNeg ≤ i)) < g := by
    have := (List.length_filter_lt_length_iff_exists (l := List.range g)
      (p := fun r => decide ((o.toList[r+1]!).toNatClampNeg ≤ i))).2 ⟨g-1, List.mem_range.2 (by omega),
      by simp only [Nat.sub_add_cancel hg, decide_eq_true_eq, cg]; omega⟩
    rw [List.countP_eq_length_filter]; simpa using this
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Parted.key]
  rw [hgrp, Nat.min_eq_left (by omega)]

/-- `d` copies of `a` zipped with `zs`: the first `d` of `zs`, each paired with `a`. -/
theorem zip_replicate {α β : Type} (a : α) : ∀ (d : Nat) (zs : List β),
    (List.replicate d a).zip zs = (zs.take d).map (a, ·)
  | 0, _ => by simp
  | _ + 1, [] => by simp
  | d + 1, z :: zs => by simp [List.replicate_succ, zip_replicate a d zs]

/-- Runs of keys zipped with a list at least as long: run `r`, `c (r+1) − c r` copies of `f r`, meets the
    elements from `c r`, for cuts ascending from `c 0 = 0`. -/
theorem zip_runs {α β : Type} (f : Nat → α) (c : Nat → Nat) (h0 : c 0 = 0) : ∀ g, (∀ r, r < g → c r ≤ c (r+1)) →
    ∀ ys : List β, c g ≤ ys.length →
      ((List.range g).flatMap fun r => List.replicate (c (r+1) - c r) (f r)).zip ys =
        (List.range g).flatMap fun r => ((ys.drop (c r)).take (c (r+1) - c r)).map (f r, ·)
  | 0, _, _, _ => by simp
  | g + 1, hm, ys, hy => by
    have hm' : ∀ r, r < g → c r ≤ c (r+1) := fun r hr => hm r (by omega)
    have mono : ∀ d r, r + d = g → c r ≤ c g := by
      intro d; induction d with
      | zero => intro r h; rw [← h, Nat.add_zero]; exact Nat.le_refl _
      | succ d ih => intro r h; exact Nat.le_trans (hm r (by omega)) (ih (r+1) (by omega))
    have hg := hm g (by omega)
    have hlen := congrArg List.length (runs_countP f c h0 g hm')
    simp only [List.length_map, List.length_range] at hlen
    conv => lhs; rw [← List.take_append_drop (c g) ys]
    rw [List.range_succ, List.flatMap_append, List.flatMap_append,
      List.zip_append (by rw [← hlen, List.length_take]; omega), zip_runs f c h0 g hm' _ (by rw [List.length_take]; omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, zip_replicate]
    congr 1
    exact congrArg List.flatten (List.map_congr_left fun r hr => by
      have := mono (g - (r+1)) (r+1) (by have := List.mem_range.1 hr; omega)
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)])

/-- **A flat form lists its runs**: run `r` is the values `[o[r], o[r+1])`, each beside `r`. -/
theorem parted_toList {v : QAtomicType} (P : Parted v) :
    P.toList = (List.range P.g).flatMap fun r =>
      ((P.val.toList.drop (P.o.toList[r]!).toNatClampNeg).take
        ((P.o.toList[r+1]!).toNatClampNeg - (P.o.toList[r]!).toNatClampNeg)).map (Int64.ofNat r, ·) := by
  have hz : P.toList = (List.ofFn fun i : Fin P.n => Int64.ofNat (P.key i)).zip P.val.toList :=
    List.ext_getElem (by simp [Parted.toList, Arr.toList]) fun i _ _ => by simp [Parted.toList, Arr.toList]
  obtain ⟨h0, cg, mono⟩ := cuts_nat P.co
  rw [hz, keys_toList]
  exact zip_runs Int64.ofNat (fun r => (P.o.toList[r]!).toNatClampNeg) h0 P.g mono _
    (by dsimp only; rw [cg, Arr.length_toList]; exact Nat.le_refl _)

/-- An `Arr.of` answer holds the payload it was given. -/
theorem of_c {t : QAtomicType} {n : Nat} {c : Column} {w : String} {a : Arr t n} (h : Arr.of t n c w = .ok a) :
    a.c = c := by
  unfold Arr.of at h; split at h
  · cases h; rfl
  · cases h

/-- What `partedP` answers: `val` cut by offsets whose payload is `B`, cuts of `n`. -/
theorem parted_ok {v : QAtomicType} {n : Nat} {verb : String} {B : ByteArray} {val : Arr v n} {r : Parted v}
    (h : partedP verb B val = .ok r) : ∃ (g : Nat) (o : Arr .long (g+1)) (co : Cuts o n),
      o.c.enc = .bytes B ∧ r = ⟨g, n, o, co, val⟩ := by
  unfold partedP at h
  cases ha : Arr.of .long (B.size / 8 - 1 + 1) (Alg.longs B) verb with
  | error e => simp [ha, bind, Except.bind] at h
  | ok oa =>
    have hoa := of_c ha
    cases hk : Parted.of? oa val with
    | none => simp [ha, hk, bind, Except.bind] at h
    | some P =>
      simp only [ha, hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      unfold Parted.of? at hk
      rw [hoa] at hk
      simp only [Alg.longs, longBytes, bind, Option.bind] at hk
      repeat' split at hk
      all_goals first | (cases hk; exact ⟨_, _, _, rfl, rfl⟩) | cases hk

/-- Element `r ≤ |xs|` of `xs` closed by `y`. -/
theorem getElem!_concat {α : Type} [Inhabited α] (xs : List α) (y : α) {r : Nat} (hr : r ≤ xs.length) :
    (xs ++ [y])[r]! = if r < xs.length then xs[r]! else y := by
  rcases Nat.lt_or_eq_of_le hr with h | rfl
  · rw [if_pos h, getElem!_pos _ r (by simp; omega), getElem!_pos xs r h, List.getElem_append_left h]
  · simp

/-- Runs read off offsets `s + c r` of `xs` are `cutSpec os xs`, for `os` and `|xs|` the offsets. -/
theorem cutSpec_of {α : Type} {os : List Int64} {xs : List α} {g s : Nat} (c : Nat → Nat) (hg : os.length = g)
    (hc : ∀ r, r ≤ g → (os.map (·.toInt.toNat) ++ [xs.length])[r]! = s + c r) :
    ((List.range g).flatMap fun r => (((xs.drop s).drop (c r)).take (c (r+1) - c r)).map (Int64.ofNat r, ·)) =
      cutSpec os xs := by
  subst hg
  exact congrArg List.flatten (List.map_congr_left fun r hr => by
    have hr := List.mem_range.1 hr
    rw [hc r (by omega), hc (r+1) (by omega), List.drop_drop, Nat.add_sub_add_left])

/-- `a + −o₀` at `i64`, read back: for `0 < o₀`, a sum in `[0, 2^63 − o₀)` is the exact difference, since a `0N`
    operand answers `0N < 0` and a wrapped difference lies at or above `2^63 − o₀`. -/
theorem add_neg_toInt {a o₀ : Int64} (h0 : 0 < o₀.toInt) (hw0 : 0 ≤ (Ew.intStep Ew.add Int64.minValue a (-o₀)).toInt)
    (hw : (Ew.intStep Ew.add Int64.minValue a (-o₀)).toInt + o₀.toInt < 2 ^ 63) :
    a.toInt = (Ew.intStep Ew.add Int64.minValue a (-o₀)).toInt + o₀.toInt := by
  have bm : ∀ t : Int, t.bmod (2^64) = t % 2^64 ∨ t.bmod (2^64) = t % 2^64 - 2^64 := fun t => by
    dsimp only [Int.bmod]; split <;> simp
  unfold Ew.intStep at hw0 hw ⊢
  simp only [show (Ew.add == Ew.add) = true by decide, if_true] at hw0 hw ⊢
  split at hw0
  · exact absurd hw0 (by decide)
  · rename_i hnul
    simp only [hnul, Bool.false_eq_true, if_false] at hw ⊢
    rw [Int64.toInt_add, Int64.toInt_neg] at hw0 hw ⊢
    have := Int64.le_toInt a; have := Int64.toInt_lt a; have := Int64.toInt_lt o₀
    rcases bm (-o₀.toInt) with e | e <;> rw [e] at hw0 hw ⊢ <;>
      rcases bm (a.toInt + (-o₀.toInt % 2 ^ 64)) with f | f <;> try rcases bm (a.toInt + (-o₀.toInt % 2 ^ 64 - 2 ^ 64)) with f | f
    all_goals omega

/-- **`o cut x` is `cutSpec`** on long `bytes` columns, `o` of whole words. Above a first offset `o₀ > 0` the
    offsets are lowered by `o₀` in 64 bits (`plus`), so `nx < 2^63` keeps a wrapped difference from reading as
    cuts, and the kernel counts `o` in a `USize`. -/
theorem cut_toList {no nx : Nat} {o : Arr .long no} {x : Arr .long nx} {r : Parted .long}
    {b : ByteArray} (hw : Words o.c) (hc : x.c.enc = .bytes b) (hn : nx < 2 ^ 63) (hoU : no < USize.size)
    (h : cutP o x = .ok r) : r.toList = cutSpec o.toList x.toList := by
  obtain ⟨ob, ho, hob⟩ := words_bytes hw
  have hl : x.toList.length = nx := Arr.length_toList _
  have hol : o.toList.length = no := Arr.length_toList _
  have hos := toList_bytes o ho
  have hE : (Verify.elemsW 8 ob).length = no := by simp [Verify.elemsW, Arr.n_long_bytes o ho]
  have one8 : ∀ v, (one v).size = 8 := fun v => by simp [one, Column.pushBits_size]
  have w1 : ∀ v, Verify.elemsW 8 (one v) = [v] := fun v => by
    have := Verify.bitsAt_pushBits8 ByteArray.empty v
    rw [show ByteArray.empty.size = 0 from rfl] at this
    simp [Verify.elemsW, one8]; exact this
  -- the offsets `P` closed by `N`, as `parted` reads them, and the run read at `os`
  have words : ∀ {P : ByteArray} {N g : Nat} {oa : Arr .long (g+1)}, P.size % 8 = 0 →
      oa.c.enc = .bytes (concatBytes #[P, one N.toUInt64]) →
      oa.toList = (Verify.elemsW 8 P).map UInt64.toInt64 ++ [N.toUInt64.toInt64] := fun hP hoa => by
    rw [toList_bytes _ hoa, elemsW_concatBytes 8 (by decide) _ (by simp [hP, one8])]
    simp [w1]
  unfold cutP at h
  rw [o.c_eq ho, show dense "o cut x" .long ⟨.long, no, .bytes ob, o.attrCell⟩ = pure ob from rfl, pure_bind] at h
  generalize ho₀ : (if no = 0 then (0 : Int64) else (Column.bitsAt ob 0 8).toInt64) = o₀ at h
  dsimp only at h
  split at h
  · simp [bind, Except.bind] at h
  rename_i hd
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int64.not_lt] at hd
  simp only [pure_bind] at h
  split at h
  · -- `o₀ = 0`: `x` untouched, the offsets as they are
    rw [bind_pure] at h
    obtain ⟨g, oa, co, hoa, rfl⟩ := parted_ok h
    have hW := words hob hoa
    obtain ⟨h0, cg, -⟩ := cuts_nat co
    have hg : g = no := by
      have := congrArg List.length hW
      simp only [List.length_append, List.length_map, List.length_singleton, hE] at this; have := Arr.length_toList oa; omega
    subst g
    have hcr : ∀ r, r ≤ no → (o.toList.map (·.toInt.toNat) ++ [x.toList.length])[r]! =
        0 + (oa.toList[r]!).toNatClampNeg := fun r hr => by
      rw [getElem!_concat _ _ (by simpa [hol] using hr)]
      simp only [List.length_map, hol]
      split
      · rename_i h1
        rw [hW, getElem!_concat _ _ (by simp [hE]; omega), if_pos (by simp [hE]; omega), hos, Nat.zero_add,
          getElem!_pos _ r (by simp [hE]; omega), getElem!_pos _ r (by simp [hE]; omega), List.getElem_map,
          List.getElem_map, Int64.toNat_toInt]
      · rename_i h1
        obtain rfl : r = no := by omega
        rw [Nat.zero_add, hl, cg]
    rw [parted_toList,
      ← cutSpec_of (fun r => (oa.toList[r]!).toNatClampNeg) hol hcr]
    simp only [List.drop_zero]
  · -- `o₀ > 0`: `x` dropped by `o₀`, the offsets lowered by it
    rename_i hne
    have h0₀ : 0 < o₀.toInt := by
      have := Int64.le_iff_toInt_le.1 hd.1
      have : o₀.toInt ≠ 0 := fun e => hne (Int64.toInt_inj.1 e)
      simp at *; omega
    cases hv : vec "o cut x" .long (dropColumn .long x.c o₀.toInt) with
    | error e => simp [hv, bind, Except.bind] at h
    | ok cv =>
      cases ha : Arr.of .long (nx - o₀.toNatClampNeg) cv "o cut x" with
      | error e => simp [hv, ha, bind, Except.bind] at h
      | ok a =>
        simp only [hv, ha, bind, Except.bind] at h
        have hxs : a.toList = x.toList.drop o₀.toNatClampNeg := by
          rw [dropColumn_toList hc (by rw [of_c ha]; exact hv), dropSpec, if_pos (by omega), Int64.toNat_toInt]
        have hP : (plus ob (-o₀)).size = 8 * no := by
          rw [plus, (Verify.val_spec _ _ _ _ _ _ _).1, show Ew.width Ew.i64 = 8 from rfl, show Alg.len ob = ob.size / 8 from rfl,
            Arr.n_long_bytes o ho, USize.toNat_ofNat_of_lt' hoU]
        have hPw : Verify.elemsW 8 (plus ob (-o₀)) = (List.range no).map fun i =>
            (Ew.intStep Ew.add Int64.minValue (Column.bitsAt ob (i * 8) 8).toInt64 (-o₀)).toUInt64 := by
          rw [plus, show Alg.len ob = no from Arr.n_long_bytes o ho, show one (-o₀).toUInt64 = atomBytes Ew.i64 (-o₀).toUInt64 from rfl,
            Verify.val_i64_va _ _ _ _ _ hoU, Int64.toInt64_toUInt64]; rfl
        obtain ⟨g, oa, co, hoa, rfl⟩ := parted_ok h
        have hW := words (by omega) hoa
        obtain ⟨h0, cg, -⟩ := cuts_nat co
        have hg : g = no := by
          have := congrArg List.length hW
          simp only [List.length_append, List.length_map, List.length_singleton, hPw,
            List.length_range] at this; have := Arr.length_toList oa; omega
        subst g
        have hcr : ∀ r, r ≤ no → (o.toList.map (·.toInt.toNat) ++ [x.toList.length])[r]! =
            o₀.toNatClampNeg + (oa.toList[r]!).toNatClampNeg := fun r hr => by
          rw [getElem!_concat _ _ (by simpa [hol] using hr)]
          simp only [List.length_map, hol]
          split
          · rename_i h1
            obtain ⟨a0, -, am⟩ := cuts_get co (Nat.le_refl r) (Nat.le_of_lt h1)
            have hlenP : (Verify.elemsW 8 (plus ob (-o₀))).length = no := by simp [hPw]
            have hWr : oa.toList[r]! = Ew.intStep Ew.add Int64.minValue (Column.bitsAt ob (r * 8) 8).toInt64 (-o₀) := by
              rw [hW, getElem!_concat _ _ (by simp [hlenP]; omega), if_pos (by simp [hlenP]; omega),
                getElem!_map_toInt64 _ _ (by omega), hPw, getElem!_pos _ r (by simp; omega)]
              simp [Int64.toInt64_toUInt64]
            have hor : o.toList[r]! = (Column.bitsAt ob (r * 8) 8).toInt64 := by
              rw [hos, getElem!_map_toInt64 _ _ (by omega), getElem!_pos _ r (by omega)]
              simp [Verify.elemsW]
            rw [hWr] at a0 am
            have := Int64.toNat_toInt o₀
            have := Int64.toNat_toInt (Ew.intStep Ew.add Int64.minValue (Column.bitsAt ob (r * 8) 8).toInt64 (-o₀))
            have := add_neg_toInt h0₀ a0 (by omega)
            rw [getElem!_pos _ r (by simp [hol]; omega), List.getElem_map,
              show o.toList[r]'(by omega) = o.toList[r]! from (getElem!_pos _ r (by omega)).symm, hor, hWr]
            omega
          · rename_i h1
            obtain rfl : r = no := by omega
            rw [hl, cg]; omega
        rw [parted_toList, hxs,
          ← cutSpec_of (fun r => (oa.toList[r]!).toNatClampNeg) hol hcr]

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

private def ans {α β : Type} (f : β → α) : Except String β → Option α
  | .ok r => some (f r)
  | .error _ => none
/-- A nested list of `v`s read through its flat form: the pairs `(run, element)`. -/
private def ansP (v : QAtomicType) : Except String ((g : Nat) × Arr .general g) → Option (List (Int64 × El v))
  | .ok r => (Parted.ofBoxes v r.2).toOption.map Parted.toList
  | .error _ => none
private abbrev Lg := QAtomicType.long
private def lv (xs : List Int64) (h : (Alg.longs (packLongs xs)).ty = .long ∧ (Alg.longs (packLongs xs)).n = xs.length ∧
    (Alg.longs (packLongs xs)).WF := by decide) : Arr .long xs.length := { c := Alg.longs (packLongs xs), wf := h }

private def xs := lv [5, 3, 5, 9, 3]
private def ys := lv [7, 8]
-- the five longs Frame-of-Reference encoded
private def xf : Arr .long 5 :=
  { c := ⟨.long, 5, .foR (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).2, none⟩,
    wf := ⟨rfl, rfl, foRLongs_wf [5, 3, 5, 9, 3]⟩ }
private def bs : Arr .boolean 5 := { c := ⟨.boolean, 5, .bits (ByteArray.mk #[0b10110]), none⟩, wf := by decide }
-- one symbol column `bc a bc` as `syms` and as `enum` over the dictionary `a, bc`
private def sy : Arr .symbol 3 :=
  { c := ⟨.symbol, 3, .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8], none⟩, wf := by decide }
private def se : Arr .symbol 3 :=
  { c := ⟨.symbol, 3, .enum (ByteArray.mk #[97, 0, 98, 99, 0]) #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!), none⟩, wf := by decide }
private def cs : Arr .char 6 := { c := ⟨.char, 6, .bytes "aaabaa".toUTF8, none⟩, wf := by decide }
-- the parted list `(10 20; 30)`, keys `0 0 1`
private def o2 : Arr .long 3 := { c := Alg.longs (packLongs [0, 2, 3]), wf := by decide }
private def pl : Except String ((g : Nat) × Arr .general g) := do
  let some P := Parted.of? o2 (lv [10, 20, 30]) | throw "pl: not cuts"
  boxed P

#guard [xs, xf].all fun x => ans (·.toList) (concat x ys) == some (x.toList ++ ys.toList)
#guard ans (·.toList) (concat bs bs) == some (bs.toList ++ bs.toList)
#guard [sy, se].all fun x => [sy, se].all fun y => ans (·.toList) (concat x y) == some (x.toList ++ y.toList)
#guard [xs, xf].all fun x => [7, -7, 2, -2, 0].all fun n => ans (·.toList) (take n x) == some (takeSpec n x.toList)
#guard ans (·.toList) (take (-7) xs) == some [9, 3, 5, 3, 5, 9, 3]
#guard [sy, se].all fun x => [4, -2].all fun n => ans (·.toList) (take n x) == some (takeSpec n x.toList)
#guard [xs, xf].all fun x => [2, -2, 9, -9, 0].all fun n => ans (·.toList) (drop n x) == some (dropSpec n x.toList)
#guard [sy, se].all fun x => ans (·.toList) (drop 1 x) == some (dropSpec 1 x.toList)
#guard [xs, xf].all fun x => ans (·.toList) (reverse x) == some x.toList.reverse
#guard [sy, se].all fun x => ans (·.toList) (reverse x) == some x.toList.reverse
#guard ans (·.toList) (reverse bs) == some bs.toList.reverse
#guard [xs, xf].all fun x => [2, -2, 7, 0].all fun n => ans (·.toList) (rotate n x) == some (rotateSpec n x.toList)
#guard ans (·.toList) (rotate 2 xs) == some [5, 9, 3, 5, 3]
#guard [sy, se].all fun x => ans (·.toList) (rotate (-1) x) == some (rotateSpec (-1) x.toList)
#guard [xs, xf].all fun x =>
  ans (·.toList) (index x (lv [4, 0, 7, -1])) == some (indexSpec Int64.minValue x.toList [4, 0, 7, -1])
#guard [sy, se].all fun x => ans (·.toList) (index x (lv [2, 1])) == some (indexSpec "" x.toList [2, 1])
#guard ans (·.toList) (amend xs (lv [1, 3, 1]) none (lv [0, 7, 2])) == some (amendSpec (fun _ y => y) xs.toList [1, 3, 1] [0, 7, 2])
#guard ans (·.toList) (amend xs (lv [1, 3, 1]) none (lv [0, 7, 2])) == some [5, 2, 5, 7, 3]
#guard [xs, xf].all fun x =>
  ans (·.toList) (amend x (lv [0, 0, 4, 0]) (some .add) (lv [1, 2, 3, 4])) == some (amendSpec (· + ·) x.toList [0, 0, 4, 0] [1, 2, 3, 4])
#guard ans (·.toList) (amend xs (lv [0, 0, 4, 0]) (some .add) (lv [1, 2, 3, 4])) == some [12, 3, 5, 9, 6]
#guard (amend xs (lv [5]) none (lv [0])).toOption.isNone
-- the other value types: `bits` (width 1), `float` with a `float` or a `long` `y`, `int` (width 4)
private def bs3 : Arr .boolean 3 := { c := ⟨.boolean, 3, .bits (ByteArray.mk #[0b101]), none⟩, wf := by decide }
private def fv (xs : List Float) : (m : Nat) × Arr .float m :=
  match Arr.of .float xs.length ⟨.float, xs.length, .bytes (xs.foldl (fun b x => pushBits b x.toBits 8) .empty), none⟩ "fv" with
  | .ok a => ⟨xs.length, a⟩ | .error _ => ⟨0, { c := ⟨.float, 0, .bytes .empty, none⟩, wf := by decide }⟩
private def iv (xs : List Int32) : (m : Nat) × Arr .int m :=
  match Arr.of .int xs.length ⟨.int, xs.length, .bytes (xs.foldl (fun b x => pushBits b x.toUInt32.toUInt64 4) .empty), none⟩ "iv" with
  | .ok a => ⟨xs.length, a⟩ | .error _ => ⟨0, { c := ⟨.int, 0, .bytes .empty, none⟩, wf := by decide }⟩
#guard [(Prim.Dyadic.greater, (· || ·)), (.lesser, (· && ·)), (.eq, (· == ·))].all fun (v, f) =>
  ans (·.toList) (amend bs (lv [0, 0, 4]) (some v) bs3) == some (amendSpec f bs.toList [0, 0, 4] bs3.toList)
#guard ans (·.toList) (amend bs (lv [0, 0, 4]) (some .greater) bs3) == some [true, true, true, false, true]
#guard ans (·.toList) (amend bs (lv [3, 0, 3]) none bs3) == some [false, true, true, true, true]
-- a float element is its IEEE bits (`Carrier .float`), read as a `Float` by `Float.ofBits`
private def fl {m : Nat} (r : Arr .float m) : List Float := r.toList.map Float.ofBits
#guard ans fl (amend (fv [1.5, 2.5, 4]).2 (lv [0, 2, 0]) (some .add) (fv [1, 2, 3]).2) == some (amendSpec (· + ·) [1.5, 2.5, 4] [0, 2, 0] [1, 2, 3])
#guard ans fl (amend (fv [1.5, 2.5, 4]).2 (lv [0, 2, 0]) (some .add) (fv [1, 2, 3]).2) == some [5.5, 2.5, 6]
#guard ans fl (amend (fv [1.5, 2.5, 4]).2 (lv [0, 2]) (some .add) (lv [1, 2])) == some [2.5, 2.5, 6]
#guard ans fl (amend (fv [1.5, 2.5, 4]).2 (lv [1, 1]) (some .lesser) (fv [2, 0.5]).2) == some [1.5, 0.5, 4]
#guard ans (·.toList) (amend (iv [1, 2, 3]).2 (lv [1, 1, 2]) (some .add) (iv [10, 20, 5]).2) ==
  some (amendSpec (· + ·) [1, 2, 3] [1, 1, 2] [10, 20, 5])
#guard ans (·.toList) (amend (iv [1, 2, 3]).2 (lv [1, 1, 2]) (some .add) (iv [10, 20, 5]).2) == some [1, 32, 8]
-- `:` keeps `x`'s type: a `long` `y` into a `float` list is q's 'type
#guard (amend (fv [1.5]).2 (lv [0]) none (lv [1])).toOption.isNone
-- `:` on symbols, every pair of encodings: `y` is `d a e` (`d`, `e` in neither `x` dictionary), the index
-- `2` repeated so the last write stays
private def sy3 : Arr .symbol 3 :=
  { c := ⟨.symbol, 3, .syms (ByteArray.mk #[100, 0, 97, 0, 101, 0]) #[0, 2, 4, 6], none⟩, wf := by decide }
private def se3 : Arr .symbol 3 :=
  { c := ⟨.symbol, 3, .enum (ByteArray.mk #[97, 0, 100, 0, 101, 0]) #[0, 2, 4, 6] (packIds (idWidth #[0, 2, 4, 6]) 3 fun i => [1, 0, 2][i]!), none⟩, wf := by decide }
#guard [sy, se].all fun x => [sy3, se3].all fun y =>
  ans (·.toList) (amend x (lv [2, 0, 2]) none y) == some (amendSpec (fun _ y => y) x.toList [2, 0, 2] y.toList)
#guard [sy, se].all fun x => [sy3, se3].all fun y => ans (·.toList) (amend x (lv [2, 0, 2]) none y) == some ["a", "a", "e"]
-- the encoding kept: a blob stays a blob only against a blob, an interned `x` stays interned
#guard ans (fun (r : Arr .symbol 3) => r.c.enc matches .syms ..) (amend sy (lv [0, 1, 2]) none sy3) == some true
#guard [sy3, se3].all fun y => ans (fun (r : Arr .symbol 3) => r.c.enc matches .enum ..) (amend se (lv [0, 1, 2]) none y) == some true
#guard ans (·.2.toList) (do raze Lg (← pl).2) == some [10, 20, 30]
#guard ansP Lg pl == some [(0, 10), (0, 20), (1, 30)]
#guard [sy, se].all fun x => ans (·.toList) (like x "b*") == some [true, false, true]
#guard [sy, se].all fun x => ans (·.toList) (like x "?") == some [false, true, false]
#guard ans (·.2.toList) (ss cs "aa") == some [0, 4]

-- parted lists, on `bytes` and on `foR` payloads
private def x6 := lv [1, 2, 3, 4, 5, 6]
private def x6f : Arr .long 6 :=
  { c := ⟨.long, 6, .foR (Coc.encode 8 (packLongs [1, 2, 3, 4, 5, 6])).1 (Coc.encode 8 (packLongs [1, 2, 3, 4, 5, 6])).2, none⟩,
    wf := ⟨rfl, rfl, foRLongs_wf [1, 2, 3, 4, 5, 6]⟩ }
#guard [xs, xf].all fun x => ansP Lg (cut (lv [0, 2, 2]) x) == some (cutSpec [0, 2, 2] x.toList)
#guard [xs, xf].all fun x => ans (·.toList) (cutP (lv [0, 2, 2]) x) == some (cutSpec [0, 2, 2] x.toList)
#guard ansP Lg (cut (lv [0, 2]) xf) == some [(0, 5), (0, 3), (1, 5), (1, 9), (1, 3)]
-- q: `2 4 _ til 6` is `(2 3;4 5)`; the rows before the first offset are dropped
#guard [x6, x6f].all fun x => ansP Lg (cut (lv [2, 4]) x) == some (runsSpec [[3, 4], [5, 6]])
#guard [x6, x6f].all fun x => ansP Lg (cut (lv [0, 2, 4]) x) == some (runsSpec [[1, 2], [3, 4], [5, 6]])
#guard [xs, xf].all fun x => ansP Lg (cut (lv [1, 2]) x) == some (cutSpec [1, 2] x.toList) &&
  ansP Lg (cut (lv [1, 1, 4]) x) == some (cutSpec [1, 1, 4] x.toList) && ansP Lg (cut (lv [5]) x) == some (cutSpec [5] x.toList)
#guard [(cut (lv [-1, 2]) xs), (cut (lv [0, 3, 2]) xs), (cut (lv [0, 9]) xs), (cut (lv [6]) xs)].all (·.toOption.isNone)
#guard [sy, se].all fun x => ansP .symbol (cut (lv [0, 1]) x) == some (cutSpec [0, 1] x.toList)
#guard [xs, xf].all fun x => ansP Lg (eachRight .add .long x ys) == some (eachRightSpec (· + ·) x.toList ys.toList)
#guard ansP .boolean (eachRight .lt .boolean xf (lv [5, 4])) == some (eachRightSpec (fun a b => decide (a < b)) xf.toList [5, 4])
#guard [x6, x6f].all fun x => ansP Lg (do flip .long (← cut (lv [0, 2, 4]) x).2) == some (runsSpec [[1, 3, 5], [2, 4, 6]])
#guard [x6, x6f].all fun x => ansP Lg (do flip .long (← flip .long (← cut (lv [0, 2, 4]) x).2).2) == some (cutSpec [0, 2, 4] x6.toList)
#guard (do flip .long (← cut (lv [0, 1, 4]) x6).2).toOption.isNone
#guard [xs, xf].all fun x => ansP Lg (do indexParted .long (← cut (lv [0, 2, 3]) x).2 (lv [2, 0, 5, -1, 3])) ==
  some (runsSpec [[9, 3], [5, 3], [], [], []])
#guard [sy, se].all fun x => ansP .symbol (do indexParted .symbol (← cut (lv [0, 1]) x).2 (lv [1, 1])) ==
  some (runsSpec [x.toList.drop 1, x.toList.drop 1])

-- joins: left keys `lk` (and `lk₂`), times `lt`; right keys `rk` (and `rk₂`), times `rt`
private def key (xs : List Int64) : Struct.KCol := ⟨.long, Alg.longs (packLongs xs)⟩
-- keys of any encoding: `bits` `101b` against `01b`, and `syms` `` `a`b `` against its interned self
#guard ans (·.toList) (ej #[⟨.boolean, ⟨.boolean, 3, .bits (ByteArray.mk #[0b101]), none⟩⟩] #[⟨.boolean, ⟨.boolean, 2, .bits (ByteArray.mk #[0b10]), none⟩⟩]) == some [(0, 1), (1, 0), (2, 1)]
#guard ans (·.toList) (ej #[⟨.symbol, ⟨.symbol, 2, .syms (ByteArray.mk #[97, 0, 98, 0]) #[0, 2, 4], none⟩⟩] #[⟨.symbol, Column.intern ⟨.symbol, 2, .syms (ByteArray.mk #[98, 0, 97, 0]) #[0, 2, 4], none⟩⟩]) == some [(0, 1), (1, 0)]
#guard (ej #[key [1]] #[⟨.boolean, ⟨.boolean, 1, .bits (ByteArray.mk #[1]), none⟩⟩]).toOption.isNone
private def lk : List Int64 := [1, 1, 2, 3]
private def lk₂ : List Int64 := [0, 1, 0, 0]
private def lt : List Int64 := [5, 10, 3, 4]
private def rk : List Int64 := [1, 2, 1, 2, 9]
private def rk₂ : List Int64 := [0, 0, 1, 0, 0]
private def rt : List Int64 := [3, 1, 7, 4, 0]
-- the right times also as a `foR` column, which `groupEdge` bisects where it lies
private def rtf : Struct.KCol := ⟨.long, ⟨.long, 5, .foR (Coc.encode 8 (packLongs rt)).1 (Coc.encode 8 (packLongs rt)).2, none⟩⟩
#guard ans (·.toList) (ej #[key lk] #[key rk]) == some (ejSpec (lk.map ([·])) (rk.map ([·])))
#guard ans (·.toList) (ej #[key lk] #[key rk]) == some [(0, 0), (0, 2), (1, 0), (1, 2), (2, 1), (2, 3)]
#guard ans (·.toList) (ej #[key lk, key lk₂] #[key rk, key rk₂]) == some (ejSpec (lk.zipWith (fun a b => [a, b]) lk₂) (rk.zipWith (fun a b => [a, b]) rk₂))
#guard ans (·.toList) (ij #[key lk] #[key rk]) == some [(0, 0), (1, 0), (2, 1)]
-- `aj` over keys interleaved in the right table (the hashed grouping), dense and `foR` times; key `3` is missing
#guard [key rt, rtf].all fun c => ans (·.2.toList) (aj #[key lk] #[key rk] (key lt) c) == some (ajSpec lk lt rk rt)
#guard ans (·.2.toList) (aj #[key lk] #[key rk] (key lt) (key rt)) == some [0, 2, 1, Int64.minValue]
-- two key columns
#guard ans (·.2.toList) (aj #[key lk, key lk₂] #[key rk, key rk₂] (key lt) (key rt)) ==
  some (ajSpec (lk.zip lk₂) lt (rk.zip rk₂) rt)
#guard ans (·.2.toList) (aj #[key lk, key lk₂] #[key rk, key rk₂] (key lt) (key rt)) == some [0, 2, 1, Int64.minValue]
-- q 4.1, ``aj[`s`t;flip `s`t!(`a`b;3 8);([]s:`a`a`a`a`b`b`b`b;t:5 1 9 2 5 1 9 2;v:10+10*til 8)]``: the groups
-- bisected as they lie answer `v` `20 60` (rows 1 5); `` `s`t xasc `` of the same rows answers `40 50` (rows 1 6)
private def sk : List Int64 := [0, 0, 0, 0, 1, 1, 1, 1]
#guard ans (·.2.toList) (aj #[key [0, 1]] #[key sk] (key [3, 8]) (key [5, 1, 9, 2, 5, 1, 9, 2])) == some [1, 5]
#guard ajSpec [0, 1] [3, 8] sk [5, 1, 9, 2, 5, 1, 9, 2] == [1, 5]
#guard ans (·.2.toList) (aj #[key [0, 1]] #[key sk] (key [3, 8]) (key [1, 2, 5, 9, 1, 2, 5, 9])) == some [1, 6]
#guard (aj #[key lk] #[key rk] (key lt) ⟨.int, ⟨.int, 10, .bytes (packLongs rt), none⟩⟩).toOption.isNone
private def w₀ : List Int64 := lt.map (· - 3)
#guard [false, true].all fun p => [key rt, rtf].all fun c =>
  ansP Lg (wj p (key w₀) (key lt) #[key lk] #[key rk] c) == some (wjSpec p lk w₀ lt rk rt)
-- q's `wj` reads a range of the right table: on interleaved keys `wj1`'s run for row 1 takes row 1 of key `2`
#guard ansP Lg (wj true (key w₀) (key lt) #[key lk] #[key rk] (key rt)) == some [(0, 0), (1, 2), (2, 1)]
#guard ansP Lg (wj false (key w₀) (key lt) #[key lk] #[key rk] (key rt)) == some [(0, 0), (1, 1), (1, 2), (2, 1)]
-- qlean's measured case: window `[4;6]` over the times `1 3 5` — `wj` takes the quote at `3`, prevailing on
-- entry, `wj1` does not; key `2` has only its prevailing row `3`, key `4` is missing
private def qk : List Int64 := [1, 1, 1, 2, 2]
private def qt : List Int64 := [1, 3, 5, 2, 8]
#guard [false, true].all fun p =>
  ansP Lg (wj p (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt)) == some (wjSpec p [1, 2, 4] [4, 4, 4] [6, 6, 6] qk qt)
#guard ansP Lg (wj true (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt)) == some [(0, 1), (0, 2), (1, 3)]
#guard ansP Lg (wj false (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt)) == some [(0, 2)]
/-- A `long` answer of `wjBy`, `none` at any other type. -/
private def ansL : Except String ((u : QAtomicType) × (m : Nat) × Arr u m) → Option (List Int64)
  | .ok ⟨.long, _, v⟩ => some v.toList
  | _ => none
/-- `wjBy`'s law on a value list `cv`: answer `i` is `f/` (here `+/`) of `cv` at window `i`'s rows, the runs
    `wjSpec` lists — `0` at an empty window. -/
private def wjSumSpec (p : Bool) (lk w₀ w₁ rk rt cv : List Int64) : List Int64 :=
  (List.range lk.length).map fun i => ((wjSpec p lk w₀ w₁ rk rt).filter (·.1 == Int64.ofNat i)).foldl
    (fun s (_, j) => s + cv[j.toNatClampNeg]!) 0
private def cv : List Int64 := (List.range rk.length).map fun j => Int64.ofNat (10 * j + 1)
#guard [false, true].all fun p => [key rt, rtf].all fun c =>
  ansL (wjBy .add p (key w₀) (key lt) #[key lk] #[key rk] c (key cv)) == some (wjSumSpec p lk w₀ lt rk rt cv)
#guard [false, true].all fun p =>
  ansL (wjBy .add p (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt) (key [1, 10, 100, 1000, 10000])) ==
    some (wjSumSpec p [1, 2, 4] [4, 4, 4] [6, 6, 6] qk qt [1, 10, 100, 1000, 10000])
#guard ansL (wjBy .add true (key [4, 4, 4]) (key [6, 6, 6]) #[key [1, 2, 4]] #[key qk] (key qt) (key [1, 10, 100, 1000, 10000])) ==
  some [110, 1000, 0]
#guard (ej #[key lk] #[]).toOption.isNone

end Checks

#print axioms concat
#print axioms take
#print axioms drop
#print axioms reverse
#print axioms rotate
#print axioms index
#print axioms amend
#print axioms raze
#print axioms cut_toList
#print axioms parted_toList
#print axioms like
#print axioms ss
#print axioms cut
#print axioms flip
#print axioms indexParted
#print axioms aj
#print axioms wj
#print axioms wjBy

end LeetQ.Rel.Struct
