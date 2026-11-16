import LeetQ.Run.Lang.Elab

/-! # Bit matrices: a closed term over small objects with no table at its inner nodes

`K₀ ∩ π₁\(sup(X) X)` as tables joins `sup(X)` with `X` row by row. As bit matrices (`Λ` of each relation, the
set of each element one bit row) the inner nodes are rows folded by one kernel, `bitRowsOver`:

```
u {π₁°} (u,m) {sup(K)} w {K} v        row (u,m) of sup(K) K  =  ∨ of K's bit rows at the w with (u,m) {sup(K)} w
                                      row u of π₁\(sup(K) K) =  ∧ of those rows over the m, i.e. over (u,m) {π₁} u
```

- `(S T)[x] = ∨ { T[w] ∣ x S w }`     // the row of `x` is the union of the rows of its `S`-successors
- `(R\M)[y] = ∧ { M[x] ∣ x R y }`     // the row of `y` is the intersection of the rows of its `R`-predecessors

A route is a term of `Tm` over the constructors that have a bit rule (`≫`, `°`, `∩`, `∪`, `−`, `\`), its other
sub-terms evaluated to their tables (`Tm.val`). Every column of the route is coded jointly per object and renumbered
`0 … n-1`, so a relation `A ⟶ B` is `|A| · |B|` bits; the route runs as bits only when every node's matrix is at most
`2²⁷` bits (`Tm.fits`, false at every other constructor), and is evaluated as its tables otherwise. The answer is
turned back into a table once, at the root. -/

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg

/-! ### The route: a term over its tables -/

/-- A binary C twin `op` on two results with their bits: its relation, and the `&&` of the inputs' bits and its own. -/
def opC {α β γ : Type} (op : α → β → γ × Bool) (r : α × Bool) (s : β × Bool) : γ × Bool :=
  let c := op r.1 s.1; (c.1, r.2 && s.2 && c.2)

/-- Whether the term is a table, the one leaf a route has. -/
def _root_.LeetQ.Rel.Lang.Tm.isVal {A B : Obj} {d : Bool} : Tm A B d → Bool
  | .val _ => true
  | _ => false

/-- A table leaf's relation, `𝟘` at any other term: the universes of `\` in a route. -/
def _root_.LeetQ.Rel.Lang.Tm.tab {A B : Obj} {d : Bool} : Tm A B d → Rel A B
  | .val R => R
  | _ => Alg.zero

/-- The route as a table and whether every node's op ran within capacity: `Alg`'s C twin at each node, what the expander
    runs for the term. Bit false at a constructor with no bit rule. -/
def _root_.LeetQ.Rel.Lang.Tm.tableC : {A B : Obj} → {d : Bool} → Tm A B d → Rel A B × Bool
  | _, _, _, .val R => (R, true)
  | _, _, _, .comp R S => let r := R.tableC; if r.1.n == 0 then (Alg.zero, r.2) else opC compC r S.tableC
  | _, _, _, .conv R => let r := R.tableC; (r.1°, r.2)
  | _, _, _, .meet R S => opC interC R.tableC S.tableC
  | _, _, _, .join R S => opC unionC R.tableC S.tableC
  | _, _, _, .diff R S => opC diffC R.tableC S.tableC
  | _, _, _, .ldiv R S UB UC => opC (leftDivC · · UB.tab.val UC.tab.val) R.tableC S.tableC
  | _, _, _, _ => (Alg.zero, false)

/-- The route as a table: `tableC`'s relation. -/
def _root_.LeetQ.Rel.Lang.Tm.table {A B : Obj} {d : Bool} (p : Tm A B d) : Rel A B := p.tableC.1

/-- A column of some object. -/
abbrev Col := (X : Obj) × Part X

def relCols {A B : Obj} (R : Rel A B) (cs : Array Col) : Array Col := (cs.push ⟨A, ⟨R.n, R.key⟩⟩).push ⟨B, ⟨R.n, R.val⟩⟩

/-- The tables' columns, two per table, in the order `Tm.bits` reads them back. -/
def _root_.LeetQ.Rel.Lang.Tm.cols : {A B : Obj} → {d : Bool} → Tm A B d → Array Col → Array Col
  | _, _, _, .val R, cs => relCols R cs
  | _, _, _, .comp R S, cs | _, _, _, .meet R S, cs | _, _, _, .join R S, cs | _, _, _, .diff R S, cs => S.cols (R.cols cs)
  | _, _, _, .conv R, cs => R.cols cs
  | _, _, _, .ldiv R S UB UC, cs => relCols UC.tab (relCols UB.tab (S.cols (R.cols cs)))
  | _, _, _, _, cs => cs

/-- Every matrix the route builds at most `2²⁷` bits (16 MB), `sz` each object's code count; false at a constructor with
    no bit rule. The left side of `≫` and `\` is read as its pairs (`Tm.pairs`): a table's from its codes, with no
    matrix. -/
def _root_.LeetQ.Rel.Lang.Tm.fits (sz : Obj → Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Bool
  | A, B, _, .val _ => sz A * sz B ≤ 2 ^ 27
  | A, B, _, .meet R S | A, B, _, .join R S | A, B, _, .diff R S => sz A * sz B ≤ 2 ^ 27 && R.fits sz && S.fits sz
  | A, B, _, .comp R S | A, B, _, .ldiv R S _ _ => sz A * sz B ≤ 2 ^ 27 && (R.isVal || R.fits sz) && S.fits sz
  | A, B, _, .conv R => sz A * sz B ≤ 2 ^ 27 && R.fits sz
  | _, _, _, _ => false

/-! ### Codes -/

/-- Each column's codes as longs, the columns of one object coded jointly (`Obj.codesC`) and renumbered
    `0 … n-1` by `groupIds` of their concatenation, so equal elements are equal codes and an object of `n`
    elements is `n` bits; and each object's elements at those codes, the parts razed and picked at each code's
    first row. `none` when a coding or a raze did not run within capacity. -/
def codeAll (cs : Array Col) : Option (Array ByteArray × Array Col) := do
  let mut out : Array ByteArray := Array.replicate cs.size .empty
  let mut sps : Array Col := #[]
  for c in cs do
    let A := c.1
    if sps.any (·.1 == A) then continue
    let js := (Array.range cs.size).filter fun j => (cs.getD j c).1 == A
    let parts : Array (Part A) := js.map fun j => match cs.getD j c with
      | ⟨B, p⟩ => if h : B = A then h ▸ p else ⟨0, Vals.empty A⟩
    let (codes, ok) := A.codesC (p := parts.size) ⟨parts, rfl⟩
    guard ok
    let cc := Code.cat codes.toArray
    let (gid, firsts) := cc.groupIds
    let ids := gatherPacked cc.n (Column.idWidthOf (len firsts)).toUSize 64 0 gid (tilLongs cc.n)
    let some (all, ok) := (if h : (parts.toList.map fun c : Part A => c.1.toNat).sum < USize.size then
      some (A.razeC parts h) else none) | none
    guard ok
    guard (Vals.fitsN A all (len firsts))
    sps := sps.push ⟨A, Vals.pickPart A all firsts⟩
    let mut o := 0
    for k in [0:js.size] do
      let n := (parts.getD k ⟨0, Vals.empty A⟩).1.toNat
      out := out.set! (js.getD k 0) (ids.extract (8 * o) (8 * (o + n)))
      o := o + n
  pure (out, sps)

/-! ### The matrices -/

/-- A relation between codes as `na` rows of `w` bits, row `i` at bits `[i·w, (i+1)·w)`: bit `i·w + j` is set
    when code `i` is related to code `j`. The payload is a boolean column's. -/
structure Bits where
  na : Nat
  w : Nat
  b : ByteArray

/-- `n` zero longs. -/
def zeros (n : Nat) : ByteArray := Kernel.Ew.val Ew.mul Ew.i64 Ew.va nul (tilLongs n.toUSize) (one 0) n.toUSize

/-- `na` rows of `w` bits, all `v`: `bitRowsOver` over `na` empty segments, which `∨` answers with zeros and
    `∧` with ones. -/
def Bits.const (v : Bool) (na w : Nat) : Bits := ⟨na, w, bitRowsOver v w.toUSize (zeros (na + 1)) .empty .empty⟩

/-- The matrix of the code pairs `(k[r], v[r])`: bit `k[r]·w + v[r]` set by `scatterPacked` at one bit. -/
def Bits.ofCodes (na w : Nat) (k v : ByteArray) : Bits :=
  let n := (len k).toUSize
  let ix := Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul (Kernel.Ew.val Ew.mul Ew.i64 Ew.va nul k (one w.toUInt64) n) v n
  ⟨na, w, scatterPacked 1 (Bits.const false na w).b ix ⟨#[1]⟩ 0 true⟩

/-- The set bits as code pairs `(i, j)`, `i` ascending: `whereBits`, then `÷ w` and `mod w`. -/
def Bits.pairs (x : Bits) : ByteArray × ByteArray :=
  let p := whereBits (x.na * x.w).toUSize x.b
  let m := (len p).toUSize
  (Kernel.Ew.val Ew.idiv Ew.i64 Ew.va nul p (one x.w.toUInt64) m,
    Kernel.Ew.val Ew.imod Ew.i64 Ew.va nul p (one x.w.toUInt64) m)

/-- `R°`: the pairs swapped and scattered. -/
def Bits.conv (x : Bits) : Bits := let (i, j) := x.pairs; Bits.ofCodes x.w x.na j i

/-- The `ng + 1` offsets of an ascending group column `g` over the groups `0 … ng-1`: `groupSizes`, `sums`. -/
def offsOf (ng : Nat) (g : ByteArray) : ByteArray :=
  concatBytes #[one 0, sums ng.toUSize (Order.groupSizes ng.toUSize 64 (len g).toUSize g)]

/-- `R S` from `R`'s pairs `i`, `j` (`i` ascending, below `na`): row `x` the `∨` of the rows of `S` at `x`'s
    `R`-successors. -/
def Bits.comp (na : Nat) (i j : ByteArray) (s : Bits) : Bits :=
  ⟨na, s.w, bitRowsOver false s.w.toUSize (offsOf na i) j s.b⟩

/-- The code pairs `(g, o)` with `g` ascending: `grade` of `g`, both gathered. -/
def sortBy (g o : ByteArray) : ByteArray × ByteArray :=
  let p := (Code.ofLongs g).grade
  (gather 8 g p, gather 8 o p)

/-- `∩`, `∪` and `−` of two matrices of one shape: `Ew.bit` lesser, greater, and lesser with `~`. -/
def Bits.meet (x y : Bits) : Bits := ⟨x.na, x.w, Ew.bit Ew.lesser Ew.vv x.b y.b (x.na * x.w).toUSize⟩
def Bits.join (x y : Bits) : Bits := ⟨x.na, x.w, Ew.bit Ew.greater Ew.vv x.b y.b (x.na * x.w).toUSize⟩
def Bits.diff (x y : Bits) : Bits := x.meet ⟨y.na, y.w, Ew.notBits (y.na * y.w).toUSize y.b⟩

/-- `R \ S` from `R°`'s pairs `y`, `a` (`y` ascending, below `nb`) and the universes' codes `ub`, `uc`: row `y`
    the `∧` of the rows of `S` at `y`'s `R`-predecessors. An empty segment answers ones; `leftDiv`'s vacuous
    clause keeps them only at `y ∈ Ub` and `c ∈ Uc`, so the rows are masked by `ran R ⊗ ⊤ ∪ Ub ⊗ Uc`, each a
    composition through the one point. -/
def Bits.ldiv (nb : Nat) (y a : ByteArray) (s : Bits) (ub uc : ByteArray) : Bits :=
  let d : Bits := ⟨nb, s.w, bitRowsOver true s.w.toUSize (offsOf nb y) a s.b⟩
  let ran := Bits.comp nb y (zeros (len y)) (Bits.const true 1 s.w)
  let (ub', _) := sortBy ub ub
  let vac := Bits.comp nb ub' (zeros (len ub)) (Bits.ofCodes 1 s.w (zeros (len uc)) uc)
  d.meet (ran.join vac)

/-- A relation from its matrix and its objects' elements at the codes: the pairs' codes picked. -/
def Bits.table {A B : Obj} (x : Bits) (ua : Part A) (ub : Part B) : Rel A B :=
  let (i, j) := x.pairs
  let k := Vals.pickPart A ua.2 i
  if h : k.1.toNat ≤ len j then ⟨k.1, k.2, Vals.pickN B ub.2 j k.1 h⟩ else zero

/-- The next table's two code columns. -/
def take (ids : Array ByteArray) : StateM Nat (ByteArray × ByteArray) :=
  modifyGet fun i => ((ids.getD i .empty, ids.getD (i + 1) .empty), i + 2)

/-- The pairs of codes of `p`, the key ascending, of the converse under `flip`: a table's from its codes, sorted,
    with no matrix (so a large table on the left of `≫` or `\` builds none); any other node's from its matrix `x`. -/
def pairsOf {A B : Obj} {d : Bool} (p : Tm A B d) (x : StateM Nat Bits) (ids : Array ByteArray) (flip : Bool) :
    StateM Nat (ByteArray × ByteArray) :=
  if p.isVal then do let (k, v) ← take ids; pure (if flip then sortBy v k else sortBy k v)
  else do let x ← x; pure (if flip then x.conv.pairs else x.pairs)

/-- The route's matrix, one kernel call per node, the tables' code columns read in `Tm.cols`' order. -/
def _root_.LeetQ.Rel.Lang.Tm.bits (ids : Array ByteArray) (sz : Obj → Nat) : {A B : Obj} → {d : Bool} → Tm A B d →
    StateM Nat Bits
  | A, B, _, .val _ => do let (k, v) ← take ids; pure (Bits.ofCodes (sz A) (sz B) k v)
  | A, _, _, .comp R S => do
    let (i, j) ← pairsOf R (R.bits ids sz) ids false; return Bits.comp (sz A) i j (← S.bits ids sz)
  | _, _, _, .conv R => return (← R.bits ids sz).conv
  | _, _, _, .meet R S => return (← R.bits ids sz).meet (← S.bits ids sz)
  | _, _, _, .join R S => return (← R.bits ids sz).join (← S.bits ids sz)
  | _, _, _, .diff R S => return (← R.bits ids sz).diff (← S.bits ids sz)
  | A, _, _, .ldiv R S _ _ => do
    let (y, a) ← pairsOf R (R.bits ids sz) ids true; let s ← S.bits ids sz; let ub ← take ids; let uc ← take ids
    pure (Bits.ldiv (sz A) y a s ub.2 uc.2)
  | _, _, _, _ => pure (Bits.const false 0 0)

/-- The route's pairs of codes (`pairsOf` at its matrix). -/
def _root_.LeetQ.Rel.Lang.Tm.pairs (ids : Array ByteArray) (sz : Obj → Nat) (flip : Bool) {A B : Obj} {d : Bool}
    (p : Tm A B d) : StateM Nat (ByteArray × ByteArray) := pairsOf p (p.bits ids sz) ids flip

/-- The capacities the bit run is proved under, read off counts alone: every column's rows below `2^63` (a table
    sorted or scattered by its codes), every object's codes at most `2²⁷`, and the root's picks at its at most
    `|A| · |B|` pairs in range (`Vals.fitsN`). -/
def capsOK {A B : Obj} (cs sps : Array Col) (pa : Part A) (pb : Part B) : Bool :=
  cs.all (·.2.1.toNat < 2 ^ 63) && sps.all (·.2.1.toNat ≤ 2 ^ 27) &&
    Vals.fitsN A pa.2 (pa.1.toNat * pb.1.toNat) && Vals.fitsN B pb.2 (pa.1.toNat * pb.1.toNat)

/-- The route run as bit matrices and turned into a table at the root; `none` where a coding did not run within
    capacity, a node's matrix is over `2²⁷` bits, or the counts fail `capsOK`. -/
def run? {A B : Obj} {d : Bool} (p : Tm A B d) : Option (Rel A B) := do
  let (ids, sps) ← codeAll (p.cols #[])
  let sp (X : Obj) : Part X := match sps.find? (·.1 == X) with
    | some ⟨Y, q⟩ => if h : Y = X then h ▸ q else ⟨0, Vals.empty X⟩
    | none => ⟨0, Vals.empty X⟩
  let sz (X : Obj) : Nat := (sp X).1.toNat
  guard (p.fits sz && capsOK (p.cols #[]) sps (sp A) (sp B))
  pure ((Id.run ((p.bits ids sz).run' 0)).table (sp A) (sp B))

/-- Differential-test mode, read once from the environment (`LEETQ_CHECK=1 lake env lean <test file>`: unset is off,
    `LEETQ_CHECK=paths` only traces which path ran, any other value also compares both paths); off in
    production, where `runC` costs one `Bool` test more. An environment variable because `runC` is pure and is called
    from the expander, so no flag can be threaded to it. -/
unsafe def checkOnU : Nat := match unsafeBaseIO (IO.getEnv "LEETQ_CHECK") with | none => 0 | some "paths" => 1 | some _ => 2
@[implemented_by checkOnU] opaque checkOn : Nat

/-- Stops the process naming the difference. Logically it is `x`, so a proof about `runC` reads the bit path's
    answer on every branch (`GenSpec.rep_runC`); compiled, it never returns. `never_extract` and an action over
    `msg`: a closed effect is hoisted into the module initializer by native code. -/
@[never_extract] unsafe def dieU {α : Type} (msg : String) (x : α) : α :=
  unsafeBaseIO (EIO.catchExceptions (do IO.eprintln msg; IO.Process.exit 1) fun _ => pure x)
@[never_extract, implemented_by dieU] def die {α : Type} (_msg : String) (x : α) : α := x

/-- The route's relation with its bit: `run?`'s answer, bit set, or the table with `tableC.2` where it does not run as
    bits (`codeAll`, `fits`, `capsOK` failed). In check mode both paths run, the path taken is traced
    (`LEETQ bits` / `LEETQ table`), and `R ⊑ T ∧ T ⊑ R` failing stops the process. -/
def runC {A B : Obj} {d : Bool} (p : Tm A B d) : Rel A B × Bool :=
  if p.isVal then p.tableC else match run? p with
    | some R => (if checkOn == 0 then R else dbgTrace "LEETQ bits" fun _ => if checkOn == 1 then R else
        let T := p.table
        if R ⊑ T && T ⊑ R then R else die "LEETQ DIFF: bit path and table path differ" R, true)
    | none => if checkOn == 0 then p.tableC else (dbgTrace "LEETQ table" fun _ => p.table, p.tableC.2)

end LeetQ.Rel.Lang.Bits
