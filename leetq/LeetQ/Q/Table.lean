/-
  q's dictionary, table, qSQL and join operators as `RelRep` expressions, each checked by `#guard`
  against real q's output on the same input (q 4.x, the line under each `#guard`).

  Representation.
  * A dict `d` is a relation `key ↦ value`, a `FinRel` (a map when the keys are unique); `!` is the
    constructor `FinRel.mk` itself, the two parallel arrays.
  * A table `T` is `ix(rows) : Idx ⟶ Row`; a keyed table is a relation `KeyRow ↦ ValRow`.
  * `fin?`/`ps`/`rows` read an answer back; they fail (`none`) on an answer held as `enum`/`test`, whose
    pairs are not listed.

  The point-free specs (diagram order, `xy` = first `x` then `y`):
  * `d k = k̂ d`, `d@ks = ix(ks) d`, `ks#d = (∈ks)? d`, `ks _ d = (∉ks)? d`.
  * `d,e = e ⊕ d ≜ e ∪ (¬dom e)? d` — relational override, which RelRep lacks; `comma` builds it.
  * `d+e = dom(d,e) ⟨d ⊕ 0̂, e ⊕ 0̂⟩ (+)`.
  * `flip(a!xs; b!ys) = ⟨ix(xs), ix(ys)⟩`; back is `T outl`, `T outr`.
  * `k xkey T = (T k)° (T v)`.
  * `select where p = T p?`, `delete where p = T (¬p)?`, `exec f where p = T p? f`,
    `update f where p = T (p? f ∪ (¬p)?)`, the conditional `(p → f, id)`.
  * `k xgroup T = ran(T k) Λ((T k)° (T v))`, `select agg v by k = k xgroup T ; agg`,
    `ungroup G = G ∋`.
  * `ij = ⟨T, T k KT⟩`, `ej` = `ij` against `xkey` of the right table, `lj = ⟨T, T k (KT some ⊕ ˆnone)⟩`,
    `pj = lj` with `0̂` then `(+)`, `uj = [T f, U g]` (the junction on `Idx ⊕ Idx`),
    `upsert`/keyed `uj` = `⊕`, `insert` = `∪` when `dom r ∩ dom s = 0`.
  * `aj = ⟨T, Λ(C ∩ (≥ on time)) est(≥ on time) last ⊕ ˆnone⟩`, `C = (T k)(U k)°` the right rows of the
    same key; `asof` is `aj` of one row; `wj1 = Λ(C ∩ window) sum`, `wj` adds the prevailing row.

  Missing from RelRep, named here and not added to AOP: override `⊕` (domain antirestriction
  `(¬dom R)?`), a `first`/`last` of a fibre (q answers one row where a relation has several), the
  descending sort, and bags: `Λ` is a set, so every aggregate is computed over row indices.
-/
import AOP.A6_FinRel

namespace LeetQ.Q

open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {K V W R S X κ : Type}

abbrev Sym := String

/-! ## Reading an answer back -/

/-- The `FinRel` an answer holds, `none` when it is held as a fibre function or a test. -/
def fin? : RelRep K V → Option (FinRel K V) | .pairs r => some r | _ => none

/-- An answer's pairs. -/
def ps (o : Option (RelRep K V)) : Option (List (K × V)) := (o.bind fin?).map FinRel.toList

/-- An answer's values: a table's rows. -/
def rows (o : Option (RelRep K V)) : Option (List V) := (ps o).map (·.map Prod.snd)

/-- A table: `ix(xs) : Idx ⟶ Row`. -/
def tab (xs : List R) : RelRep Nat R := .pairs (FinRel.ofList (xs.zipIdx.map Prod.swap))

/-- `dom r` held as pairs, in `r`'s order. -/
def domP (r : FinRel K V) : RelRep K K := .pairs (FinRel.ofList (r.toList.map fun p => (p.1, p.1)))

/-! ## Dictionaries -/

/-- `ks!vs`. -/
def bang (ks : Array K) (vs : Array V) (h : ks.size = vs.size) : RelRep K V := .pairs ⟨ks, vs, h⟩

def dF : FinRel Sym Int := ⟨#["a", "b", "c"], #[1, 2, 3], rfl⟩
def eF : FinRel Sym Int := ⟨#["b", "c", "d"], #[10, 20, 30], rfl⟩
def d : RelRep Sym Int := bang dF.keys dF.vals dF.len

-- `a`b`c!1 2 3
#guard ps (some d) == some [("a", 1), ("b", 2), ("c", 3)]
-- key d: `a`b`c ; value d: 1 2 3
#guard dF.keys == #["a", "b", "c"] && dF.vals == #[1, 2, 3]

variable [DecidableEq K] [DecidableEq V] [DecidableEq W] [DecidableEq R] [DecidableEq S] [DecidableEq X]
  [DecidableEq κ]

/-- `d k = k̂ d`: the constant `k̂ : 1 → K`, then `d`. -/
def get (D : RelRep K V) (k : K) : Option (RelRep Unit V) := (RelRep.pairs (FinRel.ofList [((), k)])).comp D

/-- `d@ks = ix(ks) d`. -/
def getAll (D : RelRep K V) (ks : List K) : Option (RelRep Nat V) := (tab ks).comp D

-- d`b: 2 ; d`z: 0N (RelRep: no value) ; d`a`c: 1 3
#guard rows (get d "b") == some [2]
#guard rows (get d "z") == some []
#guard rows (getAll d ["a", "c"]) == some [1, 3]

/-- `p? D`, held as `D ∩ p?⊤` so a `FinRel` stays one. -/
def restrict (p : K → Bool) (D : RelRep K V) : RelRep K V := D.inter (.test fun k _ => p k)

/-- `ks#d`. -/
def take (ks : List K) : RelRep K V → RelRep K V := restrict (ks.contains ·)

/-- `ks _ d`. -/
def drop (ks : List K) : RelRep K V → RelRep K V := restrict (!ks.contains ·)

-- `a`c#d: `a`c!1 3 ; `a`c _ d: (,`b)!,2
#guard ps (some (take ["a", "c"] d)) == some [("a", 1), ("c", 3)]
#guard ps (some (drop ["a", "c"] d)) == some [("b", 2)]

theorem rel_take (ks : List K) (D : RelRep K V) :
    (take ks D).rel = D.rel ∩ (fun k _ => ks.contains k = true : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) :=
  RelRep.rel_inter _ _

/-- `r,s = s ⊕ r ≜ s ∪ (¬dom s)? r`: `s` overrides `r`, on `FinRel`s so the answer lists. -/
def comma (r s : FinRel K V) : FinRel K V := (r.filter (fun k _ => s.keys.contains k = false)).union s

omit [DecidableEq V] in
theorem rep_comma (r s : FinRel K V) :
    (comma r s).rep = (r.rep ∩ (fun k _ => s.keys.contains k = false : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩)) ∪ s.rep := by
  rw [comma, FinRel.rep_union, FinRel.rep_filter]

-- d,e: `a`b`c`d!1 10 20 30
#guard (comma dF eF).toList == [("a", 1), ("b", 10), ("c", 20), ("d", 30)]

/-- `R ⊕ D ≜ R ∪ (¬dom R)? D` on any `R` whose fibres enumerate: the default `D` where `R` is empty. -/
def over (R D : RelRep K V) : Option (RelRep K V) := do
  let f ← R.fibre?
  pure (R.union (← (RelRep.corefl fun k => (f k).isEmpty).comp D))

/-- `d+e = dom(d,e) ⟨d ⊕ 0̂, e ⊕ 0̂⟩ (+)`. -/
def plus [Add V] [Zero V] (r s : FinRel K V) : Option (RelRep K V) := do
  let z : RelRep K V := RelRep.ofFn fun _ => 0
  (domP (comma r s)).comp (← ((← over (.pairs r) z).pair (← over (.pairs s) z)).comp (RelRep.ofFn fun p => p.1 + p.2))

-- d+e: `a`b`c`d!1 12 23 30
#guard ps (plus dF eF) == some [("a", 1), ("b", 12), ("c", 23), ("d", 30)]

/-! ## Tables and qSQL -/

/-- `flip(a!xs; b!ys) = ⟨ix(xs), ix(ys)⟩`. -/
def flip (xs : List V) (ys : List W) : RelRep Nat (V × W) := (tab xs).pair (tab ys)

-- flip `a`b!(1 2;3 4): +`a`b!(1 2;3 4) ; flip back: `a`b!(1 2;3 4)
#guard rows (some (flip [1, 2] [3, 4])) == some [(1, 3), (2, 4)]
#guard rows ((flip [1, 2] [3, 4]).comp (RelRep.ofFn Prod.fst)) == some [1, 2]
#guard rows ((flip [1, 2] [3, 4]).comp (RelRep.ofFn Prod.snd)) == some [3, 4]

def t : RelRep Nat (Sym × Int) := tab [("a", 1), ("b", 2), ("a", 3), ("c", 4)]

/-- `k xkey T = (T k)° (T v)`: a relation, not a map, when a key repeats — q allows that too. -/
def xkey (k : R → κ) (v : R → V) (T : RelRep Nat R) : Option (RelRep κ V) := do
  (← T.comp (RelRep.ofFn k)).conv.comp (← T.comp (RelRep.ofFn v))

-- `k xkey t: (+(,`k)!,`a`b`a`c)!+(,`v)!,1 2 3 4
#guard ps (xkey Prod.fst Prod.snd t) == some [("a", 1), ("b", 2), ("a", 3), ("c", 4)]

def ktF : FinRel Sym Int := ⟨#["a", "b", "d"], #[10, 20, 40], rfl⟩
-- key kt: +(,`k)!,`a`b`d ; value kt: +(,`w)!,10 20 40
#guard ktF.keys == #["a", "b", "d"] && ktF.vals == #[10, 20, 40]

/-- `select from T where p = T p?`. -/
def selw (p : R → Bool) (T : RelRep Nat R) : Option (RelRep Nat R) := T.comp (RelRep.corefl p)

/-- `delete from T where p = T (¬p)?`. -/
def del (p : R → Bool) (T : RelRep Nat R) : Option (RelRep Nat R) := T.comp (RelRep.corefl (!p ·))

/-- `exec f from T where p = T p? f`. -/
def exec (p : R → Bool) (f : R → V) (T : RelRep Nat R) : Option (RelRep Nat V) :=
  selw p T >>= (·.comp (RelRep.ofFn f))

/-- `update f from T where p = T (p? f ∪ (¬p)?)`, the conditional `(p → f, id)`. -/
def upd (p : R → Bool) (f : R → R) (T : RelRep Nat R) : Option (RelRep Nat R) := do
  T.comp ((← (RelRep.corefl p).comp (RelRep.ofFn f)).union (RelRep.corefl (!p ·)))

-- select from t where v>1: +`k`v!(`b`a`c;2 3 4)
#guard rows (selw (·.2 > 1) t) == some [("b", 2), ("a", 3), ("c", 4)]
-- exec v from t where k=`a: 1 3
#guard rows (exec (·.1 == "a") Prod.snd t) == some [1, 3]
-- update v:v*10 from t where k=`a: +`k`v!(`a`b`a`c;10 2 30 4)
#guard rows (upd (·.1 == "a") (fun r => (r.1, r.2 * 10)) t) == some [("a", 10), ("b", 2), ("a", 30), ("c", 4)]
-- delete from t where k=`a: +`k`v!(`b`c;2 4)
#guard rows (del (·.1 == "a") t) == some [("b", 2), ("c", 4)]

/-- `k xgroup T = ran(T k) Λ((T k)° (T v))`: the keys `ran` lists sorted, each with its fibre. -/
def xgroup [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ] (k : R → κ) (v : R → V) (T : RelRep Nat R) :
    Option (RelRep κ (List V)) := do
  (RelRep.pairs (← fin? (← T.comp (RelRep.ofFn k))).ran).comp (← (← xkey k v T).transpose)

/-- `select agg v by k from T = (k xgroup T) agg`. The fibre is a list of pairs, so it keeps repeats;
    the spec `Λ` is a set and does not — the aggregate is a bag operation outside the relation. -/
def selby [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ] (agg : List V → W) (k : R → κ) (v : R → V)
    (T : RelRep Nat R) : Option (RelRep κ W) :=
  xgroup k v T >>= (·.comp (RelRep.ofFn agg))

/-- `ungroup G = G ∋`. -/
def ungroup (G : RelRep κ (List V)) : Option (RelRep κ V) := G.comp (.enum id)

-- `k xgroup t: (+(,`k)!,`a`b`c)!+(,`v)!,(1 3;,2;,4)
#guard ps (xgroup Prod.fst Prod.snd t) == some [("a", [1, 3]), ("b", [2]), ("c", [4])]
-- select sum v by k from t: (`s#+(,`k)!,`s#`a`b`c)!+(,`v)!,4 2 4
#guard ps (selby List.sum Prod.fst Prod.snd t) == some [("a", 4), ("b", 2), ("c", 4)]
-- ungroup `k xgroup t: +`k`v!(`a`a`b`c;1 3 2 4)
#guard ps (xgroup Prod.fst Prod.snd t >>= ungroup) == some [("a", 1), ("a", 3), ("b", 2), ("c", 4)]

/-- `k xasc T`: `(T k)° T` sorted by key, stably. Order is not a relation property: `sortByKey`. -/
def xasc [Ord κ] [Std.TransOrd κ] (k : R → κ) (T : RelRep Nat R) : Option (List R) := do
  pure (SortedRel.sortByKey (← fin? (← xkey k id T))).toFinRel.vals.toList

/-- `k xdesc T`: RelRep sorts only ascending by the key's `Ord`, so this is a list sort. -/
def xdesc [Ord κ] (k : R → κ) (T : RelRep Nat R) : Option (List R) :=
  (rows (some T)).map (·.mergeSort fun a b => (compare (k b) (k a)).isLE)

-- `k xasc t: +`k`v!(`s#`a`a`b`c;1 3 2 4) ; `k xdesc t: +`k`v!(`c`b`a`a;4 2 1 3)
#guard xasc Prod.fst t == some [("a", 1), ("a", 3), ("b", 2), ("c", 4)]
#guard xdesc Prod.fst t == some [("c", 4), ("b", 2), ("a", 1), ("a", 3)]

/-! ## Joins -/

/-- `T ij KT = ⟨T, T k KT⟩`: every match of the key, not q's first. -/
def ij (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat (R × W)) := do
  pure (T.pair (← (← T.comp (RelRep.ofFn k)).comp KT))

/-- The first value of each fibre: q's keyed lookup, a choice by array position. -/
def first (r : FinRel κ W) : RelRep κ W := .enum fun x => (r.scanLookup x).take 1

/-- The last value of each fibre, when the fibres enumerate. -/
def lastOf (D : RelRep K V) : Option (RelRep K V) := D.fibre?.map fun f => .enum fun x => (f x).getLast?.toList

/-- `ej[k; T; U] = ij` against `k xkey U`: all matches, as q's `ej`. -/
def ej (k : R → κ) (k' : S → κ) (w : S → W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × W)) := xkey k' w U >>= ij k T

/-- `T lj KT = ⟨T, T k (KT some ⊕ ˆnone)⟩`. -/
def lj (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat (R × Option W)) := do
  ij k T (← over (← KT.comp (RelRep.ofFn some)) (RelRep.ofFn fun _ => none))

/-- `T pj KT`: `lj` with `0̂` for the missing key, then `f` adds. -/
def pj [Zero W] (k : R → κ) (f : R → W → R) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat R) := do
  (← ij k T (← over KT (RelRep.ofFn fun _ => 0))).comp (RelRep.ofFn fun p => f p.1 p.2)

/-- `T uj U = [T f, U g]` on `Idx ⊕ Idx`, `f`, `g` padding the missing columns with nulls. -/
def uj (f : R → X) (g : S → X) (T : RelRep Nat R) (U : RelRep Nat S) : Option (RelRep (Nat ⊕ Nat) X) := do
  pure ((← T.comp (RelRep.ofFn f)).junction (← U.comp (RelRep.ofFn g)))

/-- Keyed `insert`: `r ∪ s` when no key of `s` is in `r`, else q's `'insert` error, here `none`. -/
def insert (r s : FinRel K V) : Option (FinRel K V) := if s.keys.any r.keys.contains then none else some (r.union s)

def kt : RelRep Sym Int := .pairs ktF
def kt3F : FinRel Sym Int := ⟨#["a", "a", "b"], #[1, 2, 3], rfl⟩

-- t ij kt: +`k`v`w!(`a`b`a;1 2 3;10 20 10)
#guard rows (ij Prod.fst t kt) == some [(("a", 1), 10), (("b", 2), 20), (("a", 3), 10)]
-- t lj kt: +`k`v`w!(`a`b`a`c;1 2 3 4;10 20 10 0N)
#guard rows (lj Prod.fst t kt) == some [(("a", 1), some 10), (("b", 2), some 20), (("a", 3), some 10), (("c", 4), none)]
-- t ij kt3, kt3 keyed with `a twice: +`k`v`w!(`a`b`a;1 2 3;1 3 1) — q takes the first match;
-- `ij` over the relation answers both, `first` restores q.
#guard rows (ij Prod.fst t (.pairs kt3F)) ==
  some [(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
#guard rows (ij Prod.fst t (first kt3F)) == some [(("a", 1), 1), (("b", 2), 3), (("a", 3), 1)]
-- t lj kt3: +`k`v`w!(`a`b`a`c;1 2 3 4;1 3 1 0N)
#guard rows (lj Prod.fst t (first kt3F)) == some [(("a", 1), some 1), (("b", 2), some 3), (("a", 3), some 1), (("c", 4), none)]
-- ej[`k;t;([] k:`a`a`b; w:1 2 3)]: +`k`v`w!(`a`a`b`a`a;1 1 2 3 3;1 2 3 1 2)
#guard rows (ej Prod.fst Prod.fst Prod.snd t (tab [("a", (1 : Int)), ("a", 2), ("b", 3)])) ==
  some [(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
-- t pj ([k:`a`b] v:100 200): +`k`v!(`a`b`a`c;101 202 103 4)
#guard rows (pj Prod.fst (fun r w => (r.1, r.2 + w)) t (.pairs (⟨#["a", "b"], #[100, 200], rfl⟩ : FinRel Sym Int))) ==
  some [("a", 101), ("b", 202), ("a", 103), ("c", 4)]
-- t uj ([] k:`b`e; u:5 6): +`k`v`u!(`a`b`a`c`b`e;1 2 3 4 0N 0N;0N 0N 0N 0N 5 6)
#guard rows (uj (fun r => (r.1, some r.2, (none : Option Int))) (fun r => (r.1, none, some r.2)) t
    (tab [("b", (5 : Int)), ("e", 6)])) ==
  some [("a", some 1, none), ("b", some 2, none), ("a", some 3, none), ("c", some 4, none),
    ("b", none, some 5), ("e", none, some 6)]
-- t upsert ([] k:enlist`z; v:enlist 9), and `t insert (`z;9): +`k`v!(`a`b`a`c`z;1 2 3 4 9)
#guard rows (uj id id t (tab [("z", 9)])) == some [("a", 1), ("b", 2), ("a", 3), ("c", 4), ("z", 9)]
-- kt uj / upsert ([k:`b`e] w:22 50): (+(,`k)!,`a`b`d`e)!+(,`w)!,10 22 40 50 — same pairs, q keeps
-- `b in place, `comma` appends it after the survivors of `r`.
#guard (comma ktF ⟨#["b", "e"], #[22, 50], rfl⟩).toList == [("a", 10), ("d", 40), ("b", 22), ("e", 50)]
#guard (comma ktF ⟨#["b", "e"], #[22, 50], rfl⟩).toList.isPerm [("a", 10), ("b", 22), ("d", 40), ("e", 50)]
-- `kt insert (`b;99): 'insert
#guard (insert ktF ⟨#["b"], #[99], rfl⟩).isNone

/-! ## As-of and window joins -/

/-- `C = (T k)(U k)°`, then each right row's `(time, value)` beside the left time. -/
def cand (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (Int × (Int × W))) := do
  let C ← (← T.comp (RelRep.ofFn k)).comp (← U.comp (RelRep.ofFn k')).conv
  pure ((← T.comp (RelRep.ofFn tm)).pair (← C.comp (← U.comp (RelRep.ofFn tv))))

/-- `≥` on the right time. -/
def geT : RelRep (Int × (Int × W)) (Int × (Int × W)) := .test fun a b => decide (b.2.1 ≤ a.2.1)

/-- `Λ(C ∩ (right time ≤ left time + o)) est(≥)`: every right row at the greatest such time. -/
def prevail (o : Int) (C : RelRep Nat (Int × (Int × W))) : Option (RelRep Nat (Int × (Int × W))) :=
  RelRep.est geT (C.inter (.test fun _ x => decide (x.2.1 ≤ x.1 + o)))

/-- `⟨T, D ⊕ ˆz⟩` on every row of `T`, `D` keyed by row. -/
def onRows (T : RelRep Nat R) (D : RelRep Nat V) (z : V) : Option (RelRep Nat (R × V)) := do
  pure (T.pair (← (domP (← fin? T)).comp (← over D (RelRep.ofFn fun _ => z))))

/-- `aj = ⟨T, prevail(0) last p ⊕ ˆnone⟩`. -/
def aj (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × Option W)) := do
  onRows T (← (← lastOf (← prevail 0 (← cand k tm k' tv T U))).comp (RelRep.ofFn fun x => some x.2.2)) none

/-- `wj1`: `Λ(C ∩ window) sum` per left row, the window `[t+lo, t+hi]`. -/
def wj1 [Add W] [Zero W] (lo hi : Int) (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W)
    (T : RelRep Nat R) (U : RelRep Nat S) : Option (RelRep Nat (R × W)) := do
  let C ← cand k tm k' tv T U
  let L ← (C.inter (.test fun _ x => decide (x.1 + lo ≤ x.2.1 ∧ x.2.1 ≤ x.1 + hi))).transpose
  onRows T (← L.comp (RelRep.ofFn fun xs => (xs.map (·.2.2)).sum)) 0

/-- `wj`: the window `(t+lo, t+hi]` and the row prevailing at `t+lo`, summed. -/
def wj [Add W] [Zero W] (lo hi : Int) (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W)
    (T : RelRep Nat R) (U : RelRep Nat S) : Option (RelRep Nat (R × W)) := do
  let C ← cand k tm k' tv T U
  let P ← lastOf (← prevail lo C)
  let L ← (P.union (C.inter (.test fun _ x => decide (x.1 + lo < x.2.1 ∧ x.2.1 ≤ x.1 + hi)))).transpose
  onRows T (← L.comp (RelRep.ofFn fun xs => (xs.map (·.2.2)).sum)) 0

def tr : RelRep Nat (Sym × Int) := tab [("x", 2), ("x", 5), ("y", 4)]
def qr : RelRep Nat (Sym × Int × Int) := tab [("x", 1, 10), ("x", 3, 20), ("x", 3, 21), ("y", 5, 30)]

-- aj[`s`tm;tr;qr]: +`s`tm`p!(`x`x`y;2 5 4;10 21 0N)
#guard rows (aj Prod.fst Prod.snd Prod.fst Prod.snd tr qr) ==
  some [(("x", 2), some 10), (("x", 5), some 21), (("y", 4), none)]
-- `est(≥)` alone answers both rows at time 3 for the left row `x 5; q's `aj` takes the last.
#guard ps (cand Prod.fst Prod.snd Prod.fst Prod.snd tr qr >>= prevail 0) ==
  some [(0, (2, (1, 10))), (1, (5, (3, 20))), (1, (5, (3, 21)))]
-- qr asof `s`tm!(`x;3): (,`p)!,21 ; at 2: (,`p)!,10
#guard rows (aj Prod.fst Prod.snd Prod.fst Prod.snd (tab [("x", (3 : Int))]) qr) == some [(("x", 3), some 21)]
#guard rows (aj Prod.fst Prod.snd Prod.fst Prod.snd (tab [("x", (2 : Int))]) qr) == some [(("x", 2), some 10)]
-- wj1[-2 0+\:tr`tm;`s`tm;tr;(qr;(sum;`p))]: +`s`tm`p!(`x`x`y;2 5 4;10 41 0)
#guard rows (wj1 (-2) 0 Prod.fst Prod.snd Prod.fst Prod.snd tr qr) == some [(("x", 2), 10), (("x", 5), 41), (("y", 4), 0)]
-- wj[...]: +`s`tm`p!(`x`x`y;2 5 4;10 21 0)
#guard rows (wj (-2) 0 Prod.fst Prod.snd Prod.fst Prod.snd tr qr) == some [(("x", 2), 10), (("x", 5), 21), (("y", 4), 0)]

end LeetQ.Q
