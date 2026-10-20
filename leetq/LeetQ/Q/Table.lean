/-
  q's dictionary, table, qSQL and join operators as `RelRep` expressions, each checked by `#guard`
  against real q's output on the same input (q 4.x, the line under each `#guard`).

  Representation.
  * A dict `d` is a relation `key ↦ value`, a `FinRel` (a map when the keys are unique); `!` is the
    constructor `FinRel.mk` itself, the two parallel arrays.
  * A table `T` is `ix(rows) : Idx ⟶ Row`; a keyed table is a relation `KeyRow ↦ ValRow`.
  * A `RelRep` means a list per key (`app`: order and repeats), so q's choices by position — the first
    match of a key, the last row at a time — are `first`/`last` of a fibre, and an aggregate sees the
    group's fibre with its repeats (`app_selby`).
  * `fin?`/`ps`/`rows` read an answer back; they fail (`none`) on an answer held as `enum`, whose pairs
    are not listed. A converse `(T k)°` is enumerable only from pairs, so `xkey`, `cand` and what uses
    them stay `Option`; every other operator is total.

  The point-free specs (diagram order, `xy` = first `x` then `y`), `ks` the keys of a dict listed once in
  order of first appearance (`domP`):
  * `d k = k̂ look(d)`, `d@ks = ix(ks) look(d)`, `look(d) ≜ first(d) some ⊕ ˆnone`;
    `ks#d = (∈ks)? d`, `ks _ d = (∉ks)? d`.
  * `d,e = dom(d ∪ e) (e ⊕ d)`, `⊕` RelRep's `override`.
  * `d op e = dom(d ∪ e) ⟨Λd, Λe⟩ zipFib ∋` for `+ - * | &`, the missing side read as `z` = `0 0 1 -0W 0W`:
    `d`'s first row of a key meets `e`'s first value, `d`'s later rows stay, a key only `e` has keeps every
    row (`app?_zipD`).
  * `flip(a!xs; b!ys) = ⟨ix(xs), ix(ys)⟩`; back is `T outl`, `T outr`.
  * `k xkey T = (T k)° (T v)`.
  * `select where p = T p?`, `delete where p = T (¬p)?`, `exec f where p = T p? f`,
    `update f where p = T (p? f ∪ (¬p)?)`, the conditional `(p → f, id)`.
  * `k xgroup T = dom((T k)°) Λ((T k)° (T v))`, `select agg v by k = ran(T k) Λ((T k)° (T v)) agg`,
    `ungroup G = G ∋`.
  * `ij = ⟨T, T k first(KT)⟩`, `ej = ⟨T, T k (k xkey U)⟩` (every match), `lj = ⟨T, T k look(KT)⟩`,
    `pj = lj` with `0N` read as `0`, then `(+)`, `uj = [T f, U g]` (the junction on `Idx ⊕ Idx`),
    `upsert`/keyed `uj` = `d,e`, `insert` = `∪` when `dom r ∩ dom s = 0`.
  * `aj = ⟨T, Λ(C ∩ (≥ on time)) est(≥ on time) last ⊕ ˆnone⟩`, `C = (T k)(U k)°` the right rows of the
    same key; `asof` is `aj` of one row; `wj1 = Λ(C ∩ window) sum`, `wj` adds the prevailing row.

  | operator            | before                                   | now                                  |
  |---------------------|------------------------------------------|--------------------------------------|
  | `d k`, `d@ks`       | missing key: no value, q: `0N`           | q: `0N`; repeated key: the first     |
  | `d,e`, keyed upsert | local `comma`; moved `b to the end       | q: the key keeps its position        |
  | `lj`, `pj`          | local `over` for `⊕`                     | RelRep `override`                    |
  | `d+e` … `d&e`       | `+` only, all rows of a key added        | `zipD op z`; q: the first row only   |
  | `ij`, `lj`, `pj`    | every match of a repeated key; q's first | q: `first`                           |
  | `aj`, `asof`, `wj`  | local `lastOf`                           | RelRep `last`                        |
  | `xgroup`            | groups sorted by key                     | q: groups by first appearance        |
  | `select … by`       | aggregate a bag outside the relation     | `app?_selby`: `agg` of the fibre     |

  Still missing from RelRep, named here and not added to AOP: the descending sort.
-/
import LeetQ.Q.List

namespace LeetQ.Q

open Freyd Freyd.Alg Freyd.Alg.RelSet
open scoped Freyd.Alg.RelSet.RelRep

variable {K V W R S X κ : Type}

abbrev Sym := String

/-! ## Reading an answer back -/

/-- An answer's pairs. -/
def ps (R : RelRep K V) : Option (Array (K × V)) := (fin? R).map fun r => r.keys.zip r.vals

/-- An answer's values: a table's rows. -/
def rows (R : RelRep K V) : Option (Array V) := (fin? R).map FinRel.vals

/-- A table: `ix(xs) : Idx ⟶ Row`, the row array itself. -/
def tab (xs : Array R) : RelRep Nat R := .vec xs rfl

/-- `ix(xs)` as the pairs `(i, xs[i])`: the spelling `Compressed`'s statements about a row list use. -/
def tabL (xs : List R) : RelRep Nat R := .pairs (FinRel.ofList (xs.zipIdx.map Prod.swap))

/-! ## Dictionaries -/

/-- `ks!vs`. -/
def bang (ks : Array K) (vs : Array V) (h : ks.size = vs.size) : RelRep K V := .pairs ⟨ks, vs, h⟩

def dF : FinRel Sym Int := ⟨#["a", "b", "c"], #[1, 2, 3], rfl⟩
def eF : FinRel Sym Int := ⟨#["b", "c", "d"], #[10, 20, 30], rfl⟩
def d : RelRep Sym Int := bang dF.keys dF.vals dF.len

-- `a`b`c!1 2 3
#guard ps d == some #[("a", 1), ("b", 2), ("c", 3)]
-- key d: `a`b`c ; value d: 1 2 3
#guard dF.keys == #["a", "b", "c"] && dF.vals == #[1, 2, 3]

variable [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X]
  [DecidableEq κ] [FibreIndex κ]

/-- `dom r` held as pairs, each key once, in order of first appearance: q's key order. -/
def domP (r : FinRel K V) : RelRep K K := .pairs (FinRel.ofList ((FibreIndex.dedup (r.toList.map Prod.fst)).map fun k => (k, k)))

/-- q's keyed lookup `look(D) ≜ first(D) some ⊕ ˆnone`: the first value of the fibre, `0N` when empty.
    A `FinRel`'s is read by one `first?` probe per key: no fibre, and no composite of three enumerations. -/
def look : RelRep K V → RelRep K (Option V)
  | .pairs r => let i := FibreIndex.build r; .arr fun k => #[FibreIndex.first? i k]
  | D => RelRep.override (D.first ≫ RelRep.ofFn some) (RelRep.ofFn fun _ => none)

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
theorem app_lookSpec (D : RelRep K V) (k : K) :
    (RelRep.override (D.first ≫ RelRep.ofFn some) (RelRep.ofFn fun _ => none)).app k = [(D.app k).head?] := by
  simp only [RelRep.override_eq, RelRep.app_enum, RelRep.app_comp, RelRep.first_eq]
  cases D.app k <;> rfl

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- `look` reads the fibre list: its head, or `0N` when it is empty. -/
theorem app_look (D : RelRep K V) (k : K) : (look D).app k = [(D.app k).head?] := by
  cases D with
  | pairs r => show [FibreIndex.first? _ k] = _; rw [FibreIndex.first?_eq]; rfl
  | enum f => exact app_lookSpec _ k
  | arr f => exact app_lookSpec _ k
  | vec a e => exact app_lookSpec _ k

/-- `d k = k̂ look(d)`: the constant `k̂ : 1 → K`, then the lookup. -/
def get (D : RelRep K V) (k : K) : RelRep Unit (Option V) := RelRep.pairs (FinRel.ofList [((), k)]) ≫ look D

/-- `d@ks = ix(ks) look(d)`. -/
def getAll (D : RelRep K V) (ks : Array K) : RelRep Nat (Option V) := tab ks ≫ look D

-- d`b: 2 ; d`z: 0N ; d`a`c: 1 3 ; d`a`z: 1 0N ; (`a`a`b!1 2 3)`a: 1
#guard rows (get d "b") == some #[some 2]
#guard rows (get d "z") == some #[none]
#guard rows (getAll d #["a", "c"]) == some #[some 1, some 3]
#guard rows (getAll d #["a", "z"]) == some #[some 1, none]
#guard rows (get (.pairs (⟨#["a", "a", "b"], #[1, 2, 3], rfl⟩ : FinRel Sym Int)) "a") == some #[some 1]

/-- `p? D`, held as `D ∩ p?⊤` so a `FinRel` stays one. -/
def restrict (p : K → Bool) (D : RelRep K V) : RelRep K V := D.inter (.test fun k _ => p k)

/-- `ks#d`. -/
def take (ks : Array K) : RelRep K V → RelRep K V := restrict (ks.contains ·)

/-- `ks _ d`. -/
def drop (ks : Array K) : RelRep K V → RelRep K V := restrict (!ks.contains ·)

-- `a`c#d: `a`c!1 3 ; `a`c _ d: (,`b)!,2
#guard ps (take #["a", "c"] d) == some #[("a", 1), ("c", 3)]
#guard ps (drop #["a", "c"] d) == some #[("b", 2)]

theorem rel_take (ks : Array K) (D : RelRep K V) :
    (take ks D).rel = D.rel ∩ (fun k _ => ks.contains k = true : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) :=
  RelRep.rel_inter _ _

/-- `r,s = dom(r ∪ s) (s ⊕ r)`, dicts and keyed `upsert`: the keys in first appearance, each answered by
    `s` where it has a value. -/
def upsert (r s : FinRel K V) : RelRep K V := domP (r.union s) ≫ RelRep.override (.pairs s) (.pairs r)

-- d,e: `a`b`c`d!1 10 20 30
#guard ps (upsert dF eF) == some #[("a", 1), ("b", 10), ("c", 20), ("d", 30)]

omit [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- `eraseDups` keeps one copy of each key: the fibre of `k` in `(a,a)` over it is `[k]` when `k` occurs. -/
theorem sel_eraseDups (k : K) : (xs : List K) →
    ((xs.eraseDups.map fun a => (a, a)).filterMap (FinRel.sel k)) = if k ∈ xs then [k] else []
  | [] => rfl
  | a :: as => by
    have ih := sel_eraseDups k (as.filter fun b => !b == a)
    rw [List.eraseDups_cons, List.map_cons, List.filterMap_cons, ih]
    by_cases e : a = k
    · subst e; simp [FinRel.sel]
    · simp [FinRel.sel, e, List.mem_filter, Ne.symm e]
termination_by xs => xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

omit [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- `dom r` answers `k` itself exactly when `k` is a key of `r`. -/
theorem app_domP (r : FinRel K V) (k : K) :
    (domP r).app k = if k ∈ r.toList.map Prod.fst then [k] else [] := by
  simp only [domP, RelRep.app_pairs, FibreIndex.dedup_eq, FinRel.scanLookup_ofList]
  simpa [List.map_map, Function.comp_def] using sel_eraseDups k _

/-- One key's answer from its two fibres, as q's dict arithmetic gives it: `d`'s first row meets `e`'s first
    value (`z` when `e` has none) and `d`'s later rows stay; a key only `e` has keeps every row, each `z op v`. -/
def zipFib (op : V → V → V) (z : V) : List V × List V → List V
  | (a :: t, m) => op a (m.headD z) :: t
  | ([], m) => m.map (op z)

/-- q's `d op e` on dicts, `dom(d ∪ e) ⟨Λd, Λe⟩ zipFib ∋`: `z` stands for the side a key is missing from. -/
def zipD (op : V → V → V) (z : V) (r s : FinRel K V) : RelRep K V :=
  domP (r.union s) ≫ ((RelRep.pairs r).transpose.pair (RelRep.pairs s).transpose ≫ .enum (zipFib op z))

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- **`d op e`** on fibre lists: each key of `d ∪ e`, once, answered by `zipFib` of its two fibres. -/
theorem app_zipD (op : V → V → V) (z : V) (r s : FinRel K V) (k : K) :
    (zipD op z r s).app k =
      if k ∈ (r.union s).toList.map Prod.fst then zipFib op z (r.scanLookup k, s.scanLookup k) else [] := by
  rw [zipD, RelRep.app_comp, app_domP]
  split <;> simp [RelRep.app_comp, RelRep.app_pair, RelRep.transpose_eq, RelRep.app_pairs, RelRep.ofFn,
    RelRep.app_arr_fun, RelRep.cross]

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- The Set reading: `d op e` relates `k` to `v` iff `k` is a key and `v` is in `zipFib` of its fibres. -/
theorem rel_zipD (op : V → V → V) (z : V) (r s : FinRel K V) (k : K) (v : V) : (zipD op z r s).rel k v ↔
      k ∈ (r.union s).toList.map Prod.fst ∧ v ∈ zipFib op z (r.scanLookup k, s.scanLookup k) := by
  rw [← RelRep.mem_app, app_zipD]; split <;> simp_all

/-- q's long infinities `-0W`, `0W`: the units of `|` and `&` on every non-null long. -/
def negInf : Int := -9223372036854775807
def posInf : Int := 9223372036854775807

-- d+e: `a`b`c`d!1 12 23 30 ; d-e: 1 -8 -17 -30 ; d*e: 1 20 60 30 ; d|e: 1 10 20 30 ; d&e: 1 2 3 30
#guard ps (zipD (· + ·) 0 dF eF) == some #[("a", 1), ("b", 12), ("c", 23), ("d", 30)]
#guard ps (zipD (· - ·) 0 dF eF) == some #[("a", 1), ("b", -8), ("c", -17), ("d", -30)]
#guard ps (zipD (· * ·) 1 dF eF) == some #[("a", 1), ("b", 20), ("c", 60), ("d", 30)]
#guard ps (zipD max negInf dF eF) == some #[("a", 1), ("b", 10), ("c", 20), ("d", 30)]
#guard ps (zipD min posInf dF eF) == some #[("a", 1), ("b", 2), ("c", 3), ("d", 30)]
-- Repeated keys. (`a`a`b!1 2 3)+`a`c!10 20: `a`a`b`c!11 2 3 20 ; (`a`c!10 20)+`a`a`b!1 2 3: `a`c`b!11 20 3 ;
-- d+`b`b!10 20: `a`b`c!1 12 3 ; (`a`b!1 2)+`c`c!10 20: `a`b`c`c!1 2 10 20 ; minus: 1 2 -10 -20
def aabF : FinRel Sym Int := ⟨#["a", "a", "b"], #[1, 2, 3], rfl⟩
def acF : FinRel Sym Int := ⟨#["a", "c"], #[10, 20], rfl⟩
def bbF : FinRel Sym Int := ⟨#["b", "b"], #[10, 20], rfl⟩
def abF : FinRel Sym Int := ⟨#["a", "b"], #[1, 2], rfl⟩
def ccF : FinRel Sym Int := ⟨#["c", "c"], #[10, 20], rfl⟩
def abaF : FinRel Sym Int := ⟨#["a", "b", "a"], #[1, 2, 3], rfl⟩
#guard ps (zipD (· + ·) 0 aabF acF) == some #[("a", 11), ("a", 2), ("b", 3), ("c", 20)]
#guard ps (zipD (· + ·) 0 acF aabF) == some #[("a", 11), ("c", 20), ("b", 3)]
#guard ps (zipD (· + ·) 0 dF bbF) == some #[("a", 1), ("b", 12), ("c", 3)]
#guard ps (zipD (· + ·) 0 abF ccF) == some #[("a", 1), ("b", 2), ("c", 10), ("c", 20)]
#guard ps (zipD (· - ·) 0 abF ccF) == some #[("a", 1), ("b", 2), ("c", -10), ("c", -20)]
-- (`a`b`a!1 2 3)+`a`c!10 20: `a`b`a`c!11 2 3 20 — the same fibres, a:11 3, b:2, c:20; the pairs come grouped
-- by key, not in q's positions.
#guard ["a", "b", "c"].map (zipD (· + ·) 0 abaF acF).app == [[11, 3], [2], [20]]

#print axioms app_zipD
#print axioms rel_zipD

/-! ## Tables and qSQL -/

/-- `flip(a!xs; b!ys) = ⟨ix(xs), ix(ys)⟩`. -/
def flip (xs : Array V) (ys : Array W) : RelRep Nat (V × W) := (tab xs).pair (tab ys)

-- flip `a`b!(1 2;3 4): +`a`b!(1 2;3 4) ; flip back: `a`b!(1 2;3 4)
#guard rows (flip #[1, 2] #[3, 4]) == some #[(1, 3), (2, 4)]
#guard rows (flip #[1, 2] #[3, 4] ≫ RelRep.ofFn Prod.fst) == some #[1, 2]
#guard rows (flip #[1, 2] #[3, 4] ≫ RelRep.ofFn Prod.snd) == some #[3, 4]

def t : RelRep Nat (Sym × Int) := tab #[("a", 1), ("b", 2), ("a", 3), ("c", 4)]

/-- `k xkey T = (T k)° (T v)`: a relation, not a map, when a key repeats — q allows that too. `(T k)°` is
    enumerable only when `T k` is held as pairs, hence the `Option`. -/
def xkey (k : R → κ) (v : R → V) (T : RelRep Nat R) : Option (RelRep κ V) :=
  (fin? (T ≫ RelRep.ofFn k)).map fun c => RelRep.pairs c.conv ≫ (T ≫ RelRep.ofFn v)

-- `k xkey t: (+(,`k)!,`a`b`a`c)!+(,`v)!,1 2 3 4
#guard (xkey Prod.fst Prod.snd t).bind ps == some #[("a", 1), ("b", 2), ("a", 3), ("c", 4)]

def ktF : FinRel Sym Int := ⟨#["a", "b", "d"], #[10, 20, 40], rfl⟩
-- key kt: +(,`k)!,`a`b`d ; value kt: +(,`w)!,10 20 40
#guard ktF.keys == #["a", "b", "d"] && ktF.vals == #[10, 20, 40]

/-- `select from T where p = T p?`. -/
def selw (p : R → Bool) (T : RelRep Nat R) : RelRep Nat R := T ≫ RelRep.corefl p

/-- `delete from T where p = T (¬p)?`. -/
def del (p : R → Bool) (T : RelRep Nat R) : RelRep Nat R := T ≫ RelRep.corefl (!p ·)

/-- `exec f from T where p = T p? f`. -/
def exec (p : R → Bool) (f : R → V) (T : RelRep Nat R) : RelRep Nat V := selw p T ≫ RelRep.ofFn f

/-- `update f from T where p = T (p? f ∪ (¬p)?)`, the conditional `(p → f, id)`. -/
def upd (p : R → Bool) (f : R → R) (T : RelRep Nat R) : RelRep Nat R :=
  T ≫ (RelRep.corefl p ≫ RelRep.ofFn f).union (RelRep.corefl (!p ·))

-- select from t where v>1: +`k`v!(`b`a`c;2 3 4)
#guard rows (selw (·.2 > 1) t) == some #[("b", 2), ("a", 3), ("c", 4)]
-- exec v from t where k=`a: 1 3
#guard rows (exec (·.1 == "a") Prod.snd t) == some #[1, 3]
-- update v:v*10 from t where k=`a: +`k`v!(`a`b`a`c;10 2 30 4)
#guard rows (upd (·.1 == "a") (fun r => (r.1, r.2 * 10)) t) == some #[("a", 10), ("b", 2), ("a", 30), ("c", 4)]
-- delete from t where k=`a: +`k`v!(`b`c;2 4)
#guard rows (del (·.1 == "a") t) == some #[("b", 2), ("c", 4)]

/-- `ks Λ((T k)° (T v))`: each key `ks` lists, with its group's fibre. -/
def grp (ks : RelRep κ κ) (k : R → κ) (v : R → V) (T : RelRep Nat R) : Option (RelRep κ (List V)) :=
  (xkey k v T).map fun X => ks ≫ X.transpose

/-- `k xgroup T = dom((T k)°) Λ((T k)° (T v))`: the keys in first appearance, as q's `group`. -/
def xgroup (k : R → κ) (v : R → V) (T : RelRep Nat R) : Option (RelRep κ (List V)) := do
  grp (domP (← fin? (T ≫ RelRep.ofFn k)).conv) k v T

/-- `select agg v by k from T = ran(T k) Λ((T k)° (T v)) agg`: q sorts the keys (`s#`). -/
def selby [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ] [FibreIndex (List V)] (agg : List V → W) (k : R → κ) (v : R → V)
    (T : RelRep Nat R) : Option (RelRep κ W) := do
  -- the keys listed once by `FibreIndex.dedup` before `ran` sorts them: the sort sees each key once
  let ks := FibreIndex.dedup (← fin? (T ≫ RelRep.ofFn k)).vals.toList
  pure ((← grp (.pairs (FinRel.ofList (ks.map fun c => (c, c))).ran) k v T) ≫ RelRep.ofFn agg)

omit [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] in
/-- **`select agg v by k`**: at each key `ks` lists, `agg` of the group's whole fibre — in row order and with
    its repeats, which `sum`/`count`/`avg` need and the Set reading of `Λ` drops. -/
theorem app_selby [FibreIndex (List V)] {agg : List V → W} {k : R → κ} {v : R → V} {T : RelRep Nat R}
    {ks : RelRep κ κ} {X : RelRep κ V} (hX : xkey k v T = some X) {G : RelRep κ (List V)}
    (hG : grp ks k v T = some G) (c : κ) : (G ≫ RelRep.ofFn agg).app c = (ks.app c).map fun c' => agg (X.app c') := by
  simp only [grp, hX, Option.map_some, Option.some.injEq] at hG
  subst hG
  simp [RelRep.app_comp, RelRep.transpose_eq, RelRep.ofFn, RelRep.app_arr_fun, List.flatMap_assoc,
    List.map_eq_flatMap]

/-- `ungroup G = G ∋`. -/
def ungroup (G : RelRep κ (List V)) : RelRep κ V := G ≫ .enum id

-- `k xgroup t: (+(,`k)!,`a`b`c)!+(,`v)!,(1 3;,2;,4)
#guard (xgroup Prod.fst Prod.snd t).bind ps == some #[("a", [1, 3]), ("b", [2]), ("c", [4])]
-- select sum v by k from t: (`s#+(,`k)!,`s#`a`b`c)!+(,`v)!,4 2 4
#guard (selby List.sum Prod.fst Prod.snd t).bind ps == some #[("a", 4), ("b", 2), ("c", 4)]
-- ungroup `k xgroup t: +`k`v!(`a`a`b`c;1 3 2 4)
#guard (xgroup Prod.fst Prod.snd t).bind (ps ∘ ungroup) == some #[("a", 1), ("a", 3), ("b", 2), ("c", 4)]

def t2 : RelRep Nat (Sym × Int) := tab #[("b", 1), ("a", 2), ("b", 3)]
-- `k xgroup t2: (+(,`k)!,`b`a)!+(,`v)!,(1 3;,2) — first appearance
#guard (xgroup Prod.fst Prod.snd t2).bind ps == some #[("b", [1, 3]), ("a", [2])]
-- select sum v by k from t2: (`s#+(,`k)!,`s#`a`b)!+(,`v)!,2 4 ; count: 1 2 — sorted, repeats counted
#guard (selby List.sum Prod.fst Prod.snd t2).bind ps == some #[("a", 2), ("b", 4)]
#guard (selby List.length Prod.fst Prod.snd t2).bind ps == some #[("a", 1), ("b", 2)]

/-- `k xasc T`: `(T k)° T` sorted by key, stably. Order is not a relation property: `sortByKey`. -/
def xasc [Ord κ] [Std.TransOrd κ] (k : R → κ) (T : RelRep Nat R) : Option (Array R) := do
  pure (SortedRel.sortByKey (← (xkey k id T).bind fin?)).toFinRel.vals

/-- `k xdesc T`: RelRep sorts only ascending by the key's `Ord`, so this is a stable list sort (core has
    no stable array sort). -/
def xdesc [Ord κ] (k : R → κ) (T : RelRep Nat R) : Option (Array R) :=
  (rows T).map fun a => (a.toList.mergeSort fun a b => (compare (k b) (k a)).isLE).toArray

-- `k xasc t: +`k`v!(`s#`a`a`b`c;1 3 2 4) ; `k xdesc t: +`k`v!(`c`b`a`a;4 2 1 3)
#guard xasc Prod.fst t == some #[("a", 1), ("a", 3), ("b", 2), ("c", 4)]
#guard xdesc Prod.fst t == some #[("c", 4), ("b", 2), ("a", 1), ("a", 3)]

/-! ## Joins -/

/-- `⟨T, T k KT⟩`: every match of the key, the relational join. -/
def joinAll (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : RelRep Nat (R × W) :=
  T.pair ((T ≫ RelRep.ofFn k) ≫ KT)

/-- `T ij KT = ⟨T, T k first(KT)⟩`: q's keyed lookup takes the first match. -/
def ij (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : RelRep Nat (R × W) := joinAll k T KT.first

/-- `ej[k; T; U] = ⟨T, T k (k xkey U)⟩`: every match, as q's `ej`. -/
def ej (k : R → κ) (k' : S → κ) (w : S → W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × W)) := (xkey k' w U).map (joinAll k T)

/-- `T lj KT = ⟨T, T k look(KT)⟩`. -/
def lj (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : RelRep Nat (R × Option W) := joinAll k T (look KT)

/-- `T pj KT`: `lj`, `0N` read as `0`, then `f` adds. -/
def pj [Zero W] (k : R → κ) (f : R → W → R) (T : RelRep Nat R) (KT : RelRep κ W) : RelRep Nat R :=
  lj k T KT ≫ RelRep.ofFn fun p => f p.1 (p.2.getD 0)

/-- `T uj U = [T f, U g]` on `Idx ⊕ Idx`, `f`, `g` padding the missing columns with nulls. -/
def uj (f : R → X) (g : S → X) (T : RelRep Nat R) (U : RelRep Nat S) : RelRep (Nat ⊕ Nat) X :=
  (T ≫ RelRep.ofFn f).junction (U ≫ RelRep.ofFn g)

/-- Keyed `insert`: `r ∪ s` when no key of `s` is in `r`, else q's `'insert` error, here `none`. -/
def insert (r s : FinRel K V) : Option (FinRel K V) := if s.keys.any r.keys.contains then none else some (r.union s)

def kt : RelRep Sym Int := .pairs ktF
def kt3F : FinRel Sym Int := ⟨#["a", "a", "b"], #[1, 2, 3], rfl⟩

-- t ij kt: +`k`v`w!(`a`b`a;1 2 3;10 20 10)
#guard rows (ij Prod.fst t kt) == some #[(("a", 1), 10), (("b", 2), 20), (("a", 3), 10)]
-- t lj kt: +`k`v`w!(`a`b`a`c;1 2 3 4;10 20 10 0N)
#guard rows (lj Prod.fst t kt) == some #[(("a", 1), some 10), (("b", 2), some 20), (("a", 3), some 10), (("c", 4), none)]
-- t ij kt3, kt3 keyed with `a twice: +`k`v`w!(`a`b`a;1 2 3;1 3 1) — the first match; the relational
-- join answers both.
#guard rows (ij Prod.fst t (.pairs kt3F)) == some #[(("a", 1), 1), (("b", 2), 3), (("a", 3), 1)]
#guard rows (joinAll Prod.fst t (.pairs kt3F)) ==
  some #[(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
-- t lj kt3: +`k`v`w!(`a`b`a`c;1 2 3 4;1 3 1 0N)
#guard rows (lj Prod.fst t (.pairs kt3F)) ==
  some #[(("a", 1), some 1), (("b", 2), some 3), (("a", 3), some 1), (("c", 4), none)]
-- ej[`k;t;([] k:`a`a`b; w:1 2 3)]: +`k`v`w!(`a`a`b`a`a;1 1 2 3 3;1 2 3 1 2)
#guard (ej Prod.fst Prod.fst Prod.snd t (tab #[("a", (1 : Int)), ("a", 2), ("b", 3)])).bind rows ==
  some #[(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
-- t pj ([k:`a`b] v:100 200): +`k`v!(`a`b`a`c;101 202 103 4)
#guard rows (pj Prod.fst (fun r w => (r.1, r.2 + w)) t (.pairs (⟨#["a", "b"], #[100, 200], rfl⟩ : FinRel Sym Int))) ==
  some #[("a", 101), ("b", 202), ("a", 103), ("c", 4)]
-- t pj ([k:`a`a`b] v:1 2 3): +`k`v!(`a`b`a`c;2 5 4 4) — the first match
#guard rows (pj Prod.fst (fun r w => (r.1, r.2 + w)) t (.pairs kt3F)) == some #[("a", 2), ("b", 5), ("a", 4), ("c", 4)]
-- t uj ([] k:`b`e; u:5 6): +`k`v`u!(`a`b`a`c`b`e;1 2 3 4 0N 0N;0N 0N 0N 0N 5 6)
#guard rows (uj (fun r => (r.1, some r.2, (none : Option Int))) (fun r => (r.1, none, some r.2)) t
    (tab #[("b", (5 : Int)), ("e", 6)])) ==
  some #[("a", some 1, none), ("b", some 2, none), ("a", some 3, none), ("c", some 4, none),
    ("b", none, some 5), ("e", none, some 6)]
-- t upsert ([] k:enlist`z; v:enlist 9), and `t insert (`z;9): +`k`v!(`a`b`a`c`z;1 2 3 4 9)
#guard rows (uj id id t (tab #[("z", 9)])) == some #[("a", 1), ("b", 2), ("a", 3), ("c", 4), ("z", 9)]
-- kt uj / upsert ([k:`b`e] w:22 50): (+(,`k)!,`a`b`d`e)!+(,`w)!,10 22 40 50 — `b keeps its place
#guard ps (upsert ktF ⟨#["b", "e"], #[22, 50], rfl⟩) == some #[("a", 10), ("b", 22), ("d", 40), ("e", 50)]
-- `kt insert (`b;99): 'insert
#guard (insert ktF ⟨#["b"], #[99], rfl⟩).isNone

/-! ## As-of and window joins -/

/-- `C = (T k)(U k)°`, then each right row's `(time, value)` beside the left time. `(U k)°` is enumerable
    only when `U k` is held as pairs. -/
def cand (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (Int × (Int × W))) :=
  (fin? (U ≫ RelRep.ofFn k')).map fun u =>
    (T ≫ RelRep.ofFn tm).pair (((T ≫ RelRep.ofFn k) ≫ .pairs u.conv) ≫ (U ≫ RelRep.ofFn tv))

/-- `≥` on the right time. -/
def geT : RelTest (Int × (Int × W)) (Int × (Int × W)) := .test fun a b => decide (b.2.1 ≤ a.2.1)

/-- `Λ(C ∩ (right time ≤ left time + o)) est(≥)`: every right row at the greatest such time. -/
def prevail (o : Int) (C : RelRep Nat (Int × (Int × W))) : RelRep Nat (Int × (Int × W)) :=
  RelRep.est geT (C.inter (.test fun _ x => decide (x.2.1 ≤ x.1 + o)))

/-- `⟨T, D ⊕ ˆz⟩` on every row of `T`, `D` keyed by row; `dom T` is listed only when `T` is held as pairs. -/
def onRows (T : RelRep Nat R) (D : RelRep Nat V) (z : V) : Option (RelRep Nat (R × V)) :=
  (fin? T).map fun r => T.pair (domP r ≫ RelRep.override D (RelRep.ofFn fun _ => z))

/-- `aj = ⟨T, prevail(0) last p ⊕ ˆnone⟩`, the spec: it lists `C`, every right row of a left row's key. -/
def ajSpec (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × Option W)) :=
  (cand k tm k' tv T U).bind fun C => onRows T ((prevail 0 C).last ≫ RelRep.ofFn fun x => some x.2.2) none

/-! ### `aj` by binary search

q's `aj` searches each left row's time in its key's right rows, sorted by time. `ajSpec`'s fibre at a left
row is restated over the fibre lists (`ajFib`); where the row is one and its key's right rows are ascending
in time, `fastOne` answers it by a binary search whose answer is checked at its two neighbours. -/

omit [DecidableEq W] [FibreIndex W] in
/-- The right rows `(time, value)` ascend in time, checked on neighbours. -/
def ascT : List (Int × W) → Bool
  | x :: y :: t => decide (x.1 ≤ y.1) && ascT (y :: t)
  | _ => true

omit [DecidableEq W] [FibreIndex W] in
theorem ascT_iff : (l : List (Int × W)) → (ascT l = true ↔ l.Pairwise fun x y => x.1 ≤ y.1)
  | [] => by simp [ascT]
  | [_] => by simp [ascT]
  | x :: y :: t => by
    rw [ascT, Bool.and_eq_true, decide_eq_true_iff, ascT_iff (y :: t), List.pairwise_cons (l := y :: t)]
    refine ⟨fun ⟨h, hp⟩ => ⟨fun z hz => ?_, hp⟩, fun ⟨h, hp⟩ => ⟨h y (List.mem_cons_self ..), hp⟩⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h
    · exact Int.le_trans h (List.rel_of_pairwise_cons hp hz)

omit [DecidableEq W] [FibreIndex W] in
/-- On ascending rows, the rows at time `≤ t` are the first `p`, when row `p - 1` is and row `p` is not. -/
theorem filter_eq_take {t : Int} : (l : List (Int × W)) → l.Pairwise (fun x y => x.1 ≤ y.1) → (p : Nat) →
    (p = 0 ∨ l[p - 1]?.any (·.1 ≤ t)) → l[p]?.all (fun x => !decide (x.1 ≤ t)) →
    l.filter (fun y => decide (y.1 ≤ t)) = l.take p
  | [], _, _, _, _ => by simp
  | x :: r, hs, 0, _, h2 => by
    have hx : ¬ x.1 ≤ t := fun h => by
      have e : (!decide (x.1 ≤ t)) = true := h2
      rw [decide_eq_true h] at e; exact Bool.noConfusion e
    rw [List.pairwise_cons] at hs
    rw [List.filter_cons, if_neg (fun e => hx (of_decide_eq_true e)), List.take_zero]
    -- by hand: `List.filter_eq_nil_iff` uses `Classical.choice`
    have hnil : ∀ l : List (Int × W), (∀ y ∈ l, ¬ y.1 ≤ t) → l.filter (fun y => decide (y.1 ≤ t)) = [] := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons y l ih =>
        intro h
        rw [List.filter_cons, if_neg (fun e => h y (List.mem_cons_self ..) (of_decide_eq_true e)),
          ih fun z hz => h z (List.mem_cons_of_mem _ hz)]
    exact hnil r fun y hy hyt => hx (Int.le_trans (hs.1 y hy) hyt)
  | x :: r, hs, p + 1, h1, h2 => by
    rw [List.pairwise_cons] at hs
    have h1' : (x :: r)[p]?.any (·.1 ≤ t) = true := h1.resolve_left (Nat.succ_ne_zero p)
    have hx : x.1 ≤ t := by
      cases p with
      | zero => exact of_decide_eq_true h1'
      | succ q =>
        rw [List.getElem?_cons_succ] at h1'
        cases hq : r[q]? with
        | none => rw [hq] at h1'; exact Bool.noConfusion h1'
        | some y => rw [hq] at h1'; exact Int.le_trans (hs.1 y (List.mem_of_getElem? hq)) (of_decide_eq_true h1')
    have h1r : p = 0 ∨ r[p - 1]?.any (·.1 ≤ t) = true := by
      cases p with
      | zero => exact .inl rfl
      | succ q => rw [List.getElem?_cons_succ] at h1'; exact .inr h1'
    rw [List.getElem?_cons_succ] at h2
    rw [List.filter_cons, if_pos (decide_eq_true hx), List.take_succ_cons, filter_eq_take r hs.2 p h1r h2]

omit [DecidableEq W] [FibreIndex W] in
/-- On ascending rows, `est(≥)` keeps the last row, so its last is the last row. -/
theorem getLast?_estList (xs : List (Int × W)) (hs : xs.Pairwise fun x y => x.1 ≤ y.1) :
    (RelRep.estList (fun a b => decide (b.1 ≤ a.1)) xs).getLast? = xs.getLast? := by
  rcases List.eq_nil_or_concat xs with rfl | ⟨L, b, rfl⟩
  · rfl
  · rw [List.concat_eq_append] at hs ⊢
    rw [List.pairwise_append] at hs
    have hb : ∀ y ∈ L ++ [b], y.1 ≤ b.1 := fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · exact hs.2.2 y hy b (List.mem_singleton_self b)
      · rw [List.mem_singleton.1 hy]; exact Int.le_refl _
    simp only [RelRep.estList, List.filter_append, List.getLast?_append, List.getLast?_singleton]
    simp only [List.filter_cons, List.filter_nil, List.all_eq_true, decide_eq_true_eq, if_pos hb]
    simp

omit [DecidableEq W] [FibreIndex W] in
/-- The number of rows at time `≤ t`, by halving `[lo, hi)`: the search is not proved, its answer is
    checked by `fastOne`. -/
def bsearch (a : Array (Int × W)) (t : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    match a[(lo + hi) / 2]? with
    | some x => if x.1 ≤ t then bsearch a t ((lo + hi) / 2 + 1) hi else bsearch a t lo ((lo + hi) / 2)
    | none => lo
  else lo
termination_by hi - lo
decreasing_by all_goals omega

omit [DecidableEq W] [FibreIndex W] in
/-- The value of the last row at the greatest time `≤ t`, when the search's answer `p` passes its check. -/
def fastOne (a : Array (Int × W)) (t : Int) : Option (List (Option W)) :=
  let p := bsearch a t 0 a.size
  if (p == 0 || a[p - 1]?.any (·.1 ≤ t)) && a[p]?.all (fun x => !decide (x.1 ≤ t)) then
    some (if p = 0 then [] else a[p - 1]?.toList.map fun x => some x.2)
  else none

/-- **`fastOne` is `prevail(0) last` of one left row** at time `t` against its key's ascending rows. -/
theorem fastOne_eq {a : Array (Int × W)} {t : Int} (hs : ascT a.toList = true) {x : List (Option W)}
    (h : fastOne a t = some x) :
    x = ((RelRep.estList (geT (W := W)).mem ((RelRep.cross [t] a.toList).filter fun x => decide (x.2.1 ≤ x.1 + 0))).getLast?.toList).flatMap
      fun x => [some x.2.2] := by
  rw [ascT_iff] at hs
  simp only [fastOne, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  split at h
  · rename_i hc
    cases h
    have ht := filter_eq_take a.toList hs (bsearch a t 0 a.size) (by simpa using hc.1) (by simpa using hc.2)
    have hf : (RelRep.cross [t] a.toList).filter (fun x => decide (x.2.1 ≤ x.1 + 0)) =
        (a.toList.take (bsearch a t 0 a.size)).map ((t, ·)) := by
      rw [← ht]; simp [RelRep.cross, List.filter_map, Function.comp_def]
    have he : ∀ xs : List (Int × W), RelRep.estList (geT (W := W)).mem (xs.map ((t, ·))) =
        (RelRep.estList (fun a b => decide (b.1 ≤ a.1)) xs).map ((t, ·)) := fun xs => by
      simp [RelRep.estList, geT, RelRep.mem, List.filter_map, Function.comp_def, List.all_map]
    rw [hf, he, List.getLast?_map, getLast?_estList _ (hs.sublist (List.take_sublist _ _)), List.getLast?_take]
    split
    · simp
    · rename_i hp
      obtain ⟨y, hy, -⟩ : ∃ y, a[bsearch a t 0 a.size - 1]? = some y ∧ y.1 ≤ t := by
        simpa [hp, Option.any_eq_true] using hc.1
      simp [hy]
  · cases h

/-- `ajSpec`'s fibre at left row `i`, over `T`'s fibres `fT` and the right rows `gG` of a key. -/
def ajFib {I : Type} (k : R → κ) (tm : R → Int) (fT : I → List R) (gG : κ → List (Int × W)) (i : I) :
    List (Option W) :=
  ((RelRep.estList (geT (W := W)).mem ((RelRep.cross ((fT i).flatMap fun r => [tm r])
      ((fT i).flatMap fun r => gG (k r))).filter fun x => decide (x.2.1 ≤ x.1 + 0))).getLast?.toList).flatMap
    fun x => [some x.2.2]

/-- The fibres of `aj`: one left row whose key's rows ascend by `fastOne`, every other by `ajFib`.  The
    ascending groups are found once, each key's `(rows, ascending)` held in `h`. -/
def ajFast {I : Type} [DecidableEq I] [FibreIndex I] (k : R → κ) (tm : R → Int) (t : FinRel I R)
    (g : FinRel κ (Int × W)) : RelRep I (Option W) :=
  let ti := FibreIndex.build t
  let gi := FibreIndex.build g
  let hi := FibreIndex.build (FinRel.ofList ((FibreIndex.dedup g.keys.toList).filterMap fun c =>
    let l := FibreIndex.get gi c
    if ascT l then some (c, l.toArray) else none))
  .enum fun i => match FibreIndex.get ti i with
    | [r] => match FibreIndex.get hi (k r) with
      | [a] => match fastOne a (tm r) with
        | some x => x
        | none => ajFib k tm (FibreIndex.get ti) (FibreIndex.get gi) i
      | _ => ajFib k tm (FibreIndex.get ti) (FibreIndex.get gi) i
    | _ => ajFib k tm (FibreIndex.get ti) (FibreIndex.get gi) i

/-- q's `aj`: `ajFast` on two tables held as pairs (`aj_eq`), `ajSpec` itself otherwise. -/
def aj (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × Option W)) :=
  match fin? T, fin? (U ≫ RelRep.ofFn k') with
  | some t, some u => match RelRep.pairs u.conv ≫ (U ≫ RelRep.ofFn tv) with
    | .pairs g => onRows T (ajFast k tm t g) none
    | _ => ajSpec k tm k' tv T U
  | _, _ => ajSpec k tm k' tv T U

omit [DecidableEq W] [FibreIndex W] in
theorem onRows_congr (T : RelRep Nat R) {D D' : RelRep Nat V} (h : D.app = D'.app) (z : V) :
    onRows T D z = onRows T D' z := by
  simp only [onRows, RelRep.override_eq, h]

omit [DecidableEq X] [FibreIndex X] in
/-- **`aj` is `ajSpec`**: the binary search answers what `Λ(C ∩ ≥) est(≥) last` does. -/
theorem aj_eq (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    aj k tm k' tv T U = ajSpec k tm k' tv T U := by
  unfold aj
  split
  · rename_i t u ht hu
    have hT := app_of_fin? ht
    split
    · rename_i g hg
      have hgG : g.scanLookup = fun c => ((RelRep.pairs u.conv).app c).flatMap (U ≫ RelRep.ofFn tv).app := by
        funext c; rw [← RelRep.app_pairs, ← hg, RelRep.app_comp]
      rw [ajSpec, cand, hu, Option.map_some, Option.bind_some]
      refine onRows_congr _ (funext fun i => ?_) none
      simp only [ajFast, RelRep.app_enum]
      refine Eq.trans (b := ajFib k tm (@FibreIndex.get Nat instDecidableEqNat _ R (@FibreIndex.build Nat instDecidableEqNat _ R t))
        (FibreIndex.get (FibreIndex.build g)) i) ?_ ?_
      · split
        · rename_i r hr
          split
          · rename_i a ha
            split
            · rename_i x hx
              have hm := List.mem_singleton_self a
              rw [← ha, FibreIndex.get_build, FinRel.mem_scanLookup, FinRel.rep_ofList] at hm
              obtain ⟨c, -, hc⟩ := List.mem_filterMap.1 hm
              dsimp only at hc
              split at hc
              · rename_i hasc
                simp only [Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨rfl, rfl⟩ := hc
                rw [fastOne_eq (by simpa using hasc) hx]
                simp [ajFib, hr]
              · cases hc
            · rfl
          · rfl
        · rfl
      · simp only [ajFib, FibreIndex.get_build, hgG, prevail, RelRep.app_comp, RelRep.last_eq, RelRep.app_enum,
          RelRep.app_est, RelRep.app_inter, RelRep.app_pair, RelRep.app_pairs, hT, RelRep.ofFn, RelRep.app_arr_fun, List.flatMap_assoc,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · rfl
  · rfl

/-- `wj1`: `Λ(C ∩ window) sum` per left row, the window `[t+lo, t+hi]`. -/
def wj1 [Add W] [Zero W] (lo hi : Int) (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W)
    (T : RelRep Nat R) (U : RelRep Nat S) : Option (RelRep Nat (R × W)) :=
  (cand k tm k' tv T U).bind fun C =>
    onRows T ((C.inter (.test fun _ x => decide (x.1 + lo ≤ x.2.1 ∧ x.2.1 ≤ x.1 + hi))).transpose
      ≫ RelRep.ofFn fun xs => (xs.map (·.2.2)).sum) 0

/-- `wj`, the spec: the window `(t+lo, t+hi]` and the row prevailing at `t+lo`, summed; it lists `C`, every
    right row of a left row's key. -/
def wjSpec [Add W] [Zero W] (lo hi : Int) (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W)
    (T : RelRep Nat R) (U : RelRep Nat S) : Option (RelRep Nat (R × W)) :=
  (cand k tm k' tv T U).bind fun C =>
    onRows T (RelRep.transpose ((prevail lo C).last.union
        (C.inter (.test fun _ x => decide (x.1 + lo < x.2.1 ∧ x.2.1 ≤ x.1 + hi))))
      ≫ RelRep.ofFn fun xs => (xs.map (·.2.2)).sum) 0

/-! ### `wj` by binary search

As `aj`: `wjSpec`'s fibre at a left row restated over the fibre lists (`wjFib`); a single left row whose key's
right rows ascend in time is answered by two binary searches, `t+lo` and `t+hi`, each checked at its two
neighbours (`wjOne`). -/

omit [DecidableEq W] [FibreIndex W] in
/-- On ascending rows, the rows at time `> t` are those from `p` on, when row `p - 1` is at `≤ t` and row `p`
    is not. -/
theorem filter_not_eq_drop {t : Int} (l : List (Int × W)) (hs : l.Pairwise fun x y => x.1 ≤ y.1) (p : Nat)
    (h1 : p = 0 ∨ l[p - 1]?.any (·.1 ≤ t)) (h2 : l[p]?.all (fun x => !decide (x.1 ≤ t))) :
    l.filter (fun y => !decide (y.1 ≤ t)) = l.drop p := by
  rw [show l.filter (fun y => !decide (y.1 ≤ t)) = (l.take p ++ l.drop p).filter (fun y => !decide (y.1 ≤ t)) by rw [List.take_append_drop]]
  rw [List.filter_append, ← filter_eq_take l hs p h1 h2, List.filter_filter,
    List.filter_congr (q := fun _ => false) (fun y _ => by cases decide (y.1 ≤ t) <;> rfl), List.rec (motive := fun m => m.filter (fun _ => false) = []) rfl (fun _ _ ih => ih) l,
    List.nil_append]
  have hd := hs.sublist (List.drop_sublist p l)
  cases hdp : l.drop p with
  | nil => rfl
  | cons z r =>
    rw [hdp, List.pairwise_cons] at hd
    have hz : ¬ z.1 ≤ t := by
      have e : l[p]? = some z := by rw [← List.head?_drop, hdp]; rfl
      rw [e] at h2; intro hle; have h3 : (!decide (z.1 ≤ t)) = true := h2; rw [decide_eq_true hle] at h3; cases h3
    rw [List.filter_cons, if_pos (by rw [decide_eq_false hz]; rfl),
      List.filter_congr (q := fun _ => true) (fun y hy => by rw [decide_eq_false fun h => hz (Int.le_trans (hd.1 y hy) h)]; rfl),
      List.filter_eq_self.2 (fun _ _ => rfl)]

omit [DecidableEq W] [FibreIndex W] in
/-- The search's answer `p` for time `s` passes its check at both neighbours. -/
def chk (a : Array (Int × W)) (s : Int) (p : Nat) : Bool :=
  (p == 0 || a[p - 1]?.any (·.1 ≤ s)) && a[p]?.all (fun x => !decide (x.1 ≤ s))

omit [DecidableEq W] [FibreIndex W] in
theorem chk_spec {a : Array (Int × W)} {s : Int} {p : Nat} (h : chk a s p = true) :
    (p = 0 ∨ a.toList[p - 1]?.any (·.1 ≤ s)) ∧ a.toList[p]?.all (fun x => !decide (x.1 ≤ s)) := by
  simp only [chk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  simpa using h

omit [FibreIndex W] in
/-- The row prevailing at `t+o`, by `est(≥) last` over the rows at time `≤ t+o`: row `p - 1`. -/
theorem prev_eq {a : Array (Int × W)} {t o : Int} (hs : a.toList.Pairwise fun x y => x.1 ≤ y.1) {p : Nat}
    (hc : chk a (t + o) p = true) :
    ((RelRep.estList (geT (W := W)).mem ((RelRep.cross [t] a.toList).filter fun x =>
        decide (x.2.1 ≤ x.1 + o))).getLast?.toList).map (·.2.2) =
      if p = 0 then [] else a[p - 1]?.toList.map (·.2) := by
  obtain ⟨h1, h2⟩ := chk_spec hc
  have ht := filter_eq_take a.toList hs p h1 h2
  have hf : (RelRep.cross [t] a.toList).filter (fun x => decide (x.2.1 ≤ x.1 + o)) = (a.toList.take p).map ((t, ·)) := by
    rw [← ht]; simp [RelRep.cross, List.filter_map, Function.comp_def]
  have he : ∀ xs : List (Int × W), RelRep.estList (geT (W := W)).mem (xs.map ((t, ·))) =
      (RelRep.estList (fun a b => decide (b.1 ≤ a.1)) xs).map ((t, ·)) := fun xs => by
    simp [RelRep.estList, geT, RelRep.mem, List.filter_map, Function.comp_def, List.all_map]
  rw [hf, he, List.getLast?_map, getLast?_estList _ (hs.sublist (List.take_sublist _ _)), List.getLast?_take]
  by_cases hp : p = 0
  · simp [hp]
  · have h1' := h1.resolve_left hp
    simp only [Array.getElem?_toList] at h1'
    simp only [hp, if_false]
    cases e : a[p - 1]? with
    | none => rw [e] at h1'; cases h1'
    | some z => simp [Array.getElem?_toList, e]

omit [DecidableEq W] [FibreIndex W] in
omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- Rows `p … p+m-1` read by index are the slice `drop p (take (p+m))`; core's `List.drop_take` uses
    `Classical.choice`, this induction does not. -/
theorem range'_filterMap {α : Type} : ∀ (l : List α) (p m : Nat),
    (List.range' p m).filterMap (l[·]?) = (l.take (p + m)).drop p
  | [], p, m => by
    have hn : ∀ (js : List Nat), js.filterMap (fun j => ([] : List α)[j]?) = [] := fun js => by
      induction js with
      | nil => rfl
      | cons j js ih => simpa only [List.filterMap_cons, List.getElem?_nil] using ih
    simp only [hn, List.take_nil, List.drop_nil]
  | x :: l, 0, 0 => rfl
  | x :: l, 0, m + 1 => by
    have ih := range'_filterMap l 0 m
    rw [List.range'_succ, List.filterMap_cons, List.range'_succ_left, List.filterMap_map]
    simp only [List.drop_zero, Nat.zero_add] at ih ⊢
    rw [List.take_succ_cons, ← ih]; rfl
  | x :: l, p + 1, m => by
    rw [List.range'_succ_left, List.filterMap_map, Nat.add_right_comm]
    exact range'_filterMap l p m

/-- The rows in the window `(t+lo, t+hi]`: rows `p₁ … p₂ - 1`. -/
theorem window_eq {a : Array (Int × W)} {t lo hi : Int} (hs : a.toList.Pairwise fun x y => x.1 ≤ y.1) {p₁ p₂ : Nat}
    (h12 : p₁ ≤ p₂) (c₁ : chk a (t + lo) p₁ = true) (c₂ : chk a (t + hi) p₂ = true) :
    ((RelRep.cross [t] a.toList).filter fun x => decide (x.1 + lo < x.2.1 ∧ x.2.1 ≤ x.1 + hi)).map (·.2.2) =
      ((List.range' p₁ (p₂ - p₁)).filterMap (a.toList[·]?)).map (·.2) := by
  obtain ⟨c1, d1⟩ := chk_spec c₁
  obtain ⟨c2, d2⟩ := chk_spec c₂
  have e : (RelRep.cross [t] a.toList).filter (fun x => decide (x.1 + lo < x.2.1 ∧ x.2.1 ≤ x.1 + hi)) =
      ((a.toList.filter fun y => decide (y.1 ≤ t + hi)).filter fun y => !decide (y.1 ≤ t + lo)).map ((t, ·)) := by
    simp only [RelRep.cross, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_map, List.filter_filter]
    congr 1
    exact List.filter_congr fun y _ => by
      by_cases h : y.1 ≤ t + lo <;> by_cases h' : y.1 ≤ t + hi <;> simp [h, h'] <;> omega
  rw [e, filter_eq_take _ hs p₂ c2 d2, filter_not_eq_drop _ (hs.sublist (List.take_sublist _ _)) p₁ ?_ ?_]
  · rw [range'_filterMap, Nat.add_sub_cancel' h12, List.map_map]; rfl
  · by_cases hp : p₁ = 0
    · exact .inl hp
    · rcases c1 with h | h
      · exact .inl h
      · exact .inr (by rw [List.getElem?_take, if_pos (by omega)]; exact h)
  · rw [List.getElem?_take]; split
    · exact d1
    · rfl

omit [DecidableEq W] [FibreIndex W] in
/-- `wj`'s sum at one left row at time `t` against its key's ascending rows, when both searches pass their
    checks. -/
def wjOne [Add W] [Zero W] (lo hi : Int) (a : Array (Int × W)) (t : Int) : Option (List W) :=
  let p₁ := bsearch a (t + lo) 0 a.size
  let p₂ := bsearch a (t + hi) 0 a.size
  if p₁ ≤ p₂ ∧ chk a (t + lo) p₁ = true ∧ chk a (t + hi) p₂ = true then
    some [((if p₁ = 0 then [] else a[p₁ - 1]?.toList.map (·.2)) ++
      ((List.range' p₁ (p₂ - p₁)).filterMap (a.toList[·]?)).map (·.2)).sum]
  else none

/-- `wjOne` summed on the array: the window right to left, so the sum nests as `List.sum`'s `foldr` does,
    and the prevailing row added last; no list but the one-value fibre. -/
def wjOneTR [Add W] [Zero W] (lo hi : Int) (a : Array (Int × W)) (t : Int) : Option (List W) :=
  let p₁ := bsearch a (t + lo) 0 a.size
  let p₂ := bsearch a (t + hi) 0 a.size
  if p₁ ≤ p₂ ∧ chk a (t + lo) p₁ = true ∧ chk a (t + hi) p₂ = true then
    let s := rangeFoldDown (fun j s => match a[j]? with | some x => x.2 + s | none => s) (p₂ - p₁) p₁ 0
    some [if p₁ = 0 then s else match a[p₁ - 1]? with | some x => x.2 + s | none => s]
  else none

omit [DecidableEq W] [FibreIndex W] in
@[csimp] theorem wjOne_eq_wjOneTR : @wjOne = @wjOneTR := by
  funext W _ _ lo hi a t
  simp only [wjOne, wjOneTR]
  split
  · have e : ∀ (m p : Nat), (((List.range' p m).filterMap (a.toList[·]?)).map (·.2)).sum =
        rangeFoldDown (fun j (s : W) => match a[j]? with | some x => x.2 + s | none => s) m p 0 := by
      intro m p
      rw [rangeFoldDown_eq]
      induction List.range' p m with
      | nil => rfl
      | cons j js ih => cases h : a[j]? <;> simp_all
    rw [← e]
    split
    · simp
    · cases a[bsearch a (t + lo) 0 a.size - 1]? <;> simp [List.sum_cons]
  · rfl

/-- `wjSpec`'s fibre at left row `i`, over `T`'s fibres `fT` and the right rows `gG` of a key. -/
def wjFib [Add W] [Zero W] {I : Type} (lo hi : Int) (k : R → κ) (tm : R → Int) (fT : I → List R)
    (gG : κ → List (Int × W)) (i : I) : List W :=
  let c := RelRep.cross ((fT i).flatMap fun r => [tm r]) ((fT i).flatMap fun r => gG (k r))
  [(((RelRep.estList (geT (W := W)).mem (c.filter fun x => decide (x.2.1 ≤ x.1 + lo))).getLast?.toList ++
    c.filter fun x => decide (x.1 + lo < x.2.1 ∧ x.2.1 ≤ x.1 + hi)).map (·.2.2)).sum]

omit [FibreIndex W] in
/-- **`wjOne` is `wjFib` of one left row** against its key's ascending rows. -/
theorem wjOne_eq [Add W] [Zero W] {lo hi : Int} {a : Array (Int × W)} {t : Int} (hs : ascT a.toList = true)
    {x : List W} (h : wjOne lo hi a t = some x) :
    x = [(((RelRep.estList (geT (W := W)).mem ((RelRep.cross [t] a.toList).filter fun x => decide (x.2.1 ≤ x.1 + lo))).getLast?.toList ++
      (RelRep.cross [t] a.toList).filter fun x => decide (x.1 + lo < x.2.1 ∧ x.2.1 ≤ x.1 + hi)).map (·.2.2)).sum] := by
  rw [ascT_iff] at hs
  simp only [wjOne] at h
  split at h
  · rename_i hc
    cases h
    rw [List.map_append, prev_eq hs hc.2.1, window_eq hs hc.1 hc.2.1 hc.2.2]
  · cases h

/-- The fibres of `wj`: one left row whose key's rows ascend by `wjOne`, every other by `wjFib`. -/
def wjFast [Add W] [Zero W] {I : Type} [DecidableEq I] [FibreIndex I] (lo hi : Int) (k : R → κ) (tm : R → Int)
    (t : FinRel I R) (g : FinRel κ (Int × W)) : RelRep I W :=
  let ti := FibreIndex.build t
  let gi := FibreIndex.build g
  let hi' := FibreIndex.build (FinRel.ofList ((FibreIndex.dedup g.keys.toList).filterMap fun c =>
    let l := FibreIndex.get gi c
    if ascT l then some (c, l.toArray) else none))
  .enum fun i => match FibreIndex.get ti i with
    | [r] => match FibreIndex.get hi' (k r) with
      | [a] => match wjOne lo hi a (tm r) with
        | some x => x
        | none => wjFib lo hi k tm (FibreIndex.get ti) (FibreIndex.get gi) i
      | _ => wjFib lo hi k tm (FibreIndex.get ti) (FibreIndex.get gi) i
    | _ => wjFib lo hi k tm (FibreIndex.get ti) (FibreIndex.get gi) i

/-- q's `wj`: `wjFast` on two tables held as pairs (`wj_eq`), `wjSpec` itself otherwise. -/
def wj [Add W] [Zero W] (lo hi : Int) (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W)
    (T : RelRep Nat R) (U : RelRep Nat S) : Option (RelRep Nat (R × W)) :=
  match fin? T, fin? (U ≫ RelRep.ofFn k') with
  | some t, some u => match RelRep.pairs u.conv ≫ (U ≫ RelRep.ofFn tv) with
    | .pairs g => onRows T (wjFast lo hi k tm t g) 0
    | _ => wjSpec lo hi k tm k' tv T U
  | _, _ => wjSpec lo hi k tm k' tv T U

omit [DecidableEq X] [FibreIndex X] in
/-- **`wj` is `wjSpec`**: the two binary searches answer what the prevailing row and the window of `C` do. -/
theorem wj_eq [Add W] [Zero W] (lo hi : Int) (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W)
    (T : RelRep Nat R) (U : RelRep Nat S) : wj lo hi k tm k' tv T U = wjSpec lo hi k tm k' tv T U := by
  unfold wj
  split
  · rename_i t u ht hu
    have hT := app_of_fin? ht
    split
    · rename_i g hg
      have hgG : g.scanLookup = fun c => ((RelRep.pairs u.conv).app c).flatMap (U ≫ RelRep.ofFn tv).app := by
        funext c; rw [← RelRep.app_pairs, ← hg, RelRep.app_comp]
      rw [wjSpec, cand, hu, Option.map_some, Option.bind_some]
      refine onRows_congr _ (funext fun i => ?_) 0
      simp only [wjFast, RelRep.app_enum]
      refine Eq.trans (b := wjFib lo hi k tm (@FibreIndex.get Nat instDecidableEqNat _ R (@FibreIndex.build Nat instDecidableEqNat _ R t))
        (FibreIndex.get (FibreIndex.build g)) i) ?_ ?_
      · split
        · rename_i r hr
          split
          · rename_i a ha
            split
            · rename_i x hx
              have hm := List.mem_singleton_self a
              rw [← ha, FibreIndex.get_build, FinRel.mem_scanLookup, FinRel.rep_ofList] at hm
              obtain ⟨c, -, hc⟩ := List.mem_filterMap.1 hm
              dsimp only at hc
              split at hc
              · rename_i hasc
                simp only [Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨rfl, rfl⟩ := hc
                rw [wjOne_eq (by simpa using hasc) hx]
                simp [wjFib, hr]
              · cases hc
            · rfl
          · rfl
        · rfl
      · simp only [wjFib, FibreIndex.get_build, hgG, prevail, RelRep.app_comp, RelRep.last_eq, RelRep.app_enum,
          RelRep.app_est, RelRep.app_inter, RelRep.app_pair, RelRep.app_pairs, RelRep.app_union, RelRep.transpose_eq,
          hT, RelRep.ofFn, RelRep.app_arr_fun, List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
    · rfl
  · rfl

def tr : RelRep Nat (Sym × Int) := tab #[("x", 2), ("x", 5), ("y", 4)]
def qr : RelRep Nat (Sym × Int × Int) := tab #[("x", 1, 10), ("x", 3, 20), ("x", 3, 21), ("y", 5, 30)]

-- aj[`s`tm;tr;qr]: +`s`tm`p!(`x`x`y;2 5 4;10 21 0N)
#guard (aj Prod.fst Prod.snd Prod.fst Prod.snd tr qr).bind rows ==
  some #[(("x", 2), some 10), (("x", 5), some 21), (("y", 4), none)]
-- `est(≥)` alone answers both rows at time 3 for the left row `x 5; q's `aj` takes the last.
#guard (cand Prod.fst Prod.snd Prod.fst Prod.snd tr qr).bind (ps ∘ prevail 0) ==
  some #[(0, (2, (1, 10))), (1, (5, (3, 20))), (1, (5, (3, 21)))]
-- qr asof `s`tm!(`x;3): (,`p)!,21 ; at 2: (,`p)!,10
#guard (aj Prod.fst Prod.snd Prod.fst Prod.snd (tab #[("x", (3 : Int))]) qr).bind rows == some #[(("x", 3), some 21)]
#guard (aj Prod.fst Prod.snd Prod.fst Prod.snd (tab #[("x", (2 : Int))]) qr).bind rows == some #[(("x", 2), some 10)]
-- wj1[-2 0+\:tr`tm;`s`tm;tr;(qr;(sum;`p))]: +`s`tm`p!(`x`x`y;2 5 4;10 41 0)
#guard (wj1 (-2) 0 Prod.fst Prod.snd Prod.fst Prod.snd tr qr).bind rows ==
  some #[(("x", 2), 10), (("x", 5), 41), (("y", 4), 0)]
-- wj[...]: +`s`tm`p!(`x`x`y;2 5 4;10 21 0)
#guard (wj (-2) 0 Prod.fst Prod.snd Prod.fst Prod.snd tr qr).bind rows ==
  some #[(("x", 2), 10), (("x", 5), 21), (("y", 4), 0)]

#print axioms app_look
#print axioms app_selby
#print axioms aj_eq
#print axioms wj_eq

end LeetQ.Q
