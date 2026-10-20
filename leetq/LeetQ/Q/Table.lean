/-
  q's dictionary, table, qSQL and join operators as `RelRep` expressions, each checked by `#guard`
  against real q's output on the same input (q 4.x, the line under each `#guard`).

  Representation.
  * A dict `d` is a relation `key ↦ value`, a `FinRel` (a map when the keys are unique); `!` is the
    constructor `FinRel.mk` itself, the two parallel arrays.
  * A table `T` is `ix(rows) : Idx ⟶ Row`; a keyed table is a relation `KeyRow ↦ ValRow`.
  * A `RelRep` means a list per key (`app?`: order and repeats), so q's choices by position — the first
    match of a key, the last row at a time — are `first`/`last` of a fibre, and an aggregate sees the
    group's fibre with its repeats (`app?_selby`).
  * `fin?`/`ps`/`rows` read an answer back; they fail (`none`) on an answer held as `enum`/`test`, whose
    pairs are not listed.

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

variable [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X]
  [DecidableEq κ] [FibreIndex κ]

/-- `dom r` held as pairs, each key once, in order of first appearance: q's key order. -/
def domP (r : FinRel K V) : RelRep K K := .pairs (FinRel.ofList ((FibreIndex.dedup (r.toList.map Prod.fst)).map fun k => (k, k)))

/-- q's keyed lookup `look(D) ≜ first(D) some ⊕ ˆnone`: the first value of the fibre, `0N` when empty. -/
def look (D : RelRep K V) : Option (RelRep K (Option V)) := do
  RelRep.override (← (← D.first).comp (RelRep.ofFn some)) (RelRep.ofFn fun _ => none)

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- `look` reads the fibre list: its head, or `0N` when it is empty. -/
theorem app?_look {D : RelRep K V} {f : K → List V} (h : D.app? = some f) {L : RelRep K (Option V)}
    (hL : look D = some L) : L.app? = some fun k => [(f k).head?] := by
  simp only [look, RelRep.first_of_app? h, RelRep.ofFn, RelRep.comp, RelRep.override, RelRep.app?,
    Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.some.injEq] at hL
  subst hL
  simp only [RelRep.app?, Option.some.injEq]
  funext k; cases f k <;> simp

/-- `d k = k̂ look(d)`: the constant `k̂ : 1 → K`, then the lookup. -/
def get (D : RelRep K V) (k : K) : Option (RelRep Unit (Option V)) := do
  (RelRep.pairs (FinRel.ofList [((), k)])).comp (← look D)

/-- `d@ks = ix(ks) look(d)`. -/
def getAll (D : RelRep K V) (ks : List K) : Option (RelRep Nat (Option V)) := do (tab ks).comp (← look D)

-- d`b: 2 ; d`z: 0N ; d`a`c: 1 3 ; d`a`z: 1 0N ; (`a`a`b!1 2 3)`a: 1
#guard rows (get d "b") == some [some 2]
#guard rows (get d "z") == some [none]
#guard rows (getAll d ["a", "c"]) == some [some 1, some 3]
#guard rows (getAll d ["a", "z"]) == some [some 1, none]
#guard rows (get (.pairs (⟨#["a", "a", "b"], #[1, 2, 3], rfl⟩ : FinRel Sym Int)) "a") == some [some 1]

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

/-- `r,s = dom(r ∪ s) (s ⊕ r)`, dicts and keyed `upsert`: the keys in first appearance, each answered by
    `s` where it has a value. -/
def upsert (r s : FinRel K V) : Option (RelRep K V) := do
  (domP (r.union s)).comp (← RelRep.override (.pairs s) (.pairs r))

-- d,e: `a`b`c`d!1 10 20 30
#guard ps (upsert dF eF) == some [("a", 1), ("b", 10), ("c", 20), ("d", 30)]

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
theorem app?_domP (r : FinRel K V) :
    (domP r).app? = some fun k => if k ∈ r.toList.map Prod.fst then [k] else [] := by
  simp only [domP, RelRep.app?, FibreIndex.get_build, FibreIndex.dedup_eq, FinRel.scanLookup_ofList]
  exact congrArg some (funext fun k => by simpa [List.map_map, Function.comp_def] using sel_eraseDups k _)

/-- One key's answer from its two fibres, as q's dict arithmetic gives it: `d`'s first row meets `e`'s first
    value (`z` when `e` has none) and `d`'s later rows stay; a key only `e` has keeps every row, each `z op v`. -/
def zipFib (op : V → V → V) (z : V) : List V × List V → List V
  | (a :: t, m) => op a (m.headD z) :: t
  | ([], m) => m.map (op z)

/-- q's `d op e` on dicts, `dom(d ∪ e) ⟨Λd, Λe⟩ zipFib ∋`: `z` stands for the side a key is missing from. -/
def zipD (op : V → V → V) (z : V) (r s : FinRel K V) : Option (RelRep K V) := do
  (domP (r.union s)).comp
    (← ((← (RelRep.pairs r).transpose).pair (← (RelRep.pairs s).transpose)).comp (.enum (zipFib op z)))

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- **`d op e`** on fibre lists: each key of `d ∪ e`, once, answered by `zipFib` of its two fibres. -/
theorem app?_zipD {op : V → V → V} {z : V} {r s : FinRel K V} {D : RelRep K V} (h : zipD op z r s = some D) :
    D.app? = some fun k =>
      if k ∈ (r.union s).toList.map Prod.fst then zipFib op z (r.scanLookup k, s.scanLookup k) else [] := by
  simp only [zipD, RelRep.transpose_of_app? (R := .pairs r) rfl, RelRep.transpose_of_app? (R := .pairs s) rfl,
    Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨X, hX, hD⟩ := Option.bind_eq_some_iff.1 h
  rw [RelRep.app?_comp hD (app?_domP _) (RelRep.app?_comp hX (RelRep.app?_pair rfl rfl) rfl)]
  exact congrArg some (funext fun k => by split <;> simp [RelRep.cross])

omit [DecidableEq W] [FibreIndex W] [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] [DecidableEq κ] [FibreIndex κ] in
/-- The Set reading: `D` relates `k` to `v` iff `k` is a key and `v` is in `zipFib` of its fibres. -/
theorem rel_zipD {op : V → V → V} {z : V} {r s : FinRel K V} {D : RelRep K V} (h : zipD op z r s = some D)
    (k : K) (v : V) : D.rel k v ↔
      k ∈ (r.union s).toList.map Prod.fst ∧ v ∈ zipFib op z (r.scanLookup k, s.scanLookup k) := by
  rw [← RelRep.mem_app? (app?_zipD h)]; split <;> simp_all

/-- q's long infinities `-0W`, `0W`: the units of `|` and `&` on every non-null long. -/
def negInf : Int := -9223372036854775807
def posInf : Int := 9223372036854775807

-- d+e: `a`b`c`d!1 12 23 30 ; d-e: 1 -8 -17 -30 ; d*e: 1 20 60 30 ; d|e: 1 10 20 30 ; d&e: 1 2 3 30
#guard ps (zipD (· + ·) 0 dF eF) == some [("a", 1), ("b", 12), ("c", 23), ("d", 30)]
#guard ps (zipD (· - ·) 0 dF eF) == some [("a", 1), ("b", -8), ("c", -17), ("d", -30)]
#guard ps (zipD (· * ·) 1 dF eF) == some [("a", 1), ("b", 20), ("c", 60), ("d", 30)]
#guard ps (zipD max negInf dF eF) == some [("a", 1), ("b", 10), ("c", 20), ("d", 30)]
#guard ps (zipD min posInf dF eF) == some [("a", 1), ("b", 2), ("c", 3), ("d", 30)]
-- Repeated keys. (`a`a`b!1 2 3)+`a`c!10 20: `a`a`b`c!11 2 3 20 ; (`a`c!10 20)+`a`a`b!1 2 3: `a`c`b!11 20 3 ;
-- d+`b`b!10 20: `a`b`c!1 12 3 ; (`a`b!1 2)+`c`c!10 20: `a`b`c`c!1 2 10 20 ; minus: 1 2 -10 -20
def aabF : FinRel Sym Int := ⟨#["a", "a", "b"], #[1, 2, 3], rfl⟩
def acF : FinRel Sym Int := ⟨#["a", "c"], #[10, 20], rfl⟩
def bbF : FinRel Sym Int := ⟨#["b", "b"], #[10, 20], rfl⟩
def abF : FinRel Sym Int := ⟨#["a", "b"], #[1, 2], rfl⟩
def ccF : FinRel Sym Int := ⟨#["c", "c"], #[10, 20], rfl⟩
def abaF : FinRel Sym Int := ⟨#["a", "b", "a"], #[1, 2, 3], rfl⟩
#guard ps (zipD (· + ·) 0 aabF acF) == some [("a", 11), ("a", 2), ("b", 3), ("c", 20)]
#guard ps (zipD (· + ·) 0 acF aabF) == some [("a", 11), ("c", 20), ("b", 3)]
#guard ps (zipD (· + ·) 0 dF bbF) == some [("a", 1), ("b", 12), ("c", 3)]
#guard ps (zipD (· + ·) 0 abF ccF) == some [("a", 1), ("b", 2), ("c", 10), ("c", 20)]
#guard ps (zipD (· - ·) 0 abF ccF) == some [("a", 1), ("b", 2), ("c", -10), ("c", -20)]
-- (`a`b`a!1 2 3)+`a`c!10 20: `a`b`a`c!11 2 3 20 — the same fibres, a:11 3, b:2, c:20; the pairs come grouped
-- by key, not in q's positions.
#guard ((zipD (· + ·) 0 abaF acF).bind RelRep.app?).map (["a", "b", "c"].map ·) == some [[11, 3], [2], [20]]

#print axioms app?_zipD
#print axioms rel_zipD

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

/-- `ks Λ((T k)° (T v))`: each key `ks` lists, with its group's fibre. -/
def grp (ks : RelRep κ κ) (k : R → κ) (v : R → V) (T : RelRep Nat R) : Option (RelRep κ (List V)) := do
  ks.comp (← (← xkey k v T).transpose)

/-- `k xgroup T = dom((T k)°) Λ((T k)° (T v))`: the keys in first appearance, as q's `group`. -/
def xgroup (k : R → κ) (v : R → V) (T : RelRep Nat R) : Option (RelRep κ (List V)) := do
  grp (domP (← fin? (← T.comp (RelRep.ofFn k)).conv)) k v T

/-- `select agg v by k from T = ran(T k) Λ((T k)° (T v)) agg`: q sorts the keys (`s#`). -/
def selby [Ord κ] [Std.TransOrd κ] [Std.LawfulEqOrd κ] [FibreIndex (List V)] (agg : List V → W) (k : R → κ) (v : R → V)
    (T : RelRep Nat R) : Option (RelRep κ W) := do
  (← grp (.pairs (← fin? (← T.comp (RelRep.ofFn k))).ran) k v T).comp (RelRep.ofFn agg)

omit [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] in
/-- **`select agg v by k`**: at each key `ks` lists, `agg` of the group's whole fibre `g c` — in row order
    and with its repeats, which `sum`/`count`/`avg` need and the Set reading of `Λ` drops. -/
theorem app?_selby [FibreIndex (List V)] {agg : List V → W} {k : R → κ} {v : R → V} {T : RelRep Nat R} {ks : RelRep κ κ}
    {e : κ → List κ} (he : ks.app? = some e) {X : RelRep κ V} {g : κ → List V} (hX : xkey k v T = some X)
    (hg : X.app? = some g) {G : RelRep κ (List V)} (hG : grp ks k v T = some G) {A : RelRep κ W}
    (hA : G.comp (RelRep.ofFn agg) = some A) : A.app? = some fun c => (e c).map fun c' => agg (g c') := by
  simp only [grp, hX, RelRep.transpose_of_app? hg, Option.bind_eq_bind, Option.bind_some] at hG
  rw [RelRep.app?_comp hA (RelRep.app?_comp hG he rfl) rfl]
  simp [List.flatMap_assoc, List.map_eq_flatMap]

/-- `ungroup G = G ∋`. -/
def ungroup (G : RelRep κ (List V)) : Option (RelRep κ V) := G.comp (.enum id)

-- `k xgroup t: (+(,`k)!,`a`b`c)!+(,`v)!,(1 3;,2;,4)
#guard ps (xgroup Prod.fst Prod.snd t) == some [("a", [1, 3]), ("b", [2]), ("c", [4])]
-- select sum v by k from t: (`s#+(,`k)!,`s#`a`b`c)!+(,`v)!,4 2 4
#guard ps (selby List.sum Prod.fst Prod.snd t) == some [("a", 4), ("b", 2), ("c", 4)]
-- ungroup `k xgroup t: +`k`v!(`a`a`b`c;1 3 2 4)
#guard ps (xgroup Prod.fst Prod.snd t >>= ungroup) == some [("a", 1), ("a", 3), ("b", 2), ("c", 4)]

def t2 : RelRep Nat (Sym × Int) := tab [("b", 1), ("a", 2), ("b", 3)]
-- `k xgroup t2: (+(,`k)!,`b`a)!+(,`v)!,(1 3;,2) — first appearance
#guard ps (xgroup Prod.fst Prod.snd t2) == some [("b", [1, 3]), ("a", [2])]
-- select sum v by k from t2: (`s#+(,`k)!,`s#`a`b)!+(,`v)!,2 4 ; count: 1 2 — sorted, repeats counted
#guard ps (selby List.sum Prod.fst Prod.snd t2) == some [("a", 2), ("b", 4)]
#guard ps (selby List.length Prod.fst Prod.snd t2) == some [("a", 1), ("b", 2)]

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

/-- `⟨T, T k KT⟩`: every match of the key, the relational join. -/
def joinAll (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat (R × W)) := do
  pure (T.pair (← (← T.comp (RelRep.ofFn k)).comp KT))

/-- `T ij KT = ⟨T, T k first(KT)⟩`: q's keyed lookup takes the first match. -/
def ij (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat (R × W)) := KT.first >>= joinAll k T

/-- `ej[k; T; U] = ⟨T, T k (k xkey U)⟩`: every match, as q's `ej`. -/
def ej (k : R → κ) (k' : S → κ) (w : S → W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × W)) := xkey k' w U >>= joinAll k T

/-- `T lj KT = ⟨T, T k look(KT)⟩`. -/
def lj (k : R → κ) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat (R × Option W)) :=
  look KT >>= joinAll k T

/-- `T pj KT`: `lj`, `0N` read as `0`, then `f` adds. -/
def pj [Zero W] (k : R → κ) (f : R → W → R) (T : RelRep Nat R) (KT : RelRep κ W) : Option (RelRep Nat R) :=
  lj k T KT >>= (·.comp (RelRep.ofFn fun p => f p.1 (p.2.getD 0)))

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
-- t ij kt3, kt3 keyed with `a twice: +`k`v`w!(`a`b`a;1 2 3;1 3 1) — the first match; the relational
-- join answers both.
#guard rows (ij Prod.fst t (.pairs kt3F)) == some [(("a", 1), 1), (("b", 2), 3), (("a", 3), 1)]
#guard rows (joinAll Prod.fst t (.pairs kt3F)) ==
  some [(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
-- t lj kt3: +`k`v`w!(`a`b`a`c;1 2 3 4;1 3 1 0N)
#guard rows (lj Prod.fst t (.pairs kt3F)) ==
  some [(("a", 1), some 1), (("b", 2), some 3), (("a", 3), some 1), (("c", 4), none)]
-- ej[`k;t;([] k:`a`a`b; w:1 2 3)]: +`k`v`w!(`a`a`b`a`a;1 1 2 3 3;1 2 3 1 2)
#guard rows (ej Prod.fst Prod.fst Prod.snd t (tab [("a", (1 : Int)), ("a", 2), ("b", 3)])) ==
  some [(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
-- t pj ([k:`a`b] v:100 200): +`k`v!(`a`b`a`c;101 202 103 4)
#guard rows (pj Prod.fst (fun r w => (r.1, r.2 + w)) t (.pairs (⟨#["a", "b"], #[100, 200], rfl⟩ : FinRel Sym Int))) ==
  some [("a", 101), ("b", 202), ("a", 103), ("c", 4)]
-- t pj ([k:`a`a`b] v:1 2 3): +`k`v!(`a`b`a`c;2 5 4 4) — the first match
#guard rows (pj Prod.fst (fun r w => (r.1, r.2 + w)) t (.pairs kt3F)) == some [("a", 2), ("b", 5), ("a", 4), ("c", 4)]
-- t uj ([] k:`b`e; u:5 6): +`k`v`u!(`a`b`a`c`b`e;1 2 3 4 0N 0N;0N 0N 0N 0N 5 6)
#guard rows (uj (fun r => (r.1, some r.2, (none : Option Int))) (fun r => (r.1, none, some r.2)) t
    (tab [("b", (5 : Int)), ("e", 6)])) ==
  some [("a", some 1, none), ("b", some 2, none), ("a", some 3, none), ("c", some 4, none),
    ("b", none, some 5), ("e", none, some 6)]
-- t upsert ([] k:enlist`z; v:enlist 9), and `t insert (`z;9): +`k`v!(`a`b`a`c`z;1 2 3 4 9)
#guard rows (uj id id t (tab [("z", 9)])) == some [("a", 1), ("b", 2), ("a", 3), ("c", 4), ("z", 9)]
-- kt uj / upsert ([k:`b`e] w:22 50): (+(,`k)!,`a`b`d`e)!+(,`w)!,10 22 40 50 — `b keeps its place
#guard ps (upsert ktF ⟨#["b", "e"], #[22, 50], rfl⟩) == some [("a", 10), ("b", 22), ("d", 40), ("e", 50)]
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
  pure (T.pair (← (domP (← fin? T)).comp (← RelRep.override D (RelRep.ofFn fun _ => z))))

/-- `aj = ⟨T, prevail(0) last p ⊕ ˆnone⟩`, the spec: it lists `C`, every right row of a left row's key. -/
def ajSpec (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    Option (RelRep Nat (R × Option W)) := do
  onRows T (← (← (← prevail 0 (← cand k tm k' tv T U)).last).comp (RelRep.ofFn fun x => some x.2.2)) none

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
    have hx : ¬ x.1 ≤ t := by simpa using h2
    rw [List.pairwise_cons] at hs
    simp only [List.filter_cons, decide_eq_true_eq, hx, ↓reduceIte, List.take_zero, List.filter_eq_nil_iff,
      decide_eq_true_eq]
    exact fun y hy hyt => hx (Int.le_trans (hs.1 y hy) hyt)
  | x :: r, hs, p + 1, h1, h2 => by
    rw [List.pairwise_cons] at hs
    have hx : x.1 ≤ t := by
      rcases p with _ | p
      · simpa using h1
      · obtain ⟨y, hy, hyt⟩ : ∃ y, r[p]? = some y ∧ y.1 ≤ t := by simpa [Option.any_eq_true] using h1
        exact Int.le_trans (hs.1 y (List.mem_of_getElem? hy)) hyt
    rw [List.filter_cons, if_pos (decide_eq_true hx), List.take_succ_cons,
      filter_eq_take r hs.2 p (by rcases p with _ | p <;> simp_all) (by simpa using h2)]

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
  match T, (do (← U.comp (RelRep.ofFn k')).conv.comp (← U.comp (RelRep.ofFn tv))) with
  | .pairs t, some (.pairs g) => onRows T (ajFast k tm t g) none
  | _, _ => ajSpec k tm k' tv T U

omit [DecidableEq R] [FibreIndex R] [DecidableEq S] [FibreIndex S] [DecidableEq X] [FibreIndex X] in
theorem comp_some {R : RelRep K V} {f : K → List V} (hR : R.app? = some f) (S : RelRep V W) :
    ∃ T, R.comp S = some T := by
  cases R <;> cases S <;> first | exact ⟨_, rfl⟩ | simp [RelRep.app?] at hR

omit [DecidableEq W] [FibreIndex W] in
theorem onRows_congr (T : RelRep Nat R) {D D' : RelRep Nat V} (h : D.app? = D'.app?) (z : V) :
    onRows T D z = onRows T D' z := by
  simp only [onRows, RelRep.override, h]

omit [DecidableEq X] [FibreIndex X] in
/-- **`aj` is `ajSpec`**: the binary search answers what `Λ(C ∩ ≥) est(≥) last` does. -/
theorem aj_eq (k : R → κ) (tm : R → Int) (k' : S → κ) (tv : S → Int × W) (T : RelRep Nat R) (U : RelRep Nat S) :
    aj k tm k' tv T U = ajSpec k tm k' tv T U := by
  unfold aj
  split
  · rename_i t g hG
    obtain ⟨A, hA, hAB⟩ := Option.bind_eq_some_iff.1 hG
    obtain ⟨B, hB, hG⟩ := Option.bind_eq_some_iff.1 hAB
    obtain ⟨fU, hU⟩ := RelRep.app?_of_comp hA
    obtain ⟨fAc, hAc⟩ := RelRep.app?_of_comp hG
    have hfB := RelRep.app?_comp hB hU rfl
    have hgG := RelRep.app?_comp hG hAc hfB
    simp only [RelRep.app?, Option.some.injEq] at hgG
    have hfT : (RelRep.pairs t).app? = some (FibreIndex.get (FibreIndex.build t)) := rfl
    obtain ⟨Tk, hTk⟩ := comp_some hfT (RelRep.ofFn k)
    obtain ⟨Ttm, hTtm⟩ := comp_some hfT (RelRep.ofFn tm)
    have hfTk := RelRep.app?_comp hTk hfT rfl
    obtain ⟨C, hC⟩ := comp_some hfTk A.conv
    have hfC := RelRep.app?_comp hC hfTk hAc
    obtain ⟨Y, hY⟩ := comp_some hfC B
    have hfY := RelRep.app?_comp hY hfC hfB
    have hfX := RelRep.app?_comp hTtm hfT rfl
    have hcand : cand k tm k' tv (.pairs t) U = some (Ttm.pair Y) := by
      simp only [cand, hTk, hA, hC, hTtm, hB, hY, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    have hfI := RelRep.app?_inter_left (.test fun _ (x : Int × (Int × W)) => decide (x.2.1 ≤ x.1 + 0))
      (RelRep.app?_pair hfX hfY)
    obtain ⟨P, hP⟩ : ∃ P, prevail 0 (Ttm.pair Y) = some P := by
      simp only [prevail, RelRep.est, RelRep.div]; rw [hfI]; exact ⟨_, rfl⟩
    have hfP := RelRep.app?_est hP hfI
    obtain ⟨Pf, hPf⟩ : ∃ Pf, P.app? = some Pf := ⟨_, hfP⟩
    have ePf := Option.some.inj (hPf.symm.trans hfP)
    have hL := RelRep.last_of_app? hPf
    obtain ⟨D, hD⟩ := comp_some (R := RelRep.enum fun i => (Pf i).getLast?.toList) rfl
      (RelRep.ofFn fun (x : Int × (Int × W)) => some x.2.2)
    have hfD := RelRep.app?_comp hD rfl rfl
    simp only [ajSpec, hcand, hP, hL, hD, Option.bind_eq_bind, Option.bind_some]
    refine onRows_congr _ ?_ none
    rw [hfD]
    simp only [ajFast, RelRep.app?, Option.some.injEq]
    funext i
    subst ePf
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
    · simp only [ajFib, hgG, List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil, RelRep.mem]
  · rfl

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
  let P ← (← prevail lo C).last
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

#print axioms app?_look
#print axioms app?_selby
#print axioms aj_eq

end LeetQ.Q
