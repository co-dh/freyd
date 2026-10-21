/-
  Each verb of `LeetQ.Rel.Verbs` on each container q allows it on, against `q/generic.q`: a `#guard` here
  and the line of the same expression there.  A dict reads back as its `(key, value)` pairs, a table as its
  rows, an atom as the fibre at the point `0` (`[]` is q's null).
-/
import LeetQ.Rel.Verbs
import LeetQ.Q.List

namespace LeetQ.Rel.Test

open Freyd.Alg.RelSet (RelRep)
open LeetQ.Rel LeetQ.Rel.Q
open LeetQ.Q.Agg (QF)

abbrev Sym := String

def kv {K V : Type} [DecidableEq K] [DecidableEq V] (C : Q K V) : List (K × V) := C.keyList.zip C.vals
def fl (R : RelRep Nat QF) : List Float := (R.app 0).map QF.f

def x : Q Nat Int := list [3, 1, 4, 1, 5]
def d : Q Sym Int := dict ["a", "b", "c", "d"] [3, 1, 3, 2]
def e : Q Sym Int := dict ["a", "b", "c"] [1, 2, 3]
def f : Q Sym Int := dict ["b", "c", "d"] [10, 20, 30]
def t : Q Nat (Sym × Int) := list [("a", 1), ("b", 2), ("a", 3), ("c", 4)]
def kt : Q Sym Int := dict ["a", "b", "d"] [10, 20, 40]
def ints (xs : List Int) : Q Nat Int := list xs
def syms (xs : List Sym) : Q Nat Sym := list xs

/-! ## Reindexing -/

#guard (reverse x).vals == [5, 1, 4, 1, 3]
#guard kv (reverse d) == [("d", 2), ("c", 3), ("b", 1), ("a", 3)]
#guard (reverse t).vals == [("c", 4), ("a", 3), ("b", 2), ("a", 1)]
#guard kv (reverse kt) == [("d", 40), ("b", 20), ("a", 10)]
#guard (first x).app 0 == [3] && (last x).app 0 == [5]
#guard (first d).app 0 == [3] && (last d).app 0 == [2]
#guard (first t).app 0 == [("a", 1)] && (last t).app 0 == [("c", 4)]
#guard (first kt).app 0 == [10] && (last kt).app 0 == [40]
#guard (first (ints [])).app 0 == []
#guard (take 2 x).vals == [3, 1] && (take (-2) x).vals == [1, 5] && (take 7 x).vals == [3, 1, 4, 1, 5, 3, 1]
#guard kv (take 2 d) == [("a", 3), ("b", 1)] && kv (take (-1) d) == [("d", 2)]
#guard (take 2 t).vals == [("a", 1), ("b", 2)]
#guard kv (take 2 kt) == [("a", 10), ("b", 20)]
#guard (drop 1 x).vals == [1, 4, 1, 5] && (drop (-1) x).vals == [3, 1, 4, 1]
#guard kv (drop 1 d) == [("b", 1), ("c", 3), ("d", 2)]
#guard (drop 1 t).vals == [("b", 2), ("a", 3), ("c", 4)]
#guard kv (drop 1 kt) == [("b", 20), ("d", 40)]
#guard (sublist 2 x).vals == [3, 1] && (sublist (-2) x).vals == [1, 5] && (sublist 10 x).vals == [3, 1, 4, 1, 5]
#guard (sublist2 1 2 x).vals == [1, 4]
#guard (rotate 2 x).vals == [4, 1, 5, 3, 1] && (rotate (-1) x).vals == [5, 3, 1, 4, 1]
#guard (rotate 1 t).vals == [("b", 2), ("a", 3), ("c", 4), ("a", 1)]
#guard (next x).valsN == [some 1, some 4, some 1, some 5, none]
#guard (prev x).valsN == [none, some 3, some 1, some 4, some 1]
#guard (xprev 2 x).valsN == [none, none, some 3, some 1, some 4]
#guard (til 5).vals == [0, 1, 2, 3, 4]
#guard (join x (ints [1, 2])).vals == [3, 1, 4, 1, 5, 1, 2]
#guard (join t (list [("z", 9)])).vals == [("a", 1), ("b", 2), ("a", 3), ("c", 4), ("z", 9)]
#guard (raze [ints [1, 2], ints [3], ints [4, 5, 6]]).vals == [1, 2, 3, 4, 5, 6]
#guard (cross (ints [1, 2]) (ints [3, 4, 5])).vals == [(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]
#guard (flip (ints [1, 2]) (ints [3, 4])).vals == [(1, 3), (2, 4)]

/-! ## Search -/

#guard (index x (list [2, 0])).vals == [4, 3] && (index x (list [7])).valsN == [none]
#guard (index d (syms ["b", "d"])).vals == [1, 2] && (index d (syms ["z"])).valsN == [none]
#guard (index t (list [1])).vals == [("b", 2)]
#guard (index kt (syms ["b"])).vals == [20] && (index kt (syms ["z"])).valsN == [none]
#guard (find x (ints [1, 5, 7])).vals == [1, 4, 5]
#guard (find d (ints [3, 1, 7])).valsN == [some "a", some "b", none]
#guard (find t (list [("a", 3), ("z", 0)])).vals == [2, 4]
#guard (find kt (ints [20])).vals == ["b"]
#guard (whereB (list [false, true, true, false, true])).vals == [1, 2, 4]
#guard (whereB (dict ["a", "b", "c"] [true, false, true])).vals == ["a", "c"]
#guard (whereN (list [2, 0, 1])).vals == [0, 0, 2]
#guard (distinct x).vals == [3, 1, 4, 5]
-- `distinct d` is a type error in q; `distinct` takes a list-shaped container
#guard (distinct (list [("a", 1), ("a", 1), ("b", 2)])).vals == [("a", 1), ("b", 2)]
#guard kv (group x) == [(3, [0]), (1, [1, 3]), (4, [2]), (5, [4])]
#guard kv (group d) == [(3, ["a", "c"]), (1, ["b"]), (2, ["d"])]
#guard (union (ints [1, 2, 3, 2]) (ints [2, 4, 1, 5])).vals == [1, 2, 3, 4, 5]
#guard (inter (ints [1, 2, 3, 2]) (ints [2, 3, 4])).vals == [2, 3, 2]
#guard (except (ints [1, 2, 3, 2]) (ints [2])).vals == [1, 3]
#guard (except t (list [("a", 1)])).vals == [("b", 2), ("a", 3), ("c", 4)]
#guard (in_ (ints [1, 2, 5]) (ints [2, 3, 5])).vals == [false, true, true]
#guard (within 2 5 (ints [3, 1, 7])).vals == [true, false, false]
#guard (bin (ints [1, 3, 5, 7]) (ints [0, 1, 4, 9])).vals == [-1, 0, 1, 3]
#guard (binr (ints [1, 3, 5, 7]) (ints [0, 1, 4, 9])).vals == [0, 0, 2, 4]
#guard (cut [0, 2, 4] (til 6)).vals == [[0, 1], [2, 3], [4, 5]]
#guard (cut [1, 3] (til 6)).vals == [[1, 2], [3, 4, 5]]

/-! ## Sort -/

#guard (rank x).vals == [2, 0, 3, 1, 4]
#guard (iasc x).vals == [1, 3, 0, 2, 4] && (idesc x).vals == [4, 2, 0, 1, 3]
#guard (asc x).vals == [1, 1, 3, 4, 5] && (desc x).vals == [5, 4, 3, 1, 1]
#guard (iasc d).vals == ["b", "d", "a", "c"] && (idesc d).vals == ["a", "c", "d", "b"]
#guard kv (asc d) == [("b", 1), ("d", 2), ("a", 3), ("c", 3)]
#guard kv (desc d) == [("a", 3), ("c", 3), ("d", 2), ("b", 1)]
#guard (xasc Prod.fst t).vals == [("a", 1), ("a", 3), ("b", 2), ("c", 4)]
#guard (xdesc Prod.fst t).vals == [("c", 4), ("b", 2), ("a", 1), ("a", 3)]

/-! ## Each, neighbours, nulls -/

#guard (differ (ints [1, 1, 2, 2, 2, 3, 1])).vals == [true, false, true, false, false, true, true]
#guard kv (differ (dict ["a", "b", "c"] [1, 1, 2])) == [("a", true), ("b", false), ("c", true)]
#guard (null (listN [some (1 : Int), none, some 3])).vals == [false, true, false]
#guard (fills (listN [none, some (1 : Int), none, none, some 3, none])).valsN == [none, some 1, some 1, some 1, some 3, some 3]
#guard (fills ⟨3, .rel (ix ["a", "b", "c"]), (listN [some (1 : Int), none, some 3]).ν⟩).vals == [1, 1, 3]
#guard kv (each (· * 10) d) == [("a", 30), ("b", 10), ("c", 30), ("d", 20)]
#guard (each2 LeetQ.Q.Agg.qdiv (ints [-7, 7, -7, 7]) (ints [2, 2, -2, -2])).vals == [-4, 3, 3, -4]

/-! ## Aggregates -/

#guard (count x).app 0 == [5] && (count d).app 0 == [4] && (count t).app 0 == [4] && (count kt).app 0 == [3]
#guard (sum x).app 0 == [14] && (sum d).app 0 == [9] && (sum kt).app 0 == [70]
#guard (prd x).app 0 == [60]
#guard (qmin x).app 0 == [1] && (qmax x).app 0 == [5] && (qmax d).app 0 == [3]
#guard (all (list [true, false, true])).app 0 == [false] && (any (list [true, false, true])).app 0 == [true]
#guard fl (avg (ints [1, 2, 3, 4])) == [2.5] && fl (avg d) == [2.25]
#guard fl (med (ints [1, 3, 2, 4])) == [2.5] && fl (med x) == [3] && fl (med d) == [2.5]
#guard fl (var (ints [1, 2, 3, 4])) == [1.25]
#guard fl (dev (ints [2, 4, 4, 4, 5, 5, 7, 9])) == [2]
#guard fl (wavg (ints [1, 3]) (ints [2, 6])) == [5]
#guard (wsum (ints [1, 2, 3]) (ints [4, 5, 6])).app 0 == [32]
#guard fl (cov (ints [1, 2, 3, 4]) (ints [2, 4, 6, 8])) == [2.5]
#guard (fl (cor (ints [1, 2, 3, 4]) (ints [2, 4, 6, 8]))).map (fun c => decide ((c - 1).abs < 1e-12)) == [true]
#guard (over1 (· - ·) (ints [1, 2, 3])).app 0 == [-4] && (over (· - ·) 10 (ints [1, 2, 3])).app 0 == [4]

/-! ## Running and moving -/

#guard (sums x).vals == [3, 4, 8, 9, 14] && kv (sums d) == [("a", 3), ("b", 4), ("c", 7), ("d", 9)]
#guard (prds x).vals == [3, 3, 12, 12, 60]
#guard (mins x).vals == [3, 1, 1, 1, 1] && (maxs x).vals == [3, 3, 4, 4, 5]
#guard kv (maxs d) == [("a", 3), ("b", 3), ("c", 3), ("d", 3)]
#guard (scan1 (· - ·) (ints [1, 2, 3])).vals == [1, -1, -4] && (scan (· - ·) 10 (ints [1, 2, 3])).vals == [9, 7, 4]
#guard (deltas x).vals == [3, -2, 3, -3, 4] && kv (deltas d) == [("a", 3), ("b", -2), ("c", 2), ("d", -1)]
#guard (ratios (ints [1, 2, 8, 4])).vals.map QF.f == [1, 2, 4, 0.5]
#guard (msum 2 x).vals == [3, 4, 5, 5, 6] && kv (msum 2 d) == [("a", 3), ("b", 4), ("c", 4), ("d", 5)]
#guard (mavg 2 x).vals.map QF.f == [3, 2, 2.5, 2.5, 3]
#guard (mmin 3 x).vals == [3, 1, 1, 1, 1] && (mmax 3 x).vals == [3, 3, 4, 4, 5]
#guard (mcount 3 x).vals == [1, 2, 3, 3, 3]
#guard (ema 0.5 (list ([1, 2, 3].map QF.ofInt))).vals.map QF.f == [1, 1.5, 2.25]

/-! ## Dicts and keyed tables -/

#guard (key d).vals == ["a", "b", "c", "d"] && (value d).vals == [3, 1, 3, 2]
-- `key x` is `` `long `` in q (a list's type); `key` on a list here is `til count`, no q counterpart
#guard (key kt).vals == ["a", "b", "d"] && (value kt).vals == [10, 20, 40]
#guard kv (takeK (syms ["a", "c"]) e) == [("a", 1), ("c", 3)]
#guard kv (dropK (syms ["a", "c"]) e) == [("b", 2)]
#guard kv (dropK (syms ["b"]) kt) == [("a", 10), ("d", 40)]
#guard kv (upsert e f) == [("a", 1), ("b", 10), ("c", 20), ("d", 30)]
#guard kv (upsert kt (dict ["b", "e"] [22, 50])) == [("a", 10), ("b", 22), ("d", 40), ("e", 50)]
#guard kv (zipD (· + ·) 0 e f) == [("a", 1), ("b", 12), ("c", 23), ("d", 30)]
#guard kv (zipD (· - ·) 0 e f) == [("a", 1), ("b", -8), ("c", -17), ("d", -30)]

/-! ## qSQL -/

#guard kv (xkey Prod.fst Prod.snd t) == [("a", 1), ("b", 2), ("a", 3), ("c", 4)]
#guard (selectW (·.2 > 1) t).vals == [("b", 2), ("a", 3), ("c", 4)]
#guard kv (selectW (· > 15) kt) == [("b", 20), ("d", 40)]
#guard (exec Prod.snd (·.1 == "a") t).vals == [1, 3]
#guard (update (·.1 == "a") (fun r => (r.1, r.2 * 10)) t).vals == [("a", 10), ("b", 2), ("a", 30), ("c", 4)]
#guard (deleteW (·.1 == "a") t).vals == [("b", 2), ("c", 4)]
#guard kv (xgroup Prod.fst Prod.snd t) == [("a", [1, 3]), ("b", [2]), ("c", [4])]
#guard kv (selby (fold 0 (· + ·)) Prod.fst Prod.snd t) == [("a", 4), ("b", 2), ("c", 4)]
#guard kv (selby len Prod.fst Prod.snd (list [("b", (1 : Int)), ("a", 2), ("b", 3)])) == [("a", 1), ("b", 2)]
#guard (ungroup (xgroup Prod.fst Prod.snd t)).vals == [("a", 1), ("a", 3), ("b", 2), ("c", 4)]

/-! ## Joins -/

#guard (ij Prod.fst t kt).vals == [(("a", 1), 10), (("b", 2), 20), (("a", 3), 10)]
#guard (lj Prod.fst t kt).vals == [(("a", 1), some 10), (("b", 2), some 20), (("a", 3), some 10), (("c", 4), none)]
#guard (ej Prod.fst Prod.fst Prod.snd t (list [("a", (1 : Int)), ("a", 2), ("b", 3)])).vals ==
  [(("a", 1), 1), (("a", 1), 2), (("b", 2), 3), (("a", 3), 1), (("a", 3), 2)]
#guard (pj Prod.fst (fun r w => (r.1, r.2 + w)) t (dict ["a", "b"] [100, 200])).vals ==
  [("a", 101), ("b", 202), ("a", 103), ("c", 4)]
#guard (uj id id t (list [("z", 9)])).vals == [("a", 1), ("b", 2), ("a", 3), ("c", 4), ("z", 9)]

def tr : Q Nat (Sym × Int) := list [("x", 2), ("x", 5), ("y", 4)]
def qr : Q Nat (Sym × Int × Int) := list [("x", 1, 10), ("x", 3, 20), ("x", 3, 21), ("y", 5, 30)]

#guard (aj Prod.fst Prod.snd Prod.fst (·.2.1) (·.2.2) tr qr).vals == [(("x", 2), some 10), (("x", 5), some 21), (("y", 4), none)]
#guard (wj1 (-2) 0 Prod.fst Prod.snd Prod.fst (·.2.1) (·.2.2) tr qr).vals == [(("x", 2), 10), (("x", 5), 41), (("y", 4), 0)]
#guard (wj (-2) 0 Prod.fst Prod.snd Prod.fst (·.2.1) (·.2.2) tr qr).vals == [(("x", 2), 10), (("x", 5), 21), (("y", 4), 0)]

/-! ## Bridges to `LeetQ.Q` -/

theorem reverse_list {A : Type} [DecidableEq A] (xs : List A) :
    (reverse (list xs)).vals = (LeetQ.Q.QL.reverse (LeetQ.Q.QL.ofList xs)).out := rfl
theorem rotate_list {A : Type} [DecidableEq A] (k : Int) (xs : List A) :
    (rotate k (list xs)).vals = (LeetQ.Q.QL.rotate k (LeetQ.Q.QL.ofList xs)).out := rfl
theorem next_list {A : Type} [DecidableEq A] (xs : List A) :
    (next (list xs)).vals = (LeetQ.Q.QL.next (LeetQ.Q.QL.ofList xs)).out := rfl
theorem prev_list {A : Type} [DecidableEq A] (xs : List A) :
    (prev (list xs)).vals = (LeetQ.Q.QL.prev (LeetQ.Q.QL.ofList xs)).out := rfl
theorem sublist2_list {A : Type} [DecidableEq A] (s l : Nat) (xs : List A) :
    (sublist2 s l (list xs)).vals = (LeetQ.Q.QL.sublist2 s l (LeetQ.Q.QL.ofList xs)).out := rfl

#print axioms reverse_list
#print axioms rotate_list
#print axioms next_list
#print axioms prev_list
#print axioms sublist2_list
#print axioms LeetQ.Rel.cv
#print axioms LeetQ.Rel.Q.sel
#print axioms LeetQ.Rel.Q.find
#print axioms LeetQ.Rel.Q.group
#print axioms LeetQ.Rel.Q.cut
#print axioms LeetQ.Rel.Q.rank
#print axioms LeetQ.Rel.Q.asc
#print axioms LeetQ.Rel.Q.med
#print axioms LeetQ.Rel.Q.cor
#print axioms LeetQ.Rel.Q.mavg
#print axioms LeetQ.Rel.Q.upsert
#print axioms LeetQ.Rel.Q.zipD
#print axioms LeetQ.Rel.Q.selby
#print axioms LeetQ.Rel.Q.ungroup
#print axioms LeetQ.Rel.Q.ij
#print axioms LeetQ.Rel.Q.ej
#print axioms LeetQ.Rel.Q.aj
#print axioms LeetQ.Rel.Q.wj
#print axioms LeetQ.Rel.Q.raze
#print axioms LeetQ.Rel.Q.whereN
#print axioms LeetQ.Rel.Q.binr
#print axioms LeetQ.Rel.Q.fills
#print axioms LeetQ.Rel.Q.avg
#print axioms LeetQ.Q.Agg.qfdiv
#print axioms LeetQ.Q.Agg.QF.of
#print axioms Float.ofInt
#print axioms Float.sqrt
#print axioms LeetQ.Rel.Q.mcount
#print axioms LeetQ.Rel.Q.msum

end LeetQ.Rel.Test
