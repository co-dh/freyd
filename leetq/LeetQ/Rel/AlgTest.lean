/-
  Guards of the relation algebra: every operator against its `toList` spec on small literal relations.
  Nothing imports this file; it is built so a guard that fails fails the build.
-/
import LeetQ.Rel.Alg

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel

/-! ## Checks against the `toList` specs, on small literal relations -/

section Checks

private abbrev L := QAtomicType.long
private abbrev LL := Rel .long .long

private def seteq {α : Type} [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains

-- R = {1↦10, 1↦20, 2↦10, 3↦30}, S = {1↦10, 2↦10, 2↦20, 4↦40}
private def R : LL := ⟨4, (Arr.mk (.bytes <| packLongs [1, 1, 2, 3]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [10, 20, 10, 30]) (by wf_lit))⟩
private def S : LL := ⟨4, (Arr.mk (.bytes <| packLongs [1, 2, 2, 4]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [10, 10, 20, 40]) (by wf_lit))⟩
-- T : b ⟶ c, {10↦7, 20↦8, 20↦9}
private def T : LL := ⟨3, (Arr.mk (.bytes <| packLongs [10, 20, 20]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [7, 8, 9]) (by wf_lit))⟩
-- a list with a repeat, (5 3 5 9), and the same as a relation from its positions
private def U4 : Vals L 4 := (Arr.mk (.bytes <| packLongs [0, 1, 2, 3]) (by wf_lit))
private def LsV : Arr L 4 := (Arr.mk (.bytes <| packLongs [5, 3, 5, 9]) (by wf_lit))
private def Ls : LL := ⟨4, U4, LsV⟩
private def Ua : Vals L 4 := (Arr.mk (.bytes <| packLongs [1, 2, 3, 4]) (by wf_lit))
private def Ub : Vals L 4 := (Arr.mk (.bytes <| packLongs [10, 20, 30, 40]) (by wf_lit))
private def Uc : Vals L 3 := (Arr.mk (.bytes <| packLongs [7, 8, 9]) (by wf_lit))

#guard (R ⊑ S) == false
#guard (R ∩ S ⊑ R) && (R ∩ S ⊑ S)
#guard seteq (R ∩ S).toList (R.toList.filter S.toList.contains)
#guard seteq (R \ S).toList (R.toList.filter fun p => !S.toList.contains p)
#guard (R \ R).n == 0
#guard seteq ((R ∩ S) ∪ (R \ S)).toList R.toList
#guard seteq (R ∪ S).toList (R.toList ++ S.toList) && (R ∪ S).n == 6
#guard (zero (A := L) (B := L)).n == 0
#guard seteq (top Ua Uc).toList (Ua.toList.flatMap fun x => Uc.toList.map (x, ·))
#guard (idU Ua).toList == Ua.toList.map fun x => (x, x)
#guard seteq (R°).toList (R.toList.map fun (x, y) => (y, x))
#guard seteq (Ls°).toList (Ls.toList.map fun (x, y) => (y, x))
#guard seteq (R ≫ T).toList
  (R.toList.flatMap fun (x, y) => T.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard seteq (Ls ≫ Ls).toList
  (Ls.toList.flatMap fun (x, y) => Ls.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard seteq (dom R).toList [(1, 1), (2, 2), (3, 3)] && (dom R).n == 3
#guard seteq (ran S).toList [(10, 10), (20, 20), (40, 40)] && (ran S).n == 3

-- `R \ S` over `Ub × Ub`: `y (R\S) z ↔ ∀ x, x R y → x S z`
private def leftSpec (R S : LL) (Ub Uc : List Int64) : List (Int64 × Int64) :=
  Ub.flatMap fun y => (Uc.filter fun z => R.toList.all fun (x, y') => y' != y || S.toList.contains (x, z)).map (y, ·)
#guard seteq (leftDiv R S Ub Ub).toList (leftSpec R S Ub.toList Ub.toList)
#guard seteq (leftDiv R R Ub Ub).toList (leftSpec R R Ub.toList Ub.toList)
-- `R / S` (`R : a ⟶ c`, `S : b ⟶ c`): `x (R/S) y ↔ ∀ z, y S z → x R z`
#guard seteq (rightDiv R S Ua Ua).toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => S.toList.all fun (y', z) => y' != y || R.toList.contains (x, z)).map (x, ·))
-- `R /ₛ S`: equal fibres
private def fib (R : LL) (x : Int64) : List Int64 := R.toList.filterMap fun (x', z) => if x == x' then some z else none
#guard seteq (symDiv R S Ua Ua).toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib S y)).map (x, ·))
#guard seteq (symDiv R R Ua Ua).toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib R y)).map (x, ·))

/-- The facts of `Λ(R)`: (1) `Λ(R) ≫ ∋(R) = R`; (2) one row per distinct key of `R`; (3) each cell is the
    key's values, each once; (4) `Λ(R) ≫ Λ(R)°` relates two keys iff they have one set of values. -/
private def lamOk {A B : Obj} [BEq A.El] [BEq B.El] (R : Rel A B) : Bool :=
  let Lm := Λ(R)
  let r := R.toList; let l : List (A.El × List B.El) := Lm.toList
  let fibr (x : A.El) := r.filterMap fun (x', z) => if x == x' then some z else none
  let same := (Lm ≫ Lm°).toList
  (Lm ≫ ∋(R) == R) &&
  (l.map (·.1)).eraseDups.length == l.length && seteq (l.map (·.1)) (r.map (·.1)) &&
  l.all (fun (x, c) => seteq c (fibr x) && c.eraseDups.length == c.length) &&
  l.all (fun (x, _) => l.all fun (y, _) => same.contains (x, y) == seteq (fibr x) (fibr y))

/-- Arrays across two relations: `Λ(R₁) ≫ Λ(R₂)°` relates a key of `R₁` to a key of `R₂` iff their sets of
    values are one, and `ran (Λ(R₁) ∪ Λ(R₂))` holds each distinct set once. -/
private def crossOk {A B : Obj} [BEq A.El] [BEq B.El] (R₁ R₂ : Rel A B) : Bool :=
  let f (R : Rel A B) (x : A.El) : List B.El := R.toList.filterMap fun (x', z) => if x == x' then some z else none
  let k₁ := (R₁.toList.map (·.1)).eraseDups; let k₂ := (R₂.toList.map (·.1)).eraseDups
  let rel := (Λ(R₁) ≫ Λ(R₂)°).toList
  let sets := k₁.map (f R₁) ++ k₂.map (f R₂)
  let distinct := sets.foldl (fun acc s => if acc.any (seteq s) then acc else acc ++ [s]) ([] : List (List B.El))
  k₁.all (fun x => k₂.all fun y => rel.contains (x, y) == seteq (f R₁ x) (f R₂ y)) &&
  (ran (Λ(R₁) ∪ Λ(R₂))).n.toNat == distinct.length

-- `Λ(R)`, `∋(R)`: R with a repeated pair, R ∪ S, a key with a repeat and its values out of order (D, below),
-- a foR column, an empty relation, the family `G`, `G ≫ R`
#guard lamOk R && lamOk S && lamOk (R ∪ R) && lamOk (R ∪ S) && lamOk T && lamOk Ls && lamOk (Ls°)
#guard lamOk (zero (A := L) (B := L)) && lamOk (R ≫ T) && lamOk (R°)
#guard (Λ(R).toList : List (Int64 × List Int64)) == [(1, [10, 20]), (2, [10]), (3, [30])] && ∋(R).n == 4
-- arrays of pairs: `B = X×X`
#guard lamOk (pair R S) && lamOk (pair S R) && crossOk (pair R S) (pair S R) && crossOk (pair R R) (pair R S)
private def LfV : Arr L 4 := Arr.mk (.foR (Coc.encode 8 (packLongs [5, 3, 5, 9])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9])).2) (foRLongs_wf [5, 3, 5, 9] (by simp))
private def Lf : LL := ⟨4, U4, LfV⟩
#guard lamOk Lf && lamOk (Lf°) && Λ(Lf°).n == 3
#guard Λ(R ∪ R).n == 3 && ∋(R ∪ R).n == 4
#guard Λ(zero (A := L) (B := L)).n == 0 && ∋(zero (A := L) (B := L)).n == 0
-- `anti`: the positions of `x` not in `y`
#guard anti (Code.ofLongs (packLongs [3, 1, 4, 1])) (Code.ofLongs (packLongs [1, 5])) == packLongs [0, 2]
-- `R ≫ corNeg(C)` at a `C` that is no coreflexive: `1` is a key of `C` and no value, so the row stays
private def Ra : LL := ⟨1, (Arr.mk (.bytes <| packLongs [0]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [1]) (by wf_lit))⟩
private def Ca : LL := ⟨1, (Arr.mk (.bytes <| packLongs [1]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [2]) (by wf_lit))⟩
#guard (antiJoin Ra Ca).toList == [(0, 1)]
-- `E(R)` of the family `G = {X₁ = {1, 2}, X₂ = {3}}`: `Λ(G ≫ R)`
private def G : LL := ⟨3, (Arr.mk (.bytes <| packLongs [1, 1, 2]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [1, 2, 3]) (by wf_lit))⟩
#guard lamOk G && lamOk (G ≫ R) && seteq (Λ(G ≫ R) ≫ ∋(G ≫ R)).toList
  (G.toList.flatMap fun (s, x) => R.toList.filterMap fun (x', y) => if x == x' then some (s, y) else none)
-- arrays across two relations: `[10 20]` and `[10]` are cells of both, `[30]` and `[40]` of one
#guard seteq (Λ(R) ≫ Λ(S)°).toList [(1, 2), (2, 1)] && (ran (Λ(R) ∪ Λ(S))).n == 4
#guard crossOk R S && crossOk S R && crossOk R R && crossOk Lf Ls && crossOk (zero (A := L) (B := L)) R
-- an array column built by hand: `[1 2] [2 1] [1 1] [1 2]`, equal as arrays only where equal position by
-- position, so rows 0 and 3 alone; `∋` one row per element, a repeat twice
private def Xs : Vals (.arr L) 4 := ⟨8, col [0, 2, 4, 6], col [2, 4, 6, 8], col [1, 2, 2, 1, 1, 1, 1, 2]⟩
private def K : Rel L (.arr L) := ⟨4, U4, Xs⟩
#guard (K.toList.map (·.2) : List (List Int64)) == [[1, 2], [2, 1], [1, 1], [1, 2]]
#guard seteq (K ≫ K°).toList [(0, 0), (0, 3), (3, 0), (3, 3), (1, 1), (2, 2)] && (ran K).n == 3
#guard ((mem Xs).toList : List (List Int64 × Int64)) ==
  [([1, 2], 1), ([1, 2], 2), ([2, 1], 2), ([2, 1], 1), ([1, 1], 1), ([1, 1], 1), ([1, 2], 1), ([1, 2], 2)]
-- slices past the payload read clamped: `[-1, 1)` is `[1]`, `[3, 9)` is `[1 2]`, `[5, 2)` is empty
private def Xc : Vals (.arr L) 3 := ⟨4, col [-1, 2, 5], col [1, 9, 2], col [1, 5, 1, 2]⟩
#guard ((idU Xc).toList.map (·.1) : List (List Int64)) == [[1], [1, 2], []]
#guard ((mem Xc).toList : List (List Int64 × Int64)) == [([1], 1), ([1, 2], 1), ([1, 2], 2)]
#guard (idU Xc ≫ mem Xc).n == 3 && (ran (idU Xc)).n == 3

#guard seteq (pair R S).toList
  (R.toList.flatMap fun (x, y) => S.toList.filterMap fun (x', z) => if x == x' then some (x, y, z) else none)
#guard seteq (outl (pair R S)).toList (R.toList.filter fun (x, _) => S.toList.any (·.1 == x))
#guard seteq (outr (pair R S)).toList (S.toList.filter fun (x, _) => R.toList.any (·.1 == x))
#guard seteq (prod R T).toList
  (R.toList.flatMap fun (x, x') => T.toList.map fun (y, y') => ((x, y), (x', y')))

-- `est(Q)` and `thin(Q)`: the order `Q` a relation on `10 15 20 30 40`, `≤` and `<` alike, `≥` and `>` the
-- greatest
private def ordOn (p : Int64 → Int64 → Bool) : LL :=
  let vs : List Int64 := [10, 15, 20, 30, 40]
  ofPairs (vs.flatMap fun a => (vs.filter (p a)).map (a, ·))
private def LE := ordOn (· ≤ ·)
private def LT := ordOn (· < ·)
/-- `thin`'s spec: the rows `(a, b)` of `G` with no `(a, c)` of `G` where `c Q b` and not `b Q c`. -/
private def thinSpec {A B : Obj} [BEq A.El] [BEq B.El] (Q : Rel B B) (G : Rel A B) : List (A.El × B.El) :=
  let q := Q.toList; let g := G.toList
  g.filter fun (a, b) => g.all fun (a', c) => a' != a || !(q.contains (c, b) && !q.contains (b, c))
/-- `est`'s spec: the rows `(a, b)` of `G` with `b Q c` for every other `(a, c)` of `G`. -/
private def estSpec {A B : Obj} [BEq A.El] [BEq B.El] (Q : Rel B B) (G : Rel A B) : List (A.El × B.El) :=
  let q := Q.toList; let g := G.toList
  g.filter fun (a, b) => g.all fun (a', c) => a' != a || c == b || q.contains (b, c)
#guard seteq (est LE R).toList [(1, 10), (2, 10), (3, 30)] && est LT R == est LE R && thin LT R == est LE R
#guard seteq (est LE° R).toList [(1, 20), (2, 10), (3, 30)] && est LT° R == est LE° R && thin LE° R == est LE° R
#guard seteq (est LE S).toList (estSpec LE S) && seteq (est LT° S).toList (estSpec LT° S) &&
  seteq (thin LE S).toList (thinSpec LE S) && seteq (thin LT° S).toList (thinSpec LT° S)
-- ties: the preorder by tens, `10` and `15` tied; `(2, 20)` twice, kept twice
private def Rt : LL := ofPairs [(1, 10), (1, 15), (1, 20), (2, 20), (2, 20)]
private def tens := ordOn fun a b => a / 10 ≤ b / 10
#guard seteq (est tens Rt).toList [(1, 10), (1, 15), (2, 20)] && (est tens Rt).n == 4 &&
  seteq (est tens Rt).toList (estSpec tens Rt) && seteq (thin tens Rt).toList (thinSpec tens Rt) && thin tens Rt == est tens Rt
-- empty: no rows; no order: `thin` drops nothing, `est` keeps the one-value sets alone
#guard (est LE (zero (A := L) (B := L))).n == 0 && (thin LE (zero (A := L) (B := L))).n == 0
#guard thin (zero (A := L) (B := L)) R == R && seteq (est (zero (A := L) (B := L)) R).toList [(2, 10), (3, 30)]
-- `B = X×X`, the Pareto orders on pairs: strict `<×<` thins nothing of {(10,10) (20,10)} {(10,10) (10,20)} and
-- has no least; `≤×≤`, a partial order, keeps the minimal `(10,10)` of each, which is least too
#guard thin (prod LT LT) (pair R S) == pair R S && (est (prod LT LT) (pair R S)).n == 0
#guard seteq (est (prod LE LE) (pair R S)).toList [(1, 10, 10), (2, 10, 10)] && est (prod LE LE) (pair R S) == thin (prod LE LE) (pair R S)
-- where `≤×≤` is partial they differ: `{(10,20) (20,10) (20,20)}` has two minimal values and no least one
private def Gp : Rel L (.prod L L) := ⟨5, col [1, 1, 1, 2, 2], (col [10, 20, 20, 10, 20], col [20, 10, 20, 10, 20])⟩
#guard seteq (thin (prod LE LE) Gp).toList [(1, 10, 20), (1, 20, 10), (2, 10, 10)] &&
  seteq (thin (prod LE LE) Gp).toList (thinSpec (prod LE LE) Gp)
#guard seteq (est (prod LE LE) Gp).toList [(2, 10, 10)] && seteq (est (prod LE LE) Gp).toList (estSpec (prod LE LE) Gp)

-- sums, `LS = L + L`: `inl`, `inr`, `[R, S]`, `R + S` against their pairs
private abbrev LS : Obj := .sum L L
private def J : Rel LS L := junc R S
private def J' : Rel LS L := junc S R
private def Ps : Rel LS LS := sum R T
#guard ((inl (B := L) Ua).toList : List (Int64 × (Int64 ⊕ Int64))) == Ua.toList.map fun x => (x, .inl x)
#guard ((inr (A := L) Ub).toList : List (Int64 × (Int64 ⊕ Int64))) == Ub.toList.map fun x => (x, .inr x)
#guard (J.toList : List ((Int64 ⊕ Int64) × Int64)) ==
  R.toList.map (fun (x, y) => (.inl x, y)) ++ S.toList.map fun (x, y) => (.inr x, y)
#guard (Ps.toList : List ((Int64 ⊕ Int64) × (Int64 ⊕ Int64))) ==
  R.toList.map (fun (x, y) => (.inl x, .inl y)) ++ T.toList.map fun (x, y) => (.inr x, .inr y)
-- `R + T = [R inl, T inr]`, the term's values on other payloads than `R + T`'s
#guard Ps == junc (R ≫ inl (B := L) (ran R).val) (T ≫ inr (A := L) (ran T).val)
-- `inl ≫ [R, S] = R` on the universe of `inl`, `inr ≫ [R, S] = S`; `inl° inl ∪ inr° inr = 𝟙` on `A + B`
#guard inl (B := L) Ua ≫ J == idU Ua ≫ R && inr (A := L) Ua ≫ J == idU Ua ≫ S
#guard ((inl (B := L) Ua)° ≫ inl Ua) ∪ ((inr (A := L) Ub)° ≫ inr Ub) == idU (sumVals Ua Ub (by fits_lit))
-- `∩ ∪ \ ≫ dom` with a sum key; `J2` holds `J`'s rows over other payloads (razed), so equal by value
private def J2 : Rel LS L := junc R (zero (A := L) (B := L)) ∪ junc (zero (A := L) (B := L)) S
#guard J2 == J && seteq J2.toList J.toList && (J2 ∩ J).n == J2.n && (J2 \ J).n == 0
#guard seteq (J ∩ J').toList (J.toList.filter J'.toList.contains) &&
  seteq (J \ J').toList (J.toList.filter fun p => !J'.toList.contains p)
#guard seteq (J ∪ J').toList (J.toList ++ J'.toList) && (J ∪ J').n.toNat == (J.toList ++ J'.toList).eraseDups.length
#guard (dom J).n.toNat == (J.toList.map (·.1)).eraseDups.length && seteq (dom J).toList (J.toList.map fun (x, _) => (x, x))
#guard seteq (Ps ≫ Ps°).toList
  (Ps.toList.flatMap fun (x, y) => Ps.toList.filterMap fun (x', y') => if y == y' then some (x, x') else none)
#guard seteq (J° ≫ J').toList
  (J.toList.flatMap fun (x, y) => J'.toList.filterMap fun (x', z) => if x == x' then some (y, z) else none)
-- `Λ`, `∋`, `pair`, `est`, `thin` with sums as keys and values; `Λ(P)`'s cells are arrays of sums
#guard lamOk J && lamOk Ps && lamOk (Ps°) && lamOk J2 && crossOk J J2 && crossOk J J'
#guard seteq (pair J J').toList
  (J.toList.flatMap fun (x, y) => J'.toList.filterMap fun (x', z) => if x == x' then some (x, y, z) else none)
#guard seteq (est (sum LE LE) Ps).toList (estSpec (sum LE LE) Ps) && seteq (thin (sum LT LT) Ps).toList (thinSpec (sum LT LT) Ps)
-- a sum of a product and an array, as key
private def M : Rel (.sum (.prod L L) (.arr L)) LS := sum (pair R S)° K°
#guard lamOk M && lamOk (M°) && crossOk M (M ∪ M) && M ∩ (M ∪ M) == M &&
  (dom M).n.toNat == (M.toList.map (·.1)).eraseDups.length && (dom M).n == 6
-- a sum column by hand: tags `0110`, positions `-5 7 0 9` into `[1 2]` and `[10 20 30]`, read clamped into
-- each side, `inl 1, inr 30, inr 10, inl 2`; `Xi` the same values at in-range positions of other payloads
private def tg4 : Arr .boolean 4 := Arr.mk (.bits (ByteArray.mk #[0b0110])) (by wf_lit)
private def Xo : Vals LS 4 := ⟨2, 3, tg4, col [-5, 7, 0, 9], col [1, 2], col [10, 20, 30]⟩
private def Xi : Vals LS 4 := ⟨3, 2, tg4, col [2, 1, 0, 1], col [7, 2, 1], col [10, 30]⟩
#guard ((idU Xo).toList.map (·.1) : List (Int64 ⊕ Int64)) == [.inl 1, .inr 30, .inr 10, .inl 2]
#guard idU Xo == idU Xi && (idU Xo ∪ idU Xi).n == 4 && (idU Xo ≫ idU Xi).n == 4 && (ran (top Xo Xi)).n == 4
#guard ((idU (Obj.raze LS #[⟨_, Xo⟩, ⟨_, Xi⟩] (by fits_lit))).toList.map (·.1) : List (Int64 ⊕ Int64)) ==
  [.inl 1, .inr 30, .inr 10, .inl 2, .inl 1, .inr 30, .inr 10, .inl 2]
-- arrays of sums by hand, over `Xo` and over `Xi`: equal arrays by value across the two payloads
private def Xa : Vals (.arr LS) 3 := ⟨4, col [0, 2, 2], col [2, 4, 3], Xo⟩
private def Xb : Vals (.arr LS) 3 := ⟨4, col [2, 0, 2], col [4, 2, 3], Xi⟩
#guard ((idU Xa).toList.map (·.1) : List (List (Int64 ⊕ Int64))) == [[.inl 1, .inr 30], [.inr 10, .inl 2], [.inr 10]]
#guard idU Xa == idU Xb && (idU Xa ≫ idU Xb).n == 3 && seteq (mem Xa).toList (mem Xb).toList
-- an empty side: `inl` has no right values, `[R, 𝟘]` none either
#guard seteq (inl (B := L) Ua ∪ inr (A := L) Ub).toList ((inl (B := L) Ua).toList ++ (inr (A := L) Ub).toList)
#guard (dom (junc R (zero (A := L) (B := L)))).n == 3 && lamOk (junc R (zero (A := L) (B := L)))
-- empty left, empty right, both: `inl inr [R, S] R + S`, then `° ≫ ∩ ∪` on them, against their pairs
private def Z : LL := zero
private def E0 : Vals L 0 := Vals.empty L
#guard (inl (B := L) E0).n == 0 && (inr (A := L) E0).n == 0 && (junc Z Z).n == 0 && (sum Z Z).n == 0
#guard (junc R Z).toList == R.toList.map (fun (x, y) => (.inl x, y)) &&
  (junc Z S).toList == S.toList.map (fun (x, y) => (.inr x, y))
#guard (sum R Z).toList == R.toList.map (fun (x, y) => (.inl x, .inl y)) &&
  (sum Z T).toList == T.toList.map (fun (x, y) => (.inr x, .inr y))
#guard (sum R Z)°.toList == R°.toList.map (fun (x, y) => (.inl x, .inl y)) &&
  (sum Z T)°.toList == T°.toList.map (fun (x, y) => (.inr x, .inr y)) && ((sum Z Z)°).n == 0
#guard sum R Z ≫ junc R S == junc (R ≫ R) Z && sum Z T ≫ sum Z T == sum Z (T ≫ T) && (sum Z Z ≫ junc R S).n == 0
#guard junc R Z ∩ junc R S == junc R Z && junc Z S ∩ junc R Z == junc Z Z &&
  junc R Z ∪ junc Z S == junc R S && junc Z Z ∪ junc Z Z == junc Z Z
-- a sum column by hand with a row tagged to a side of no values: `Xel`'s `inl` row, `Xer`'s `inr` row. Each
-- reads its own side's null, as a gather past a side reads it, and `∪` (razed), `∩` (coded) read it so too
private def tg2 : Arr .boolean 2 := Arr.mk (.bits (ByteArray.mk #[0b10])) (by wf_lit)
private def Xel : Vals LS 2 := ⟨0, 1, tg2, col [0, 0], Vals.empty L, col [20]⟩
private def Xer : Vals LS 2 := ⟨1, 0, tg2, col [0, 3], col [7], Vals.empty L⟩
private def Yn : Vals LS 2 := ⟨2, 0, tags #[(2, false)] 2, col [0, 1], col [7, Int64.minValue], Vals.empty L⟩
#guard ((idU Xel).toList.map (·.1) : List (Int64 ⊕ Int64)) == [.inl Int64.minValue, .inr 20] &&
  ((idU Xer).toList.map (·.1) : List (Int64 ⊕ Int64)) == [.inl 7, .inr Int64.minValue]
#guard ((idU (Obj.raze LS #[⟨_, Xel⟩, ⟨_, Xer⟩] (by fits_lit))).toList.map (·.1) : List (Int64 ⊕ Int64)) ==
  [.inl Int64.minValue, .inr 20, .inl 7, .inr Int64.minValue]
#guard idU Xel == idU (Vals.compact LS Xel) && idU Xer == idU (Vals.compact LS Xer) &&
  ((idU Yn ∩ idU Xel).toList.map (·.1) : List (Int64 ⊕ Int64)) == [.inl Int64.minValue]
-- `α ≜ [nil, cons] : 1 + L × arr L ⟶ arr L`, the one point `0` standing for `1`
private def nilR : Rel L (.arr L) := ⟨1, col [0], ⟨0, col [0], col [0], Vals.empty .long⟩⟩
private def XP : Vals (.prod L (.arr L)) 2 := (col [5, 6], ⟨2, col [0, 2], col [2, 2], col [1, 2]⟩)
#guard seteq ((junc nilR (cons (idU XP))).toList : List ((Int64 ⊕ (Int64 × List Int64)) × List Int64))
  [(.inl 0, []), (.inr (5, [1, 2]), [5, 1, 2]), (.inr (6, []), [6])]

-- `uncons`, `fold`, `map` on arrays, against the List-level fold of cons-lists
private def arrs {n : USize} (X : Vals (.arr L) n) : List (List Int64) := (idU X).toList.map (·.1)
private def unconsSpec (xss : List (List Int64)) : List (List Int64 × Int64 × List Int64) :=
  xss.filterMap fun | [] => none | y :: ys => some (y :: ys, y, ys)
/-- `⦇e, S⦈` of one list, `S` read as its pairs. -/
private def foldSpec (e : List Int64) (S : List ((Int64 × Int64) × Int64)) (xs : List Int64) : List Int64 :=
  xs.foldr (fun x acc => acc.flatMap fun v => S.filterMap fun ((x', v'), w) => if x' == x && v' == v then some w else none) e
private def foldOk {n m : USize} (e : Arr L m) (S : Rel (.prod L L) L) (X : Vals (.arr L) n) : Bool :=
  seteq ((fold e S X).toList : List (List Int64 × Int64))
    ((arrs X).flatMap fun xs => (foldSpec e.toList S.toList xs).map (xs, ·))
/-- `F(R)` of one list: every choice of an image at each position. -/
private def mapSpec (R : List (Int64 × Int64)) (xs : List Int64) : List (List Int64) :=
  xs.foldr (fun x acc => (R.filterMap fun (x', y) => if x' == x then some y else none).flatMap fun y => acc.map (y :: ·)) [[]]
private def mapOk {n : USize} (R : LL) (X : Vals (.arr L) n) : Bool :=
  seteq ((map R X).toList : List (List Int64 × List Int64)) ((arrs X).flatMap fun xs => (mapSpec R.toList xs).map (xs, ·))
/-- The table of `f` on `xs × vs`, as a relation `(x, v) ⟶ f x v`. -/
private def tab (xs vs : List Int64) (f : Int64 → Int64 → Int64) : Rel (.prod L L) L :=
  let ps := xs.flatMap fun x => vs.map fun v => (x, v, f x v)
  ⟨ps.length.toUSize, (List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2.1))),
    List.length_map _ ▸ col (ps.map (·.2.2))⟩
private def upto (k : Nat) : List Int64 := (List.range (k + 1)).map Int64.ofNat
-- long arrays over one payload of 33 digits: rows of 20, 0 and 13, and `[-3, 2)` read clamped as `[0, 2)`
private def ds : List Int64 := (List.range 33).map fun i => Int64.ofNat (i * 7 % 5)
private def Xl : Vals (.arr L) 4 := ⟨_, col [0, 5, 20, -3], col [20, 5, 33, 2], col ds⟩
private def zero1 : Vals L 1 := col [0]
private def sumT := tab (upto 4) (upto 80) (· + ·)
private def maxT := tab (upto 4) (upto 4) max
#guard arrs Xl == [ds.take 20, [], ds.drop 20, ds.take 2]
#guard ((uncons Xl).toList : List (List Int64 × Int64 × List Int64)) == unconsSpec (arrs Xl)
#guard ((uncons Xc).toList : List (List Int64 × Int64 × List Int64)) == unconsSpec (arrs Xc) && (uncons Xc).n == 2
#guard ((uncons Xs).toList : List (List Int64 × Int64 × List Int64)) == unconsSpec (arrs Xs)
#guard (uncons (Vals.empty (.arr L))).n == 0
-- the sum and the max of each array, `[]` to `0`
#guard foldOk zero1 sumT Xl && ((fold zero1 sumT Xl).toList.map (·.2)).length == 4 &&
  seteq (fold zero1 sumT Xl).toList ((arrs Xl).map fun xs => (xs, xs.foldl (· + ·) 0))
#guard foldOk zero1 maxT Xl && seteq (fold zero1 maxT Xl).toList ((arrs Xl).map fun xs => (xs, xs.foldl max 0))
#guard foldOk zero1 sumT Xs && foldOk zero1 sumT Xc && (fold zero1 sumT (Vals.empty (.arr L))).n == 0
-- `S` not a function: `(x, v)` to `v` and to `v + x`, every subset sum; two start values
#guard foldOk (col [0, 100]) (tab (upto 4) (upto 110) (· + ·) ∪ tab (upto 4) (upto 110) fun _ v => v) Xs
#guard foldOk zero1 (tab (upto 4) (upto 80) (· + ·) ∪ tab (upto 4) (upto 80) fun _ v => v) Xc
-- `foldRows`, a seed per row: every row of `Xs` given the seeds `0, 100` is `fold` from `0, 100`; rows 0 and 3,
-- both `[1 2]`, started from `0` and from `100` end apart
private def subsums := tab (upto 4) (upto 110) (· + ·) ∪ tab (upto 4) (upto 110) fun _ v => v
#guard seteq ((num (idU Xs) 0)° ≫ foldRows (num (idU Xs) 0)
    (ofPairs [(0, 0), (0, 100), (1, 0), (1, 100), (2, 0), (2, 100), (3, 0), (3, 100)]) (demandStep fun _ => subsums)).toList
  (fold (col [0, 100]) subsums Xs).toList
#guard seteq (foldRows (num (idU Xs) 0) (ofPairs [(0, 0), (1, 0), (2, 0), (3, 100)])
    (demandStep fun _ => tab (upto 4) (upto 110) (· + ·))).toList
  [(0, 3), (1, 3), (2, 2), (3, 103)]
-- `S` partial: no `2` in its domain, so an array holding a `2` has no result
#guard foldOk zero1 (tab [0, 1, 3, 4] (upto 80) (· + ·)) Xl && foldOk zero1 (tab [0, 1, 3, 4] (upto 80) (· + ·)) Xs
#guard ((fold zero1 (tab [0, 1, 3, 4] (upto 80) (· + ·)) Xs).toList : List (List Int64 × Int64)) == [([1, 1], 2)]
-- `uncons` then `fold`: on a non-empty array the fold is `S` of its head and the fold of its rest
#guard let U := uncons Xl
  pair (outl U) (outr U ≫ fold zero1 sumT U.val.2) ≫ sumT == dom U ≫ fold zero1 sumT Xl
-- `F(R)` with a map (negate, a table) and with a relation of two values at `1` and `3` and none at `9`
private def neg : LL := ofPairs ((upto 4).map fun x => (x, -x))
#guard mapOk neg Xl && seteq (map neg Xl).toList ((arrs Xl).map fun xs => (xs, xs.map (- ·)))
private def two : LL := ofPairs [(1, 10), (1, 11), (2, 20), (3, 30), (3, 31)]
#guard mapOk two Xs && mapOk two Xc && mapOk two (Vals.empty (.arr L))
private def X9 : Vals (.arr L) 3 := ⟨_, col [0, 2, 3], col [2, 3, 3], col [1, 3, 9]⟩
#guard mapOk two X9 && (map two X9).n == 5
-- setIds: segments {3 1 1} {1 3} {2} {} {} {1 3 3}: the three spellings of {1, 3} one id, `{}` one id
#guard setIds (Code.ofLongs (packLongs [3, 1, 1, 1, 3, 2, 1, 3, 3])) (packLongs [0, 3, 5, 6, 6, 6]) ==
  packLongs [0, 0, 1, 2, 2, 0]
-- Λ(R ∪ S): fibres {10 20} {10 20} {30} {40}
#guard (ran Λ(R ∪ S)).n == 3
-- Λ of {1↦10, 2↦20, 1↦20, 2↦10, 2↦10}: both fibres {10, 20}, in another order and with a repeat
private def D : LL := ⟨5, (Arr.mk (.bytes <| packLongs [1, 2, 1, 2, 2]) (by wf_lit)), (Arr.mk (.bytes <| packLongs [10, 20, 20, 10, 10]) (by wf_lit))⟩
#guard (Λ(D).toList.map (·.2) : List (List Int64)) == [[10, 20], [10, 20]] && ∋(D).n == 4 && lamOk D &&
  lamOk (D°) && lamOk (D ∪ R) && crossOk D R && crossOk D S
-- `setIds` on the kernel path, repeats and order inside a set ignored (the reference it was checked against,
-- `setIdsRef`, is gone: `setIds` stops where `rankSlices` declines)
#guard let c := Code.ofLongs (packLongs [1, 2, 2, 1, 1, 2, 5, 5, 3]); let s := packLongs [0, 2, 4, 6, 8, 8]
  setIds c s == packLongs [0, 0, 0, 1, 2, 3]

private def Ua3 : Vals L 3 := (Arr.mk (.bytes <| packLongs [3, 1, 2]) (by wf_lit))
#guard entire R Ua == false && entire R Ua3
#guard simple R == false && simple (idU Ua) && simple Ls
#guard isMap (idU Ua) Ua && isMap R Ua3 == false
#guard injective Ls == false && injective T
#guard surjective R Ub == false && surjective (idU Ub) Ub

/-! ### Every other encoding: the list `i ↦ x i` of four elements in each, against its own spec -/

/-- A column of four as a relation from its positions, `U4` the key. -/
private def lst {t : QAtomicType} (x : Arr t 4) : Rel L t := ⟨4, U4, x⟩
/-- `L ≫ L°`: the pairs of positions holding one element. -/
private def same {t : QAtomicType} (X Y : Rel L t) : LL := X ≫ Y°
-- the positions of `(p q p r)` paired with equal elements: `(0 2)` share, `1` and `3` alone
private def pqpr : List (Int64 × Int64) := [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (3, 3)]

-- boolean, `bits`: `1010b`, whose positions pair `(0 2)` and `(1 3)`
private abbrev Bo := QAtomicType.boolean
private def bitsC : Arr Bo 4 := Arr.mk (.bits (ByteArray.mk #[0b0101])) (by wf_lit)
#guard let X := same (lst bitsC) (lst bitsC)
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)] && X.n == 8
#guard let X := ran (lst bitsC); seteq X.toList [(true, true), (false, false)] && X.n == 2
#guard (lst bitsC ∪ lst bitsC).n == 4
#guard seteq (symDiv (lst bitsC) (lst bitsC) U4 U4).toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)]

-- symbol,`syms` and `enum`: `` `bc`a`bc`d `` in both, compared across the two
private abbrev Sy := QAtomicType.symbol
private def symsC : Arr Sy 4 := Arr.mk (.syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0, 100, 0]) #[0, 3, 5, 8, 10]) (by wf_lit)
private def enumC : Arr Sy 4 :=
  Arr.mk (.enum (ByteArray.mk #[97, 0, 98, 99, 0, 100, 0]) #[0, 2, 5, 7] (Column.packIds (Column.idWidth #[0, 2, 5, 7]) 4 fun i => [1, 0, 1, 2][i]!)) (by wf_lit)
#guard (lst enumC).toList == [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
-- `Λ` of `{bc, a}` met in two orders, in two relations, and of syms against enum: one array, `[a bc]`, by
-- the strings' order, not by first appearance
#guard let X := ofPairs [(0, 0), (0, 1)] ≫ lst symsC; let Y := ofPairs [(0, 1), (0, 0)] ≫ lst enumC
  crossOk X Y && crossOk Y X && lamOk X && lamOk Y &&
    (Λ(X).toList.map (·.2) : List (List String)) == [["a", "bc"]] && (Λ(Y).toList.map (·.2) : List (List String)) == [["a", "bc"]]
#guard let X := same (lst symsC) (lst enumC); seteq X.toList pqpr && X.n == 6
#guard let X := same (lst enumC) (lst enumC); seteq X.toList pqpr && X.n == 6
#guard let X := lst symsC ∪ lst enumC; X.n == 4 && seteq X.toList [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
#guard seteq (symDiv (lst symsC) (lst enumC) U4 U4).toList pqpr
#guard seteq (leftDiv (lst enumC) (lst symsC) symsC enumC).toList [("bc", "bc"), ("a", "a"), ("d", "d")]
#guard (top (A := .atom Sy) (B := .atom Bo) enumC bitsC).n == 16
#guard Λ((lst enumC)°).n == 3 && lamOk (lst enumC) && lamOk ((lst enumC)°)
#guard lamOk (lst symsC) && lamOk ((lst symsC)°)
#guard lamOk (lst bitsC) && lamOk ((lst bitsC)°) && Λ((lst bitsC)°).n == 2

-- the lane each encoding codes at: bits a bit; a three-symbol enum, or three distinct longs whose range
-- outruns the rows (a grouping pass's ids), a 2-bit lane; foR and dense offsets a byte
private def laneOf {t : QAtomicType} {n : USize} (x : Arr t n) : Nat := (codes t #v[⟨_, x⟩])[0].w
#guard laneOf bitsC == 1 && laneOf enumC == 2 && laneOf symsC == 2
#guard laneOf LfV == 8 && laneOf (col [5, 3, 5, 9]) == 8 && laneOf (col [5, 3, 5, 1099511627776]) == 2
-- a byte code below 3 beside a bit: `composeKey`'s `a·2 + b` at domain `3·2`, no grouping pass
#guard match pairCode false ⟨8, 4, 3, ByteArray.mk #[0, 1, 2, 1]⟩ ⟨1, 4, 2, ByteArray.mk #[0b0101]⟩ with
  | (c, none) => c.w == 4 && c.card == 6 && c.b == ByteArray.mk #[0x21, 0x25] | _ => false
-- the same pair at 2 and 1 bits: the 2-bit lane read by `eIds` where it lies
#guard match pairCode false ⟨2, 4, 3, Column.packIds 2 4 ([0, 1, 2, 1][·]!)⟩ ⟨1, 4, 2, ByteArray.mk #[0b0101]⟩ with
  | (c, none) => c.w == 4 && c.b == ByteArray.mk #[0x21, 0x25] | _ => false
-- a 2-bit code cut inside a byte, gathered, graded, grouped, run-started where it lies
private def c2 : Code := ⟨2, 6, 3, Column.packIds 2 6 ([2, 0, 1, 2, 0, 2][·]!)⟩
#guard (c2.cut #v[3, 3]).toArray.map (fun p => (List.range p.n.toNat).map (Column.idAt p.b 2)) == #[[2, 0, 1], [2, 0, 2]]
#guard (Code.cat (c2.cut #v[1, 5]).toArray).b == c2.b
#guard let g := c2.gather (packLongs [5, 1]); (List.range 2).map (Column.idAt g.b 2) == [2, 0]
#guard c2.grade == packLongs [1, 4, 2, 0, 3, 5]
#guard c2.groupIds.2 == packLongs [0, 1, 2]
#guard c2.find ⟨2, 2, 3, Column.packIds 2 2 ([1, 2][·]!)⟩ == packLongs [2, 0]
#guard c2.eqAt ⟨2, 6, 3, Column.packIds 2 6 ([2, 1, 1, 0, 0, 2][·]!)⟩ == packLongs [0, 2, 4, 5]
-- two foR parts of different bases, one negative: rebased (`foRShift`), equal elements equal codes
private def Lneg : LL := ⟨4, U4, Arr.mk (.foR (Coc.encode 8 (packLongs [9, -3, 5, 5])).1 (Coc.encode 8 (packLongs [9, -3, 5, 5])).2) (foRLongs_wf [9, -3, 5, 5] (by simp))⟩
#guard seteq (Lneg ≫ Lf°).toList
  (Lneg.toList.flatMap fun (i, x) => Lf.toList.filterMap fun (j, y) => if x == y then some (i, j) else none)

-- float through ALP: `1.5 2.25 1.5 0.1`, and the same as dense bytes
private abbrev Fl := QAtomicType.float
private def fs : List Float := [1.5, 2.25, 1.5, 0.1]
private def fb : ByteArray := packLongs (fs.map (·.toBits.toInt64))
private def fd : Arr Fl 4 := Arr.mk (.bytes fb) (by unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; rw [fb, packLongs_size]; rfl)
-- `alpOf` and not `Column.answer`, which keeps a column this short dense; no theorem yet says its payload is
-- well formed, so `Arr.of` decides it and a refusal fails the check
private def alpE : Enc := (Enc.alpOf Fl 4 fd.enc).getD fd.enc
#guard alpE matches .alp ..
#guard match Arr.of Fl 4 (.vector Fl 4 alpE none) "alp" with
  | .ok a => let X := same (lst a) (lst a); let Y := same (lst a) (lst fd)
    seteq X.toList pqpr && X.n == 6 && seteq Y.toList pqpr && Y.n == 6 &&
    -- a float element is its IEEE bits
    (lst a ∪ lst fd).n == 4 && seteq (symDiv (lst a) (lst a) U4 U4).toList pqpr
  | .error _ => false

-- a general list, `(1; (); 1; ,2)`, elements matched by identity
private def gs : Arr .general 4 :=
  Arr.mk (.gen #[.atom (.long 1), QValue.general #[] 0, .atom (.long 1), QValue.general #[.atom (.long 2)] 1])
    (by unfold Enc.WF; simp only [USize.reduceToNat]; rfl)
#guard let X := same (lst gs) (lst gs); seteq X.toList pqpr && X.n == 6
#guard (lst gs ∪ lst gs).n == 4 && (dom (lst gs)°).n == 3
#guard seteq (symDiv (lst gs) (lst gs) U4 U4).toList pqpr
#guard (zero (A := .general) (B := Sy)).n == 0

/-! ### Order, the power side, the list functions -/

-- `lt`, `leq` on `10 15 20 30 40` are the tables `LT`, `LE`; `est` and `thin` answer as on the tables
private def U5 : Vals L 5 := col [10, 15, 20, 30, 40]
#guard lt U5 == LT && leq U5 == LE && est (leq U5) R == est LE R && est (lt U5) R == est LE R &&
  thin (lt U5) R == thin LT R && est (leq U5)° S == est LE° S
-- a universe with repeats, a foR column, symbols (by their strings), booleans, floats
#guard seteq (leq (col [20, 10, 20])).toList [(10, 10), (10, 20), (20, 20)] && (lt (col [20, 10, 20])).n == 2
#guard seteq (lt LfV).toList [(3, 5), (3, 9), (5, 9)] && (lt LfV).n == 5 && lt LfV == lt (col [5, 3, 5, 9])
#guard seteq (lt symsC).toList [("a", "bc"), ("a", "d"), ("bc", "d")]
#guard seteq (lt bitsC).toList [(false, true)] && (leq bitsC).nub.n == 3
#guard seteq (lt fd).toList ([(0.1, 1.5), (0.1, 2.25), (1.5, 2.25)].map fun (a, b) => (Float.toBits a, Float.toBits b))
#guard (lt (Vals.empty L)).n == 0
-- a general list has no order: no witness
/-- error: could not synthesize default value for parameter '_h' using tactics
---
error: Tactic `decide` proved that the proposition
  QAtomicType.general ≠ QAtomicType.general
is false
---
info: lt gs ⋯ : Rel (Obj.atom QAtomicType.general) (Obj.atom QAtomicType.general) -/
#guard_msgs in #check lt gs

-- `succ`, `plus` on their universes
#guard seteq (succ Ua).toList ((Ua.toList.filter fun x => Ua.toList.contains (x + 1)).map fun x => (x, x + 1))
-- partial at the top: on `0 … 6` the range stays in `0 … 6`, and `6` goes to nothing
#guard (succ (tilCol 7)).toList == [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]
#guard seteq ((plus ((col [1, 2, 3], col [10, 20, 30]) : Vals (.prod L L) 3)).toList : List ((Int64 × Int64) × Int64))
  [((1, 10), 11), ((2, 20), 22), ((3, 30), 33)]

/-- A list of longs as a set: each value once, ascending, as `Λ` lays it out. -/
private def setOf (xs : List Int64) : List Int64 := xs.eraseDups.mergeSort fun a b => decide (a ≤ b)
-- `τ`: each element to `[x]`
#guard seteq ((τ Ua).toList : List (Int64 × List Int64)) (Ua.toList.map fun x => (x, [x]))
-- `E(R)`: every array of the universe, `[]` and arrays whose elements have no image included, to the set of
-- images; a map (`two` is not), repeated arrays (`Xs`), clamped arrays (`Xc`), no array
private def EOk {n : USize} (R : LL) (X : Vals (.arr L) n) : Bool :=
  seteq ((E R X).toList : List (List Int64 × List Int64)) ((arrs X).map fun xs => (xs, setOf (xs.flatMap (fib R)))) &&
    isMap (E R X) X
#guard EOk two Xl && EOk two Xs && EOk two Xc && EOk neg Xl && EOk R Xc && EOk (zero (A := L) (B := L)) Xl
#guard (E two (Vals.empty (.arr L))).n == 0
-- `Λ(R) E(S) = Λ(RS)` where every value of `G` has an image under `R`; `E(RT) = E(R) E(T)`; `E(𝟙) = 𝟙` on sets
#guard Λ(G) ≫ E R Λ(G).val == Λ(G ≫ R)
#guard E (R ≫ T) Xl == E R Xl ≫ E T (E R Xl).val && E (two ≫ neg) Xs == E two Xs ≫ E neg (E two Xs).val
#guard E (idU Ub) Λ(R).val == idU Λ(R).val
-- `union`: arrays of arrays over `Xc`'s `[1] [1 2] []`: `[[1] [1 2]]`, `[[1 2] []]`, `[]` twice
private def XX : Vals (.arr (.arr L)) 4 := ⟨3, col [0, 1, 0, 3], col [2, 3, 0, 3], Xc⟩
#guard ((idU XX).toList.map (·.1) : List (List (List Int64))) == [[[1], [1, 2]], [[1, 2], []], [], []]
#guard seteq ((Arr.union XX).toList : List (List (List Int64) × List Int64))
  (((idU XX).toList.map (·.1) : List (List (List Int64))).map fun xss => (xss, setOf xss.flatten)) && isMap (Arr.union XX) XX
-- `∪` of a relation with itself, again and again: its payloads hold the cells its rows refer to and no more,
-- for a nested array, an array of sums and a sum (`Vals.pick`)
private def selfU {A : Obj} (R : Rel A A) : Nat → Rel A A | 0 => R | k + 1 => selfU R k ∪ selfU R k
#guard let b := selfU (idU XX) 4; b == idU XX && (b.val.1, b.val.2.2.2.1) == (4, 5)
#guard let b := selfU (idU Xa) 4; b == idU Xa && (b.val.1, b.val.2.2.2.1, b.val.2.2.2.2.1) == (5, 2, 3)
#guard let b := selfU (idU Xo) 4; b == idU Xo && (b.val.1, b.val.2.1) == (2, 2)
-- `τ union = 𝟙` on sets; `union` of `τ`'s images of arrays not sets is their set
#guard τ Λ(R).val ≫ Arr.union (τ Λ(R).val).val == idU Λ(R).val
#guard seteq ((τ Xs ≫ Arr.union (τ Xs).val).toList : List (List Int64 × List Int64)) ((arrs Xs).map fun xs => (xs, setOf xs))
-- `P(R)`, Egli–Milner, `R` not a function, into the arrays `[10] [11 20] [] [10 20] [10 20 11 7]`
private def Yp : Vals (.arr L) 5 := ⟨7, col [0, 1, 0, 3, 3], col [1, 3, 0, 5, 7], col [10, 11, 20, 10, 20, 11, 7]⟩
private def pSpec {n m : USize} (R : LL) (X : Vals (.arr L) n) (Y : Vals (.arr L) m) : List (List Int64 × List Int64) :=
  (arrs X).flatMap fun xs => ((arrs Y).filter fun ys => xs.all (fun x => ys.any fun y => R.toList.contains (x, y)) &&
    ys.all fun y => xs.any fun x => R.toList.contains (x, y)).map (xs, ·)
#guard seteq ((P two Xc Yp).toList : List (List Int64 × List Int64)) (pSpec two Xc Yp) && (P two Xc Yp).n > 0
#guard seteq ((P two Xs Yp).toList : List (List Int64 × List Int64)) (pSpec two Xs Yp)
-- on a map `P(f) = E(f)` into `E(f)`'s own arrays
#guard P neg Xl (E neg Xl).val == E neg Xl
-- `nil`, `α = [nil, cons]`
#guard ((nil (B := L) zero1).toList : List (Int64 × List Int64)) == [(0, [])]
#guard alpha zero1 XP == junc nilR (cons (idU XP))
-- `tail`, `length`, `Arr.sum`, `suffix` against `List`
#guard seteq ((tail Xs).toList : List (List Int64 × List Int64)) ((unconsSpec (arrs Xs)).map fun (a, _, t) => (a, t))
private def onArrs {n : USize} {B : Obj} [BEq B.El] (X : Vals (.arr L) n) (R : Rel (.arr L) B) (f : List Int64 → List B.El) : Bool :=
  let r : List (List Int64 × B.El) := R.toList
  seteq r ((arrs X).flatMap fun xs => (f xs).map (xs, ·))
#guard onArrs Xl (length Xl) (fun xs => [Int64.ofNat xs.length]) && onArrs Xc (length Xc) (fun xs => [Int64.ofNat xs.length])
#guard onArrs Xs (length Xs) (fun xs => [Int64.ofNat xs.length]) && (length (Vals.empty (.arr L))).n == 0
#guard onArrs Xl (Arr.sum Xl) (fun xs => [xs.foldl (· + ·) 0]) && onArrs Xc (Arr.sum Xc) (fun xs => [xs.foldl (· + ·) 0])
#guard onArrs Xl (suffix Xl) (fun xs => (List.range (xs.length + 1)).map xs.drop) &&
  onArrs Xc (suffix Xc) (fun xs => (List.range (xs.length + 1)).map xs.drop)

-- arrays of arrays in list order: `[3 1 2] [] [1 5] [1 2] [2 1 5]` beside `[7] [8 9] [] [9 6] []`
private def Xp : Vals (.arr L) 5 := ⟨_, col [0, 0, 3, 1, 2], col [3, 0, 5, 3, 5], col [3, 1, 2, 1, 5]⟩
private def Yz : Vals (.arr L) 5 := ⟨_, col [0, 1, 0, 2, 3], col [1, 3, 0, 4, 3], col [7, 8, 9, 6]⟩
private def W2 : Vals (.prod (.arr L) (.arr L)) 5 := (Xp, Yz)
private def Ws : Vals (.prod (.arr L) L) 5 := (Xp, col [4, 5, 6, 7, 8])
private def pairsOf {n : USize} (W : Vals (.prod (.arr L) (.arr L)) n) : List (List Int64 × List Int64) := (idU W).toList.map (·.1)
#guard arrs Xp == [[3, 1, 2], [], [1, 5], [1, 2], [2, 1, 5]] && arrs Yz == [[7], [8, 9], [], [9, 6], []]
-- `inits`, `tails` against `List`, each array once; `inits ∋` the prefixes, `tails ∋ = suffix`
#guard onArrs Xl (inits Xl) (fun xs => [(List.range (xs.length + 1)).map xs.take]) &&
  onArrs Xp (inits Xp) (fun xs => [(List.range (xs.length + 1)).map xs.take]) && isMap (inits Xc) Xc
#guard onArrs Xl (tails Xl) (fun xs => [(List.range (xs.length + 1)).map xs.drop]) &&
  onArrs Xc (tails Xc) (fun xs => [(List.range (xs.length + 1)).map xs.drop]) && isMap (tails Xp) Xp
#guard onArrs Xl (inits Xl ≫ mem (inits Xl).val) (fun xs => (List.range (xs.length + 1)).map xs.take) &&
  seteq (tails Xp ≫ mem (tails Xp).val).toList (suffix Xp).toList
-- `cat`, `zip` on pairs of arrays, `cat°` against `take`/`drop`, `cat° cat = 𝟙`
#guard seteq ((cat (idU W2)).toList : List ((List Int64 × List Int64) × List Int64))
  ((pairsOf W2).map fun (x, y) => ((x, y), x ++ y))
#guard seteq ((zip (idU W2)).toList : List ((List Int64 × List Int64) × List (Int64 × Int64)))
  ((pairsOf W2).map fun (x, y) => ((x, y), x.zip y))
#guard seteq ((uncat Xp).toList : List (List Int64 × List Int64 × List Int64))
  ((arrs Xp).flatMap fun xs => (List.range (xs.length + 1)).map fun k => (xs, xs.take k, xs.drop k))
#guard seteq (cat (uncat Xl)).toList (idU Xl).toList
-- `snoc`; `snoc snoc° = 𝟙`, and `snoc° snoc = 𝟙` on the non-empty arrays
#guard seteq ((snoc (idU Ws)).toList : List ((List Int64 × Int64) × List Int64))
  (((idU Ws).toList.map (·.1) : List (List Int64 × Int64)).map fun (x, a) => ((x, a), x ++ [a]))
#guard seteq (snoc (idU Ws) ≫ unsnoc (snoc (idU Ws)).val).toList (idU Ws).toList
#guard seteq (snoc (unsnoc Xl)).toList (dom (unsnoc Xl)).toList

-- `at(k)` against `List`'s `[k]?`; `at(0) = head`, `tail at(k) = at(k+1)`; past every row's end, no pair
private def atOk {n : USize} (X : Vals (.arr L) n) : Bool :=
  seteq (atPos 0 X).toList (outl (uncons X)).toList && (List.range 21).all fun k =>
    onArrs X (atPos k X) (fun xs => xs[k]?.toList) &&
      seteq (tail X ≫ atPos k (tail X).val).toList (atPos (k + 1) X).toList
#guard atOk Xl && atOk Xp && atOk Xc && atOk Xs
#guard (atPos 2 Xp).n == 2 && (atPos 20 Xl).n == 0 && (atPos 0 (Vals.empty (.arr L))).n == 0

-- `perm` against the insertions of `List`; `perm perm = perm`
private def perms : List Int64 → List (List Int64)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun ys => (List.range (ys.length + 1)).map fun k => ys.take k ++ x :: ys.drop k
#guard onArrs Xp (perm Xp) perms && onArrs Xs (perm Xs) perms
#guard seteq (perm Xp ≫ perm (perm Xp).val).toList (perm Xp).toList
-- `setify` a map, `= E(𝟙)`; `ordered(≤)`, `ordered(<)`; `sort(≤)` a map, `⊑ perm`
private def LE9 : LL := leq (tilCol 10)
private def sorted (xs : List Int64) : List Int64 := xs.mergeSort fun a b => decide (a ≤ b)
#guard onArrs Xp (setify Xp) (fun xs => [setOf xs]) && onArrs Xs (setify Xs) (fun xs => [setOf xs]) && isMap (setify Xp) Xp
#guard seteq (setify Xl).toList (E (idU Xl.2.2.2) Xl).toList
#guard onArrs Xs (ordered LE9 Xs) (fun xs => if sorted xs == xs then [xs] else []) &&
  onArrs Xp (ordered LE9 Xp) (fun xs => if sorted xs == xs then [xs] else [])
#guard onArrs Xs (ordered (lt (tilCol 10)) Xs) (fun xs => if sorted xs == xs && xs.eraseDups == xs then [xs] else [])
-- `sort(Q) ≜ perm ordered(Q)`, the order tested on the arrays `perm` reaches
#guard let sort {n} (X : Vals (.arr L) n) := let P := perm X; P ≫ ordered LE9 (ran P).val
  onArrs Xp (sort Xp) (fun xs => [sorted xs]) && onArrs Xs (sort Xs) (fun xs => [sorted xs]) &&
  isMap (sort Xp) Xp && sort Xp ⊑ perm Xp
-- sorting sets: `setify° ordered(≤)` among the rearrangements of `Xp`, none with a repeat, is `sort(≤)` after `setify`
private def Yp' := (perm Xp).val
#guard seteq ((sortSet LE9 Yp').toList : List (List Int64 × List Int64))
  (((arrs Yp').filter fun ys => sorted ys == ys).map fun ys => (setOf ys, ys))
#guard let P := perm Yp'; seteq (setify Yp' ≫ sortSet LE9 Yp').toList (P ≫ ordered LE9 (ran P).val).toList

-- `subseq`; binary thinning among the subsequences of `Xp`, `Q` the `≤` on longs: keep a lower element
private def subs : List Int64 → List (List Int64)
  | [] => [[]]
  | x :: xs => (subs xs).map (x :: ·) ++ subs xs
#guard onArrs Xp (subseq Xp) subs && onArrs Xs (subseq Xs) subs
private def Ysub := (subseq Xp).val
#guard seteq ((thinL LE9 Ysub).toList : List (List Int64 × List Int64))
  ((arrs Ysub).flatMap fun xs => ((subs xs).filter fun ys => (arrs Ysub).contains ys &&
    xs.all fun a => ys.any (· ≤ a)).map (xs, ·))
#guard thinL LE9 Ysub ⊑ subseq Ysub && (thinL LE9 Ysub).n > 0
-- on the sources `Xp`, not closed under subsequence: the formula at `Y = ran(subseq Xp)` restricted to `Xp`,
-- `⊑ subseq`, and a row for every source
#guard let Y := (ran (subseq Xp)).val; let S := (setify Y).val
  let T := rightDiv (mem S) (mem S) S S ∩ leftDiv (mem S)° (LE9° ≫ (mem S)°) S S
  seteq (thinL LE9 Xp).toList (idU Xp ≫ ((setify Y ≫ T ≫ (setify Y)°) ∩ subseq Y)).toList
#guard thinL LE9 Xp ⊑ subseq Xp && seteq (dom (thinL LE9 Xp)).toList (idU Xp).toList
-- the one-pass thinning refines its specification and is entire: a thinned array of each source, not
-- always one, since an order may hold both ways between two elements
#guard let T := thinLOn (pairsIn LE9) Xp; T ⊑ thinL LE9 Xp && seteq (dom T).toList (idU Xp).toList
#guard let T := thinLOn (pairsIn LE9) Ysub; T ⊑ thinL LE9 Ysub && seteq (dom T).toList (idU Ysub).toList
-- `merge(≤)` against `List.merge`, on ordered and on unordered arrays; `merge(⊤) = cat` (B&dM p.212)
#guard seteq ((merge LE9 (idU W2)).toList : List ((List Int64 × List Int64) × List Int64))
  ((pairsOf W2).map fun (x, y) => ((x, y), List.merge x y fun a b => decide (a ≤ b))) && isMap (merge LE9 (idU W2)) W2
#guard seteq (merge (top (tilCol 10) (tilCol 10)) (idU W2)).toList (cat (idU W2)).toList
-- merging two ordered arrays gives an ordered one
#guard let P := perm Xp; let O := P ≫ ordered LE9 (ran P).val; let M := idU (O.val, O.val)
  seteq (merge LE9 M ≫ ordered LE9 (merge LE9 M).val).toList (merge LE9 M).toList
-- `loop(plus)` is the sum from a start; `loop(F)` against `List.foldl` with `F` not a function
private def Wl : Vals (.prod L (.arr L)) 5 := (col [0, 100, 0, 7, 1], Xp)
private def Tp : LL := top (tilCol 120) (tilCol 10)
#guard seteq ((loop (plus (Tp.key, Tp.val)) (idU Wl)).toList : List ((Int64 × List Int64) × Int64))
  (((idU Wl).toList.map (·.1) : List (Int64 × List Int64)).map fun (c, ys) => ((c, ys), ys.foldl (· + ·) c))
#guard seteq ((loop (tab (upto 30) (upto 9) (· + ·) ∪ tab (upto 30) (upto 9) fun c _ => c) (idU Wl)).toList :
    List ((Int64 × List Int64) × Int64))
  (((idU Wl).toList.map (·.1) : List (Int64 × List Int64)).flatMap fun (c, ys) =>
    if c ≤ 30 || ys.isEmpty then (ys.foldl (fun cs y => cs.flatMap fun c => [c + y, c]) [c]).map ((c, ys), ·) else [])
-- `tic`: the non-empty prefixes of `a :: xs`
#guard seteq ((tic (idU XP)).toList : List ((Int64 × List Int64) × List (List Int64)))
  [((5, [1, 2]), [[5], [5, 1], [5, 1, 2]]), ((6, []), [[6]])]

-- `bagify` against `mergeSort`, a map, idempotent; `[3 1 3]` and `[1 3 3]` one bag, also each on its own
#guard onArrs Xp (bagify Xp) (fun xs => [sorted xs]) && onArrs Xl (bagify Xl) (fun xs => [sorted xs]) &&
  onArrs Xc (bagify Xc) (fun xs => [sorted xs]) && onArrs Xs (bagify Xs) (fun xs => [sorted xs]) && isMap (bagify Xp) Xp
#guard let B := bagify Xp; seteq (B ≫ bagify B.val).toList B.toList
private def X3 : Vals (.arr L) 2 := ⟨6, col [0, 3], col [3, 6], col [3, 1, 3, 1, 3, 3]⟩
private def X31 : Vals (.arr L) 1 := ⟨3, col [0], col [3], col [3, 1, 3]⟩
#guard seteq ((bagify X3).toList : List (List Int64 × List Int64)) [([3, 1, 3], [1, 3, 3]), ([1, 3, 3], [1, 3, 3])] &&
  ((bagify X31).toList : List (List Int64 × List Int64)) == [([3, 1, 3], [1, 3, 3])]
-- `bagify bagify° = perm` (B&dM's `bagify° · bagify`) among the rearrangements of `Xp`, and of the arrays of
-- arrays `XX`; `bagify setify = setify`; the empty column
#guard let Y := (perm Xp).val; seteq (bagify Y ≫ (bagify Y)°).toList (perm Y).toList
#guard let Y := (perm XX).val; seteq (bagify Y ≫ (bagify Y)°).toList (perm Y).toList && isMap (bagify XX) XX
#guard seteq (bagify Xp ≫ setify (bagify Xp).val).toList (setify Xp).toList
#guard (bagify (Vals.empty (.arr L))).n == 0
-- an array of pairs, lexicographic: `[(2,5) (1,7) (2,3)]`, `[(9,1) (0,1)]`, `[]`
private def Xq : Vals (.arr (.prod L L)) 3 := ⟨5, col [0, 3, 5], col [3, 5, 5], (col [2, 1, 2, 9, 0], col [5, 7, 3, 1, 1])⟩
#guard seteq ((bagify Xq).toList : List (List (Int64 × Int64) × List (Int64 × Int64)))
  [([(2, 5), (1, 7), (2, 3)], [(1, 7), (2, 3), (2, 5)]), ([(9, 1), (0, 1)], [(0, 1), (9, 1)]), ([], [])]

-- `arith` against `Int`: each pair of `W` to `f(u, v)` where the operands are not q's null, `ok(v)`, and `f(u, v)`
-- is a `long` above the null; nothing elsewhere (a zero divisor, an overflow)
private def arithSpec {n : USize} (W : Vals (.prod L L) n) (f : Int → Int → Int) (ok : Int64 → Bool := fun _ => true) :
    List ((Int64 × Int64) × Int64) :=
  (W.1.toList.zip W.2.toList).filterMap fun (a, b) =>
    let r := f a.toInt b.toInt
    if a == nul || b == nul || !ok b || r ≤ nul.toInt || r > Int64.maxValue.toInt then none else some ((a, b), Int64.ofInt r)
private def square (xs : List Int64) : List (Int64 × Int64) := xs.flatMap fun a => xs.map (a, ·)
private def Wof (ps : List (Int64 × Int64)) : Vals (.prod L L) ps.length.toUSize :=
  (List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2)))
-- `-7 … 7` both sides, so negative operands and a zero divisor
private def Us : List Int64 := (List.range 15).map fun i => i.toInt64 - 7
private def Wn := Wof (square Us)
-- the edges of `long`: the null, its neighbour, the top, `±2³²`
private def Wo := Wof (square [nul, nul + 1, Int64.maxValue, Int64.maxValue - 1, 4294967296, -4294967296, 3, -1, 0])
private def arithOk {n : USize} (W : Vals (.prod L L) n) : Bool :=
  seteq ((plus W).toList : List ((Int64 × Int64) × Int64)) (arithSpec W (· + ·)) &&
  seteq ((times W).toList : List ((Int64 × Int64) × Int64)) (arithSpec W (· * ·)) &&
  seteq ((minus W).toList : List ((Int64 × Int64) × Int64)) (arithSpec W (· - ·)) &&
  seteq ((div W).toList : List ((Int64 × Int64) × Int64)) (arithSpec W Int.fdiv (· != 0)) &&
  seteq ((mod W).toList : List ((Int64 × Int64) × Int64)) (arithSpec W Int.fmod (· != 0))
#guard arithOk Wn && arithOk Wo
-- q's convention on negative operands: `div` floors, `mod` takes the divisor's sign
#guard ((div Wn).toList.lookup (-7, 2), (mod Wn).toList.lookup (-7, 2), (div Wn).toList.lookup (7, -2),
  (mod Wn).toList.lookup (7, -2)) == (some (-4), some 1, some (-4), some (-1))
-- no row at divisor `0`
#guard (div Wn).toList.all (·.1.2 != 0) && (mod Wn).toList.all (·.1.2 != 0) &&
  (div Wo).toList.all (·.1.2 != 0) && (mod Wo).toList.all (·.1.2 != 0)
-- overflow is no row: `max + 3`, `max · 3`, `(null + 1) - 3`; nor is a result on the null, `(null + 1) + -1`
#guard ((plus Wo).toList.lookup (Int64.maxValue, 3), (times Wo).toList.lookup (Int64.maxValue, 3),
  (minus Wo).toList.lookup (nul + 1, 3), (plus Wo).toList.lookup (nul + 1, -1)) == (none, none, none, none)
-- `u = v · div + mod`, `0 ≤ mod < v` for `v > 0` and `v < mod ≤ 0` for `v < 0`, every pair of `div` having its `mod`
#guard (div Wn).toList.all fun ((a, b), d) => ((mod Wn).toList.lookup (a, b)).any fun r =>
  a == b * d + r && (if b > 0 then 0 ≤ r && r < b else b < r && r ≤ 0)
-- `minus` is the converse reading of `plus`: `(u, v) minus w ⟺ (w, v) plus u`, on the pairs whose `w` is in `Us`
#guard seteq (((minus Wn).toList.filter fun (_, w) => Us.contains w) : List ((Int64 × Int64) × Int64))
  (((plus Wn).toList.filter fun (_, u) => Us.contains u).map fun ((w, v), u) => ((u, v), w))
-- `max`/`min` on numbers are the term `est (leq U) (outl ∪ outr)` and its converse order, no new op
private def UsC : Vals L Us.length.toUSize := col Us
#guard seteq ((est (leq UsC) (outl (idU Wn) ∪ outr (idU Wn))).toList : List ((Int64 × Int64) × Int64))
  ((square Us).map fun (a, b) => ((a, b), min a b))
#guard seteq ((est (leq UsC)° (outl (idU Wn) ∪ outr (idU Wn))).toList : List ((Int64 × Int64) × Int64))
  ((square Us).map fun (a, b) => ((a, b), max a b))

end Checks

#print axioms idU_holds
#print axioms convArr_holds
#print axioms outl_holds
#print axioms outr_holds
#print axioms zero
#print axioms top
#print axioms dom
#print axioms ran
#print axioms leftDiv
#print axioms rightDiv
#print axioms symDiv
#print axioms transpose
#print axioms setIds_size
#print axioms pair
#print axioms prod
#print axioms junc
#print axioms inl
#print axioms sum
#print axioms est
#print axioms thin
#print axioms uncons
#print axioms cons
#print axioms fold
#print axioms map
#print axioms setIds
#print axioms tuples
#print axioms codes
#print axioms entire
#print axioms simple
#print axioms injective
#print axioms surjective


end LeetQ.Rel.Alg
