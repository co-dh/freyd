/-
  `rep` of the power side's ops built on `Λ` (`transpose`), read in `Rel(Set)`. `Λ` itself is `rep_transpose`
  (`RepLambda`): defined only on `dom R`, a key outside it has no row.
-/
import LeetQ.Rel.RepLambda
import LeetQ.Rel.RepMem
import LeetQ.Rel.KernelWF.RazeFoR

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A : Obj}

-- the notations are `scoped` in `Pow` so that `RepE` states `rep_E` with them too
namespace Pow
-- Freyd's global `/` (`DivisionAllegory.div`) and `\` (`leftDiv`) make every `a / 8` and `R \ S` an overload
-- whose losing branch searches every division allegory instance; these win the parse and elaborate as core's
scoped notation:70 (priority := high) x:70 " / " y:71 => binop% HDiv.hDiv x y
scoped notation:70 (priority := high) x:70 " \\ " y:71 => SDiff.sdiff x y
-- `transpose`'s pieces at a relation `R` (`RepLambda`'s `kcT`, `pT`, `loT`, as notations taking `R`)
set_option hygiene false in
scoped notation "kcT(" R ")" =>
  (Obj.codes _ (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "pT(" R ")" => gather 8 (Obj.sortBy _ (Rel.nub R).val (tilLongs (Rel.nub R).n))
  (Code.gather (kcT(R)) (Obj.sortBy _ (Rel.nub R).val (tilLongs (Rel.nub R).n))).grade
set_option hygiene false in
scoped notation "loT(" R ")" => ByteArray.extract (Code.runStarts (Code.gather (kcT(R)) (pT(R)))) 0
  (ByteArray.size (Code.runStarts (Code.gather (kcT(R)) (pT(R)))) - 8)
-- the codes of a side `X`, and the rows `nub` keeps of `idU X`, whose key and value are both `X`
set_option hygiene false in
scoped notation "kcX(" X ")" => (Obj.codes _ (#v[⟨_, X⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "nubX(" X ")" => (tuples.tupleIds (kcX(X)) #[kcX(X)]).2
end Pow
open Pow OpsN UnionN

/-- **`rep (τ X)`: each element of `X` to the array holding it alone**: an array `τ X` gives `a` holds exactly
    `a`, and `τ X` has a row at `a` exactly when `X` lists `a` — `rep_transpose` at `idU X`, whose key and value
    are both `X`, so `rep_nub`'s two code hypotheses are one (`hX`, `hx`). -/
theorem rep_tau {n : USize} (X : Vals A n)
    (hX : (∀ {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat),
        Column.idAt (kcX(X)).b (kcX(X)).w i = Column.idAt (kcX(X)).b (kcX(X)).w j ↔
          Vals.row X ⟨i, hi⟩ = Vals.row X ⟨j, hj⟩) ∧
      laneOK((kcX(X)).w) ∧
        (kcX(X)).n = n ∧ (kcX(X)).b.size = ((kcX(X)).n.toNat * (kcX(X)).w + 7) / 8 ∧
        ((kcX(X)).w < 8 → (kcX(X)).card < USize.size ∧
          ∀ i < (kcX(X)).n.toNat, Column.idAt (kcX(X)).b (kcX(X)).w i < (kcX(X)).card))
    (hx : Vals.PickFits A X (List.range n.toNat))
    -- generic `A`: the nub copies `X`'s cells, whose dictionaries, general cells, nested payloads no `X` fact bounds
    (hWk : A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).key⟩] : Vector (Part A) 1))
    (hW : A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).val⟩] : Vector (Part A) 1))
    (h63 : n.toNat < 2 ^ 63) :
    (∀ a Y, rep (τ X) a Y → ∀ x, x ∈ Y ↔ x = a) ∧ (∀ a, (∃ Y, rep (τ X) a Y) ↔ ∃ i, Vals.row X i = a) := by
  obtain ⟨h1, h2⟩ := rep_transpose (idU X) hX hX hx hx hWk hW h63
  have hid : ∀ a b, rep (idU X) a b ↔ a = b ∧ ∃ i, X.row i = a := idU_holds X
  refine ⟨fun a Y h x => ?_, fun a => (h2 a).trans
    ⟨fun ⟨b, hb⟩ => ((hid a b).1 hb).2, fun hi => ⟨a, (hid a a).2 ⟨rfl, hi⟩⟩⟩⟩
  obtain ⟨b, hb⟩ := (h2 a).1 ⟨Y, h⟩
  have hi := ((hid a b).1 hb).2
  rw [h1 a Y h x, hid]
  exact ⟨fun ⟨e, _⟩ => e.symm, fun e => ⟨e.symm, hi⟩⟩

#print axioms rep_tau

/-! ## `lamOn`, `setify`, `E`: `Λ(R)` made total on a side -/

namespace Pow
-- `lamOn R U`'s parts: `Λ(R)`; the elements of `U` that `R` relates to nothing; each of them to the empty array
set_option hygiene false in
scoped notation "lT(" R ")" => LeetQ.Rel.Alg.transpose R
set_option hygiene false in
scoped notation "lD(" R ", " U ")" => (LeetQ.Rel.Alg.idU U \ LeetQ.Rel.Alg.dom R)
set_option hygiene false in
scoped notation "lN(" R ", " U ", " B ")" =>
  LeetQ.Rel.Alg.top (Rel.key (LeetQ.Rel.Alg.idU U \ LeetQ.Rel.Alg.dom R)) (LeetQ.Rel.Alg.nilVal B)
end Pow
open Pow

/-- **`rep_top`'s fits at `lamOn R U`'s empty-array part**: its keys are rows of `idU U \ dom R`, which fits where
    `U` does (`diff_pickFits`); the empty array fits anywhere (`pickFits_nilVal`); one value per key. -/
theorem lamOn_top_fits {B : Obj} {m : USize} (R : Rel A B) (U : Vals A m)
    (hc : pairsOK(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R)) (hdU : Vals.PickFits A U (List.range m.toNat)) :
    (Rel.n (lD(R, U))).toNat * USize.toNat 1 < USize.size ∧
      Vals.PickFits A (Rel.key (lD(R, U)))
        ((List.range ((Rel.n (lD(R, U))).toNat * USize.toNat 1)).map (· / USize.toNat 1)) ∧
      Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
        ((List.range ((Rel.n (lD(R, U))).toNat * USize.toNat 1)).map (· % USize.toNat 1)) := by
  have e : ((List.range ((Rel.n (lD(R, U))).toNat * USize.toNat 1)).map (· / USize.toNat 1)) =
      List.range (Rel.n (lD(R, U))).toNat := by
    simp
  refine ⟨by simpa using USize.toNat_lt_size (Rel.n (lD(R, U))), ?_, pickFits_nilVal B _⟩
  rw [e]
  exact (diff_pickFits _ _ hc hdU hdU).1

#print axioms lamOn_top_fits

/-- **`rep (lamOn R U)`: `Λ(R)` total on `U`**: an array `lamOn R U` gives `a` holds exactly the values `R`
    relates `a` to, and `lamOn R U` has a row at `a` exactly when `R` has a pair at `a` or `U` lists `a`.
    `rep_union_full` splits it into `Λ(R)` (`rep_transpose`) and `⊤` (`rep_top`) from the `U`-rows outside
    `dom R` (`rep_diff`, `rep_dom`) to the empty array. Hypotheses: those of each, at the parts named above. -/
theorem rep_lamOn {B : Obj} {m : USize} (R : Rel A B) (U : Vals A m)
    -- `rep_transpose` at `R`
    (kc vc : Code) (hkc : kc = kcR(R)) (hvc : vc = vcR(R))
    (hK : cOK(kc, Rel.n R, Rel.key R)) (hV : cOK(vc, Rel.n R, Rel.val R))
    (hk : Vals.PickFits A (Rel.key R) (List.range (Rel.n R).toNat))
    (hv : Vals.PickFits B (Rel.val R) (List.range (Rel.n R).toNat))
    -- generic sides: the nub copies `R`'s cells, whose dictionaries, general cells, nested payloads no `R` fact bounds
    (hWk : A.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part A) 1))
    (hW : B.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.n R).toNat < 2 ^ 63)
    -- `rep_diff` at `idU U`, `dom R`; two parts coded jointly: a generic `A`'s ALP sum and dictionaries are unbounded
    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R)))
    (hdU : Vals.PickFits A U (List.range m.toNat))
    -- `rep_top` at `D.key`, `nilVal B`
    (D : Rel A A) (hD : D = lD(R, U))
    -- `D`'s count is bounded only by `U`'s, a `USize`; `top`'s `cross` needs it below `2^63`
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    -- `rep_union_full` at `T`, `N`; `L` their raze
    (T N : Rel A (.arr B)) (hT : T = lT(R)) (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hFk : Vals.RazeFits A (Rel.key T) (Rel.key N)) (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel A (.arr B)) (hL : L = Uc(T, N, hN)) (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits A (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat)) :
    (∀ a Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y → ∀ y, y ∈ Y ↔ rep R a y) ∧
      (∀ a, (∃ Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y) ↔ (∃ b, rep R a b) ∨ ∃ i, Vals.row U i = a) := by
  subst hku hvu hL hN0 hD hT hpc hkc hvc
  obtain ⟨htN, htA, htB⟩ := lamOn_top_fits R U hc hdU
  obtain ⟨h1, h2⟩ := rep_transpose R hK hV hk hv hWk hW h63
  have hu := rep_union_full (lT(R)) (lN(R, U, B)) hN hFk hFv huK huV huk huv
  have hL : ∀ a Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y ↔ rep (lT(R)) a Y ∨ rep (lN(R, U, B)) a Y := fun a Y => by
    rw [show LeetQ.Rel.Alg.lamOn R U = lT(R) ∪ lN(R, U, B) from rfl, hu]; exact Iff.rfl
  have hd : ∀ a b, rep (LeetQ.Rel.Alg.dom R) a b ↔ a = b ∧ ∃ c, rep R a c := fun a b => by
    rw [rep_dom_corefl R hK hk]; exact Iff.rfl
  have hD : ∀ a, (∃ i, Vals.row (Rel.key (lD(R, U))) i = a) ↔ (∃ i, Vals.row U i = a) ∧ ¬ ∃ c, rep R a c := by
    intro a
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨hI, hR⟩ := (rep_diff _ _ hc hdU hdU a _).1 ⟨i, hi, rfl⟩
      obtain ⟨e, hU⟩ := (idU_holds U _ _).1 hI
      exact ⟨hU, fun hc' => hR ((hd _ _).2 ⟨e, hc'⟩)⟩
    · rintro ⟨hU, hR⟩
      obtain ⟨i, hi, -⟩ := (rep_diff _ _ hc hdU hdU a a).2
        ⟨(idU_holds U a a).2 ⟨rfl, hU⟩, fun h => hR ((hd a a).1 h).2⟩
      exact ⟨i, hi⟩
  have hT : ∀ a Y, rep (lN(R, U, B)) a Y ↔ (∃ i, Vals.row (Rel.key (lD(R, U))) i = a) ∧ Y = [] := fun a Y => by
    rw [rep_top _ _ htN ht63 htA htB]
    show (∃ a', (a = a' ∧ ∃ i, Vals.row (Rel.key (lD(R, U))) i = a) ∧
      ∃ b', True ∧ (b' = Y ∧ ∃ j, Vals.row (LeetQ.Rel.Alg.nilVal B) j = b')) ↔ _
    have hnil : (∃ j, Vals.row (LeetQ.Rel.Alg.nilVal B) j = Y) ↔ Y = [] :=
      ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨⟨0, by simp⟩, h.symm⟩⟩
    rw [← hnil]
    exact ⟨fun ⟨_, ⟨rfl, ha⟩, _, _, rfl, hb⟩ => ⟨ha, hb⟩, fun ⟨ha, hb⟩ => ⟨a, ⟨rfl, ha⟩, Y, trivial, rfl, hb⟩⟩
  refine ⟨fun a Y h y => ?_, fun a => ⟨fun ⟨Y, h⟩ => ?_, fun h => ?_⟩⟩
  · rcases (hL a Y).1 h with h | h
    · exact h1 a Y h y
    · obtain ⟨hk', rfl⟩ := (hT a Y).1 h
      exact ⟨fun hy => by simp at hy, fun hy => absurd ⟨y, hy⟩ ((hD a).1 hk').2⟩
  · rcases (hL a Y).1 h with h | h
    · exact Or.inl ((h2 a).1 ⟨Y, h⟩)
    · exact Or.inr ((hD a).1 ((hT a Y).1 h).1).1
  · by_cases hR : ∃ c, rep R a c
    · obtain ⟨Y, hY⟩ := (h2 a).2 hR
      exact ⟨Y, (hL a Y).2 (Or.inl hY)⟩
    · exact ⟨[], (hL a []).2 (Or.inr ((hT a []).2 ⟨(hD a).2 ⟨h.resolve_left hR, hR⟩, rfl⟩))⟩

#print axioms rep_lamOn

namespace Pow
-- the relation `setify X` makes total: `∋` on `X`
set_option hygiene false in
scoped notation "mS(" X ")" => (LeetQ.Rel.Alg.mem X)
-- `≫`'s two middle parts, their joint codes, the pairs `join` answers and their count (`RepComp`'s `jcs`, `jc`,
-- `jpairs`, taking `R`, `S`)
set_option hygiene false in
scoped notation "jcs(" R ", " S ")" => (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part _) 2)
set_option hygiene false in
scoped notation "jc(" R ", " S ")" => Obj.codes _ (jcs(R, S))
set_option hygiene false in
scoped notation "jpairs(" R ", " S ")" => ((List.range (Rel.n R).toNat).flatMap fun i =>
  ((List.range (Rel.n S).toNat).filter fun j =>
    Column.idAt ((jc(R, S))[1]'Nat.one_lt_two).b ((jc(R, S))[1]'Nat.one_lt_two).w j ==
      Column.idAt ((jc(R, S))[0]'Nat.zero_lt_two).b ((jc(R, S))[0]'Nat.zero_lt_two).w i).map (i, ·))
end Pow
open Pow


/-- **`rep (τ X)`, as lists**: `τ X` takes each element `a` of `X` to the array `[a]` and nothing else —
    `rep_transpose_list` at `idU X`: the array holds `a` only, each value once. Hypotheses: `rep_tau`'s. -/
theorem rep_tau_list {n : USize} (X : Vals A n)
    (hX : (∀ {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat),
        Column.idAt (kcX(X)).b (kcX(X)).w i = Column.idAt (kcX(X)).b (kcX(X)).w j ↔
          Vals.row X ⟨i, hi⟩ = Vals.row X ⟨j, hj⟩) ∧
      laneOK((kcX(X)).w) ∧
        (kcX(X)).n = n ∧ (kcX(X)).b.size = ((kcX(X)).n.toNat * (kcX(X)).w + 7) / 8 ∧
        ((kcX(X)).w < 8 → (kcX(X)).card < USize.size ∧
          ∀ i < (kcX(X)).n.toNat, Column.idAt (kcX(X)).b (kcX(X)).w i < (kcX(X)).card))
    (hx : Vals.PickFits A X (List.range n.toNat))
    -- generic `A`: the nub copies `X`'s cells, whose dictionaries, general cells, nested payloads no `X` fact bounds
    (hWk : A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).key⟩] : Vector (Part A) 1))
    (hW : A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).val⟩] : Vector (Part A) 1))
    (h63 : n.toNat < 2 ^ 63) :
    ∀ a Y, rep (τ X) a Y ↔ (∃ i, Vals.row X i = a) ∧ Y = [a] := by
  obtain ⟨h1, h2⟩ := rep_transpose_list (idU X) hX hX hx hx hWk hW h63
  have hid : ∀ a b, rep (idU X) a b ↔ a = b ∧ ∃ i, X.row i = a := idU_holds X
  -- a row of `τ X`: `a` listed in `X`, the array `[a]`
  have fwd : ∀ a Y, rep (τ X) a Y → (∃ i, Vals.row X i = a) ∧ Y = [a] := fun a Y h => by
    obtain ⟨hnd, hm, -⟩ := h1 a Y h
    obtain ⟨b, hb⟩ := (h2 a).1 ⟨Y, h⟩
    have hi := ((hid a b).1 hb).2
    have hY : ∀ x, x ∈ Y ↔ x = a := fun x =>
      (hm x).trans ((hid a x).trans ⟨fun ⟨e, _⟩ => e.symm, fun e => ⟨e.symm, hi⟩⟩)
    refine ⟨hi, ?_⟩
    rcases Y with _ | ⟨y, _ | ⟨z, zs⟩⟩
    · exact absurd ((hY a).2 rfl) (by simp)
    · rw [(hY y).1 (by simp)]
    · have e : y = z := ((hY y).1 (by simp)).trans ((hY z).1 (by simp)).symm
      exact ((List.nodup_cons.1 hnd).1 (by rw [e]; simp)).elim
  refine fun a Y => ⟨fwd a Y, fun ⟨hi, hY⟩ => ?_⟩
  obtain ⟨Y', h⟩ := (h2 a).2 ⟨a, (hid a a).2 ⟨rfl, hi⟩⟩
  rw [hY, ← (fwd a Y' h).2]
  exact h

#print axioms rep_tau_list


end LeetQ.Rel.Rep
