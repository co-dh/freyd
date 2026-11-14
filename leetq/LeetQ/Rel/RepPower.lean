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
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub (idU X)).n.toNat) (hj : j < (Rel.nub (idU X)).n.toNat),
      Column.idAt (kcT(idU X)).b (kcT(idU X)).w i = Column.idAt (kcT(idU X)).b (kcT(idU X)).w j ↔
        Vals.row (Rel.nub (idU X)).key ⟨i, hi⟩ = Vals.row (Rel.nub (idU X)).key ⟨j, hj⟩)
    (hw : laneOK((kcT(idU X)).w))
    (hn : (kcT(idU X)).n = (Rel.nub (idU X)).n)
    (hs : (kcT(idU X)).b.size = ((kcT(idU X)).n.toNat * (kcT(idU X)).w + 7) / 8)
    (hW : A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).val⟩] : Vector (Part A) 1))
    (h63 : (Rel.nub (idU X)).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits A (Rel.nub (idU X)).key (ids (pT(idU X))))
    (hpv : Vals.PickFits A (Rel.nub (idU X)).val (ids (pT(idU X))))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub (idU X)).key (pT(idU X))).2 (ids (loT(idU X)))) :
    (∀ a Y, rep (τ X) a Y → ∀ x, x ∈ Y ↔ x = a) ∧ (∀ a, (∃ Y, rep (τ X) a Y) ↔ ∃ i, Vals.row X i = a) := by
  obtain ⟨h1, h2⟩ := rep_transpose (idU X) hX hX hx hx hF hw hn hs hW h63 hpk hpv hlo
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
    (kt : Code) (hkt : kt = kcT(R))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub R).n.toNat) (hj : j < (Rel.nub R).n.toNat),
      Column.idAt kt.b kt.w i = Column.idAt kt.b kt.w j ↔
        Vals.row (Rel.nub R).key ⟨i, hi⟩ = Vals.row (Rel.nub R).key ⟨j, hj⟩)
    (hw : laneOK(kt.w))
    (hn : kt.n = (Rel.nub R).n)
    (hs : kt.b.size = (kt.n.toNat * kt.w + 7) / 8)
    (hW : B.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.nub R).n.toNat < 2 ^ 63)
    (p lo : ByteArray) (hpT : p = pT(R)) (hloT : lo = loT(R))
    (hpk : Vals.PickFits A (Rel.nub R).key (ids p))
    (hpv : Vals.PickFits B (Rel.nub R).val (ids p))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub R).key p).2 (ids lo))    -- `rep_diff` at `idU U`, `dom R`
    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R)))
    (hdU : Vals.PickFits A U (List.range m.toNat))
    -- `rep_top` at `D.key`, `nilVal B`
    (D : Rel A A) (hD : D = lD(R, U))
    (htN : (Rel.n D).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits A (Rel.key D) ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    -- `rep_union_full` at `T`, `N`; `L` their raze
    (T N : Rel A (.arr B)) (hT : T = lT(R)) (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hNk : ((pk(T, N)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (hNv : ((pv(T, N)).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits A (Rel.key T) (Rel.key N)) (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel A (.arr B)) (hL : L = Uc(T, N, hNk, hNv)) (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits A (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat)) :
    (∀ a Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y → ∀ y, y ∈ Y ↔ rep R a y) ∧
      (∀ a, (∃ Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y) ↔ (∃ b, rep R a b) ∨ ∃ i, Vals.row U i = a) := by
  subst hku hvu hL hN0 hD hT hpc hloT hpT hkt hkc hvc
  obtain ⟨h1, h2⟩ := rep_transpose R hK hV hk hv hF hw hn hs hW h63 hpk hpv hlo
  have hu := rep_union_full (lT(R)) (lN(R, U, B)) hN hNk hNv hFk hFv huK huV huk huv
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

/-- **`rep (setify X)`: each array of `X` to the array of its elements**: an array `setify X` gives `xs` holds
    exactly the elements of `xs`, and `setify X` has a row at `xs` exactly when `X` lists `xs`. `rep_lamOn` at
    `R := ∋` on `X` (`rep_mem`), `U := X`. Hypotheses: `rep_mem`'s (`hmv`, `hmk`), then `rep_lamOn`'s there. -/
theorem rep_setify {B : Obj} {n : USize} (X : Vals (.arr B) n)
    -- `rep_mem` at `X`
    (hmv : Vals.PickFits (.arr B) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    -- `rep_lamOn` at `mS(X)`, `X`
    (kc vc : Code) (hkc : kc = kcR(mS(X))) (hvc : vc = vcR(mS(X)))
    (hK : cOK(kc, Rel.n mS(X), Rel.key mS(X))) (hV : cOK(vc, Rel.n mS(X), Rel.val mS(X)))
    (hk : Vals.PickFits (.arr B) (Rel.key mS(X)) (List.range (Rel.n mS(X)).toNat))
    (hv : Vals.PickFits B (Rel.val mS(X)) (List.range (Rel.n mS(X)).toNat))
    (kt : Code) (hkt : kt = kcT(mS(X)))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub mS(X)).n.toNat) (hj : j < (Rel.nub mS(X)).n.toNat),
      Column.idAt kt.b kt.w i = Column.idAt kt.b kt.w j ↔
        Vals.row (Rel.nub mS(X)).key ⟨i, hi⟩ = Vals.row (Rel.nub mS(X)).key ⟨j, hj⟩)
    (hw : laneOK(kt.w))
    (hn : kt.n = (Rel.nub mS(X)).n)
    (hs : kt.b.size = (kt.n.toNat * kt.w + 7) / 8)
    (hW : B.CodesFit (#v[⟨(Rel.nub mS(X)).n, (Rel.nub mS(X)).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.nub mS(X)).n.toNat < 2 ^ 63)
    (p lo : ByteArray) (hpT : p = pT(mS(X))) (hloT : lo = loT(mS(X)))
    (hpk : Vals.PickFits (.arr B) (Rel.nub mS(X)).key (ids p))
    (hpv : Vals.PickFits B (Rel.nub mS(X)).val (ids p))
    (hlo : Vals.PickFits (.arr B) (Vals.pickPart (.arr B) (Rel.nub mS(X)).key p).2 (ids lo))    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X)])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X))))    (D : Rel (.arr B) (.arr B)) (hD : D = lD(mS(X), X))
    (htN : (Rel.n D).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits (.arr B) (Rel.key D) ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    (T N : Rel (.arr B) (.arr B)) (hT : T = lT(mS(X)))
    (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hNk : ((pk(T, N)).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(T, N)).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.arr B) (Rel.key T) (Rel.key N)) (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel (.arr B) (.arr B)) (hL : L = Uc(T, N, hNk, hNv)) (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits (.arr B) (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat)) :
    (∀ xs Y, rep (LeetQ.Rel.Alg.setify X) xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.setify X) xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  obtain ⟨h1, h2⟩ := rep_lamOn mS(X) X kc vc hkc hvc hK hV hk hv kt hkt hF hw hn hs hW h63 p lo hpT hloT hpk hpv hlo
    pc hpc hc hmv D hD htN ht63 htA htB T N hT hN0 hN hNk hNv hFk hFv L hL ku vu hku hvu huK huV huk huv
  have hm := rep_mem X hmv hmk
  have h2' : ∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.setify X) xs Y) ↔ ∃ i, Vals.row X i = xs := fun xs =>
    (h2 xs).trans ⟨fun h => h.elim (fun ⟨_, hb⟩ => ((hm _ _).1 hb).1) id, Or.inr⟩
  exact ⟨fun xs Y h => ⟨(h2' xs).1 ⟨Y, h⟩, fun y => (h1 xs Y h y).trans
    ((hm xs y).trans ⟨And.right, fun hy => ⟨(h2' xs).1 ⟨Y, h⟩, hy⟩⟩)⟩, h2'⟩

#print axioms rep_setify

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
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub (idU X)).n.toNat) (hj : j < (Rel.nub (idU X)).n.toNat),
      Column.idAt (kcT(idU X)).b (kcT(idU X)).w i = Column.idAt (kcT(idU X)).b (kcT(idU X)).w j ↔
        Vals.row (Rel.nub (idU X)).key ⟨i, hi⟩ = Vals.row (Rel.nub (idU X)).key ⟨j, hj⟩)
    (hw : laneOK((kcT(idU X)).w))
    (hn : (kcT(idU X)).n = (Rel.nub (idU X)).n)
    (hs : (kcT(idU X)).b.size = ((kcT(idU X)).n.toNat * (kcT(idU X)).w + 7) / 8)
    (hW : A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).val⟩] : Vector (Part A) 1))
    (h63 : (Rel.nub (idU X)).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits A (Rel.nub (idU X)).key (ids (pT(idU X))))
    (hpv : Vals.PickFits A (Rel.nub (idU X)).val (ids (pT(idU X))))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub (idU X)).key (pT(idU X))).2 (ids (loT(idU X)))) :
    ∀ a Y, rep (τ X) a Y ↔ (∃ i, Vals.row X i = a) ∧ Y = [a] := by
  obtain ⟨h1, h2⟩ := rep_transpose_list (idU X) hX hX hx hx hF hw hn hs hW h63 hpk hpv hlo
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

/-- **`rep (lamOn R U)`, as lists**: `rep_lamOn`, and every array `lamOn R U` gives holds each value once —
    a `Λ(R)` row by `rep_transpose_list`, the empty array otherwise. Hypotheses: `rep_lamOn`'s. -/
theorem rep_lamOn_list {B : Obj} {m : USize} (R : Rel A B) (U : Vals A m)
    -- `rep_transpose` at `R`
    (kc vc : Code) (hkc : kc = kcR(R)) (hvc : vc = vcR(R))
    (hK : cOK(kc, Rel.n R, Rel.key R)) (hV : cOK(vc, Rel.n R, Rel.val R))
    (hk : Vals.PickFits A (Rel.key R) (List.range (Rel.n R).toNat))
    (hv : Vals.PickFits B (Rel.val R) (List.range (Rel.n R).toNat))
    (kt : Code) (hkt : kt = kcT(R))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub R).n.toNat) (hj : j < (Rel.nub R).n.toNat),
      Column.idAt kt.b kt.w i = Column.idAt kt.b kt.w j ↔
        Vals.row (Rel.nub R).key ⟨i, hi⟩ = Vals.row (Rel.nub R).key ⟨j, hj⟩)
    (hw : laneOK(kt.w))
    (hn : kt.n = (Rel.nub R).n)
    (hs : kt.b.size = (kt.n.toNat * kt.w + 7) / 8)
    (hW : B.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.nub R).n.toNat < 2 ^ 63)
    (p lo : ByteArray) (hpT : p = pT(R)) (hloT : lo = loT(R))
    (hpk : Vals.PickFits A (Rel.nub R).key (ids p))
    (hpv : Vals.PickFits B (Rel.nub R).val (ids p))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub R).key p).2 (ids lo))    -- `rep_diff` at `idU U`, `dom R`
    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R)))
    (hdU : Vals.PickFits A U (List.range m.toNat))
    -- `rep_top` at `D.key`, `nilVal B`
    (D : Rel A A) (hD : D = lD(R, U))
    (htN : (Rel.n D).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits A (Rel.key D) ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    -- `rep_union_full` at `T`, `N`; `L` their raze
    (T N : Rel A (.arr B)) (hT : T = lT(R)) (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hNk : ((pk(T, N)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (hNv : ((pv(T, N)).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits A (Rel.key T) (Rel.key N)) (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel A (.arr B)) (hL : L = Uc(T, N, hNk, hNv)) (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits A (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat)) :
    (∀ a Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y → Y.Nodup ∧ ∀ y, y ∈ Y ↔ rep R a y) ∧
      (∀ a, (∃ Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y) ↔ (∃ b, rep R a b) ∨ ∃ i, Vals.row U i = a) := by
  obtain ⟨h1, h2⟩ := rep_lamOn R U kc vc hkc hvc hK hV hk hv kt hkt hF hw hn hs hW h63 p lo hpT hloT hpk hpv hlo
    pc hpc hc hdU D hD htN ht63 htA htB T N hT hN0 hN hNk hNv hFk hFv L hL ku vu hku hvu huK huV huk huv
  subst hku hvu hL hN0 hD hT hpc hloT hpT hkt hkc hvc
  have hX := rep_transpose_list R hK hV hk hv hF hw hn hs hW h63 hpk hpv hlo
  have hu := rep_union_full (lT(R)) (lN(R, U, B)) hN hNk hNv hFk hFv huK huV huk huv
  refine ⟨fun a Y h => ⟨?_, h1 a Y h⟩, h2⟩
  have h' : rep (lT(R)) a Y ∨ rep (lN(R, U, B)) a Y := by
    rw [show LeetQ.Rel.Alg.lamOn R U = lT(R) ∪ lN(R, U, B) from rfl, hu] at h; exact h
  rcases h' with h | h
  · exact (hX.1 a Y h).1
  · rw [rep_top _ _ htN ht63 htA htB] at h
    obtain ⟨_, -, _, -, rfl, j, hj⟩ := h
    rw [← hj]
    exact List.nodup_nil

#print axioms rep_lamOn_list

/-- **`rep (setify X)`, as lists**: `rep_setify`, and the array `setify X` gives `xs` holds each element of `xs`
    once (`rep_lamOn_list`). Hypotheses: `rep_setify`'s. -/
theorem rep_setify_list {B : Obj} {n : USize} (X : Vals (.arr B) n)
    -- `rep_mem` at `X`
    (hmv : Vals.PickFits (.arr B) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    -- `rep_lamOn` at `mS(X)`, `X`
    (kc vc : Code) (hkc : kc = kcR(mS(X))) (hvc : vc = vcR(mS(X)))
    (hK : cOK(kc, Rel.n mS(X), Rel.key mS(X))) (hV : cOK(vc, Rel.n mS(X), Rel.val mS(X)))
    (hk : Vals.PickFits (.arr B) (Rel.key mS(X)) (List.range (Rel.n mS(X)).toNat))
    (hv : Vals.PickFits B (Rel.val mS(X)) (List.range (Rel.n mS(X)).toNat))
    (kt : Code) (hkt : kt = kcT(mS(X)))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub mS(X)).n.toNat) (hj : j < (Rel.nub mS(X)).n.toNat),
      Column.idAt kt.b kt.w i = Column.idAt kt.b kt.w j ↔
        Vals.row (Rel.nub mS(X)).key ⟨i, hi⟩ = Vals.row (Rel.nub mS(X)).key ⟨j, hj⟩)
    (hw : laneOK(kt.w))
    (hn : kt.n = (Rel.nub mS(X)).n)
    (hs : kt.b.size = (kt.n.toNat * kt.w + 7) / 8)
    (hW : B.CodesFit (#v[⟨(Rel.nub mS(X)).n, (Rel.nub mS(X)).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.nub mS(X)).n.toNat < 2 ^ 63)
    (p lo : ByteArray) (hpT : p = pT(mS(X))) (hloT : lo = loT(mS(X)))
    (hpk : Vals.PickFits (.arr B) (Rel.nub mS(X)).key (ids p))
    (hpv : Vals.PickFits B (Rel.nub mS(X)).val (ids p))
    (hlo : Vals.PickFits (.arr B) (Vals.pickPart (.arr B) (Rel.nub mS(X)).key p).2 (ids lo))    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X)])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X))))    (D : Rel (.arr B) (.arr B)) (hD : D = lD(mS(X), X))
    (htN : (Rel.n D).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits (.arr B) (Rel.key D) ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    (T N : Rel (.arr B) (.arr B)) (hT : T = lT(mS(X)))
    (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hNk : ((pk(T, N)).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(T, N)).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.arr B) (Rel.key T) (Rel.key N)) (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel (.arr B) (.arr B)) (hL : L = Uc(T, N, hNk, hNv)) (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits (.arr B) (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat)) :
    (∀ xs Y, rep (LeetQ.Rel.Alg.setify X) xs Y → (∃ i, Vals.row X i = xs) ∧ Y.Nodup ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.setify X) xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  obtain ⟨h1, h2⟩ := rep_setify X hmv hmk kc vc hkc hvc hK hV hk hv kt hkt hF hw hn hs hW h63 p lo hpT hloT hpk hpv
    hlo pc hpc hc D hD htN ht63 htA htB T N hT hN0 hN hNk hNv hFk hFv L hL ku vu hku hvu huK huV huk huv
  have hl := (rep_lamOn_list mS(X) X kc vc hkc hvc hK hV hk hv kt hkt hF hw hn hs hW h63 p lo hpT hloT hpk hpv hlo
    pc hpc hc hmv D hD htN ht63 htA htB T N hT hN0 hN hNk hNv hFk hFv L hL ku vu hku hvu huK huV huk huv).1
  exact ⟨fun xs Y h => ⟨(h1 xs Y h).1, (hl xs Y h).1, (h1 xs Y h).2⟩, h2⟩

#print axioms rep_setify_list

end LeetQ.Rel.Rep
