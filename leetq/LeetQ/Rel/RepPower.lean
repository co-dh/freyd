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
  (Obj.codes _ (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part _) 1))[0]'(by decide)
set_option hygiene false in
scoped notation "pT(" R ")" => gather 8 (Obj.sortBy _ (Rel.nub R).val (tilLongs (Rel.nub R).n))
  (Code.gather (kcT(R)) (Obj.sortBy _ (Rel.nub R).val (tilLongs (Rel.nub R).n))).grade
set_option hygiene false in
scoped notation "loT(" R ")" => ByteArray.extract (Code.runStarts (Code.gather (kcT(R)) (pT(R)))) 0
  (ByteArray.size (Code.runStarts (Code.gather (kcT(R)) (pT(R)))) - 8)
-- the codes of a side `X`, and the rows `nub` keeps of `idU X`, whose key and value are both `X`
set_option hygiene false in
scoped notation "kcX(" X ")" => (Obj.codes _ (#v[⟨_, X⟩] : Vector (Part _) 1))[0]'(by decide)
set_option hygiene false in
scoped notation "nubX(" X ")" => (tuples.tupleIds (kcX(X)) #[kcX(X)]).2
end Pow
open Pow

/-- **`rep (τ X)`: each element of `X` to the array holding it alone**: an array `τ X` gives `a` holds exactly
    `a`, and `τ X` has a row at `a` exactly when `X` lists `a` — `rep_transpose` at `idU X`, whose key and value
    are both `X`, so `rep_nub`'s two code hypotheses are one (`hX`, `hx`). -/
theorem rep_tau {n : USize} (X : Vals A n)
    (hX : (∀ {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat),
        Column.idAt (kcX(X)).b (kcX(X)).w i = Column.idAt (kcX(X)).b (kcX(X)).w j ↔
          Vals.row X ⟨i, hi⟩ = Vals.row X ⟨j, hj⟩) ∧
      ((kcX(X)).w = 1 ∨ (kcX(X)).w = 2 ∨ (kcX(X)).w = 4 ∨ (kcX(X)).w = 8 ∨ (kcX(X)).w = 16 ∨
        (kcX(X)).w = 32 ∨ (kcX(X)).w = 64) ∧
        (kcX(X)).n = n ∧ (kcX(X)).b.size = ((kcX(X)).n.toNat * (kcX(X)).w + 7) / 8 ∧
        ((kcX(X)).w < 8 → (kcX(X)).card < USize.size ∧
          ∀ i < (kcX(X)).n.toNat, Column.idAt (kcX(X)).b (kcX(X)).w i < (kcX(X)).card))
    (hx : Vals.PickFits A X (ids (nubX(X))))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub (idU X)).n.toNat) (hj : j < (Rel.nub (idU X)).n.toNat),
      Column.idAt (kcT(idU X)).b (kcT(idU X)).w i = Column.idAt (kcT(idU X)).b (kcT(idU X)).w j ↔
        Vals.row (Rel.nub (idU X)).key ⟨i, hi⟩ = Vals.row (Rel.nub (idU X)).key ⟨j, hj⟩)
    (hw : (kcT(idU X)).w = 1 ∨ (kcT(idU X)).w = 2 ∨ (kcT(idU X)).w = 4 ∨ (kcT(idU X)).w = 8 ∨
      (kcT(idU X)).w = 16 ∨ (kcT(idU X)).w = 32 ∨ (kcT(idU X)).w = 64)
    (hn : (kcT(idU X)).n = (Rel.nub (idU X)).n)
    (hs : (kcT(idU X)).b.size = ((kcT(idU X)).n.toNat * (kcT(idU X)).w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]'(by decide)).w = 1 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 2 ∨
      ((Obj.codes B #v[x])[0]'(by decide)).w = 4 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 8 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 16 ∨
      ((Obj.codes B #v[x])[0]'(by decide)).w = 32 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 64) ∧
      ((Obj.codes B #v[x])[0]'(by decide)).b.size = (((Obj.codes B #v[x])[0]'(by decide)).n.toNat * ((Obj.codes B #v[x])[0]'(by decide)).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]'(by decide)).n = x.1)
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
-- a one-part code `c` of the `m` values `x` faithful and well formed, `rep_nub`'s `hK` form
set_option hygiene false in
scoped notation "cOK(" c ", " m ", " x ")" => ((∀ {i j : Nat} (hi : i < USize.toNat m) (hj : j < USize.toNat m),
    Column.idAt (c).b (c).w i = Column.idAt (c).b (c).w j ↔ Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
  ((c).w = 1 ∨ (c).w = 2 ∨ (c).w = 4 ∨ (c).w = 8 ∨ (c).w = 16 ∨ (c).w = 32 ∨ (c).w = 64) ∧ (c).n = m ∧
    (c).b.size = ((c).n.toNat * (c).w + 7) / 8 ∧
    ((c).w < 8 → (c).card < USize.size ∧ ∀ i < (c).n.toNat, Column.idAt (c).b (c).w i < (c).card))
-- two-part codes `cs` of the parts `ps` faithful and well formed (`RepOps`' `codesOK`)
set_option hygiene false in
scoped notation "codesOK(" cs ", " ps ")" => ((∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
    (hi : i < (ps[k]'hk).1.toNat) (hj : j < (ps[l]'hl).1.toNat),
    Column.idAt (cs[k]'hk).b (cs[k]'hk).w i = Column.idAt (cs[l]'hl).b (cs[l]'hl).w j ↔
      Vals.row (ps[k]'hk).2 ⟨i, hi⟩ = Vals.row (ps[l]'hl).2 ⟨j, hj⟩) ∧
  ∀ {k : Nat} (hk : k < 2),
    ((cs[k]'hk).w = 1 ∨ (cs[k]'hk).w = 2 ∨ (cs[k]'hk).w = 4 ∨ (cs[k]'hk).w = 8 ∨ (cs[k]'hk).w = 16 ∨
      (cs[k]'hk).w = 32 ∨ (cs[k]'hk).w = 64) ∧
    (cs[k]'hk).n = (ps[k]'hk).1 ∧ (cs[k]'hk).b.size = ((cs[k]'hk).n.toNat * (cs[k]'hk).w + 7) / 8 ∧
    ((cs[k]'hk).w < 8 → (cs[k]'hk).card < USize.size ∧
      ∀ i < (cs[k]'hk).n.toNat, Column.idAt (cs[k]'hk).b (cs[k]'hk).w i < (cs[k]'hk).card))
-- `rep_nub`'s codes of a relation `R` and the rows `nub` keeps (`RepLambda`'s `kcR`, `vcR`, `nubR`, taking `R`)
set_option hygiene false in
scoped notation "kcR(" R ")" => (Obj.codes _ (#v[⟨Rel.n R, Rel.key R⟩] : Vector (Part _) 1))[0]'(by decide)
set_option hygiene false in
scoped notation "vcR(" R ")" => (Obj.codes _ (#v[⟨Rel.n R, Rel.val R⟩] : Vector (Part _) 1))[0]'(by decide)
set_option hygiene false in
scoped notation "nubR(" R ")" => (tuples.tupleIds (kcR(R)) #[vcR(R)]).2
-- `lamOn R U`'s parts: `Λ(R)`; the elements of `U` that `R` relates to nothing; each of them to the empty array
set_option hygiene false in
scoped notation "lT(" R ")" => LeetQ.Rel.Alg.transpose R
set_option hygiene false in
scoped notation "lD(" R ", " U ")" => (LeetQ.Rel.Alg.idU U \ LeetQ.Rel.Alg.dom R)
set_option hygiene false in
scoped notation "lN(" R ", " U ", " B ")" =>
  LeetQ.Rel.Alg.top (Rel.key (LeetQ.Rel.Alg.idU U \ LeetQ.Rel.Alg.dom R)) (LeetQ.Rel.Alg.nilVal B)
-- `−`'s joint pair codes of `R`, `S` and the rows it keeps (`RepOps`' `pcs`, `pairsOK`, `misses`, taking `R`, `S`)
set_option hygiene false in
scoped notation "pcs(" R ", " S ")" =>
  (#v[⟨Rel.n R, (Rel.key R, Rel.val R)⟩, ⟨Rel.n S, (Rel.key S, Rel.val S)⟩] : Vector (Part (.prod _ _)) 2)
set_option hygiene false in
scoped notation "misses(" R ", " S ")" =>
  anti ((pairs #v[R, S])[0]'(by decide)) ((pairs #v[R, S])[1]'(by decide))
-- `∪`'s two key parts and two value parts, their raze and its codes (`RazeFoR`'s `Uc`, `kcU`, `vcU`, `nubU`,
-- taking the parts; the raze's count proofs are the hypotheses `hNk`, `hNv`)
set_option hygiene false in
scoped notation "pk(" R ", " S ")" => (#[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Array (Part _))
set_option hygiene false in
scoped notation "pv(" R ", " S ")" => (#[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.val S⟩] : Array (Part _))
set_option hygiene false in
scoped notation "Uc(" R ", " S ")" => (⟨_, Obj.raze _ (pk(R, S)) hNk, Obj.raze _ (pv(R, S)) hNv⟩ : Rel _ _)
set_option hygiene false in
scoped notation "kcU(" R ", " S ")" =>
  (Obj.codes _ (#v[⟨(Uc(R, S)).n, (Uc(R, S)).key⟩] : Vector (Part _) 1))[0]'(by decide)
set_option hygiene false in
scoped notation "vcU(" R ", " S ")" =>
  (Obj.codes _ (#v[⟨(Uc(R, S)).n, (Uc(R, S)).val⟩] : Vector (Part _) 1))[0]'(by decide)
set_option hygiene false in
scoped notation "nubU(" R ", " S ")" => (tuples.tupleIds (kcU(R, S)) #[vcU(R, S)]).2
end Pow
open Pow

-- the statement, at its every part's `rep` hypotheses, passes the default budget
set_option maxHeartbeats 1600000 in
/-- **`rep (lamOn R U)`: `Λ(R)` total on `U`**: an array `lamOn R U` gives `a` holds exactly the values `R`
    relates `a` to, and `lamOn R U` has a row at `a` exactly when `R` has a pair at `a` or `U` lists `a`.
    `rep_union_full` splits it into `Λ(R)` (`rep_transpose`) and `⊤` (`rep_top`) from the `U`-rows outside
    `dom R` (`rep_diff`, `rep_dom`) to the empty array. Hypotheses: those of each, at the parts named above. -/
theorem rep_lamOn {B : Obj} {m : USize} (R : Rel A B) (U : Vals A m)
    -- `rep_transpose` at `R`
    (hK : cOK(kcR(R), Rel.n R, Rel.key R)) (hV : cOK(vcR(R), Rel.n R, Rel.val R))
    (hk : Vals.PickFits A (Rel.key R) (ids (nubR(R)))) (hv : Vals.PickFits B (Rel.val R) (ids (nubR(R))))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub R).n.toNat) (hj : j < (Rel.nub R).n.toNat),
      Column.idAt (kcT(R)).b (kcT(R)).w i = Column.idAt (kcT(R)).b (kcT(R)).w j ↔
        Vals.row (Rel.nub R).key ⟨i, hi⟩ = Vals.row (Rel.nub R).key ⟨j, hj⟩)
    (hw : (kcT(R)).w = 1 ∨ (kcT(R)).w = 2 ∨ (kcT(R)).w = 4 ∨ (kcT(R)).w = 8 ∨
      (kcT(R)).w = 16 ∨ (kcT(R)).w = 32 ∨ (kcT(R)).w = 64)
    (hn : (kcT(R)).n = (Rel.nub R).n)
    (hs : (kcT(R)).b.size = ((kcT(R)).n.toNat * (kcT(R)).w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]'(by decide)).w = 1 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 2 ∨
      ((Obj.codes B #v[x])[0]'(by decide)).w = 4 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 8 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 16 ∨
      ((Obj.codes B #v[x])[0]'(by decide)).w = 32 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 64) ∧
      ((Obj.codes B #v[x])[0]'(by decide)).b.size = (((Obj.codes B #v[x])[0]'(by decide)).n.toNat * ((Obj.codes B #v[x])[0]'(by decide)).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]'(by decide)).n = x.1)
    (h63 : (Rel.nub R).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits A (Rel.nub R).key (ids (pT(R))))
    (hpv : Vals.PickFits B (Rel.nub R).val (ids (pT(R))))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub R).key (pT(R))).2 (ids (loT(R))))
    -- `rep_dom` at `R` (its code hypothesis is `hK`)
    (hp : Vals.PickFits A (Rel.key R) (ids (kcR(R)).groupIds.2))
    -- `rep_diff` at `idU U`, `dom R`
    (hc : codesOK(pairs #v[LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R], pcs(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R)))
    (hdk : Vals.PickFits A U (ids (misses(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R))))
    (hdv : Vals.PickFits A U (ids (misses(LeetQ.Rel.Alg.idU U, LeetQ.Rel.Alg.dom R))))
    -- `rep_top` at `lD(R, U).key`, `nilVal B`
    (htN : (Rel.n (lD(R, U))).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n (lD(R, U))).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits A (Rel.key (lD(R, U)))
      ((List.range ((Rel.n (lD(R, U))).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n (lD(R, U))).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    -- `rep_union_full` at `lT(R)`, `lN(R, U, B)`
    (hN : (Rel.n (lT(R))).toNat + (Rel.n (lN(R, U, B))).toNat < USize.size)
    (hNk : ((pk(lT(R), lN(R, U, B))).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (hNv : ((pv(lT(R), lN(R, U, B))).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits A (Rel.key (lT(R))) (Rel.key (lN(R, U, B))))
    (hFv : Vals.RazeFits (.arr B) (Rel.val (lT(R))) (Rel.val (lN(R, U, B))))
    (huK : cOK(kcU(lT(R), lN(R, U, B)), (Uc(lT(R), lN(R, U, B))).n, (Uc(lT(R), lN(R, U, B))).key))
    (huV : cOK(vcU(lT(R), lN(R, U, B)), (Uc(lT(R), lN(R, U, B))).n, (Uc(lT(R), lN(R, U, B))).val))
    (huk : Vals.PickFits A (Uc(lT(R), lN(R, U, B))).key (ids (nubU(lT(R), lN(R, U, B)))))
    (huv : Vals.PickFits (.arr B) (Uc(lT(R), lN(R, U, B))).val (ids (nubU(lT(R), lN(R, U, B))))) :
    (∀ a Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y → ∀ y, y ∈ Y ↔ rep R a y) ∧
      (∀ a, (∃ Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y) ↔ (∃ b, rep R a b) ∨ ∃ i, Vals.row U i = a) := by
  obtain ⟨h1, h2⟩ := rep_transpose R hK hV hk hv hF hw hn hs hW h63 hpk hpv hlo
  have hu := rep_union_full (lT(R)) (lN(R, U, B)) hN hNk hNv hFk hFv huK huV huk huv
  have hL : ∀ a Y, rep (LeetQ.Rel.Alg.lamOn R U) a Y ↔ rep (lT(R)) a Y ∨ rep (lN(R, U, B)) a Y := fun a Y => by
    rw [show LeetQ.Rel.Alg.lamOn R U = lT(R) ∪ lN(R, U, B) from rfl, hu]; exact Iff.rfl
  have hd : ∀ a b, rep (LeetQ.Rel.Alg.dom R) a b ↔ a = b ∧ ∃ c, rep R a c := fun a b => by
    rw [rep_dom R hK hp]; exact Iff.rfl
  have hD : ∀ a, (∃ i, Vals.row (Rel.key (lD(R, U))) i = a) ↔ (∃ i, Vals.row U i = a) ∧ ¬ ∃ c, rep R a c := by
    intro a
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨hI, hR⟩ := (rep_diff _ _ hc hdk hdv a _).1 ⟨i, hi, rfl⟩
      obtain ⟨e, hU⟩ := (idU_holds U _ _).1 hI
      exact ⟨hU, fun hc' => hR ((hd _ _).2 ⟨e, hc'⟩)⟩
    · rintro ⟨hU, hR⟩
      obtain ⟨i, hi, -⟩ := (rep_diff _ _ hc hdk hdv a a).2
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
    Column.idAt ((jc(R, S))[1]'(by decide)).b ((jc(R, S))[1]'(by decide)).w j ==
      Column.idAt ((jc(R, S))[0]'(by decide)).b ((jc(R, S))[0]'(by decide)).w i).map (i, ·))
set_option hygiene false in
scoped notation "jcount(" R ", " S ")" => ((List.range (Rel.n R).toNat).map fun i =>
  ((List.range (Rel.n S).toNat).filter fun j =>
    Column.idAt ((jc(R, S))[1]'(by decide)).b ((jc(R, S))[1]'(by decide)).w j ==
      Column.idAt ((jc(R, S))[0]'(by decide)).b ((jc(R, S))[0]'(by decide)).w i).length).sum
end Pow
open Pow

-- the statement, at `rep_lamOn`'s hypotheses, passes the default budget
set_option maxHeartbeats 1600000 in
/-- **`rep (setify X)`: each array of `X` to the array of its elements**: an array `setify X` gives `xs` holds
    exactly the elements of `xs`, and `setify X` has a row at `xs` exactly when `X` lists `xs`. `rep_lamOn` at
    `R := ∋` on `X` (`rep_mem`), `U := X`. Hypotheses: `rep_mem`'s (`hmv`, `hmk`), then `rep_lamOn`'s there. -/
theorem rep_setify {B : Obj} {n : USize} (X : Vals (.arr B) n)
    -- `rep_mem` at `X`
    (hmv : Vals.PickFits (.arr B) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    -- `rep_lamOn` at `mS(X)`, `X`
    (hK : cOK(kcR(mS(X)), Rel.n mS(X), Rel.key mS(X))) (hV : cOK(vcR(mS(X)), Rel.n mS(X), Rel.val mS(X)))
    (hk : Vals.PickFits (.arr B) (Rel.key mS(X)) (ids (nubR(mS(X)))))
    (hv : Vals.PickFits B (Rel.val mS(X)) (ids (nubR(mS(X)))))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub mS(X)).n.toNat) (hj : j < (Rel.nub mS(X)).n.toNat),
      Column.idAt (kcT(mS(X))).b (kcT(mS(X))).w i = Column.idAt (kcT(mS(X))).b (kcT(mS(X))).w j ↔
        Vals.row (Rel.nub mS(X)).key ⟨i, hi⟩ = Vals.row (Rel.nub mS(X)).key ⟨j, hj⟩)
    (hw : (kcT(mS(X))).w = 1 ∨ (kcT(mS(X))).w = 2 ∨ (kcT(mS(X))).w = 4 ∨ (kcT(mS(X))).w = 8 ∨
      (kcT(mS(X))).w = 16 ∨ (kcT(mS(X))).w = 32 ∨ (kcT(mS(X))).w = 64)
    (hn : (kcT(mS(X))).n = (Rel.nub mS(X)).n)
    (hs : (kcT(mS(X))).b.size = ((kcT(mS(X))).n.toNat * (kcT(mS(X))).w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]'(by decide)).w = 1 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 2 ∨
      ((Obj.codes B #v[x])[0]'(by decide)).w = 4 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 8 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 16 ∨
      ((Obj.codes B #v[x])[0]'(by decide)).w = 32 ∨ ((Obj.codes B #v[x])[0]'(by decide)).w = 64) ∧
      ((Obj.codes B #v[x])[0]'(by decide)).b.size = (((Obj.codes B #v[x])[0]'(by decide)).n.toNat * ((Obj.codes B #v[x])[0]'(by decide)).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]'(by decide)).n = x.1)
    (h63 : (Rel.nub mS(X)).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits (.arr B) (Rel.nub mS(X)).key (ids (pT(mS(X)))))
    (hpv : Vals.PickFits B (Rel.nub mS(X)).val (ids (pT(mS(X)))))
    (hlo : Vals.PickFits (.arr B) (Vals.pickPart (.arr B) (Rel.nub mS(X)).key (pT(mS(X)))).2 (ids (loT(mS(X)))))
    (hp : Vals.PickFits (.arr B) (Rel.key mS(X)) (ids (kcR(mS(X))).groupIds.2))
    (hc : codesOK(pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X)],
      pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X))))
    (hdk : Vals.PickFits (.arr B) X (ids (misses(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X)))))
    (hdv : Vals.PickFits (.arr B) X (ids (misses(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom mS(X)))))
    (htN : (Rel.n (lD(mS(X), X))).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n (lD(mS(X), X))).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits (.arr B) (Rel.key (lD(mS(X), X)))
      ((List.range ((Rel.n (lD(mS(X), X))).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n (lD(mS(X), X))).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    (hN : (Rel.n (lT(mS(X)))).toNat + (Rel.n (lN(mS(X), X, B))).toNat < USize.size)
    (hNk : ((pk(lT(mS(X)), lN(mS(X), X, B))).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(lT(mS(X)), lN(mS(X), X, B))).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.arr B) (Rel.key (lT(mS(X)))) (Rel.key (lN(mS(X), X, B))))
    (hFv : Vals.RazeFits (.arr B) (Rel.val (lT(mS(X)))) (Rel.val (lN(mS(X), X, B))))
    (huK : cOK(kcU(lT(mS(X)), lN(mS(X), X, B)), (Uc(lT(mS(X)), lN(mS(X), X, B))).n,
      (Uc(lT(mS(X)), lN(mS(X), X, B))).key))
    (huV : cOK(vcU(lT(mS(X)), lN(mS(X), X, B)), (Uc(lT(mS(X)), lN(mS(X), X, B))).n,
      (Uc(lT(mS(X)), lN(mS(X), X, B))).val))
    (huk : Vals.PickFits (.arr B) (Uc(lT(mS(X)), lN(mS(X), X, B))).key (ids (nubU(lT(mS(X)), lN(mS(X), X, B)))))
    (huv : Vals.PickFits (.arr B) (Uc(lT(mS(X)), lN(mS(X), X, B))).val (ids (nubU(lT(mS(X)), lN(mS(X), X, B))))) :
    (∀ xs Y, rep (LeetQ.Rel.Alg.setify X) xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.setify X) xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  obtain ⟨h1, h2⟩ := rep_lamOn mS(X) X hK hV hk hv hF hw hn hs hW h63 hpk hpv hlo hp hc hdk hdv htN ht63 htA htB
    hN hNk hNv hFk hFv huK huV huk huv
  have hm := rep_mem X hmv hmk
  have h2' : ∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.setify X) xs Y) ↔ ∃ i, Vals.row X i = xs := fun xs =>
    (h2 xs).trans ⟨fun h => h.elim (fun ⟨_, hb⟩ => ((hm _ _).1 hb).1) id, Or.inr⟩
  exact ⟨fun xs Y h => ⟨(h2' xs).1 ⟨Y, h⟩, fun y => (h1 xs Y h y).trans
    ((hm xs y).trans ⟨And.right, fun hy => ⟨(h2' xs).1 ⟨Y, h⟩, hy⟩⟩)⟩, h2'⟩

#print axioms rep_setify

end LeetQ.Rel.Rep
