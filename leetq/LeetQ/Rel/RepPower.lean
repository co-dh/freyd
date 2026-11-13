/-
  `rep` of the power side's ops built on `Λ` (`transpose`), read in `Rel(Set)`. `Λ` itself is `rep_transpose`
  (`RepLambda`): defined only on `dom R`, a key outside it has no row.
-/
import LeetQ.Rel.RepLambda

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A : Obj}

-- `transpose`'s pieces at a relation `R` (`RepLambda`'s `kcT`, `pT`, `loT`, as notations taking `R`)
set_option hygiene false in
local notation "kcT(" R ")" => (Obj.codes _ (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part _) 1))[0]
set_option hygiene false in
local notation "pT(" R ")" => gather 8 (Obj.sortBy _ (Rel.nub R).val (tilLongs (Rel.nub R).n))
  (Code.gather (kcT(R)) (Obj.sortBy _ (Rel.nub R).val (tilLongs (Rel.nub R).n))).grade
set_option hygiene false in
local notation "loT(" R ")" => ByteArray.extract (Code.runStarts (Code.gather (kcT(R)) (pT(R)))) 0
  (ByteArray.size (Code.runStarts (Code.gather (kcT(R)) (pT(R)))) - 8)
-- the codes of a side `X`, and the rows `nub` keeps of `idU X`, whose key and value are both `X`
set_option hygiene false in
local notation "kcX(" X ")" => (Obj.codes _ (#v[⟨_, X⟩] : Vector (Part _) 1))[0]
set_option hygiene false in
local notation "nubX(" X ")" => (tuples.tupleIds (kcX(X)) #[kcX(X)]).2

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
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]).w = 1 ∨ ((Obj.codes B #v[x])[0]).w = 2 ∨
      ((Obj.codes B #v[x])[0]).w = 4 ∨ ((Obj.codes B #v[x])[0]).w = 8 ∨ ((Obj.codes B #v[x])[0]).w = 16 ∨
      ((Obj.codes B #v[x])[0]).w = 32 ∨ ((Obj.codes B #v[x])[0]).w = 64) ∧
      ((Obj.codes B #v[x])[0]).b.size = (((Obj.codes B #v[x])[0]).n.toNat * ((Obj.codes B #v[x])[0]).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]).n = x.1)
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

end LeetQ.Rel.Rep
