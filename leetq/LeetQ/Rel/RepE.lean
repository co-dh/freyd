/-
  `rep (E R X)`: `E R X` is `lamOn` of `∋ ≫ R` on `X`. The composite is named `M` by one equation `hM`, so
  `rep_lamOn`'s hypotheses are stated at `M` and never repeat `∋ ≫ R`.
-/
import LeetQ.Rel.RepPower

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Pow

variable {A : Obj}

/-- **`rep (∋ ≫ R)` on `X`**: `∋` on `X` followed by `R` relates `xs` to `y` exactly when `X` lists `xs` and some
    element of `xs` `R`-relates to `y`. `rep_comp` at `mS(X)`, `R`, then `rep_mem`. Hypotheses: those of each. -/
theorem rep_memComp {B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n)
    -- `rep_mem` at `X`
    (hmv : Vals.PickFits (.arr A) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr A) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    -- `rep_comp` at `mS(X)`, `R`
    (hcc : codesOK(jc(mS(X), R), jcs(mS(X), R)))
    (hcrn : (Rel.n R).toNat < 2 ^ 63) (hcM : jcount(mS(X), R) < 2 ^ 63) (hcMU : jcount(mS(X), R) < USize.size)
    (hcA : Vals.PickFits (.arr A) (Rel.key mS(X)) ((jpairs(mS(X), R)).map Prod.fst))
    (hcC : Vals.PickFits B (Rel.val R) ((jpairs(mS(X), R)).map Prod.snd)) (xs : (Obj.arr A).El) (y : B.El) :
    rep (LeetQ.Rel.Alg.mem X ≫ R) xs y ↔ (∃ i, Vals.row X i = xs) ∧ ∃ x ∈ xs, rep R x y := by
  rw [rep_comp (LeetQ.Rel.Alg.mem X) R hcc hcrn hcM hcMU hcA hcC]
  show (∃ x, rep mS(X) xs x ∧ rep R x y) ↔ _
  simp only [rep_mem X hmv hmk]
  exact ⟨fun ⟨x, ⟨hi, hx⟩, hr⟩ => ⟨hi, x, hx, hr⟩, fun ⟨hi, x, hx, hr⟩ => ⟨x, ⟨hi, hx⟩, hr⟩⟩

#print axioms rep_memComp

-- the statement, at `rep_lamOn`'s hypotheses, passes the default budget
set_option maxHeartbeats 1600000 in
/-- **`rep (E R X)`: the existential image on the arrays of `X`**: an array `E R X` gives `xs` holds exactly the
    `y` some element of `xs` `R`-relates to, and `E R X` has a row at `xs` exactly when `X` lists `xs`.
    `rep_lamOn` at `M := ∋ ≫ R` (`hM`, `rep_memComp`), `U := X`. Hypotheses: `rep_memComp`'s, then `rep_lamOn`'s
    at `M`, `X`. -/
theorem rep_E {B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) (M : Rel (.arr A) B)
    -- `rep_lamOn` at `M`, `X`
    (hK : cOK(kcR(M), Rel.n M, Rel.key M)) (hV : cOK(vcR(M), Rel.n M, Rel.val M))
    (hk : Vals.PickFits (.arr A) (Rel.key M) (ids (nubR(M)))) (hv : Vals.PickFits B (Rel.val M) (ids (nubR(M))))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub M).n.toNat) (hj : j < (Rel.nub M).n.toNat),
      Column.idAt (kcT(M)).b (kcT(M)).w i = Column.idAt (kcT(M)).b (kcT(M)).w j ↔
        Vals.row (Rel.nub M).key ⟨i, hi⟩ = Vals.row (Rel.nub M).key ⟨j, hj⟩)
    (hw : (kcT(M)).w = 1 ∨ (kcT(M)).w = 2 ∨ (kcT(M)).w = 4 ∨ (kcT(M)).w = 8 ∨
      (kcT(M)).w = 16 ∨ (kcT(M)).w = 32 ∨ (kcT(M)).w = 64)
    (hn : (kcT(M)).n = (Rel.nub M).n)
    (hs : (kcT(M)).b.size = ((kcT(M)).n.toNat * (kcT(M)).w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]).w = 1 ∨ ((Obj.codes B #v[x])[0]).w = 2 ∨
      ((Obj.codes B #v[x])[0]).w = 4 ∨ ((Obj.codes B #v[x])[0]).w = 8 ∨ ((Obj.codes B #v[x])[0]).w = 16 ∨
      ((Obj.codes B #v[x])[0]).w = 32 ∨ ((Obj.codes B #v[x])[0]).w = 64) ∧
      ((Obj.codes B #v[x])[0]).b.size = (((Obj.codes B #v[x])[0]).n.toNat * ((Obj.codes B #v[x])[0]).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]).n = x.1)
    (h63 : (Rel.nub M).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits (.arr A) (Rel.nub M).key (ids (pT(M))))
    (hpv : Vals.PickFits B (Rel.nub M).val (ids (pT(M))))
    (hlo : Vals.PickFits (.arr A) (Vals.pickPart (.arr A) (Rel.nub M).key (pT(M))).2 (ids (loT(M))))
    (hp : Vals.PickFits (.arr A) (Rel.key M) (ids (kcR(M)).groupIds.2))
    (hc : codesOK(pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M], pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M)))
    (hdk : Vals.PickFits (.arr A) X (ids (misses(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M))))
    (hdv : Vals.PickFits (.arr A) X (ids (misses(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M))))
    (htN : (Rel.n (lD(M, X))).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n (lD(M, X))).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits (.arr A) (Rel.key (lD(M, X)))
      ((List.range ((Rel.n (lD(M, X))).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr B) (LeetQ.Rel.Alg.nilVal B)
      ((List.range ((Rel.n (lD(M, X))).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    (hN : (Rel.n (lT(M))).toNat + (Rel.n (lN(M, X, B))).toNat < USize.size)
    (hNk : ((pk(lT(M), lN(M, X, B))).toList.map fun c : Part (.arr A) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(lT(M), lN(M, X, B))).toList.map fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.arr A) (Rel.key (lT(M))) (Rel.key (lN(M, X, B))))
    (hFv : Vals.RazeFits (.arr B) (Rel.val (lT(M))) (Rel.val (lN(M, X, B))))
    (huK : cOK(kcU(lT(M), lN(M, X, B)), (Uc(lT(M), lN(M, X, B))).n, (Uc(lT(M), lN(M, X, B))).key))
    (huV : cOK(vcU(lT(M), lN(M, X, B)), (Uc(lT(M), lN(M, X, B))).n, (Uc(lT(M), lN(M, X, B))).val))
    (huk : Vals.PickFits (.arr A) (Uc(lT(M), lN(M, X, B))).key (ids (nubU(lT(M), lN(M, X, B)))))
    (huv : Vals.PickFits (.arr B) (Uc(lT(M), lN(M, X, B))).val (ids (nubU(lT(M), lN(M, X, B)))))
    (hM : M = LeetQ.Rel.Alg.mem X ≫ R)
    -- `rep_memComp` at `R`, `X`
    (hmv : Vals.PickFits (.arr A) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr A) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    (hcc : codesOK(jc(mS(X), R), jcs(mS(X), R)))
    (hcrn : (Rel.n R).toNat < 2 ^ 63) (hcM : jcount(mS(X), R) < 2 ^ 63) (hcMU : jcount(mS(X), R) < USize.size)
    (hcA : Vals.PickFits (.arr A) (Rel.key mS(X)) ((jpairs(mS(X), R)).map Prod.fst))
    (hcC : Vals.PickFits B (Rel.val R) ((jpairs(mS(X), R)).map Prod.snd)) :
    (∀ xs Y, rep (LeetQ.Rel.Alg.E R X) xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R x y) ∧
      (∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.E R X) xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  have hm : ∀ xs y, rep M xs y ↔ (∃ i, Vals.row X i = xs) ∧ ∃ x ∈ xs, rep R x y := fun xs y => by
    rw [hM]; exact rep_memComp R X hmv hmk hcc hcrn hcM hcMU hcA hcC xs y
  rw [show LeetQ.Rel.Alg.E R X = LeetQ.Rel.Alg.lamOn M X by rw [hM]; rfl]
  obtain ⟨h1, h2⟩ := rep_lamOn M X hK hV hk hv hF hw hn hs hW h63 hpk hpv hlo hp hc hdk hdv htN ht63 htA htB
    hN hNk hNv hFk hFv huK huV huk huv
  have h2' : ∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.lamOn M X) xs Y) ↔ ∃ i, Vals.row X i = xs := fun xs =>
    (h2 xs).trans ⟨fun h => h.elim (fun ⟨_, hb⟩ => ((hm _ _).1 hb).1) id, Or.inr⟩
  exact ⟨fun xs Y h => ⟨(h2' xs).1 ⟨Y, h⟩, fun y => (h1 xs Y h y).trans
    ((hm xs y).trans ⟨And.right, fun hy => ⟨(h2' xs).1 ⟨Y, h⟩, hy⟩⟩)⟩, h2'⟩

#print axioms rep_E

end LeetQ.Rel.Rep
