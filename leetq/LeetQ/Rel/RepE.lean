/-
  `rep (E R X)`: `E R X` is `lamOn` of `∋ ≫ R` on `X`. The composite is named `M` by one equation `hM`, so
  `rep_lamOn`'s hypotheses are stated at `M` and never repeat `∋ ≫ R`.
-/
import LeetQ.Rel.RepPower

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Pow OpsN UnionN

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
    (hcrn : (Rel.n R).toNat < 2 ^ 63) (hcM : (Rel.n (mS(X))).toNat * (Rel.n R).toNat < min (2 ^ 63) USize.size)
    (hcA : Vals.PickFits (.arr A) (Rel.key mS(X)) ((jpairs(mS(X), R)).map Prod.fst))
    (hcC : Vals.PickFits B (Rel.val R) ((jpairs(mS(X), R)).map Prod.snd)) (xs : (Obj.arr A).El) (y : B.El) :
    rep (LeetQ.Rel.Alg.mem X ≫ R) xs y ↔ (∃ i, Vals.row X i = xs) ∧ ∃ x ∈ xs, rep R x y := by
  rw [rep_comp (LeetQ.Rel.Alg.mem X) R hcc hcrn hcM hcA hcC]
  show (∃ x, rep mS(X) xs x ∧ rep R x y) ↔ _
  simp only [rep_mem X hmv hmk]
  exact ⟨fun ⟨x, ⟨hi, hx⟩, hr⟩ => ⟨hi, x, hx, hr⟩, fun ⟨hi, x, hx, hr⟩ => ⟨x, ⟨hi, hx⟩, hr⟩⟩

#print axioms rep_memComp

/-- **`rep (E R X)`: the existential image on the arrays of `X`**: an array `E R X` gives `xs` holds exactly the
    `y` some element of `xs` `R`-relates to, and `E R X` has a row at `xs` exactly when `X` lists `xs`.
    `rep_lamOn` at `M := ∋ ≫ R` (`hM`, `rep_memComp`), `U := X`. Hypotheses: `rep_lamOn`'s at `M`, `X`, each
    code, relation and row list it builds bound to a variable by its defining equation; then `rep_memComp`'s. -/
theorem rep_E {B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) (M : Rel (.arr A) B)
    -- `rep_lamOn` at `M`, `X`
    (kc vc : Code) (hkc : kc = kcR(M)) (hvc : vc = vcR(M))
    (hK : cOK(kc, Rel.n M, Rel.key M)) (hV : cOK(vc, Rel.n M, Rel.val M))
    (hk : Vals.PickFits (.arr A) (Rel.key M) (List.range (Rel.n M).toNat))
    (hv : Vals.PickFits B (Rel.val M) (List.range (Rel.n M).toNat))
    -- the nub copies `X`'s arrays: their nested payloads and `B`'s dictionaries, general cells no input fact bounds
    (hWk : (Obj.arr A).CodesFit (#v[⟨(Rel.nub M).n, (Rel.nub M).key⟩] : Vector (Part (.arr A)) 1))
    (hW : B.CodesFit (#v[⟨(Rel.nub M).n, (Rel.nub M).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.n M).toNat < 2 ^ 63)
    -- two parts coded jointly: a generic `A`'s ALP sum and dictionaries are unbounded by `X`
    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M)))    (D : Rel (.arr A) (.arr A)) (hD : D = lD(M, X))
    -- `D`'s count is bounded only by `X`'s, a `USize`; `top`'s `cross` needs it below `2^63`
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (T N : Rel (.arr A) (.arr B)) (hT : T = lT(M))
    (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hFk : Vals.RazeFits (.arr A) (Rel.key T) (Rel.key N))
    (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel (.arr A) (.arr B)) (hL : L = Uc(T, N, hN))
    (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits (.arr A) (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat))
    (hM : M = LeetQ.Rel.Alg.mem X ≫ R)
    -- `rep_memComp` at `R`, `X`
    (hmv : Vals.PickFits (.arr A) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr A) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    (hcc : codesOK(jc(mS(X), R), jcs(mS(X), R)))
    (hcrn : (Rel.n R).toNat < 2 ^ 63) (hcM : (Rel.n (mS(X))).toNat * (Rel.n R).toNat < min (2 ^ 63) USize.size)
    (hcA : Vals.PickFits (.arr A) (Rel.key mS(X)) ((jpairs(mS(X), R)).map Prod.fst))
    (hcC : Vals.PickFits B (Rel.val R) ((jpairs(mS(X), R)).map Prod.snd)) :
    (∀ xs Y, rep (LeetQ.Rel.Alg.E R X) xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R x y) ∧
      (∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.E R X) xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  have hm : ∀ xs y, rep M xs y ↔ (∃ i, Vals.row X i = xs) ∧ ∃ x ∈ xs, rep R x y := fun xs y => by
    rw [hM]; exact rep_memComp R X hmv hmk hcc hcrn hcM hcA hcC xs y
  rw [show LeetQ.Rel.Alg.E R X = LeetQ.Rel.Alg.lamOn M X by rw [hM]; rfl]
  obtain ⟨h1, h2⟩ := rep_lamOn M X kc vc hkc hvc hK hV hk hv hWk hW h63
    pc hpc hc hmv D hD ht63 T N hT hN0 hN hFk hFv L hL ku vu hku hvu huK huV huk huv
  have h2' : ∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.lamOn M X) xs Y) ↔ ∃ i, Vals.row X i = xs := fun xs =>
    (h2 xs).trans ⟨fun h => h.elim (fun ⟨_, hb⟩ => ((hm _ _).1 hb).1) id, Or.inr⟩
  exact ⟨fun xs Y h => ⟨(h2' xs).1 ⟨Y, h⟩, fun y => (h1 xs Y h y).trans
    ((hm xs y).trans ⟨And.right, fun hy => ⟨(h2' xs).1 ⟨Y, h⟩, hy⟩⟩)⟩, h2'⟩

#print axioms rep_E

/-- **`rep (E R X)`, as lists**: `rep_E`, and the array `E R X` gives `xs` holds each of its values once
    (`rep_lamOn_list` at `M`). Hypotheses: `rep_E`'s. -/
theorem rep_E_list {B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n) (M : Rel (.arr A) B)
    -- `rep_lamOn` at `M`, `X`
    (kc vc : Code) (hkc : kc = kcR(M)) (hvc : vc = vcR(M))
    (hK : cOK(kc, Rel.n M, Rel.key M)) (hV : cOK(vc, Rel.n M, Rel.val M))
    (hk : Vals.PickFits (.arr A) (Rel.key M) (List.range (Rel.n M).toNat))
    (hv : Vals.PickFits B (Rel.val M) (List.range (Rel.n M).toNat))
    -- the nub copies `X`'s arrays: their nested payloads and `B`'s dictionaries, general cells no input fact bounds
    (hWk : (Obj.arr A).CodesFit (#v[⟨(Rel.nub M).n, (Rel.nub M).key⟩] : Vector (Part (.arr A)) 1))
    (hW : B.CodesFit (#v[⟨(Rel.nub M).n, (Rel.nub M).val⟩] : Vector (Part B) 1))
    (h63 : (Rel.n M).toNat < 2 ^ 63)
    -- two parts coded jointly: a generic `A`'s ALP sum and dictionaries are unbounded by `X`
    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M)))    (D : Rel (.arr A) (.arr A)) (hD : D = lD(M, X))
    -- `D`'s count is bounded only by `X`'s, a `USize`; `top`'s `cross` needs it below `2^63`
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (T N : Rel (.arr A) (.arr B)) (hT : T = lT(M))
    (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal B))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hFk : Vals.RazeFits (.arr A) (Rel.key T) (Rel.key N))
    (hFv : Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N))
    (L : Rel (.arr A) (.arr B)) (hL : L = Uc(T, N, hN))
    (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits (.arr A) (Rel.key L) (List.range (Rel.n L).toNat))
    (huv : Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat))
    (hM : M = LeetQ.Rel.Alg.mem X ≫ R)
    -- `rep_memComp` at `R`, `X`
    (hmv : Vals.PickFits (.arr A) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr A) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    (hcc : codesOK(jc(mS(X), R), jcs(mS(X), R)))
    (hcrn : (Rel.n R).toNat < 2 ^ 63) (hcM : (Rel.n (mS(X))).toNat * (Rel.n R).toNat < min (2 ^ 63) USize.size)
    (hcA : Vals.PickFits (.arr A) (Rel.key mS(X)) ((jpairs(mS(X), R)).map Prod.fst))
    (hcC : Vals.PickFits B (Rel.val R) ((jpairs(mS(X), R)).map Prod.snd)) :
    (∀ xs Y, rep (LeetQ.Rel.Alg.E R X) xs Y →
        (∃ i, Vals.row X i = xs) ∧ Y.Nodup ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R x y) ∧
      (∀ xs, (∃ Y, rep (LeetQ.Rel.Alg.E R X) xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  obtain ⟨h1, h2⟩ := rep_E R X M kc vc hkc hvc hK hV hk hv hWk hW h63
    pc hpc hc D hD ht63 T N hT hN0 hN hFk hFv L hL ku vu hku hvu huK huV huk huv
    hM hmv hmk hcc hcrn hcM hcA hcC
  have hl := (rep_lamOn_list M X kc vc hkc hvc hK hV hk hv hWk hW h63
    pc hpc hc hmv D hD ht63 T N hT hN0 hN hFk hFv L hL ku vu hku hvu huK huV huk huv).1
  have hE : LeetQ.Rel.Alg.E R X = LeetQ.Rel.Alg.lamOn M X := by rw [hM]; rfl
  exact ⟨fun xs Y h => ⟨(h1 xs Y h).1, (hl xs Y (hE ▸ h)).1, (h1 xs Y h).2⟩, h2⟩

#print axioms rep_E_list

end LeetQ.Rel.Rep
