/-
  Capacity checked at run time, correctness proved, for the power side's ops built on `Λ`: `τ`, `lamOn`, `setify`,
  `E`. Each twin's bit is the `&&` of the bits of the twins it runs, and decides every capacity
  premise of the op's read-back (`rep_tau`, `rep_lamOn`, …), so `rep_τC` … `rep_EC` hold under that bit alone.
-/
import LeetQ.Rel.CRelRel
import LeetQ.Run.CRelRelDef
import LeetQ.Rel.RepEst
import LeetQ.Run.CRelPowerDef
import LeetQ.Rel.KernelWF.AscSpec
import LeetQ.Rel.RepPrim
import LeetQ.Rel.CRelArith

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Pow OpsN UnionN

variable {A B K : Obj}

/-- **`unionC`'s bit is `rep_union_full`'s premises**: `need`'s guard its `hN`, the razes' bits its `hFk`, `hFv`
    (`razeC_fits`), the codes' bits its `hK`, `hV` (`oneOK_of_codesC`), the `fitsN` bits its `hk`, `hv`. -/
theorem unionC_ok (R S : Rel A B) (hb : (unionC R S).2 = true) :
    ∃ hN : R.n.toNat + S.n.toNat < USize.size, Vals.RazeFits A R.key S.key ∧ Vals.RazeFits B R.val S.val ∧
      cOK(kcR(Uc(R, S, hN)), Rel.n (Uc(R, S, hN)), Rel.key (Uc(R, S, hN))) ∧
      cOK(vcR(Uc(R, S, hN)), Rel.n (Uc(R, S, hN)), Rel.val (Uc(R, S, hN))) ∧
      Vals.PickFits A (Rel.key (Uc(R, S, hN))) (List.range (Rel.n (Uc(R, S, hN))).toNat) ∧
      Vals.PickFits B (Rel.val (Uc(R, S, hN))) (List.range (Rel.n (Uc(R, S, hN))).toNat) := by
  unfold unionC need at hb
  split at hb
  · rename_i hN
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hb
    have hFk := Obj.razeC_fits A R.key S.key _ rfl _ hka
    have hFv := Obj.razeC_fits B R.val S.val _ rfl _ hvb
    simp only [razeC_fst] at hkc hvc hkf hvf
    exact ⟨hN, hFk, hFv, oneOK_of_codesC A _ hkc, oneOK_of_codesC B _ hvc,
      pickFits_of_fitsN A _ _ hkf _ (by simp only [List.length_range]; exact Nat.le_refl _),
      pickFits_of_fitsN B _ _ hvf _ (by simp only [List.length_range]; exact Nat.le_refl _)⟩
  · exact absurd hb Bool.false_ne_true

/-- **`rep (τ X)` under `τC`'s bit**: `rep_tau` at `transposeC_ok`'s premises at `idU X`, whose key and value are
    both `X`. -/
theorem rep_τC {n : USize} (X : Vals A n) (hb : (τC X).2 = true) :
    (∀ a Y, rep (τC X).1 a Y → ∀ x, x ∈ Y ↔ x = a) ∧ (∀ a, (∃ Y, rep (τC X).1 a Y) ↔ ∃ i, Vals.row X i = a) := by
  obtain ⟨hX, -, hx, -, hWk, hW, h63⟩ := transposeC_ok (idU X) hb
  exact rep_tau X hX hx hWk hW h63

/-- **`rep (lamOnByC o R U)` under its bit**, `o` listing each nub row once where its bit holds (`ho`): `rep_lamOn`
    at the intermediates `lamOnByC` builds, each defining equation `rfl` but the transpose's (`transposeBy_eq`).
    `transposeByC_ok` gives `hK`…`h63`, `diffC`'s bit `hc` (`codes_faithful_wf`, `pairs_eq_codes`) and `hdU`, `topC`'s
    `ht63`, `unionC_ok` `hN`…`huv`. -/
theorem rep_lamOnByC {m : USize} (o : Rel A B → ByteArray × Bool)
    (ho : ∀ d, (o d).2 = true → (ids (o d).1).Perm (List.range d.n.toNat)) (R : Rel A B) (U : Vals A m)
    (hb : (lamOnByC o R U).2 = true) :
    (∀ a Y, rep (lamOnByC o R U).1 a Y → ∀ y, y ∈ Y ↔ rep R a y) ∧
      (∀ a, (∃ Y, rep (lamOnByC o R U).1 a Y) ↔ (∃ b, rep R a b) ∨ ∃ i, Vals.row U i = a) ∧
      ∀ a Y, rep (lamOnByC o R U).1 a Y → rep (transposeByC o R).1 a Y ∨ Y = [] := by
  simp only [lamOnByC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨ht, -⟩, hd⟩, hn⟩, hu⟩ := hb
  obtain ⟨hK, hV, hk, hv, hWk, hW, h63⟩ := transposeByC_ok o R ht
  simp only [diffC, Bool.and_eq_true] at hd
  obtain ⟨⟨hcb, hdU⟩, -⟩ := hd
  have hc := (codes_faithful_wf (.prod A A) _ (Obj.codesC_fits (.prod A A) _ hcb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  have hp : pairsOK(idU U, dom R) := by rw [pairs_eq_codes, e]; exact hc
  simp only [topC, Bool.and_eq_true, decide_eq_true_eq] at hn
  obtain ⟨⟨⟨-, ht63⟩, -⟩, -⟩ := hn
  obtain ⟨hN, hFk, hFv, huK, huV, huk, huv⟩ := unionC_ok _ _ hu
  exact rep_lamOn R U _ _ rfl rfl hK hV hk hv hWk _ (ho _ hW) h63 _ rfl hp
    (pickFits_of_fitsN A (idU U).key _ hdU _ (by simp only [List.length_range]; exact Nat.le_refl _)) _ rfl ht63 _ _ (transposeBy_eq o R) rfl hN hFk hFv _ rfl _ _ rfl rfl
    huK huV huk huv

/-- `lamOnByC o M X` on rows of `X` when `M` relates only rows of `X`: an array it gives `xs` holds exactly the `y`
    with `P xs y`, and it has a row at `xs` exactly when `X` lists `xs`. -/
theorem rep_lamOnByC_rows {n : USize} (o : Rel K B → ByteArray × Bool)
    (ho : ∀ d, (o d).2 = true → (ids (o d).1).Perm (List.range d.n.toNat)) (M : Rel K B) (X : Vals K n)
    (P : K.El → B.El → Prop) (hm : ∀ xs y, rep M xs y ↔ (∃ i, Vals.row X i = xs) ∧ P xs y)
    (hb : (lamOnByC o M X).2 = true) :
    (∀ xs Y, rep (lamOnByC o M X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ P xs y) ∧
      (∀ xs, (∃ Y, rep (lamOnByC o M X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  obtain ⟨h1, h2, -⟩ := rep_lamOnByC o ho M X hb
  have h2' : ∀ xs, (∃ Y, rep (lamOnByC o M X).1 xs Y) ↔ ∃ i, Vals.row X i = xs := fun xs =>
    (h2 xs).trans ⟨fun h => h.elim (fun ⟨_, hb⟩ => ((hm _ _).1 hb).1) id, Or.inr⟩
  exact ⟨fun xs Y h => ⟨(h2' xs).1 ⟨Y, h⟩, fun y => (h1 xs Y h y).trans
    ((hm xs y).trans ⟨And.right, fun hy => ⟨(h2' xs).1 ⟨Y, h⟩, hy⟩⟩)⟩, h2'⟩

/-- **`rep (setify X)` under `setifyC`'s bit**: `rep_lamOnByC_rows` at `∋` on `X` (`rep_memC`). -/
theorem rep_setifyC {n : USize} (X : Vals (.arr B) n) (hb : (setifyC X).2 = true) :
    (∀ xs Y, rep (setifyC X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (setifyC X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  simp only [setifyC, Bool.and_eq_true] at hb
  exact rep_lamOnByC_rows valSortC valSortC_perm _ X (fun xs y => y ∈ xs) (rep_memC X hb.1) hb.2

/-- **`Λ(R)`'s arrays are ascending and duplicate-free**, `B` ordered: each is `R.nub`'s values at a sublist of
    `sortBy`'s permutation of its rows (`rep_transpose_list`), which lists them ascending (`sortBy_asc`). -/
theorem transposeC_asc (R : Rel A B) (hB : B.Ordered) (hb : (transposeC R).2 = true) :
    ∀ a X, rep (transposeC R).1 a X → X.Nodup ∧ X.Pairwise fun x y => ¬ B.lt y x := by
  obtain ⟨hK, hV, hk, hv, hWk, hW, h63⟩ := transposeC_ok R hb
  intro a X h
  obtain ⟨hnd, -, L, hL, -, rfl⟩ := (rep_transpose_list R hK hV hk hv hWk _ (sortBy_nub_perm _ hW) _ (transpose_eq _) h63).1 a X h
  refine ⟨hnd, ?_⟩
  have hs := (sortBy_asc (sortsAsc_all B hB) (Rel.nub R).val
    (small_of_pickFits B _ _ (nub_pickFits R hK hV hk hv).2) (tilLongs (Rel.nub R).n)
    (by rw [len_tilLongs]; exact (Rel.nub R).n.toNat_lt_size)
    (fun i h => by rw [ids_tilLongs] at h; exact List.mem_range.1 h)).sublist hL
  rw [List.pairwise_map] at hs ⊢
  exact hs.imp fun h => h _ _

/-- **`Λ(R)` total on `U` gives ascending, duplicate-free arrays**, `B` ordered: `Λ(R)`'s (`transposeC_asc`) and
    the empty arrays of the elements of `U` that `R` relates to nothing. -/
theorem lamOnC_asc {m : USize} (R : Rel A B) (U : Vals A m) (hB : B.Ordered) (hb : (lamOnC R U).2 = true) :
    ∀ a Y, rep (lamOnC R U).1 a Y → Y.Nodup ∧ Y.Pairwise fun x y => ¬ B.lt y x := by
  simp only [lamOnC, lamOnByC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨ht, -⟩, -⟩, hn⟩, hu⟩ := hb
  intro a Y h
  simp only [lamOnC, lamOnByC] at h
  rw [rep_unionC _ _ hu] at h
  rcases h with h | h
  · exact transposeC_asc R hB ht a Y h
  · rw [rep_topC _ _ hn] at h
    simp only [comp_apply] at h
    obtain ⟨_, -, _, -, rfl, j, hj⟩ := h
    rw [nilVal_row] at hj
    subst hj
    exact ⟨List.nodup_nil, List.Pairwise.nil⟩

/-- **`setify` lists each set's elements ascending, each once**, `B` ordered: `lamOnC_asc` at `∋` on `X`. -/
theorem setifyC_asc {n : USize} (X : Vals (.arr B) n) (hB : B.Ordered) (hb : (setifyC X).2 = true) :
    ∀ xs Y, rep (setifyC X).1 xs Y → Y.Nodup ∧ Y.Pairwise fun x y => ¬ B.lt y x := by
  simp only [setifyC, Bool.and_eq_true] at hb
  exact lamOnC_asc _ X hB hb.2

/-- **`rep (E R X)` under `EC`'s bit**: `rep_lamOnByC_rows` at `∋ ≫ R` on `X` (`rep_compC`, `rep_memC`). -/
theorem rep_EC {n : USize} (R : Rel A B) (X : Vals (.arr A) n) (hb : (EC R X).2 = true) :
    (∀ xs Y, rep (EC R X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R x y) ∧
      (∀ xs, (∃ Y, rep (EC R X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  simp only [EC, Bool.and_eq_true] at hb
  obtain ⟨⟨hm, hc⟩, hl⟩ := hb
  refine rep_lamOnByC_rows valSortC valSortC_perm _ X (fun xs y => ∃ x ∈ xs, rep R x y) (fun xs y => ?_) hl
  rw [rep_compC _ R hc]
  show (∃ x, rep (memC X).1 xs x ∧ rep R x y) ↔ _
  simp only [rep_memC X hm]
  exact ⟨fun ⟨x, ⟨hi, hx⟩, hr⟩ => ⟨hi, x, hx, hr⟩, fun ⟨hi, x, hx, hr⟩ => ⟨x, ⟨hi, hx⟩, hr⟩⟩

/-- **`rep (distinct X)` under `distinctC`'s bit: each array of `X` with its repeats erased**, first occurrences in
    order. `distinct` is `Λ(∋)` on `X` with the nub's rows in their own order (`tilLongs`): an array it gives `xs`
    is empty for an empty `xs` (`rep_lamOnByC_rows`), else `∋`'s nub values at the nub rows keyed `xs`, in row order
    (`rep_transpose_list`); those rows are `mem X`'s rows with repeats erased (`nub_rows`, `mem_rows`), whose rows
    keyed `xs` are copies of `xs` paired with each element (`eraseDups_flatten_copies`). -/
theorem rep_distinctC [DecidableEq B.El] {n : USize} (X : Vals (.arr B) n) (hb : (distinctC X).2 = true) :
    (∀ xs Y, rep (distinctC X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ Y = xs.eraseDups) ∧
      (∀ xs, (∃ Y, rep (distinctC X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  simp only [distinctC, Bool.and_eq_true] at hb
  obtain ⟨hm, hl⟩ := hb
  let o : Rel (.arr B) B → ByteArray × Bool := fun d => (tilLongs d.n, true)
  have ho : ∀ d, (o d).2 = true → (ids (o d).1).Perm (List.range d.n.toNat) := fun d _ => by
    simp only [o, ids_tilLongs]; exact List.Perm.refl _
  obtain ⟨h1, h2⟩ := rep_lamOnByC_rows o ho _ X (fun xs y => y ∈ xs) (rep_memC X hm) hl
  obtain ⟨-, -, h3⟩ := rep_lamOnByC o ho _ X hl
  refine ⟨fun xs Y h => ⟨(h1 xs Y h).1, ?_⟩, h2⟩
  obtain ⟨⟨i, hi⟩, hY⟩ := h1 xs Y h
  rcases h3 xs Y h with ht | rfl
  · -- the transpose's array: `∋`'s nub values at the nub rows keyed `xs`, in row order
    let M := (memC X).1
    have htb : (transposeByC o M).2 = true := by simp only [lamOnByC, Bool.and_eq_true] at hl; exact hl.1.1.1.1
    obtain ⟨hK, hV, hk, hv, hWk, -, h63⟩ := transposeByC_ok o M htb
    obtain ⟨-, -, L, hL, hLi, rfl⟩ :=
      (rep_transpose_list M hK hV hk hv hWk _ (ho _ rfl) _ (transposeBy_eq o M) h63).1 xs Y ht
    -- `L` is the nub rows keyed `xs`, ascending: both ascending with the same members
    have hLs : L.Pairwise (· < ·) := by
      simp only [o, ids_tilLongs] at hL
      have hs := List.Pairwise.sublist hL (List.pairwise_lt_range (n := (Rel.nub M).n.toNat))
      have hs' := List.pairwise_map.1 hs; exact hs'
    have hF : ((List.finRange (Rel.nub M).n.toNat).filter fun t => (Rel.nub M).key.row t = xs).Pairwise (· < ·) :=
      (finRange_pairwise_lt _).filter _
    have eL : L = (List.finRange (Rel.nub M).n.toNat).filter fun t => (Rel.nub M).key.row t = xs := by
      refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (Fin.lt_trans h1 h2) (Fin.lt_irrefl _)) hLs hF ?_
      refine List.perm_iff_count.2 fun t => ?_
      rw [List.Nodup.count (hLs.imp Fin.ne_of_lt), List.Nodup.count (hF.imp Fin.ne_of_lt)]
      simp [hLi]
    -- the nub's pairs keyed `xs`, read off `mem X`'s rows with repeats erased
    obtain ⟨hmv, hmk⟩ := memC_ok X hm
    have hmr : (List.range (Rel.n M).toNat).map (fun t => if h : t < (Rel.n M).toNat then
        (M.key.row ⟨t, h⟩, M.val.row ⟨t, h⟩) else ((Obj.arr B).dflt, B.dflt)) =
        (List.range n.toNat).flatMap fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).map (X.row ⟨r, h⟩, ·) else [] :=
      mem_rows X hmv hmk
    have hrows := nub_rows M hK hV hk hv
    rw [hmr] at hrows
    have hfl := congrArg (fun l => (l.filter fun p => p.1 = xs).map Prod.snd) hrows
    simp only [List.filter_map, List.map_map, Function.comp_def] at hfl
    rw [eL]
    refine hfl.trans ?_
    -- each row of `X` gives its copies of `xs` paired with each element, or none; `nub_rows`' equality on arrays
    letI : BEq (Obj.arr B).El := instBEqOfDecidableEq
    rw [← eraseDups_filter, List.filter_flatMap, List.flatMap_def,
      eraseDups_flatten_copies (xs.map (xs, ·)) _ ?_ ?_, eraseDups_map (xs, ·) (fun a b h => (Prod.mk.inj h).2),
      List.map_map]
    · simp [Function.comp_def]
    · simp only [List.mem_map, List.mem_range]
      rintro c ⟨r, hr, rfl⟩
      rw [dif_pos hr]
      by_cases e : X.row ⟨r, hr⟩ = xs
      · left; subst e; simp [List.filter_map, Function.comp_def]; rw [List.filter_eq_self.2 fun _ _ => rfl]
      · right; simp [List.filter_map, Function.comp_def, e]
    · subst hi
      exact List.mem_map.2 ⟨i.1, List.mem_range.2 i.2, by rw [dif_pos i.2]; simp [List.filter_map, Function.comp_def]; rw [List.filter_eq_self.2 fun _ _ => rfl]⟩
  · cases xs with
    | nil => rfl
    | cons x _ => exact absurd ((hY x).2 (by simp)) (by simp)

/-- **`setify` is `distinct` then `asc`**, `B` ordered with an injective key: both sides relate `xs` to the arrays
    holding `xs`'s elements once each, ascending, and two such are equal (`List.Perm.eq_of_pairwise`, its
    antisymmetry `Obj.eq_of_not_lt`). `setify`'s from `rep_setifyC`, `setifyC_asc`; `distinct`'s `xs.eraseDups`
    (`rep_distinctC`), a row of its values, which `asc` sorts (`rep_ascC`). -/
theorem setifyC_eq_distinct_asc [DecidableEq B.El] {n : USize} (X : Vals (.arr B) n) (hB : B.Ordered)
    (hk : ∀ x y : B.El, B.key x = B.key y → x = y) (hs : (setifyC X).2 = true) (hd : (distinctC X).2 = true)
    (ha : (ascC (distinctC X).1.val).2 = true) (xs Z : (Obj.arr B).El) :
    rep (setifyC X).1 xs Z ↔ ∃ Y, rep (distinctC X).1 xs Y ∧ rep (ascC (distinctC X).1.val).1 Y Z := by
  obtain ⟨s1, s2⟩ := rep_setifyC X hs
  obtain ⟨d1, d2⟩ := rep_distinctC X hd
  obtain ⟨a1, a2⟩ := rep_ascC _ hB ha
  -- two duplicate-free lists with the same members are permutations of each other
  have hp : ∀ l₁ l₂ : List B.El, l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁.Perm l₂ := fun l₁ l₂ h1 h2 hm =>
    List.perm_iff_count.2 fun x => by rw [List.Nodup.count h1, List.Nodup.count h2]; simp only [hm x]
  -- an ascending permutation is unique
  have hu : ∀ l₁ l₂ : List B.El, l₁.Perm l₂ → (l₁.Pairwise fun x y => ¬ B.lt y x) →
      (l₂.Pairwise fun x y => ¬ B.lt y x) → l₁ = l₂ := fun l₁ l₂ hp h1 h2 =>
    hp.eq_of_pairwise (fun a b _ _ hab hba => Obj.eq_of_not_lt B hk hba hab) h1 h2
  -- `setify`'s array at `xs` is `xs.eraseDups` up to order
  have hse : ∀ Z, rep (setifyC X).1 xs Z → Z.Perm xs.eraseDups := fun Z h =>
    hp _ _ (setifyC_asc X hB hs xs Z h).1 (nodup_eraseDups xs) fun x =>
      ((s1 xs Z h).2 x).trans (mem_eraseDups x xs).symm
  -- `distinct`'s array is a row of its values
  have hrow : ∀ Y, rep (distinctC X).1 xs Y → ∃ j, (distinctC X).1.val.row j = Y := fun Y h => by
    obtain ⟨q, -, hq⟩ : (distinctC X).1.Holds xs Y := h
    exact ⟨q, hq⟩
  constructor
  · intro h
    obtain ⟨Y, hY⟩ := (d2 xs).2 (s1 xs Z h).1
    obtain ⟨Z', hZ'⟩ := a2 Y (hrow Y hY)
    obtain ⟨-, hP, hA⟩ := a1 Y Z' hZ'
    rw [(d1 xs Y hY).2] at hP
    exact ⟨Y, hY, hu Z' Z (hP.trans (hse Z h).symm) hA (setifyC_asc X hB hs xs Z h).2 ▸ hZ'⟩
  · rintro ⟨Y, hY, hZ⟩
    obtain ⟨-, hP, hA⟩ := a1 Y Z hZ
    rw [(d1 xs Y hY).2] at hP
    obtain ⟨Z₀, h₀⟩ := (s2 xs).2 (d1 xs Y hY).1
    exact (hu Z₀ Z ((hse Z₀ h₀).trans hP.symm) (setifyC_asc X hB hs xs Z₀ h₀).2 hA) ▸ h₀

#print axioms setifyC_eq_distinct_asc
#print axioms setifyC_asc
#print axioms unionC_ok
#print axioms rep_τC
#print axioms rep_lamOnByC
#print axioms rep_setifyC
#print axioms rep_EC
#print axioms rep_distinctC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg LeetQ.Rel.Rep
open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B : Obj}

theorem rep_τ {n : USize} (X : Vals A n) (hb : (τ X).ok = true) :
    (∀ a Y, rep (τ X).rel a Y → ∀ x, x ∈ Y ↔ x = a) ∧ (∀ a, (∃ Y, rep (τ X).rel a Y) ↔ ∃ i, Vals.row X i = a) :=
  by unfold CRel.τ at hb ⊢; rw [rep_ofC hb]; exact rep_τC X (ofC_ok hb).1

theorem rep_lamOn {m : USize} (R : CRel A B) (U : Vals A m) (hb : (R.lamOn U).ok = true) :
    (∀ a Y, rep (R.lamOn U).rel a Y → ∀ y, y ∈ Y ↔ rep R.rel a y) ∧
      (∀ a, (∃ Y, rep (R.lamOn U).rel a Y) ↔ (∃ b, rep R.rel a b) ∨ ∃ i, Vals.row U i = a) := by
  have e : R.lamOn U = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact (rep_lamOnByC valSortC valSortC_perm R.rel U hb).imp id And.left

theorem rep_setify {n : USize} (X : Vals (.arr B) n) (hb : (setify X).ok = true) :
    (∀ xs Y, rep (setify X).rel xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (setify X).rel xs Y) ↔ ∃ i, Vals.row X i = xs) :=
  by unfold CRel.setify at hb ⊢; rw [rep_ofC hb]; exact rep_setifyC X (ofC_ok hb).1

theorem rep_distinct [DecidableEq B.El] {n : USize} (X : Vals (.arr B) n) (hb : (distinct X).ok = true) :
    (∀ xs Y, rep (distinct X).rel xs Y → (∃ i, Vals.row X i = xs) ∧ Y = xs.eraseDups) ∧
      (∀ xs, (∃ Y, rep (distinct X).rel xs Y) ↔ ∃ i, Vals.row X i = xs) :=
  by unfold CRel.distinct at hb ⊢; rw [rep_ofC hb]; exact rep_distinctC X (ofC_ok hb).1

theorem rep_E {n : USize} (R : CRel A B) (X : Vals (.arr A) n) (hb : (R.E X).ok = true) :
    (∀ xs Y, rep (R.E X).rel xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R.rel x y) ∧
      (∀ xs, (∃ Y, rep (R.E X).rel xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  have e : R.E X = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_EC R.rel X hb

end CRel

end LeetQ.Rel
