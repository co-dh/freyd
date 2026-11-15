/-
  Capacity checked at run time, correctness proved, for the power side's ops built on `Λ`: `τ`, `lamOn`, `setify`,
  `E`. Each twin's bit is the `&&` of the bits of the twins it runs, and decides every capacity
  premise of the op's read-back (`rep_tau`, `rep_lamOn`, …), so `rep_τC` … `rep_EC` hold under that bit alone.
-/
import LeetQ.Rel.CRelRel
import LeetQ.Run.CRelRelDef
import LeetQ.Rel.RepEst
import LeetQ.Run.CRelPowerDef

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
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

/-- **`rep (lamOn R U)` under `lamOnC`'s bit**: `rep_lamOn` at the intermediates `lamOnC` builds, each defining
    equation `rfl`. `transposeC_ok` gives `hK`…`h63`, `diffC`'s bit `hc` (`codes_faithful_wf`, `pairs_eq_codes`) and
    `hdU`, `topC`'s `ht63`, `unionC_ok` `hN`…`huv`. -/
theorem rep_lamOnC {m : USize} (R : Rel A B) (U : Vals A m) (hb : (lamOnC R U).2 = true) :
    (∀ a Y, rep (lamOnC R U).1 a Y → ∀ y, y ∈ Y ↔ rep R a y) ∧
      (∀ a, (∃ Y, rep (lamOnC R U).1 a Y) ↔ (∃ b, rep R a b) ∨ ∃ i, Vals.row U i = a) := by
  simp only [lamOnC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨ht, -⟩, hd⟩, hn⟩, hu⟩ := hb
  obtain ⟨hK, hV, hk, hv, hWk, hW, h63⟩ := transposeC_ok R ht
  simp only [diffC, Bool.and_eq_true] at hd
  obtain ⟨⟨hcb, hdU⟩, -⟩ := hd
  have hc := (codes_faithful_wf (.prod A A) _ (Obj.codesC_fits (.prod A A) _ hcb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  have hp : pairsOK(idU U, dom R) := by rw [pairs_eq_codes, e]; exact hc
  simp only [topC, Bool.and_eq_true, decide_eq_true_eq] at hn
  obtain ⟨⟨⟨-, ht63⟩, -⟩, -⟩ := hn
  obtain ⟨hN, hFk, hFv, huK, huV, huk, huv⟩ := unionC_ok _ _ hu
  exact rep_lamOn R U _ _ rfl rfl hK hV hk hv hWk hW h63 _ rfl hp
    (pickFits_of_fitsN A (idU U).key _ hdU _ (by simp only [List.length_range]; exact Nat.le_refl _)) _ rfl ht63 _ _ rfl rfl hN hFk hFv _ rfl _ _ rfl rfl
    huK huV huk huv

/-- `lamOn M X` on rows of `X` when `M` relates only rows of `X`: an array it gives `xs` holds exactly the `y` with
    `P xs y`, and it has a row at `xs` exactly when `X` lists `xs`. -/
theorem rep_lamOnC_rows {n : USize} (M : Rel K B) (X : Vals K n) (P : K.El → B.El → Prop)
    (hm : ∀ xs y, rep M xs y ↔ (∃ i, Vals.row X i = xs) ∧ P xs y) (hb : (lamOnC M X).2 = true) :
    (∀ xs Y, rep (lamOnC M X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ P xs y) ∧
      (∀ xs, (∃ Y, rep (lamOnC M X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  obtain ⟨h1, h2⟩ := rep_lamOnC M X hb
  have h2' : ∀ xs, (∃ Y, rep (lamOnC M X).1 xs Y) ↔ ∃ i, Vals.row X i = xs := fun xs =>
    (h2 xs).trans ⟨fun h => h.elim (fun ⟨_, hb⟩ => ((hm _ _).1 hb).1) id, Or.inr⟩
  exact ⟨fun xs Y h => ⟨(h2' xs).1 ⟨Y, h⟩, fun y => (h1 xs Y h y).trans
    ((hm xs y).trans ⟨And.right, fun hy => ⟨(h2' xs).1 ⟨Y, h⟩, hy⟩⟩)⟩, h2'⟩

/-- **`rep (setify X)` under `setifyC`'s bit**: `rep_lamOnC_rows` at `∋` on `X` (`rep_memC`). -/
theorem rep_setifyC {n : USize} (X : Vals (.arr B) n) (hb : (setifyC X).2 = true) :
    (∀ xs Y, rep (setifyC X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (setifyC X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  simp only [setifyC, Bool.and_eq_true] at hb
  exact rep_lamOnC_rows _ X (fun xs y => y ∈ xs) (rep_memC X hb.1) hb.2

/-- **`rep (E R X)` under `EC`'s bit**: `rep_lamOnC_rows` at `∋ ≫ R` on `X` (`rep_compC`, `rep_memC`). -/
theorem rep_EC {n : USize} (R : Rel A B) (X : Vals (.arr A) n) (hb : (EC R X).2 = true) :
    (∀ xs Y, rep (EC R X).1 xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R x y) ∧
      (∀ xs, (∃ Y, rep (EC R X).1 xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  simp only [EC, Bool.and_eq_true] at hb
  obtain ⟨⟨hm, hc⟩, hl⟩ := hb
  refine rep_lamOnC_rows _ X (fun xs y => ∃ x ∈ xs, rep R x y) (fun xs y => ?_) hl
  rw [rep_compC _ R hc]
  show (∃ x, rep (memC X).1 xs x ∧ rep R x y) ↔ _
  simp only [rep_memC X hm]
  exact ⟨fun ⟨x, ⟨hi, hx⟩, hr⟩ => ⟨hi, x, hx, hr⟩, fun ⟨hi, x, hx, hr⟩ => ⟨x, ⟨hi, hx⟩, hr⟩⟩

/-- **`rep (P R X Y)` under `PC`'s bit**: `rep_interC` of `rep_leftDivC` and `rep_rightDivC`, at `rep_compC`'s and
    `rep_memC`'s read-backs of the composites. -/
theorem rep_PC {n m : USize} (R : Rel A B) (X : Vals (.arr A) n) (Y : Vals (.arr B) m) (hb : (PC R X Y).2 = true)
    (xs : (Obj.arr A).El) (ys : (Obj.arr B).El) :
    rep (PC R X Y).1 xs ys ↔ (∃ i, X.row i = xs) ∧ (∃ j, Y.row j = ys) ∧
      (∀ a ∈ xs, ∃ b ∈ ys, rep R a b) ∧ (∀ b ∈ ys, ∃ a ∈ xs, rep R a b) := by
  simp only [PC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨hx, hy⟩, hry⟩, hxr⟩, hl⟩, hd⟩, hi⟩ := hb
  have eX : ∀ a xs, rep ((memC X).1)° a xs ↔ (∃ i, X.row i = xs) ∧ a ∈ xs := fun a xs => by
    rw [rep_conv]; exact rep_memC X hx xs a
  have eY : ∀ ys b, rep (memC Y).1 ys b ↔ (∃ j, Y.row j = ys) ∧ b ∈ ys := rep_memC Y hy
  have eRY : ∀ a ys, rep (compC R ((memC Y).1)°).1 a ys ↔ ∃ b, rep R a b ∧ (∃ j, Y.row j = ys) ∧ b ∈ ys :=
    fun a ys => by
      rw [rep_compC _ _ hry, Freyd.Alg.RelSet.comp_apply]
      exact exists_congr fun b => and_congr Iff.rfl (by rw [rep_conv]; exact eY ys b)
  have eXR : ∀ xs b, rep (compC (memC X).1 R).1 xs b ↔ ∃ a, ((∃ i, X.row i = xs) ∧ a ∈ xs) ∧ rep R a b :=
    fun xs b => by
      rw [rep_compC _ _ hxr, Freyd.Alg.RelSet.comp_apply]
      exact exists_congr fun a => and_congr (rep_memC X hx xs a) Iff.rfl
  show rep (interC (A := .arr A) (B := .arr B) _ _).1 xs ys ↔ _
  rw [rep_interC _ _ hi]
  show rep (leftDivC (A := A) (B := .arr A) (C := .arr B) _ _ X Y).1 xs ys ∧
    rep (rightDivC (A := .arr A) (B := .arr B) (C := B) _ _ X Y).1 xs ys ↔ _
  rw [rep_leftDivC _ _ X Y hl xs ys, rep_rightDivC _ _ X Y hd xs ys]
  simp only [eX, eRY, eY, eXR]
  constructor
  · rintro ⟨⟨hl, hl'⟩, ⟨hr, hr'⟩⟩
    have hx : ∃ i, X.row i = xs := by rcases hl' with ⟨_, h, _⟩ | ⟨h, _⟩ <;> exact h
    have hy : ∃ j, Y.row j = ys := by rcases hr' with ⟨_, h, _⟩ | ⟨_, h⟩ <;> exact h
    refine ⟨hx, hy, fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨b, hR, -, hb⟩ := hl a ⟨hx, ha⟩
      exact ⟨b, hb, hR⟩
    · obtain ⟨a, ⟨-, ha⟩, hR⟩ := hr b ⟨hy, hb⟩
      exact ⟨a, ha, hR⟩
  · rintro ⟨hx, hy, hl, hr⟩
    refine ⟨⟨fun a ⟨_, ha⟩ => ?_, Or.inr ⟨hx, hy⟩⟩, ⟨fun b ⟨_, hb⟩ => ?_, Or.inr ⟨hx, hy⟩⟩⟩
    · obtain ⟨b, hb, hR⟩ := hl a ha
      exact ⟨b, hR, hy, hb⟩
    · obtain ⟨a, ha, hR⟩ := hr b hb
      exact ⟨a, ⟨hx, ha⟩, hR⟩

#print axioms rep_PC
#print axioms unionC_ok
#print axioms rep_τC
#print axioms rep_lamOnC
#print axioms rep_setifyC
#print axioms rep_EC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B : Obj}

theorem rep_P {n m : USize} (R : CRel A B) (X : Vals (.arr A) n) (Y : Vals (.arr B) m) (hb : (R.P X Y).ok = true)
    (xs : (Obj.arr A).El) (ys : (Obj.arr B).El) :
    rep (R.P X Y).rel xs ys ↔ (∃ i, X.row i = xs) ∧ (∃ j, Y.row j = ys) ∧
      (∀ a ∈ xs, ∃ b ∈ ys, rep R.rel a b) ∧ (∀ b ∈ ys, ∃ a ∈ xs, rep R.rel a b) := by
  have e : R.P X Y = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_PC R.rel X Y hb xs ys

theorem rep_τ {n : USize} (X : Vals A n) (hb : (τ X).ok = true) :
    (∀ a Y, rep (τ X).rel a Y → ∀ x, x ∈ Y ↔ x = a) ∧ (∀ a, (∃ Y, rep (τ X).rel a Y) ↔ ∃ i, Vals.row X i = a) :=
  rep_τC X hb

theorem rep_lamOn {m : USize} (R : CRel A B) (U : Vals A m) (hb : (R.lamOn U).ok = true) :
    (∀ a Y, rep (R.lamOn U).rel a Y → ∀ y, y ∈ Y ↔ rep R.rel a y) ∧
      (∀ a, (∃ Y, rep (R.lamOn U).rel a Y) ↔ (∃ b, rep R.rel a b) ∨ ∃ i, Vals.row U i = a) := by
  have e : R.lamOn U = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_lamOnC R.rel U hb

theorem rep_setify {n : USize} (X : Vals (.arr B) n) (hb : (setify X).ok = true) :
    (∀ xs Y, rep (setify X).rel xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ y ∈ xs) ∧
      (∀ xs, (∃ Y, rep (setify X).rel xs Y) ↔ ∃ i, Vals.row X i = xs) :=
  rep_setifyC X hb

theorem rep_E {n : USize} (R : CRel A B) (X : Vals (.arr A) n) (hb : (R.E X).ok = true) :
    (∀ xs Y, rep (R.E X).rel xs Y → (∃ i, Vals.row X i = xs) ∧ ∀ y, y ∈ Y ↔ ∃ x ∈ xs, rep R.rel x y) ∧
      (∀ xs, (∃ Y, rep (R.E X).rel xs Y) ↔ ∃ i, Vals.row X i = xs) := by
  have e : R.E X = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_EC R.rel X hb

end CRel

end LeetQ.Rel
