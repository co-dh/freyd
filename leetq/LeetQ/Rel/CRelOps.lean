/-
  The runtime ok-bit on the Boolean tests `⊑`, `entire`, `surjective`, `simple`, `injective`, `isMap`: each twin
  answers the test and a bit, the `&&` of its pieces' bits, and under that bit the test reads back with no
  premise left: `leC_ok` reads `leC`'s bit as `rep_le`'s joint pair codes, `domC`'s and `nubC`'s bits give the
  one-part codes and fits.
-/
import LeetQ.Rel.CRelRel
import LeetQ.Rel.CRelRelDef

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open OpsN

variable {A B : Obj}

/-- **`leC`'s bit, read as `rep_le`'s premise**: the joint pair codes' bit (`codesC_fits`, `codes_faithful_wf`,
    `pairs_eq_codes`). -/
theorem leC_ok (R S : Rel A B) (hb : (leC R S).2 = true) : pairsOK(R, S) := by
  simp only [leC] at hb
  have hc := (codes_faithful_wf (.prod A B) _ (Obj.codesC_fits (.prod A B) _ hb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  rw [pairs_eq_codes, e]; exact hc

/-- **`R ⊑ S` under `leC`'s bit**: `rep_le` at `leC_ok`. -/
theorem rep_leC (R S : Rel A B) (hb : (leC R S).2 = true) : (leC R S).1 = true ↔ rep R ⊑ rep S :=
  rep_le R S (leC_ok R S hb)

/-- **`entire` under `entireC`'s bit**: `rep_entire` at `leC_ok` and `domC`'s code and `fitsN` bits. -/
theorem rep_entireC (R : Rel A B) {m : USize} (U : Vals A m) (hb : (entireC R U).2 = true) :
    (entireC R U).1 = true ↔ ∀ a, (∃ i, U.row i = a) → ∃ b, rep R a b := by
  simp only [entireC, Bool.and_eq_true] at hb
  obtain ⟨hd, hl⟩ := hb
  simp only [domC, distinctCoreflC, Bool.and_eq_true] at hd
  exact rep_entire R U (leC_ok _ _ hl) (oneOK_of_codesC A R.key hd.1) (pickFits_of_fitsN _ _ _ hd.2 _ (by simp))

/-- **`surjective` under `surjectiveC`'s bit**: `rep_surjective` at `leC_ok` and `domC`'s bits at `R°`. -/
theorem rep_surjectiveC (R : Rel A B) {m : USize} (U : Vals B m) (hb : (surjectiveC R U).2 = true) :
    (surjectiveC R U).1 = true ↔ ∀ b, (∃ i, U.row i = b) → ∃ a, rep R a b := by
  simp only [surjectiveC, entireC, Bool.and_eq_true] at hb
  obtain ⟨hd, hl⟩ := hb
  simp only [domC, distinctCoreflC, Bool.and_eq_true] at hd
  exact rep_surjective R U (leC_ok _ _ hl) (oneOK_of_codesC B R.val hd.1) (pickFits_of_fitsN _ _ _ hd.2 _ (by simp <;> exact Nat.le_refl _))

/-- **`simpleC`'s bit, read as `rep_simple`'s premises**: `nubC`'s code and `fitsN` bits, the nub's key code bit. -/
theorem simpleC_ok (R : Rel A B) (hb : (simpleC R).2 = true) :
    oneOK(A, R.n, R.key) ∧ oneOK(B, R.n, R.val) ∧ Vals.PickFits A R.key (List.range R.n.toNat) ∧
      Vals.PickFits B R.val (List.range R.n.toNat) ∧
      A.CodesFit (#v[⟨R.nub.n, R.nub.key⟩] : Vector (Part A) 1) := by
  have hb' : ((nubC R).2 && (A.codesC (#v[⟨(nubC R).1.n, (nubC R).1.key⟩] : Vector (Part A) 1)).2) = true := hb
  rw [Bool.and_eq_true] at hb'
  obtain ⟨hn, hc⟩ := hb'
  have hS : A.CodesFit (#v[⟨(nubC R).1.n, (nubC R).1.key⟩] : Vector (Part A) 1) := Obj.codesC_fits A _ hc
  rw [nubC_fst] at hS
  simp only [nubC, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨hK, hV⟩, hk⟩, hv⟩ := hn
  exact ⟨oneOK_of_codesC A R.key hK, oneOK_of_codesC B R.val hV, pickFits_of_fitsN A R.key _ hk _ (by simp),
    pickFits_of_fitsN B R.val _ hv _ (by simp), hS⟩

/-- **`simple` under `simpleC`'s bit**: `rep_simple` at `simpleC_ok`. -/
theorem rep_simpleC (R : Rel A B) (hb : (simpleC R).2 = true) :
    simple R = true ↔ ∀ a b b', rep R a b → rep R a b' → b = b' :=
  let h := simpleC_ok R hb; rep_simple R h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **`injective` under `injectiveC`'s bit**: `rep_injective` at `simpleC_ok` at `R°`. -/
theorem rep_injectiveC (R : Rel A B) (hb : (injectiveC R).2 = true) :
    injective R = true ↔ ∀ a a' b, rep R a b → rep R a' b → a = a' :=
  let h := simpleC_ok (R°) hb; rep_injective R h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- **`isMap` under `isMapC`'s bit**: `rep_entireC` and `rep_simpleC` at its two halves. -/
theorem rep_isMapC (R : Rel A B) {m : USize} (U : Vals A m) (hb : (isMapC R U).2 = true) :
    (isMapC R U).1 = true ↔
      (∀ a, (∃ i, U.row i = a) → ∃ b, rep R a b) ∧ ∀ a b b', rep R a b → rep R a b' → b = b' := by
  simp only [isMapC, Bool.and_eq_true] at hb
  show ((entireC R U).1 && simple R) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr (rep_entireC R U hb.1) (rep_simpleC R hb.2)

#print axioms leC_ok
#print axioms rep_leC
#print axioms rep_entireC
#print axioms rep_surjectiveC
#print axioms simpleC_ok
#print axioms rep_simpleC
#print axioms rep_injectiveC
#print axioms rep_isMapC

end LeetQ.Rel.Rep
