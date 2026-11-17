/-
  The runtime ok-bit on the iterative composites `loopOn`/`loop` and on `tic`: an iterative op's round
  answers its new state and a bit, the `&&` of its pieces' twins' bits; `iterC` carries the `&&` of the rounds it
  ran, and `iterC_run` reads each run round's bit back. The proofs use only the rounds `iter` ran (`done` failing
  up to them): each such round's read-back comes from its pieces' `rep_<op>C`. What stays is not a size bound:
  a step's spec (`loopOn`'s `F`, at the rounds whose step bit is set).
-/
import LeetQ.Rel.CRelFold
import LeetQ.Run.CRelFoldDef
import LeetQ.Rel.CRelList
import LeetQ.Run.CRelListDef
import LeetQ.Rel.RepLoop
import LeetQ.Rel.RepMerge
import LeetQ.Run.CRelLoopDef

namespace LeetQ.Rel

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc
open LeetQ.Rel.Rep LeetQ.Rel.Rep.FoldN LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.Prim LeetQ.Rel.Rep.ListN

namespace Rep

/-- **`tic` under `ticC`'s bit**: `tic_of` at its pieces' read-backs, `rep_consC`, `rep_compC`, `rep_initsC`,
    `rep_tailC`. -/
theorem rep_ticC {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (ticC P).2 = true) :
    ∀ k zss, rep (ticC P).1 k zss ↔ ∃ b bs, rep P k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) := by
  simp only [ticC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hC, hN⟩, hI⟩, hT⟩, hr⟩ := hb
  exact tic_of P _ rfl _ rfl (rep_consC P hC) (rep_compC _ _ hI) (rep_initsC _ hN) (rep_compC _ _ hr)
    (rep_tailC _ hT)


/-- **`loopOn` under `loopOnC`'s bit**: `loopOn_rounds`, each round `iter` ran read back by `loop_round_set` at its
    bit (`iterC_run`): `ranC`'s and `domC`'s codes and `fitsN` bits, `rep_unconsC`, `rep_compC`, `rep_pairC`,
    `rep_nubC`, `rep_antiJoinC`, `rep_unionC`. What stays: the step's spec `hS` on the coreflexive of the pairs a
    round meets, at those pairs, where its bit is set. -/
theorem rep_loopOnC {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X × Bool)
    (P : Rel K (.prod X (.arr Y))) (hb : (loopOnC F P).2 = true)
    (Fr : X.El × Y.El → X.El → Prop)
    (hS : ∀ (D : Rel (.prod X Y) (.prod X Y)) (S : (Obj.prod X Y).El → Prop),
      rep D = corefl (α := (Obj.prod X Y).El) S → (F D).2 = true →
      ∀ cy c', S cy → (Fr cy c' ↔ rep (F D).1 cy c')) :
    ∀ k c, rep (loopOnC F P).1 k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  have e : (loopOnC F P).1 = loopOn (fun D => (F D).1) P := by
    simp only [loopOnC, loopOn, iterC_fst]; rfl
  have hf : ∀ (out : Rel K X) (St : Rel K (.prod X (.arr Y))) D u p, D = ran St → u = outr D ≫ uncons (ran (outr D)).val → p = pair (outl D) (outl u) →
      (loopRound F (out, St)).1 =
        (out ∪ St ≫ outl (antiJoin D (dom u)), Rel.nub (St ≫ pair (p ≫ (F (ran p)).1) (outr u))) := by
    intro out St D u p hD hu hp; subst hD hu hp; rw [← nubC_fst]; rfl
  have one : ∀ i, i ≤ (Rel.val P).2.1.toNat →
      (∀ i' ≤ i, (((fun s => (loopRound F s).1)^[i'] (Alg.zero, P)).2.n == 0) = false) →
      (∀ k (c' : X.El) (ys : List Y.El), rep ((fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P)).2 k (c', ys) ↔
        ∃ c y, rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2 k (c, y :: ys) ∧ Fr (c, y) c') ∧
      ∀ k (c : X.El), rep ((fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P)).1 k c ↔
        rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).1 k c ∨
          rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2 k (c, []) := by
    intro i hi hne
    have h := iterC_run ((Rel.val P).2.1.toNat + 1) (fun s : Rel K X × Rel K (.prod X (.arr Y)) => s.2.n == 0)
      (loopRound F) (Alg.zero, P) hb i (by omega) hne
    rw [show (fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P) =
      (loopRound F ((fun s => (loopRound F s).1)^[i] (Alg.zero, P))).1 from rfl]
    generalize (fun s => (loopRound F s).1)^[i] (Alg.zero, P) = st at h ⊢
    obtain ⟨out, St⟩ := st
    simp only [loopRound, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hW⟩, hc⟩, hu⟩, hp⟩, hrp⟩, hG⟩, hQ⟩, hR⟩, hT⟩, hN⟩, hdu⟩, hA⟩, hO⟩, hU⟩ := h
    simp only [ranC, domC, distinctCoreflC, Bool.and_eq_true] at hD hW hdu hrp
    have eP := rep_ran_corefl _ (one_ok _ (Obj.codesC_fits _ _ hrp.1))
      (pickFits_of_fitsN _ _ _ hrp.2 _ (by simp <;> exact Nat.le_refl _))
    have hr := loop_round_set out St _ _ _ _ _ _ _ _ _
      (rep_ran_corefl St (one_ok _ (Obj.codesC_fits _ _ hD.1)) (pickFits_of_fitsN _ _ _ hD.2 _ (by simp)))
      (rep_ran_corefl _ (one_ok _ (Obj.codesC_fits _ _ hW.1)) (pickFits_of_fitsN _ _ _ hW.2 _ (by simp <;> exact Nat.le_refl _)))
      (rep_unconsC _ hc) (rep_compC _ _ hu) (rep_pairC _ _ hp) Fr
      (fun cy c' hcy => (hS _ _ eP hG cy c' hcy).symm) (rep_compC _ _ hQ) (rep_pairC _ _ hR)
      (rep_compC _ _ hT) (by rw [← nubC_fst]; exact rep_nubC _ hN)
      (rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hdu.1)) (pickFits_of_fitsN _ _ _ hdu.2 _ (by simp <;> exact Nat.le_refl _)))
      (rep_antiJoinC _ _ hA) (rep_compC _ _ hO) (rep_unionC _ _ hU)
    simp only [loopRound, nubC_fst]
    exact hr
  rw [e]
  exact loopOn_rounds (fun D => (F D).1) P (fun s => (loopRound F s).1) hf (fun _ => Fr) (fun i hi hne => (one i hi hne).1)
    (fun i hi hne => (one i hi hne).2)

/-- **`loop` under `loopC`'s bit**: `rep_loopOnC` at the step `F` with no bit of its own, its spec `rep F`. -/
theorem rep_loopC {K X Y : Obj} (F : Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) (hb : (loopC F P).2 = true) :
    ∀ k c, rep (loopC F P).1 k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), rep F (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopOnC (fun _ => (F, true)) P hb (rep F) fun _ _ _ _ _ _ _ => Iff.rfl

-- `merge`'s test `q` read back as `le`: on a coreflexive `D` of the pairs `S`, where its bit is set, a pair of `S`
-- passes exactly when `le` holds; the spec of the test, not a size bound
set_option hygiene false in
local notation "testOK(" q ")" =>
  ∀ (D : Rel (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
    rep D = corefl (α := (Obj.prod B B).El) S → (q D).2 = true →
    ∀ a b, S (a, b) → ((∃ c, rep (q D).1 (a, b) c) ↔ le a b = true)

/-- **One round of `mergeOn` under its bit**: `merge_round_set` at its twins' read-backs — `ranC`'s and `domC`'s
    codes and `fitsN` bits, `rep_unconsC`, `rep_compC`, `rep_pairC`, `rep_snocC`, `rep_antiJoinC`, `rep_unionC`,
    `rep_catC` — and the test's spec `hq` at the pairs of heads the round meets. -/
theorem rep_mergeRoundC {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (le : B.El → B.El → Bool) (hq : testOK(q)) (out : Rel K (.arr B))
    (St : Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B))) (hb : (mergeRound q (out, St)).2 = true) :
    (∀ k s', rep (mergeRound q (out, St)).1.2 k s' ↔ ∃ a x b y acc, rep St k ((a :: x, b :: y), acc) ∧
      (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b]))) ∧
    ∀ k z, rep (mergeRound q (out, St)).1.1 k z ↔
      rep out k z ∨ ∃ x y acc, rep St k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y := by
  simp only [mergeRound, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hcx⟩, hux⟩, hcy⟩, huy⟩, hpu⟩, hbo⟩, hh⟩, hrh⟩, hG⟩, hhq⟩, hl⟩,
    hA1⟩, hS1⟩, hN1⟩, hP1⟩, hL1⟩, hnb⟩, hA2⟩, hS2⟩, hN2⟩, hP2⟩, hL2⟩, htk⟩, hT⟩, hfl⟩, hSf⟩, hc1⟩, hC1⟩, hc2⟩,
    hC2⟩, hO⟩, hU⟩ := hb
  simp only [ranC, domC, distinctCoreflC, Bool.and_eq_true] at hD hbo hrh hl
  have eRh := rep_ran_corefl _ (one_ok _ (Obj.codesC_fits _ _ hrh.1))
    (pickFits_of_fitsN _ _ _ hrh.2 _ (by simp <;> exact Nat.le_refl _))
  simp only [mergeRound]
  exact merge_round_set le out St
    (hD := rep_ran_corefl St (one_ok _ (Obj.codesC_fits _ _ hD.1)) (pickFits_of_fitsN _ _ _ hD.2 _ (by simp)))
    (hx := rfl) (hy := rfl) (hacc := rfl)
    (hUx := rep_unconsC _ hcx) (hux := rep_compC _ _ hux) (hUy := rep_unconsC _ hcy) (huy := rep_compC _ _ huy)
    (hpu := rep_pairC _ _ hpu)
    (hboth := rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hbo.1))
      (pickFits_of_fitsN _ _ _ hbo.2 _ (by simp <;> exact Nat.le_refl _)))
    (hh := rep_pairC _ _ hh) (hrh := eRh)
    (htest := fun a b hab => hq _ _ eRh hG a b (by rw [eRh] at hab; exact hab.2))
    (hhq := rep_compC _ _ hhq)
    (hl := rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hl.1))
      (pickFits_of_fitsN _ _ _ hl.2 _ (by simp <;> exact Nat.le_refl _)))
    (hA1 := rep_pairC _ _ hA1) (hS1 := rep_pairC _ _ hS1) (hN1 := rep_snocC _ hN1) (hP1 := rep_pairC _ _ hP1)
    (hL1 := rep_compC _ _ hL1) (hnb := rep_antiJoinC _ _ hnb)
    (hA2 := rep_pairC _ _ hA2) (hS2 := rep_pairC _ _ hS2) (hN2 := rep_snocC _ hN2) (hP2 := rep_pairC _ _ hP2)
    (hL2 := rep_compC _ _ hL2) (htk := rep_unionC _ _ htk) (hT := rep_compC _ _ hT)
    (hfl := rep_antiJoinC _ _ hfl) (hSf := rep_compC _ _ hSf)
    (hc1 := rep_pairC _ _ hc1) (hC1 := rep_catC _ hC1) (hc2 := rep_pairC _ _ hc2) (hC2 := rep_catC _ hC2)
    (hO := rep_compC _ _ hO) (hU := rep_unionC _ _ hU)

/-- **`mergeOn` under `mergeOnC`'s bit**: `mergeOn_rounds`, the first state read back by `merge_init` at its bit
    (`ranC`'s codes and `fitsN` bits, `topC`'s count and fit, `pairC_ok`, `compC_cmpOK`), each round `iter` ran by
    `rep_mergeRoundC` at its bit (`iterC_run`). What stays: the test's spec `hq`. -/
theorem rep_mergeOnC {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool) (hq : testOK(q))
    (hb : (mergeOnC q P).2 = true) :
    ∀ k zs, rep (mergeOnC q P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  simp only [mergeOnC, Bool.and_eq_true] at hb
  obtain ⟨hI, hit⟩ := hb
  simp only [mergeInitC, topC, Bool.and_eq_true, decide_eq_true_eq] at hI
  obtain ⟨⟨⟨hR, ⟨⟨⟨-, h63⟩, hfa⟩, -⟩⟩, hQ⟩, hM⟩ := hI
  simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hR
  have h0 := merge_init P ⟨⟨Obj.codesC_fits _ _ hR.1, pickFits_of_fitsN _ _ _ hR.2 _ (by simp)⟩, h63,
    pickFits_of_fitsN _ _ _ hfa _ (by simp <;> exact Nat.le_refl _), pairC_ok _ _ hQ, compC_cmpOK _ _ hM⟩
  rw [mergeOnC_fst]
  refine mergeOn_rounds (fun D => (q D).1) P le (fun s => (mergeRound q s).1) ?_ _ rfl h0
    (fun i hi hne => (rep_mergeRoundC q le hq _ _ (iterC_run _ _ _ _ hit i (by omega) hne)).1)
    (fun i hi hne => (rep_mergeRoundC q le hq _ _ (iterC_run _ _ _ _ hit i (by omega) hne)).2)
  intro out St D hD x hx y hy acc hacc ux hux uy huy both hboth h hh l hl
  subst hD hx hy hacc hux huy hboth hh hl
  rfl

/-- **`merge` under `mergeC`'s bit**: `rep_mergeOnC`, the test `pairsIn Q` read back by `rep_pairsIn` at
    `compC`'s bit; `le a b` any Boolean test with `le a b = true` exactly when `a Q b` (`hle`). -/
theorem rep_mergeC {K B : Obj} (Q : Rel B B) (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (hle : ∀ a b, le a b = true ↔ rep Q a b) (hb : (mergeC Q P).2 = true) :
    ∀ k zs, rep (mergeC Q P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  refine rep_mergeOnC _ P le (fun D S hD hc a b hS => ?_) hb
  have eP := rep_pairsIn Q D (compC_cmpOK _ _ hc)
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨h1, h2⟩ := (eP _ _).1 h
    rw [hD] at h1
    obtain ⟨rfl, -⟩ := h1
    exact (hle a b).2 h2
  · intro h
    exact ⟨(a, b), (eP _ _).2 ⟨by rw [hD]; exact ⟨rfl, hS⟩, (hle a b).1 h⟩⟩

/-- **`fixOnC`'s answer is `fixOn`'s** at the step's relation: `iterC_fst`, `nubC_fst`. -/
theorem fixOnC_fst {A B : Obj} (n : Nat) (φC : Rel A B → Rel A B × Bool) (X₀ : Rel A B) :
    (fixOnC n φC X₀).1 = fixOn n (fun X => (φC X).1) X₀ := by
  simp only [fixOnC, iterC_fst, nubC_fst]; rfl

/-- **`fixOn` under `fixOnC`'s bit**: `rep_fixOn`, each round the loop ran read back by its bit (`iterC_run`):
    `rep_nubC` at the round's `nubC`, `hφ` at its step's bit, and the distinct rows of each round's `nub`
    (`nub_rows_inj`, its premises from the same bit). What stays is not capacity: `hφ`, the step's own spec, and
    `hm`, `hch`, the chain of `Φ`'s iterates. -/
theorem rep_fixOnC {A B : Obj} (n : Nat) (φC : Rel A B → Rel A B × Bool) (X₀ : Rel A B)
    (Φ : type_of% (rep X₀) → type_of% (rep X₀)) (hb : (fixOnC n φC X₀).2 = true)
    (hφ : ∀ X, (φC X).2 = true → rep (φC X).1 = Φ (rep X))
    (hm : ∀ x y : type_of% (rep X₀), x ⊑ y → Φ x ⊑ Φ y) (hch : rep X₀ ⊑ Φ (rep X₀) ∨ Φ (rep X₀) ⊑ rep X₀) :
    ∃ j ≤ n, (fixOnC n φC X₀).1.2 = j ∧ rep (fixOnC n φC X₀).1.1 = Φ^[j] (rep X₀) ∧
      (j < n → Φ (rep (fixOnC n φC X₀).1.1) = rep (fixOnC n φC X₀).1.1) ∧
      (∀ Y, rep X₀ ⊑ Y → Φ Y ⊑ Y → rep (fixOnC n φC X₀).1.1 ⊑ Y) ∧
      (∀ U : Rel A B, (∀ i, Φ^[i] (rep X₀) ⊑ rep U) → U.n.toNat + 1 < n → j < n) := by
  rw [fixOnC_fst]
  simp only [fixOnC, okbit] at hb
  obtain ⟨h0, hit⟩ := hb
  let g : Rel A B → Rel A B := fun X => (φC X).1.nub
  let r : Nat × Rel A B × Nat → (Nat × Rel A B × Nat) × Bool := fun s =>
    let y := φC s.2.1; let z := nubC y.1; ((s.2.1.n.toNat, z.1, s.2.2 + 1), y.2 && z.2)
  -- the round without its bit is `fixOn`'s
  have ef : (fun s => (r s).1) = fun s : Nat × Rel A B × Nat => (s.2.1.n.toNat, ((φC s.2.1).1).nub, s.2.2 + 1) :=
    funext fun s => by show (s.2.1.n.toNat, (nubC (φC s.2.1).1).1, s.2.2 + 1) = _; rw [nubC_fst]
  have es : ∀ i, ((fun s => (r s).1)^[i] ((nubC X₀).1.n.toNat + 1, (nubC X₀).1, 0)).2.1 = g^[i] X₀.nub := by
    intro i; rw [ef, nubC_fst]
    cases i with
    | zero => rfl
    | succ i => rw [fixOn_iterate (fun X => (φC X).1) X₀ i]
  -- the bits of a round the loop ran
  have hrun : ∀ i < n, (∀ k < i, (g^[k] X₀.nub).n.toNat ≠ (g^[k + 1] X₀.nub).n.toNat) →
      (φC (g^[i] X₀.nub)).2 = true ∧ (nubC (φC (g^[i] X₀.nub)).1).2 = true := fun i hi hne => by
    have hr := iterC_run n (fun s => s.1 == s.2.1.n.toNat) r _ hit i hi fun i' hi' => by
      rw [ef, nubC_fst]
      cases i' with
      | zero => show (X₀.nub.n.toNat + 1 == X₀.nub.n.toNat) = false; simp
      | succ k =>
        rw [fixOn_iterate (fun X => (φC X).1) X₀ k]
        simpa using hne k (by omega)
    rw [← es i]; exact Eq.mp (Bool.and_eq_true _ _) hr
  -- `nubC`'s bit gives `nub_rows_inj` its premises, as it gives `rep_nub` its (`rep_nubC`)
  have hu : ∀ R : Rel A B, (nubC R).2 = true → rowsInj(R.nub) := fun R hb => by
    simp only [nubC, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hK, hV⟩, hk⟩, hv⟩ := hb
    exact nub_rows_inj R (oneOK_of_codesC A R.key hK) (oneOK_of_codesC B R.val hV)
      (pickFits_of_fitsN A R.key _ hk _ (by simp)) (pickFits_of_fitsN B R.val _ hv _ (by simp))
  refine rep_fixOn n (fun X => (φC X).1) X₀ Φ (by rw [← nubC_fst]; exact rep_nubC X₀ h0) (fun i hi hne => ?_)
    (fun i hi hne => ?_) hm hch
  · have hr' := hrun i hi hne
    show rep (φC (g^[i] X₀.nub)).1.nub = Φ (rep (g^[i] X₀.nub))
    rw [← nubC_fst, rep_nubC _ hr'.2, hφ _ hr'.1]
  · cases i with
    | zero => exact hu X₀ h0
    | succ i => exact hu _ (hrun i (by omega) fun k hk => hne k (by omega)).2

#print axioms rep_fixOnC
#print axioms rep_ticC
#print axioms rep_loopOnC
#print axioms rep_loopC
#print axioms rep_mergeRoundC
#print axioms rep_mergeOnC
#print axioms rep_mergeC

end Rep

namespace CRel

variable {K X Y B : Obj}

theorem rep_tic (P : CRel K (.prod B (.arr B))) (hb : (tic P).ok = true) :
    ∀ k zss, rep (tic P).rel k zss ↔ ∃ b bs, rep P.rel k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) := by
  have e : tic P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_ticC P.rel hb

/-- `hS`: the step's spec on a coreflexive where the step was ok, at the pairs of that coreflexive. -/
theorem rep_loopOn (F : CRel (.prod X Y) (.prod X Y) → CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y)))
    (hb : (loopOn F P).ok = true) (Fr : X.El × Y.El → X.El → Prop)
    (hS : ∀ (D : Rel (.prod X Y) (.prod X Y)) (S : (Obj.prod X Y).El → Prop),
      rep D = corefl (α := (Obj.prod X Y).El) S → (F ⟨D, true⟩).ok = true →
      ∀ cy c', S cy → (Fr cy c' ↔ rep (F ⟨D, true⟩).rel cy c')) :
    ∀ k c, rep (loopOn F P).rel k c ↔ ∃ c₀ xs, rep P.rel k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  have e : loopOn F P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_loopOnC _ P.rel hb Fr hS

theorem rep_loop (F : CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) (hb : (loop F P).ok = true) :
    ∀ k c, rep (loop F P).rel k c ↔ ∃ c₀ xs, rep P.rel k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), rep F.rel (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  have e : loop F P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_loopC F.rel P.rel hb

/-- `hq`: the test's spec on a coreflexive where the test was ok. -/
theorem rep_mergeOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B))
    (P : CRel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (hq : ∀ (D : Rel (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep D = corefl (α := (Obj.prod B B).El) S → (q ⟨D, true⟩).ok = true →
      ∀ a b, S (a, b) → ((∃ c, rep (q ⟨D, true⟩).rel (a, b) c) ↔ le a b = true))
    (hb : (mergeOn q P).ok = true) :
    ∀ k zs, rep (mergeOn q P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.merge xs ys le := by
  have e : mergeOn q P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_mergeOnC _ P.rel le hq hb

/-- `hle`:`le` decides `Q`. -/
theorem rep_merge (Q : CRel B B) (P : CRel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (hle : ∀ a b, le a b = true ↔ rep Q.rel a b) (hb : (merge Q P).ok = true) :
    ∀ k zs, rep (merge Q P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.merge xs ys le := by
  have e : merge Q P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_mergeC Q.rel P.rel le hle hb

/-- `hφ` the step's spec where its bit is set; `hm`, `hch` the chain (`rep_fixOn`'s). -/
theorem rep_fixOn {A : Obj} (n : Nat) (φ : CRel A B → CRel A B) (X₀ : CRel A B)
    (Φ : type_of% (rep X₀.rel) → type_of% (rep X₀.rel)) (hb : (fixOn n φ X₀).1.ok = true)
    (hφ : ∀ D, (φ ⟨D, true⟩).ok = true → rep (φ ⟨D, true⟩).rel = Φ (rep D))
    (hm : ∀ x y : type_of% (rep X₀.rel), x ⊑ y → Φ x ⊑ Φ y)
    (hch : rep X₀.rel ⊑ Φ (rep X₀.rel) ∨ Φ (rep X₀.rel) ⊑ rep X₀.rel) :
    ∃ j ≤ n, (fixOn n φ X₀).2 = j ∧ rep (fixOn n φ X₀).1.rel = Φ^[j] (rep X₀.rel) ∧
      (j < n → Φ (rep (fixOn n φ X₀).1.rel) = rep (fixOn n φ X₀).1.rel) ∧
      (∀ Y, rep X₀.rel ⊑ Y → Φ Y ⊑ Y → rep (fixOn n φ X₀).1.rel ⊑ Y) ∧
      (∀ U : Rel A B, (∀ i, Φ^[i] (rep X₀.rel) ⊑ rep U) → U.n.toNat + 1 < n → j < n) := by
  have e : fixOn n φ X₀ = _ := guard_eq (·.1.ok) hb
  -- reduced first: the conclusion's `.2` against `fixOnC`'s otherwise sends `whnf` into `iter`'s recursion
  rw [e] at hb ⊢; dsimp only at hb ⊢
  rw [rep_ofC hb]; exact rep_fixOnC n _ X₀.rel Φ (ofC_ok hb).1 hφ hm hch

#print axioms rep_fixOn

end CRel

end LeetQ.Rel
