/-
  The runtime ok-bit on the iterative composites `suffix`, `loopOn`/`loop` and on `tic`: an iterative op's round
  answers its new state and a bit, the `&&` of its pieces' twins' bits; `iterC` carries the `&&` of the rounds it
  ran, and `iterC_run` reads each run round's bit back. The proofs use only the rounds `iter` ran (`done` failing
  up to them): each such round's read-back comes from its pieces' `rep_<op>C`. What stays is not a size bound:
  a step's spec (`loopOn`'s `F`, at the rounds whose step bit is set) and `unionC`'s `hat`.
-/
import LeetQ.Rel.CRelFold
import LeetQ.Rel.CRelList
import LeetQ.Rel.RepLoop

namespace LeetQ.Rel

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open LeetQ.Rel.Rep LeetQ.Rel.Rep.FoldN LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.Prim LeetQ.Rel.Rep.ListN

-- `unionC`'s `hat`: `razeTo`'s read-back of two atom parts, not a size bound
set_option quotPrecheck false in
local notation "hatOK" => ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
  (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
    USize.size), Vals.RazeFits (.atom t) x y → (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList

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

/-- **`suffix` under `suffixC`'s bit**: `suffix_rounds`, each round `iter` ran read back by `suffix_round_of` at
    its bit (`iterC_run`): `ranC`'s codes and `fitsN` bits, `rep_tailC`, `rep_compC`, `rep_unionC`. -/
theorem rep_suffixC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hat : hatOK) (hb : (suffixC X).2 = true) :
    ∀ xs ys, rep (suffixC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  suffix_rounds X (fun s => (suffixRound s).1) (fun _ _ => rfl) fun i hi hne => by
    have h := iterC_run (X.1.toNat + 1) (fun s : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) => s.2.n == 0)
      suffixRound (idU X, idU X) hb i (by omega) hne
    rw [show (fun s => (suffixRound s).1)^[i + 1] (idU X, idU X) =
      (suffixRound ((fun s => (suffixRound s).1)^[i] (idU X, idU X))).1 from rfl]
    generalize (fun s => (suffixRound s).1)^[i] (idU X, idU X) = st at h ⊢
    obtain ⟨S, F⟩ := st
    simp only [suffixRound, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hW, hT⟩, hC⟩, hU⟩ := h
    simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hW
    exact suffix_round_of S F (rep_tailC _ hT) (rep_compC _ _ hC)
      (rep_ran_corefl F (one_ok _ (Obj.codesC_fits _ _ hW.1)) (pickFits_of_fitsN _ _ _ hW.2 _ (by simp)))
      (rep_unionC hat _ _ hU)

/-- The pairs `(c, y)` a round of `loopOn` meets at its states `St`, whose `ran` its step sees. -/
def loopPairs {K X Y : Obj} (St : Rel K (.prod X (.arr Y))) : Rel (.prod X (.arr Y)) (.prod X Y) :=
  pair (outl (ran St)) (outl (outr (ran St) ≫ uncons (ran (outr (ran St))).val))

/-- **`loopOn` under `loopOnC`'s bit**: `loopOn_rounds`, each round `iter` ran read back by `loop_round_set` at its
    bit (`iterC_run`): `ranC`'s and `domC`'s codes and `fitsN` bits, `rep_unconsC`, `rep_compC`, `rep_pairC`,
    `rep_nubC`, `rep_antiJoinC`, `rep_unionC`. What stays: the step's spec `hS` at the rounds whose step bit is
    set, and `unionC`'s `hat`. -/
theorem rep_loopOnC {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X × Bool)
    (P : Rel K (.prod X (.arr Y))) (hat : hatOK) (hb : (loopOnC F P).2 = true)
    (Fr : Nat → X.El × Y.El → X.El → Prop)
    (hS : ∀ i, (F (ran (loopPairs ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2))).2 = true →
      ∀ cy c', Fr i cy c' ↔ rep (F (ran (loopPairs ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2))).1 cy c') :
    ∀ k c, rep (loopOnC F P).1 k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  have e : (loopOnC F P).1 = loopOn (fun D => (F D).1) P := by
    simp only [loopOnC, loopOn, iterC_fst]; rfl
  have hf : ∀ (out : Rel K X) (St : Rel K (.prod X (.arr Y))) D u p, D = ran St → u = outr D ≫ uncons (ran (outr D)).val → p = pair (outl D) (outl u) →
      (loopRound F (out, St)).1 =
        (out ∪ St ≫ outl (antiJoin D (dom u)), Rel.nub (St ≫ pair (p ≫ (F (ran p)).1) (outr u))) := by
    intro out St D u p hD hu hp; subst hD hu hp; rw [← nubC_fst]; rfl
  have one : ∀ i, i ≤ (Rel.val P).2.1.toNat →
      (∀ i' ≤ i, (((fun s => (loopRound F s).1)^[i'] (Alg.zero, P)).2.n == 0) = false) →
      (∀ k (c' : X.El) (ys : List Y.El), rep ((fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P)).2 k (c', ys) ↔
        ∃ c y, rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2 k (c, y :: ys) ∧ Fr i (c, y) c') ∧
      ∀ k (c : X.El), rep ((fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P)).1 k c ↔
        rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).1 k c ∨
          rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2 k (c, []) := by
    intro i hi hne
    have h := iterC_run ((Rel.val P).2.1.toNat + 1) (fun s : Rel K X × Rel K (.prod X (.arr Y)) => s.2.n == 0)
      (loopRound F) (Alg.zero, P) hb i (by omega) hne
    have hSi := hS i
    rw [show (fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P) =
      (loopRound F ((fun s => (loopRound F s).1)^[i] (Alg.zero, P))).1 from rfl]
    generalize (fun s => (loopRound F s).1)^[i] (Alg.zero, P) = st at h hSi ⊢
    obtain ⟨out, St⟩ := st
    simp only [loopRound, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hW⟩, hc⟩, hu⟩, hp⟩, hG⟩, hQ⟩, hR⟩, hT⟩, hN⟩, hdu⟩, hA⟩, hO⟩, hU⟩ := h
    simp only [ranC, domC, distinctCoreflC, Bool.and_eq_true] at hD hW hdu
    have hr := loop_round_set out St _ _ _ _ _ _ _ _ _
      (rep_ran_corefl St (one_ok _ (Obj.codesC_fits _ _ hD.1)) (pickFits_of_fitsN _ _ _ hD.2 _ (by simp)))
      (rep_ran_corefl _ (one_ok _ (Obj.codesC_fits _ _ hW.1)) (pickFits_of_fitsN _ _ _ hW.2 _ (by simp <;> exact Nat.le_refl _)))
      (rep_unconsC _ hc) (rep_compC _ _ hu) (rep_pairC _ _ hp) (rep_compC _ _ hQ) (rep_pairC _ _ hR)
      (rep_compC _ _ hT) (by rw [← nubC_fst]; exact rep_nubC _ hN)
      (rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hdu.1)) (pickFits_of_fitsN _ _ _ hdu.2 _ (by simp <;> exact Nat.le_refl _)))
      (rep_antiJoinC _ _ hA) (rep_compC _ _ hO) (rep_unionC hat _ _ hU)
    have hFr := hSi hG
    simp only [loopRound, nubC_fst]
    exact ⟨fun k c' ys => (hr.1 k c' ys).trans
      (exists_congr fun c => exists_congr fun y => and_congr Iff.rfl (hFr _ _).symm), hr.2⟩
  rw [e]
  exact loopOn_rounds (fun D => (F D).1) P (fun s => (loopRound F s).1) hf Fr (fun i hi hne => (one i hi hne).1)
    (fun i hi hne => (one i hi hne).2)

/-- **`loop` under `loopC`'s bit**: `rep_loopOnC` at the step `F` with no bit of its own, its spec `rep F`. -/
theorem rep_loopC {K X Y : Obj} (F : Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) (hat : hatOK)
    (hb : (loopC F P).2 = true) :
    ∀ k c, rep (loopC F P).1 k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), rep F (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopOnC (fun _ => (F, true)) P hat hb (fun _ => rep F) fun _ _ _ _ => Iff.rfl

/-- **`fixOnC`'s answer is `fixOn`'s** at the step's relation: `iterC_fst`, `nubC_fst`. -/
theorem fixOnC_fst {A B : Obj} (n : Nat) (φC : Rel A B → Rel A B × Bool) (X₀ : Rel A B) :
    (fixOnC n φC X₀).1 = fixOn n (fun X => (φC X).1) X₀ := by
  simp only [fixOnC, iterC_fst, nubC_fst]; rfl

/-- **`fixOn` under `fixOnC`'s bit**: `rep_fixOn`, each round the loop ran read back by its bit (`iterC_run`):
    `rep_nubC` at the round's `nubC`, `hφ` at its step's bit. What stays is not capacity: `hφ`, the step's own spec,
    and `hc`, the chain property. -/
theorem rep_fixOnC {A B : Obj} (n : Nat) (φC : Rel A B → Rel A B × Bool) (X₀ : Rel A B)
    (Φ : type_of% (rep X₀) → type_of% (rep X₀)) (hb : (fixOnC n φC X₀).2 = true)
    (hφ : ∀ X, (φC X).2 = true → rep (φC X).1 = Φ (rep X))
    (hc : ∀ i < n, ((fun X => (φC X).1.nub)^[i] X₀.nub).n.toNat = ((fun X => (φC X).1.nub)^[i + 1] X₀.nub).n.toNat →
      rep ((fun X => (φC X).1.nub)^[i] X₀.nub) = rep ((fun X => (φC X).1.nub)^[i + 1] X₀.nub)) :
    ∃ j ≤ n, (fixOnC n φC X₀).1.2 = j ∧ rep (fixOnC n φC X₀).1.1 = Φ^[j] (rep X₀) ∧
      (j < n → Φ (rep (fixOnC n φC X₀).1.1) = rep (fixOnC n φC X₀).1.1) := by
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
  refine rep_fixOn n (fun X => (φC X).1) X₀ Φ (by rw [← nubC_fst]; exact rep_nubC X₀ h0) (fun i hi hne => ?_) hc
  have hr := iterC_run n (fun s => s.1 == s.2.1.n.toNat) r _ hit i hi fun i' hi' => by
    rw [ef, nubC_fst]
    cases i' with
    | zero => show (X₀.nub.n.toNat + 1 == X₀.nub.n.toNat) = false; simp
    | succ k =>
      rw [fixOn_iterate (fun X => (φC X).1) X₀ k]
      simpa using hne k (by omega)
  have hr' : (φC (g^[i] X₀.nub)).2 = true ∧ (nubC (φC (g^[i] X₀.nub)).1).2 = true := by
    rw [← es i]; exact Eq.mp (Bool.and_eq_true _ _) hr
  show rep (φC (g^[i] X₀.nub)).1.nub = Φ (rep (g^[i] X₀.nub))
  rw [← nubC_fst, rep_nubC _ hr'.2, hφ _ hr'.1]

#print axioms rep_fixOnC
#print axioms rep_ticC
#print axioms rep_suffixC
#print axioms rep_loopOnC
#print axioms rep_loopC

end Rep

namespace CRel

variable {K X Y B : Obj}

/-- `tic`, ok where `P` is and `ticC` ran within capacity. -/
def tic (P : CRel K (.prod B (.arr B))) : CRel K (.arr (.arr B)) := let r := ticC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `suffix` on the arrays `X`, ok where `suffixC` ran within capacity. -/
def suffix {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := suffixC X; ⟨r.1, r.2⟩

/-- `loopOn` on a step over `CRel`s, ok where `P` is, every round's step was and `loopOnC` ran within capacity. The
    step sees its input as ok: its bit is already in the loop's. -/
def loopOn (F : CRel (.prod X Y) (.prod X Y) → CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) : CRel K X :=
  let r := loopOnC (fun D => let s := F ⟨D, true⟩; (s.rel, s.ok)) P.rel; ⟨r.1, P.ok && r.2⟩

/-- `loop(F)`, ok where `F` and `P` are and `loopC` ran within capacity. -/
def loop (F : CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) : CRel K X :=
  let r := loopC F.rel P.rel; ⟨r.1, F.ok && P.ok && r.2⟩

theorem rep_tic (P : CRel K (.prod B (.arr B))) (hb : (tic P).ok = true) :
    ∀ k zss, rep (tic P).rel k zss ↔ ∃ b bs, rep P.rel k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) :=
  rep_ticC P.rel (by simp only [tic, Bool.and_eq_true] at hb; exact hb.2)

/-- `hat`: `rep_unionC`'s. -/
theorem rep_suffix {n : USize} (X : Vals (.arr B) n) (hat : hatOK) (hb : (suffix X).ok = true) :
    ∀ xs ys, rep (suffix X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  rep_suffixC X hat hb

/-- `hat`: `rep_unionC`'s; `hS` the step's spec at each round whose step was ok. -/
theorem rep_loopOn (F : CRel (.prod X Y) (.prod X Y) → CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y)))
    (hat : hatOK) (hb : (loopOn F P).ok = true) (Fr : Nat → X.El × Y.El → X.El → Prop)
    (hS : ∀ i, (F ⟨Alg.ran (loopPairs ((fun s => (loopRound (fun D => let s := F ⟨D, true⟩; (s.rel, s.ok)) s).1)^[i]
        (Alg.zero, P.rel)).2), true⟩).ok = true →
      ∀ cy c', Fr i cy c' ↔ rep (F ⟨Alg.ran (loopPairs ((fun s => (loopRound (fun D => let s := F ⟨D, true⟩;
        (s.rel, s.ok)) s).1)^[i] (Alg.zero, P.rel)).2), true⟩).rel cy c') :
    ∀ k c, rep (loopOn F P).rel k c ↔ ∃ c₀ xs, rep P.rel k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopOnC _ P.rel hat (by simp only [loopOn, Bool.and_eq_true] at hb; exact hb.2) Fr hS

/-- `hat`: `rep_unionC`'s. -/
theorem rep_loop (F : CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) (hat : hatOK) (hb : (loop F P).ok = true) :
    ∀ k c, rep (loop F P).rel k c ↔ ∃ c₀ xs, rep P.rel k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), rep F.rel (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopC F.rel P.rel hat (by simp only [loop, Bool.and_eq_true] at hb; exact hb.2)

/-- `fixOn` on a step over `CRel`s, with the rounds run: ok where `X₀` is, every round's step was and `fixOnC` ran
    within capacity. The step sees its input as ok: its bit is already in the loop's. -/
def fixOn {A : Obj} (n : Nat) (φ : CRel A B → CRel A B) (X₀ : CRel A B) : CRel A B × Nat :=
  let r := fixOnC n (fun D => let s := φ ⟨D, true⟩; (s.rel, s.ok)) X₀.rel; (⟨r.1.1, X₀.ok && r.2⟩, r.1.2)

/-- `hφ` the step's spec where its bit is set; `hc` the chain property (`rep_fixOn`'s). -/
theorem rep_fixOn {A : Obj} (n : Nat) (φ : CRel A B → CRel A B) (X₀ : CRel A B)
    (Φ : type_of% (rep X₀.rel) → type_of% (rep X₀.rel)) (hb : (fixOn n φ X₀).1.ok = true)
    (hφ : ∀ D, (φ ⟨D, true⟩).ok = true → rep (φ ⟨D, true⟩).rel = Φ (rep D))
    (hc : ∀ i < n, ((fun X => (φ ⟨X, true⟩).rel.nub)^[i] X₀.rel.nub).n.toNat =
        ((fun X => (φ ⟨X, true⟩).rel.nub)^[i + 1] X₀.rel.nub).n.toNat →
      rep ((fun X => (φ ⟨X, true⟩).rel.nub)^[i] X₀.rel.nub) =
        rep ((fun X => (φ ⟨X, true⟩).rel.nub)^[i + 1] X₀.rel.nub)) :
    ∃ j ≤ n, (fixOn n φ X₀).2 = j ∧ rep (fixOn n φ X₀).1.rel = Φ^[j] (rep X₀.rel) ∧
      (j < n → Φ (rep (fixOn n φ X₀).1.rel) = rep (fixOn n φ X₀).1.rel) := by
  -- unfolded first: the conclusion's `.2` against `fixOnC`'s otherwise sends `whnf` into `iter`'s recursion
  simp only [fixOn, Bool.and_eq_true] at hb ⊢
  exact rep_fixOnC n _ X₀.rel Φ hb.2 hφ hc

end CRel

end LeetQ.Rel
