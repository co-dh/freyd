import LeetQ.Rel.Lang.GenSpec

/-! `refold(c, S)` (`Gen.refold`, `Gen.refoldRounds`) computes `μX : c G(X) S`, read on relations as predicates:
    `Φ X = c G(X) S` is monotonic (the elaborator's polarity check) and local — its value at `a` reads `X` only at
    the children `ch = c ∈_G` of `a`, as `G(X)` reads `X` only at the members of a `G`-value. From the nodes `N`
    closed under `ch`, nothing valued, each round values the pending nodes with no pending child by `Φ` and drops
    them; the rounds that empty the pending set leave the least fixed point on `N` (`rounds_lfp`), and rounds stuck
    with nodes pending mean `ch` is not well-founded there (`stuck_not_acc`), the cycle `Gen.refold` reports.
    `Gen.rep_refold` reads the kernel `Gen.refoldRounds` back as `rounds_lfp` on its arrays. -/

namespace LeetQ.Rel.Refold

open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {α β : Type}

/-- `Φ X` at `a` reads `X` only at the children of `a`. -/
def Local (ch : α → α → Prop) (Φ : Core.Rel α β → Core.Rel α β) : Prop :=
  ∀ X Y a, (∀ a', ch a a' → ∀ b, (X a' b ↔ Y a' b)) → ∀ b, (Φ X a b ↔ Φ Y a b)

/-- A pending node none of whose children is pending. -/
def ready (ch : α → α → Prop) (pend : α → Prop) (a : α) : Prop := pend a ∧ ∀ a', ch a a' → ¬ pend a'

/-- `n` rounds from the pending nodes `pend` and the values `X`: the ready nodes valued by `Φ X` and dropped. -/
def rounds (ch : α → α → Prop) (Φ : Core.Rel α β → Core.Rel α β) :
    Nat → (α → Prop) → Core.Rel α β → (α → Prop) × Core.Rel α β
  | 0, pend, X => (pend, X)
  | n + 1, pend, X =>
    rounds ch Φ n (fun a => pend a ∧ ¬ ready ch pend a) (fun a b => X a b ∨ (ready ch pend a ∧ Φ X a b))

/-- What the rounds keep: pending nodes lie in `N` and have no value, a node of `N` done has the least fixed
    point's value, and its children are done. -/
def Inv (ch : α → α → Prop) (Φ : Core.Rel α β → Core.Rel α β) (N pend : α → Prop) (X : Core.Rel α β) : Prop :=
  (∀ a, pend a → N a) ∧ (∀ a, N a → ¬ pend a → ∀ b, (X a b ↔ mu Φ a b)) ∧ (∀ a, pend a → ∀ b, ¬ X a b) ∧
    (∀ a a', N a → ¬ pend a → ch a a' → ¬ pend a')

/-- One round keeps `Inv`: a ready node's children are done, so `Φ X` there is `Φ (mu Φ)` (`Local`), the least
    fixed point's value. -/
theorem round_inv {ch : α → α → Prop} {Φ : Core.Rel α β → Core.Rel α β} {N pend : α → Prop} {X : Core.Rel α β}
    (hm : Monotonic Φ)
    (hl : Local ch Φ) (hN : ∀ a a', N a → ch a a' → N a') (h : Inv ch Φ N pend X) :
    Inv ch Φ N (fun a => pend a ∧ ¬ ready ch pend a) (fun a b => X a b ∨ (ready ch pend a ∧ Φ X a b)) := by
  obtain ⟨hs, hd, he, hk⟩ := h
  refine ⟨fun a ha => hs a ha.1, fun a hNa hp b => ?_, fun a hp b hx => ?_, fun a a' hNa hp hc hp' => ?_⟩
  · by_cases hpa : pend a
    · have hr : ready ch pend a := Classical.byContradiction fun hr => hp ⟨hpa, hr⟩
      have key : Φ X a b ↔ mu Φ a b :=
        (hl X (mu Φ) a (fun a' hc b' => hd a' (hN a a' hNa hc) (hr.2 a' hc) b') b).trans
          (by rw [mu_fix hm])
      exact ⟨fun hx => hx.elim (fun hx => absurd hx (he a hpa b)) (fun hx => key.1 hx.2),
        fun hx => Or.inr ⟨hr, key.2 hx⟩⟩
    · exact ⟨fun hx => hx.elim (hd a hNa hpa b).1 (fun hx => absurd hx.1.1 hpa),
        fun hx => Or.inl ((hd a hNa hpa b).2 hx)⟩
  · exact hx.elim (he a hp.1 b) (fun hx => hp.2 hx.1)
  · by_cases hpa : pend a
    · exact (Classical.byContradiction fun hr => hp ⟨hpa, hr⟩ : ready ch pend a).2 a' hc hp'.1
    · exact hk a a' hNa hpa hc hp'.1

theorem rounds_inv {ch : α → α → Prop} {Φ : Core.Rel α β → Core.Rel α β} {N : α → Prop}
    (hm : Monotonic Φ) (hl : Local ch Φ)
    (hN : ∀ a a', N a → ch a a' → N a') :
    ∀ n pend X, Inv ch Φ N pend X → Inv ch Φ N (rounds ch Φ n pend X).1 (rounds ch Φ n pend X).2
  | 0, _, _, h => h
  | n + 1, _, _, h => rounds_inv hm hl hN n _ _ (round_inv hm hl hN h)

/-- **`refold` computes the least fixed point**: from the nodes `N` closed under `ch`, all pending and none valued,
    rounds that leave nothing pending value every node of `N` as `mu Φ`, `Φ X = c G(X) S`. -/
theorem rounds_lfp {ch : α → α → Prop} {Φ : Core.Rel α β → Core.Rel α β} {N : α → Prop}
    (hm : Monotonic Φ) (hl : Local ch Φ)
    (hN : ∀ a a', N a → ch a a' → N a') (n : Nat) (hdone : ∀ a, ¬ (rounds ch Φ n N fun _ _ => False).1 a) :
    ∀ a, N a → ∀ b, ((rounds ch Φ n N fun _ _ => False).2 a b ↔ mu Φ a b) := fun a hNa b =>
  (rounds_inv hm hl hN n N _ ⟨fun _ h => h, fun _ h hn => absurd h hn, fun _ _ _ h => h,
    fun _ _ h hn => absurd h hn⟩).2.1 a hNa (hdone a) b

/-- **Rounds stuck mean a cycle**: when no pending node is ready, no pending node is accessible along `ch`, so
    `ch` (the coalgebra `c`) is not well-founded at any of them. -/
theorem stuck_not_acc {ch : α → α → Prop} {pend : α → Prop} (hs : ∀ a, ¬ ready ch pend a) :
    ∀ a, Acc (fun x y => ch y x) a → ¬ pend a := by
  intro a hacc
  induction hacc with
  | intro a _ ih => exact fun hp => hs a ⟨hp, fun a' hc hp' => ih a' hc hp'⟩

end LeetQ.Rel.Refold

/-! ### The kernel read back -/

namespace LeetQ.Rel.Lang.Gen

open LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep LeetQ.Rel.Refold
open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B : Obj}

/-- A relation with no rows relates nothing. -/
theorem rep_empty {C : Obj} {R : Rel A C} (h : (R.n == 0) = true) (a : A.El) (c : C.El) : ¬ rep R a c := by
  rintro ⟨i, -⟩
  have : R.n.toNat = 0 := by simp [beq_iff_eq.1 h]
  exact absurd i.2 (by omega)

/-- `refoldRounds`' bits: where it reports the pending nodes emptied and its value ok, the pending nodes and the
    values it started from were ok. -/
theorem refoldRounds_ok {chN : CRel A A} {φ : CRel A B → CRel A A → CRel A B} :
    ∀ (f : Nat) (pend : CRel A A) (X : CRel A B), (refoldRounds chN φ f pend X).2 = true →
      (refoldRounds chN φ f pend X).1.ok = true → pend.ok = true ∧ X.ok = true
  | 0, _, _, h, _ => by simp [refoldRounds] at h
  | f + 1, pend, X, h, hx => by
    simp only [refoldRounds] at h hx
    by_cases h0 : (pend.rel.n == 0) = true
    · rw [if_pos h0] at h hx; exact ⟨h, hx⟩
    · rw [if_neg h0] at h hx
      by_cases h1 : ((CRel.diff pend (CRel.dom (CRel.comp (CRel.comp pend chN) pend))).rel.n == 0) = true
      · rw [if_pos h1] at h; exact absurd h Bool.false_ne_true
      · rw [if_neg h1] at h hx
        obtain ⟨hp, hx'⟩ := refoldRounds_ok f _ _ h hx
        have hp' := ok_and hp; have hx'' := ok_and hx'; rw [Bool.and_eq_true] at hp' hx''
        exact ⟨hp'.1, hx''.1⟩

/-- **`refoldRounds` read back** (`rounds_lfp` on arrays): from the nodes `N` (a coreflexive closed under the
    children `chN`), all pending and none valued, rounds whose bits say the pending nodes emptied and the value is
    ok leave `mu Φ` at every node of `N`, where `φ X P` is `Φ` at the nodes `P` (`onNodes`) and `Φ` is monotonic
    and local along `chN`. Rounds stuck are `stuck_not_acc`. -/
theorem rep_refold {chN : CRel A A} {φ : CRel A B → CRel A A → CRel A B}
    {Φ : Core.Rel A.El B.El → Core.Rel A.El B.El}
    (hm : Monotonic Φ) (hl : Local (fun a a' => rep chN.rel a a') Φ)
    (hφ : ∀ X P, (φ X P).ok = true → (∀ x y, rep P.rel x y → x = y) →
      ∀ a b, (rep (φ X P).rel a b ↔ rep P.rel a a ∧ Φ (fun a b => rep X.rel a b) a b))
    {N : CRel A A} (hc : ∀ x y, rep N.rel x y → x = y)
    (hN : ∀ a a', rep N.rel a a → rep chN.rel a a' → rep N.rel a' a') (f : Nat)
    (hb : (refoldRounds chN φ f N ⟨Alg.zero, true⟩).2 = true)
    (hx : (refoldRounds chN φ f N ⟨Alg.zero, true⟩).1.ok = true) :
    ∀ a, rep N.rel a a → ∀ b, (rep (refoldRounds chN φ f N ⟨Alg.zero, true⟩).1.rel a b ↔ Core.Rel.mu Φ a b) := by
  suffices h : ∀ f (pend : CRel A A) (X : CRel A B), (refoldRounds chN φ f pend X).2 = true →
      (refoldRounds chN φ f pend X).1.ok = true → (∀ x y, rep pend.rel x y → x = y) →
      Inv (fun a a' => rep chN.rel a a') Φ (fun a => rep N.rel a a) (fun a => rep pend.rel a a)
        (fun a b => rep X.rel a b) →
      ∀ a, rep N.rel a a → ∀ b, (rep (refoldRounds chN φ f pend X).1.rel a b ↔ Core.Rel.mu Φ a b) from
    h f N _ hb hx hc ⟨fun _ h => h, fun _ h hn => absurd h hn,
      fun _ _ _ h => by rw [rep_zero] at h; exact h, fun _ _ h hn => absurd h hn⟩
  intro f
  induction f with
  | zero => intro _ _ h; simp [refoldRounds] at h
  | succ f ih =>
    intro pend X h hx hcp hinv
    simp only [refoldRounds] at h hx ⊢
    by_cases h0 : (pend.rel.n == 0) = true
    · rw [if_pos h0]
      exact fun a hNa b => hinv.2.1 a hNa (rep_empty h0 a a) b
    · rw [if_neg h0] at h hx ⊢
      by_cases h1 : ((CRel.diff pend (CRel.dom (CRel.comp (CRel.comp pend chN) pend))).rel.n == 0) = true
      · rw [if_pos h1] at h; exact absurd h Bool.false_ne_true
      · rw [if_neg h1] at h hx ⊢
        obtain ⟨hp, hxo⟩ := refoldRounds_ok f _ _ h hx
        have hpr := ok_and hp; rw [Bool.and_eq_true] at hpr
        have hxr := ok_and hxo; rw [Bool.and_eq_true] at hxr
        have hro := ok_and hpr.2; rw [Bool.and_eq_true] at hro
        have hdo := ok_and hro.2
        have hc1 := ok_and hdo; rw [Bool.and_eq_true] at hc1
        -- the pending nodes' arcs into pending nodes: `pend ≫ chN ≫ pend`, `pend` coreflexive
        have hC : ∀ a y, rep (CRel.comp (CRel.comp pend chN) pend).rel a y ↔
            rep pend.rel a a ∧ rep chN.rel a y ∧ rep pend.rel y y := fun a y => by
          rw [CRel.rep_comp _ _ hdo, CRel.rep_comp _ _ hc1.1]
          constructor
          · rintro ⟨m, ⟨k, h1, h2⟩, h3⟩
            cases hcp _ _ h1; cases hcp _ _ h3; exact ⟨h1, h2, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨y, ⟨a, h1, h2⟩, h3⟩
        have hRd := CRel.rep_diff _ _ hpr.2
        have hready : ∀ a, rep (CRel.diff pend (CRel.dom (CRel.comp (CRel.comp pend chN) pend))).rel a a ↔
            rep pend.rel a a ∧ ∀ a', rep chN.rel a a' → ¬ rep pend.rel a' a' := fun a => by
          rw [hRd, CRel.rep_dom _ hro.2]
          exact ⟨fun ⟨hp, hn⟩ => ⟨hp, fun a' hc hp' => hn ⟨rfl, a', (hC a a').2 ⟨hp, hc, hp'⟩, (hC a a').2 ⟨hp, hc, hp'⟩⟩⟩,
            fun ⟨hp, hr⟩ => ⟨hp, fun ⟨_, y, hy, _⟩ => let ⟨_, hc, hp'⟩ := (hC a y).1 hy; hr y hc hp'⟩⟩
        have hcr : ∀ x y, rep (CRel.diff pend (CRel.dom (CRel.comp (CRel.comp pend chN) pend))).rel x y → x = y :=
          fun x y h => hcp x y ((hRd x y).1 h).1
        have eP : (fun a => rep (CRel.diff pend (CRel.diff pend
              (CRel.dom (CRel.comp (CRel.comp pend chN) pend)))).rel a a) =
            fun a => rep pend.rel a a ∧ ¬ Refold.ready (fun a a' => rep chN.rel a a') (fun a => rep pend.rel a a) a :=
          funext fun a => propext <| by rw [CRel.rep_diff _ _ hp, hready]; exact Iff.rfl
        have eX : (fun a b => rep (CRel.union X (φ X (CRel.diff pend
              (CRel.dom (CRel.comp (CRel.comp pend chN) pend))))).rel a b) =
            fun a b => rep X.rel a b ∨ (Refold.ready (fun a a' => rep chN.rel a a') (fun a => rep pend.rel a a) a ∧
              Φ (fun a b => rep X.rel a b) a b) :=
          funext fun a => funext fun b => propext <| by
            rw [CRel.rep_union _ _ hxo]
            exact or_congr Iff.rfl ((hφ _ _ hxr.2 hcr a b).trans (and_congr_left' (hready a)))
        refine ih _ _ h hx (fun x y h => hcp x y ((CRel.rep_diff _ _ hp x y).1 h).1) ?_
        rw [eP, eX]; exact round_inv hm hl hN hinv

#print axioms rep_refold

end LeetQ.Rel.Lang.Gen
