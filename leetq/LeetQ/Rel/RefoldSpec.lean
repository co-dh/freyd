/-! `refold(c, S)` (`Gen.refold`, `Gen.refoldRounds`) computes `μX : c G(X) S`, read on relations as predicates:
    `Φ X = c G(X) S` is monotonic (the elaborator's polarity check) and local — its value at `a` reads `X` only at
    the children `ch = c ∈_G` of `a`, as `G(X)` reads `X` only at the members of a `G`-value. From the nodes `N`
    closed under `ch`, nothing valued, each round values the pending nodes with no pending child by `Φ` and drops
    them; the rounds that empty the pending set leave the least fixed point on `N` (`rounds_lfp`), and rounds stuck
    with nodes pending mean `ch` is not well-founded there (`stuck_not_acc`), the cycle `Gen.refold` reports. -/

namespace LeetQ.Rel.Refold

variable {α β : Type}

/-- A relation `α ⟶ β` as a predicate. -/
abbrev Rl (α β : Type) := α → β → Prop

/-- The least fixed point of `Φ`: the pairs in every pre-fixed point. -/
def lfp (Φ : Rl α β → Rl α β) : Rl α β := fun a b => ∀ Y : Rl α β, (∀ a b, Φ Y a b → Y a b) → Y a b

def Mono (Φ : Rl α β → Rl α β) : Prop := ∀ X Y : Rl α β, (∀ a b, X a b → Y a b) → ∀ a b, Φ X a b → Φ Y a b

/-- `Φ X` at `a` reads `X` only at the children of `a`. -/
def Local (ch : α → α → Prop) (Φ : Rl α β → Rl α β) : Prop :=
  ∀ X Y a, (∀ a', ch a a' → ∀ b, (X a' b ↔ Y a' b)) → ∀ b, (Φ X a b ↔ Φ Y a b)

/-- A pending node none of whose children is pending. -/
def ready (ch : α → α → Prop) (pend : α → Prop) (a : α) : Prop := pend a ∧ ∀ a', ch a a' → ¬ pend a'

/-- `n` rounds from the pending nodes `pend` and the values `X`: the ready nodes valued by `Φ X` and dropped. -/
def rounds (ch : α → α → Prop) (Φ : Rl α β → Rl α β) : Nat → (α → Prop) → Rl α β → (α → Prop) × Rl α β
  | 0, pend, X => (pend, X)
  | n + 1, pend, X =>
    rounds ch Φ n (fun a => pend a ∧ ¬ ready ch pend a) (fun a b => X a b ∨ (ready ch pend a ∧ Φ X a b))

/-- What the rounds keep: pending nodes lie in `N` and have no value, a node of `N` done has the least fixed
    point's value, and its children are done. -/
def Inv (ch : α → α → Prop) (Φ : Rl α β → Rl α β) (N pend : α → Prop) (X : Rl α β) : Prop :=
  (∀ a, pend a → N a) ∧ (∀ a, N a → ¬ pend a → ∀ b, (X a b ↔ lfp Φ a b)) ∧ (∀ a, pend a → ∀ b, ¬ X a b) ∧
    (∀ a a', N a → ¬ pend a → ch a a' → ¬ pend a')

theorem lfp_pre {Φ : Rl α β → Rl α β} (hm : Mono Φ) : ∀ a b, Φ (lfp Φ) a b → lfp Φ a b :=
  fun a b h Y hY => hY a b (hm (lfp Φ) Y (fun _ _ h' => h' Y hY) a b h)

theorem lfp_post {Φ : Rl α β → Rl α β} (hm : Mono Φ) : ∀ a b, lfp Φ a b → Φ (lfp Φ) a b :=
  fun _ _ h => h (Φ (lfp Φ)) (hm (Φ (lfp Φ)) (lfp Φ) (lfp_pre hm))

/-- One round keeps `Inv`: a ready node's children are done, so `Φ X` there is `Φ (lfp Φ)` (`Local`), the least
    fixed point's value. -/
theorem round_inv {ch : α → α → Prop} {Φ : Rl α β → Rl α β} {N pend : α → Prop} {X : Rl α β} (hm : Mono Φ)
    (hl : Local ch Φ) (hN : ∀ a a', N a → ch a a' → N a') (h : Inv ch Φ N pend X) :
    Inv ch Φ N (fun a => pend a ∧ ¬ ready ch pend a) (fun a b => X a b ∨ (ready ch pend a ∧ Φ X a b)) := by
  obtain ⟨hs, hd, he, hk⟩ := h
  refine ⟨fun a ha => hs a ha.1, fun a hNa hp b => ?_, fun a hp b hx => ?_, fun a a' hNa hp hc hp' => ?_⟩
  · by_cases hpa : pend a
    · have hr : ready ch pend a := Classical.byContradiction fun hr => hp ⟨hpa, hr⟩
      have key : Φ X a b ↔ lfp Φ a b :=
        (hl X (lfp Φ) a (fun a' hc b' => hd a' (hN a a' hNa hc) (hr.2 a' hc) b') b).trans
          ⟨lfp_pre hm a b, lfp_post hm a b⟩
      exact ⟨fun hx => hx.elim (fun hx => absurd hx (he a hpa b)) (fun hx => key.1 hx.2),
        fun hx => Or.inr ⟨hr, key.2 hx⟩⟩
    · exact ⟨fun hx => hx.elim (hd a hNa hpa b).1 (fun hx => absurd hx.1.1 hpa),
        fun hx => Or.inl ((hd a hNa hpa b).2 hx)⟩
  · exact hx.elim (he a hp.1 b) (fun hx => hp.2 hx.1)
  · by_cases hpa : pend a
    · exact (Classical.byContradiction fun hr => hp ⟨hpa, hr⟩ : ready ch pend a).2 a' hc hp'.1
    · exact hk a a' hNa hpa hc hp'.1

theorem rounds_inv {ch : α → α → Prop} {Φ : Rl α β → Rl α β} {N : α → Prop} (hm : Mono Φ) (hl : Local ch Φ)
    (hN : ∀ a a', N a → ch a a' → N a') :
    ∀ n pend X, Inv ch Φ N pend X → Inv ch Φ N (rounds ch Φ n pend X).1 (rounds ch Φ n pend X).2
  | 0, _, _, h => h
  | n + 1, _, _, h => rounds_inv hm hl hN n _ _ (round_inv hm hl hN h)

/-- **`refold` computes the least fixed point**: from the nodes `N` closed under `ch`, all pending and none valued,
    rounds that leave nothing pending value every node of `N` as `lfp Φ`, `Φ X = c G(X) S`. -/
theorem rounds_lfp {ch : α → α → Prop} {Φ : Rl α β → Rl α β} {N : α → Prop} (hm : Mono Φ) (hl : Local ch Φ)
    (hN : ∀ a a', N a → ch a a' → N a') (n : Nat) (hdone : ∀ a, ¬ (rounds ch Φ n N fun _ _ => False).1 a) :
    ∀ a, N a → ∀ b, ((rounds ch Φ n N fun _ _ => False).2 a b ↔ lfp Φ a b) := fun a hNa b =>
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
