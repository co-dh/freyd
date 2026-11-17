/-
  The concrete core (`doc/rel-repo-split-design.md` §2.1): a relation `Rel α β` is a predicate on pairs, with the
  allegory operators of `Rel(Set)` defined on it pointwise. No class: Rel proper is about this one model, and
  `LeetQ.Aop` ties each definition to the field of freyd's `RelSet` instance by `rfl`. Imports only the toolchain.
-/

namespace LeetQ.Core

universe u v w x

/-- A relation from `α` to `β`. -/
def Rel (α : Type u) (β : Type v) : Type (max u v) := α → β → Prop

namespace Rel

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-! ### Operations — the bodies of freyd's `RelSet` instance fields, so the bridge ties them by `rfl` -/

/-- The identity relation on `α`. -/
def id (α : Type u) : Rel α α := fun a b => a = b

/-- `R ≫ S`, diagram order: first `R`, then `S`. -/
def comp (R : Rel α β) (S : Rel β γ) : Rel α γ := fun a c => ∃ b, R a b ∧ S b c

/-- The converse `R°`. -/
def recip (R : Rel α β) : Rel β α := fun b a => R a b

def inter (R S : Rel α β) : Rel α β := fun a b => R a b ∧ S a b

def union (R S : Rel α β) : Rel α β := fun a b => R a b ∨ S a b

def zero : Rel α β := fun _ _ => False

/-- The allegory order, as freyd states it (§2.11): `R ⊑ S` iff `R ∩ S = R`. -/
def le (R S : Rel α β) : Prop := inter R S = R

scoped infixr:80 " ≫ " => Rel.comp
scoped postfix:max "°" => Rel.recip
scoped infixl:70 " ∩ " => Rel.inter
scoped infixl:65 " ∪ " => Rel.union
scoped infix:50 " ⊑ " => Rel.le
scoped notation "𝟘" => Rel.zero
scoped notation:max "𝟙" α:max => Rel.id α

/-! ### Structure maps -/

/-- `⊤`, every pair. -/
def top : Rel α β := fun _ _ => True

/-- The graph `b = f(a)` of a function. -/
def graph (f : α → β) : Rel α β := fun a b => b = f a

/-- The coreflexive `{(a,a) ∣ P(a)}`. -/
def corefl (P : α → Prop) : Rel α α := fun a b => a = b ∧ P a

/-- `⟨R,S⟩`: `a` to `(b,c)` when `R a b` and `S a c`. -/
def rpair (R : Rel γ α) (S : Rel γ β) : Rel γ (α × β) := fun c p => R c p.1 ∧ S c p.2

/-- `R × S` on pairs. -/
def rprodMap (R : Rel α γ) (S : Rel β δ) : Rel (α × β) (γ × δ) := fun p q => R p.1 q.1 ∧ S p.2 q.2

/-- The first injection into `α ⊕ β`. -/
def inl : Rel α (α ⊕ β) := graph Sum.inl

/-- The second injection into `α ⊕ β`. -/
def inr : Rel β (α ⊕ β) := graph Sum.inr

/-- `[R,S] = inl° R ∪ inr° S` (B&dM 5.9). -/
def junc (R : Rel α γ) (S : Rel β γ) : Rel (α ⊕ β) γ := (inl° ≫ R) ∪ (inr° ≫ S)

/-! ### Unfolding lemmas -/

theorem ext {R S : Rel α β} (h : ∀ a b, R a b ↔ S a b) : R = S :=
  funext fun a => funext fun b => propext (h a b)

theorem le_iff {R S : Rel α β} : R ⊑ S ↔ ∀ a b, R a b → S a b :=
  ⟨fun h a b hR => (show (R ∩ S) a b from (congrFun (congrFun h a) b) ▸ hR).2,
   fun h => ext fun a b => ⟨And.left, fun hR => ⟨hR, h a b hR⟩⟩⟩

@[simp] theorem comp_apply (R : Rel α β) (S : Rel β γ) (a : α) (c : γ) : (R ≫ S) a c = ∃ b, R a b ∧ S b c := rfl

@[simp] theorem recip_apply (R : Rel α β) (b : β) (a : α) : R° b a = R a b := rfl

@[simp] theorem inter_apply (R S : Rel α β) (a : α) (b : β) : (R ∩ S) a b = (R a b ∧ S a b) := rfl

@[simp] theorem union_apply (R S : Rel α β) (a : α) (b : β) : (R ∪ S) a b = (R a b ∨ S a b) := rfl

/-! ### Laws -/

theorem comp_assoc (R : Rel α β) (S : Rel β γ) (T : Rel γ δ) : (R ≫ S) ≫ T = R ≫ (S ≫ T) :=
  ext fun _ _ => ⟨fun ⟨b, ⟨c, hR, hS⟩, hT⟩ => ⟨c, hR, b, hS, hT⟩, fun ⟨c, hR, b, hS, hT⟩ => ⟨b, ⟨c, hR, hS⟩, hT⟩⟩

theorem inter_idem (R : Rel α β) : R ∩ R = R := ext fun _ _ => ⟨And.left, fun h => ⟨h, h⟩⟩

theorem union_idem (R : Rel α β) : R ∪ R = R := ext fun _ _ => ⟨fun h => h.elim (fun h => h) (fun h => h), Or.inl⟩

theorem le_refl (R : Rel α β) : R ⊑ R := inter_idem R

theorem le_antisymm {R S : Rel α β} (h₁ : R ⊑ S) (h₂ : S ⊑ R) : R = S :=
  ext fun a b => ⟨le_iff.1 h₁ a b, le_iff.1 h₂ a b⟩

theorem le_trans {R S T : Rel α β} (h₁ : R ⊑ S) (h₂ : S ⊑ T) : R ⊑ T :=
  le_iff.2 fun a b h => le_iff.1 h₂ a b (le_iff.1 h₁ a b h)

end Rel

end LeetQ.Core
