/-
  §2.30's division read in `Rel` on one concrete example: who admires (`A`), hates (`H`) and works
  for (`W`) whom.  The note's pictures of `/` and of the symmetric division are drawn from these
  declarations by `diag-export --graph`, which lists each element type's constructors and DECIDES
  every pair, so an arrow on the page is a pair Lean evaluated and not one typed into the note.
-/
module

@[expose] public section

namespace Freyd.S2_30.Example

/-- A type whose elements are LISTED, which is what lets `decide` answer a `∀` over it. -/
class Listed (α : Type) where
  all : List α
  complete : ∀ a, a ∈ all

instance {α : Type} [Listed α] (P : α → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a ∈ Listed.all, P a) ⟨fun h a => h a (Listed.complete a), fun h a _ => h a⟩

/-- `x (R/S) y ⟺ ∀p. y S p → x R p`: `x` is `R`-related to everything `y` is `S`-related to. -/
def over {α β γ : Type} (R : α → γ → Prop) (S : β → γ → Prop) (x : α) (y : β) : Prop :=
  ∀ p, S y p → R x p

/-- `x (R÷S) y ⟺ ∀p. (x R p ⟺ y S p)`: what `R` sends `x` to is exactly what `S` sends `y` to. -/
def syq {α β γ : Type} (R : α → γ → Prop) (S : β → γ → Prop) (x : α) (y : β) : Prop :=
  ∀ p, R x p ↔ S y p

instance {α β γ : Type} [Listed γ] (R : α → γ → Prop) (S : β → γ → Prop) [DecidableRel R]
    [DecidableRel S] : DecidableRel (over R S) := fun x y =>
  inferInstanceAs (Decidable (∀ p, S y p → R x p))

instance {α β γ : Type} [Listed γ] (R : α → γ → Prop) (S : β → γ → Prop) [DecidableRel R]
    [DecidableRel S] : DecidableRel (syq R S) := fun x y =>
  inferInstanceAs (Decidable (∀ p, R x p ↔ S y p))

inductive Admirer | x | x' deriving DecidableEq
inductive Hater | y | y' deriving DecidableEq
inductive Worker | z deriving DecidableEq
inductive Person | a | b | c | d deriving DecidableEq

instance : Listed Admirer := ⟨[.x, .x'], fun e => by cases e <;> decide⟩
instance : Listed Hater := ⟨[.y, .y'], fun e => by cases e <;> decide⟩
instance : Listed Worker := ⟨[.z], fun e => by cases e <;> decide⟩
instance : Listed Person := ⟨[.a, .b, .c, .d], fun e => by cases e <;> decide⟩

/-- `x A p`: `x` admires `p`. -/
def A (u : Admirer) (p : Person) : Prop :=
  (u, p) ∈ ([(.x, .a), (.x, .b), (.x, .c), (.x', .a), (.x', .b)] : List (Admirer × Person))

/-- `y H p`: `y` hates `p`. -/
def H (u : Hater) (p : Person) : Prop :=
  (u, p) ∈ ([(.y, .a), (.y, .b), (.y, .c), (.y', .a), (.y', .b), (.y', .d)] : List (Hater × Person))

/-- `z W p`: `z` works for `p`. -/
def W (u : Worker) (p : Person) : Prop :=
  (u, p) ∈ ([(.z, .a), (.z, .b)] : List (Worker × Person))

instance : DecidableRel A := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))
instance : DecidableRel H := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))
instance : DecidableRel W := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- `x (A/H) y`: `x` admires everyone `y` hates. -/
def AH : Admirer → Hater → Prop := over A H
/-- `y (H/W) z`: `y` hates everyone `z` works for. -/
def HW : Hater → Worker → Prop := over H W
/-- `x (A/W) z`: `x` admires everyone `z` works for. -/
def AW : Admirer → Worker → Prop := over A W
/-- `x (A÷H) y`: `x` admires exactly whom `y` hates. -/
def AsyqH : Admirer → Hater → Prop := syq A H

instance : DecidableRel AH := inferInstanceAs (DecidableRel (over A H))
instance : DecidableRel HW := inferInstanceAs (DecidableRel (over H W))
instance : DecidableRel AW := inferInstanceAs (DecidableRel (over A W))
instance : DecidableRel AsyqH := inferInstanceAs (DecidableRel (syq A H))

/-- `(A/H)(H/W) ⊑ A/W`, strictly: `x'` admires everyone `z` works for, and no `y` joins them. -/
theorem AH_HW_lt_AW : (∀ u v w, AH u v → HW v w → AW u w) ∧ AW .x' .z ∧ ∀ v, ¬ (AH .x' v ∧ HW v .z) := by
  decide

/-- `A÷H` holds of one pair: `x` admires exactly whom `y` hates, and no other pair agrees. -/
theorem AsyqH_iff : ∀ u v, AsyqH u v ↔ u = .x ∧ v = .y := by decide

end Freyd.S2_30.Example
