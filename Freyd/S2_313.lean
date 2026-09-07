module

/-
  Freyd & Scedrov, *Categories and Allegories* §2.313.

    "For β --S--> γ in a division allegory the function (α,β) --(−)S--> (α,γ) has a right
     adjoint, namely (α,γ) --(−)/S--> (α,β).  We could have defined division allegories in
     this manner."

  As written, §2.313 still mixes the two things `notation_as_a_tool_of_thought_adjunction.typ`
  separates: `X ≫ S` is a COMPOSITE, but `•S` is APPLIED to `X`.  The note's cure is to lift an
  element to a constant, `X : * → x`, so that `F(x)` becomes the composite `X F`.  That is what
  this file does, and the claim it settles is that `•S ⊣ •/S` is an adjunction between two
  arrows, with `•` the composition operator on both sides:

    item 1  an arrow `X : a ⟶ b` becomes the point `pt X : * ⟶ (a,b)`      (`Pre.pt_comp`)
    item 2  application becomes composition in diagram order                (`instCatPre`)
    item 5  `X ⊑ X F` at every point `X` is `𝟙 ⊑ F`                        (`one_le_of_pt`)

  so that §2.313 reads `Adj (postComp a S) (postDiv a S)` — an equivalence between containments
  of ARROWS, no element of a hom-set named.  The `•` is composition in `Pre`, NOT in `𝒜`: `•/S`
  is an arrow of `Pre`, and there is no relation `D` with `X / S = X ≫ D`.  Lifting to points is
  exactly what buys the second `•`.

  Unit, counit and the two snakes for division are `(comp_adj_div a S).unit`, `.counit`,
  `.snake_left`, `.snake_right`.

  `Pre` and its arrows are defined here rather than in the §1.51 order module because §2.313 is
  their only site; move them up if a second one appears.
-/

public import Freyd.S1_51_Order
public import Freyd.S2_30

universe v u

namespace Freyd

/-! ## Preorders and monotone maps

  §1.51's `GaloisConnection` is stated over a bare relation `le`, which is all its carriers need.
  A point `* ⟶ P` needs more: the order must travel with the carrier, or there is nothing for the
  constant to be an arrow INTO. -/

/-- A PREORDERED TYPE: §1.51's poset without antisymmetry, bundled with its carrier. -/
public structure Pre : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  /-- The order. -/
  le : carrier → carrier → Prop
  /-- Reflexivity. -/
  le_refl : ∀ x, le x x
  /-- Transitivity. -/
  le_trans : ∀ {x y z}, le x y → le y z → le x z

/-- A MONOTONE MAP, the note's `/` and `\`. -/
public structure Monotone (P Q : Pre.{u}) : Type u where
  /-- The underlying function. -/
  toFun : P.carrier → Q.carrier
  /-- Order preservation — the note's standing hypothesis "given `F`, `G` monotonic". -/
  mono : ∀ {x y}, P.le x y → Q.le (toFun x) (toFun y)

/-- Item 2: preorders and monotone maps form a category, so `F` applied to `x` can be written as
    a composite in diagram order. -/
public instance instCatPre : Cat Pre.{u} where
  Hom P Q := Monotone P Q
  id _ := ⟨fun x => x, fun h => h⟩
  comp F G := ⟨fun x => G.toFun (F.toFun x), fun h => G.mono (F.mono h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Containment of monotone maps, pointwise: the note's little box one level up. -/
@[expose] public def Monotone.le {P Q : Pre.{u}} (F G : P ⟶ Q) : Prop :=
  ∀ x, Q.le (F.toFun x) (G.toFun x)

@[inherit_doc] infix:50 " ⊑ " => Monotone.le

/-- Whiskering on the left preserves containment. -/
public theorem Monotone.whisker_left {O P Q : Pre.{u}} (E : O ⟶ P) {F G : P ⟶ Q} (h : F ⊑ G) :
    E ≫ F ⊑ E ≫ G := fun x => h (E.toFun x)

/-- Whiskering on the right preserves containment (this is where `E` must be monotone). -/
public theorem Monotone.whisker_right {P Q R : Pre.{u}} {F G : P ⟶ Q} (h : F ⊑ G) (E : Q ⟶ R) :
    F ≫ E ⊑ G ≫ E := fun x => E.mono (h x)

/-- Two monotone maps contained in each other are equal, when the target is antisymmetric.
    Antisymmetry is a hypothesis rather than a field of `Pre` because §1.51's carriers are
    preorders of representatives; the allegory hom-sets used below do have it (`le_antisymm`). -/
public theorem Monotone.ext_of_le {P Q : Pre.{u}}
    (anti : ∀ {x y : Q.carrier}, Q.le x y → Q.le y x → x = y) {F G : P ⟶ Q}
    (h₁ : F ⊑ G) (h₂ : G ⊑ F) : F = G := by
  obtain ⟨f, _⟩ := F
  obtain ⟨g, _⟩ := G
  have : f = g := funext fun x => anti (h₁ x) (h₂ x)
  subst this; rfl

/-! ## Points

  The note's item 1: an element of a preorder, presented as an arrow out of the one-point
  preorder, so that the only operation left in sight is composition. -/

/-- The one-point preorder, the note's `*`. -/
@[expose] public def Pre.star : Pre.{u} :=
  ⟨PUnit, fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

/-- Item 1: the element `x` as the constant `* ⟶ P`. -/
@[expose] public def Pre.pt {P : Pre.{u}} (x : P.carrier) : Pre.star ⟶ P :=
  ⟨fun _ => x, fun _ => P.le_refl x⟩

/-- Item 1, the point of it: APPLICATION IS COMPOSITION. -/
public theorem Pre.pt_comp {P Q : Pre.{u}} (x : P.carrier) (F : P ⟶ Q) :
    Pre.pt x ≫ F = Pre.pt (F.toFun x) := rfl

/-- A point is contained in another exactly when its value is. -/
public theorem Pre.pt_le {P : Pre.{u}} {x y : P.carrier} : (Pre.pt x ⊑ Pre.pt y) ↔ P.le x y :=
  ⟨fun h => h PUnit.unit, fun h _ => h⟩

/-! ## Adjunction without application -/

/-- `F ⊣ G`: §1.51's adjoint pair with items 1 and 2 applied — for all POINTS `X` of `P` and `Y`
    of `Q`, `X F ⊑ Y` iff `X ⊑ Y G`.  Every operation here is composition. -/
@[expose] public def Adj {P Q : Pre.{u}} (F : P ⟶ Q) (G : Q ⟶ P) : Prop :=
  ∀ (X : Pre.star ⟶ P) (Y : Pre.star ⟶ Q), X ≫ F ⊑ Y ↔ X ⊑ Y ≫ G

/-- Cancelling the points returns §1.51's `GaloisConnection`, so nothing was added or lost. -/
public theorem adj_iff_galois {P Q : Pre.{u}} (F : P ⟶ Q) (G : Q ⟶ P) :
    Adj F G ↔ GaloisConnection P.le Q.le F.toFun G.toFun := by
  constructor
  · intro h x y
    exact ⟨fun hxy => (h (Pre.pt x) (Pre.pt y)).mp (fun _ => hxy) PUnit.unit,
           fun hxy => (h (Pre.pt x) (Pre.pt y)).mpr (fun _ => hxy) PUnit.unit⟩
  · intro h X Y
    exact ⟨fun hXY u => (h _ _).mp (hXY u), fun hXY u => (h _ _).mpr (hXY u)⟩

/-- Item 5, left half: `X ⊑ X F` at every point is `𝟙 ⊑ F`. -/
public theorem one_le_of_pt {P : Pre.{u}} (F : P ⟶ P) :
    (∀ X : Pre.star ⟶ P, X ⊑ X ≫ F) ↔ 𝟙 P ⊑ F := by
  constructor
  · intro h x; exact h (Pre.pt x) PUnit.unit
  · intro h X u; exact h (X.toFun u)

/-- Item 5, right half: `Y G ⊑ Y` at every point is `G ⊑ 𝟙`. -/
public theorem le_one_of_pt {P : Pre.{u}} (G : P ⟶ P) :
    (∀ Y : Pre.star ⟶ P, Y ≫ G ⊑ Y) ↔ G ⊑ 𝟙 P := by
  constructor
  · intro h y; exact h (Pre.pt y) PUnit.unit
  · intro h Y u; exact h (Y.toFun u)

namespace Adj

variable {P Q : Pre.{u}} {F : P ⟶ Q} {G : Q ⟶ P}

/-- The UNIT `𝟙 ⊑ F G`, the note's `* over /\`: take `Y := X F` in `F ⊣ G`. -/
public theorem unit (h : Adj F G) : 𝟙 P ⊑ F ≫ G := by
  refine (one_le_of_pt (F ≫ G)).mp fun X => ?_
  have hX := (h X (X ≫ F)).mp fun x => Q.le_refl _
  rwa [Cat.assoc] at hX

/-- The COUNIT `G F ⊑ 𝟙`, the note's `\/ over *`: take `X := Y G` in `F ⊣ G`. -/
public theorem counit (h : Adj F G) : G ≫ F ⊑ 𝟙 Q := by
  refine (le_one_of_pt (G ≫ F)).mp fun Y => ?_
  have hY := (h (Y ≫ G) Y).mpr fun x => P.le_refl _
  rwa [Cat.assoc] at hY

/-- The snake `/\/ = /`, given antisymmetry in the target. -/
public theorem snake_left (anti : ∀ {x y : Q.carrier}, Q.le x y → Q.le y x → x = y)
    (h : Adj F G) : F ≫ G ≫ F = F := by
  refine Monotone.ext_of_le anti ?_ ?_
  · have := Monotone.whisker_left F h.counit
    rwa [Cat.comp_id] at this
  · have := Monotone.whisker_right h.unit F
    rwa [Cat.id_comp, Cat.assoc] at this

/-- The snake `\/\ = \`, given antisymmetry in the target. -/
public theorem snake_right (anti : ∀ {x y : P.carrier}, P.le x y → P.le y x → x = y)
    (h : Adj F G) : G ≫ F ≫ G = G := by
  refine Monotone.ext_of_le anti ?_ ?_
  · have := Monotone.whisker_right h.counit G
    rwa [Cat.id_comp, Cat.assoc] at this
  · have := Monotone.whisker_left G h.unit
    rwa [Cat.comp_id] at this

/-- Adjunctions COMPOSE, the right adjoints in the opposite order.  The proof is the note's chain
    of `adj` steps: one `h₂`, one `h₁`, and the two re-bracketings between them. -/
public theorem comp {P Q R : Pre.{u}} {F₁ : P ⟶ Q} {G₁ : Q ⟶ P} {F₂ : Q ⟶ R} {G₂ : R ⟶ Q}
    (h₁ : Adj F₁ G₁) (h₂ : Adj F₂ G₂) : Adj (F₁ ≫ F₂) (G₂ ≫ G₁) := by
  intro X Z
  rw [← Cat.assoc, ← Cat.assoc]
  exact Iff.trans (h₂ (X ≫ F₁) Z) (h₁ X (Z ≫ G₂))

/-- A left adjoint determines its right adjoint, given antisymmetry in the source. -/
public theorem right_unique {P Q : Pre.{u}}
    (anti : ∀ {x y : P.carrier}, P.le x y → P.le y x → x = y)
    {F : P ⟶ Q} {G G' : Q ⟶ P} (h : Adj F G) (h' : Adj F G') : G = G' := by
  refine Monotone.ext_of_le anti (fun y => ?_) (fun y => ?_)
  · exact (h' (Pre.pt y ≫ G) (Pre.pt y)).mp
      ((h (Pre.pt y ≫ G) (Pre.pt y)).mpr fun _ => P.le_refl _) PUnit.unit
  · exact (h (Pre.pt y ≫ G') (Pre.pt y)).mp
      ((h' (Pre.pt y ≫ G') (Pre.pt y)).mpr fun _ => P.le_refl _) PUnit.unit

end Adj

/-! ## §2.313 -/

namespace Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- The hom-set `(a,b)` of the book, as a preorder. -/
@[expose] public def homPre (a b : 𝒜) : Pre.{v} := ⟨a ⟶ b, le, le_refl, fun h k => le_trans h k⟩

/-- `•S : (a,b) ⟶ (a,c)`, the note's `/`. -/
@[expose] public def postComp (a : 𝒜) {b c : 𝒜} (S : b ⟶ c) : homPre a b ⟶ homPre a c :=
  ⟨(· ≫ S), fun h => comp_mono_right h S⟩

/-- `•/S : (a,c) ⟶ (a,b)`, the note's `\`. -/
@[expose] public def postDiv (a : 𝒜) {b c : 𝒜} (S : b ⟶ c) : homPre a c ⟶ homPre a b :=
  ⟨(· / S), fun h => div_mono_left h S⟩

/-- **§2.313**: `•S ⊣ •/S`.  Both sides are composition — `pt X ≫ postComp a S = pt (X ≫ S)`
    and `pt X ≫ postDiv a S = pt (X / S)`, by `Pre.pt_comp` — so the statement contains no
    application. -/
public theorem comp_adj_div (a : 𝒜) {b c : 𝒜} (S : b ⟶ c) : Adj (postComp a S) (postDiv a S) := by
  intro X Y
  exact ⟨fun h u => (le_div_iff _ _ _).mpr (h u), fun h u => (le_div_iff _ _ _).mp (h u)⟩

/-- `•(S T) = •S ≫ •T`: associativity, the ascending side of the note's §1.1. -/
public theorem postComp_comp (a : 𝒜) {b c d : 𝒜} (S : b ⟶ c) (T : c ⟶ d) :
    postComp a (S ≫ T) = postComp a S ≫ postComp a T :=
  Monotone.ext_of_le le_antisymm (fun X => le_of_eq (Cat.assoc X S T).symm)
    (fun X => le_of_eq (Cat.assoc X S T))

/-- **§2.314 with the point cancelled**: `•/(S T) = •/T ≫ •/S`.  Dividing by a composite is
    dividing by `T` and then by `S`; the divisors come off in the REVERSE order, which is what
    the note's §1.1 draws by putting the second factor at the top of the descent.  Proved from
    §2.313 alone: right adjoints compose the other way round, and a left adjoint has only one
    right adjoint.  `div_comp_assoc` is the same fact with a point applied,
    `R / (S ≫ T) = (R / T) / S`. -/
public theorem postDiv_comp (a : 𝒜) {b c d : 𝒜} (S : b ⟶ c) (T : c ⟶ d) :
    postDiv a (S ≫ T) = postDiv a T ≫ postDiv a S := by
  have h : Adj (postComp a (S ≫ T)) (postDiv a T ≫ postDiv a S) := by
    rw [postComp_comp]
    exact Adj.comp (comp_adj_div a S) (comp_adj_div a T)
  exact Adj.right_unique le_antisymm (comp_adj_div a (S ≫ T)) h

end Alg

end Freyd
