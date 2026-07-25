/-
  Freyd & Scedrov, *Categories and Allegories* §1.42  Finite products.

  HasTerminal (§1.421), HasBinaryProducts (§1.423).
  Diagonal: diag A = ⟨id, id⟩ : A → A×A.

  STRUCTURE: we define both classes first, then separate sections
  for terminal-dependent and product-dependent definitions so that
  `fst`, `snd`, `pair` do NOT require `HasTerminal` (§1.85 needs this).
-/

import Freyd.S1_1
import Freyd.S1_41


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ### HasTerminal class and definitions -/

class HasTerminal (𝒞 : Type u) [Cat.{v} 𝒞] where
  one   : 𝒞
  trm   : (X : 𝒞) → X ⟶ one
  uniq  : ∀ {X : 𝒞} (f g : X ⟶ one), f = g

section Terminal

variable [ht : HasTerminal 𝒞]

def one : 𝒞 := ht.one
def term (X : 𝒞) : X ⟶ one := ht.trm X

theorem term_uniq {X : 𝒞} (f g : X ⟶ one) : f = g := ht.uniq f g

/-- A SUBTERMINATOR is an object T such that T→1 is monic (§1.412). -/
def Subterminator (T : 𝒞) : Prop := Monic (term T)

/-- A VALUE is a subterminator (§1.412). -/
def Value : 𝒞 → Prop := Subterminator

/-! ### §1.421 Terminator unique up to unique iso -/

/-- The unique map between two terminator objects is an iso (§1.421).
    If `ht1` and `ht2` are both `HasTerminal` instances, then `ht1.one ≅ ht2.one`.
    We state this: for any two terminators B₁, B₂ with uniqueness, the map B₁→B₂ is iso. -/
theorem terminator_unique_iso
    (B₁ B₂ : 𝒞)
    (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₁)
    (uniq₁ : ∀ {X : 𝒞} (p q : X ⟶ B₁), p = q)
    (uniq₂ : ∀ {X : 𝒞} (p q : X ⟶ B₂), p = q) :
    IsIso f :=
  ⟨g, uniq₁ _ _, uniq₂ _ _⟩

end Terminal

/-! ### HasBinaryProducts class and definitions -/

class HasBinaryProducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  prod  : 𝒞 → 𝒞 → 𝒞
  fst   : {A B : 𝒞} → prod A B ⟶ A
  snd   : {A B : 𝒞} → prod A B ⟶ B
  pair  : {X A B : 𝒞} → (X ⟶ A) → (X ⟶ B) → (X ⟶ prod A B)
  fst_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ fst = f
  snd_pair : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B), pair f g ≫ snd = g
  pair_uniq : ∀ {X A B : 𝒞} (f : X ⟶ A) (g : X ⟶ B) (h : X ⟶ prod A B),
    h ≫ fst = f → h ≫ snd = g → h = pair f g

section Products

variable [hp : HasBinaryProducts 𝒞]

-- No wrapper defs/theorems: the class fields ARE the API, re-exposed unqualified.
-- (One-liner re-statements over wrapper defs made `rw [snd_pair]` match a different
-- spelling than the field's; exporting keeps statements and call sites identical.)
export HasBinaryProducts (prod fst snd pair fst_pair snd_pair pair_uniq)

attribute [simp] HasBinaryProducts.fst_pair HasBinaryProducts.snd_pair

def diag (A : 𝒞) : A ⟶ prod A A := pair (Cat.id A) (Cat.id A)

theorem diag_mono (A : 𝒞) : Monic (diag A) :=
  mono_of_retraction (diag A) fst (fst_pair _ _)

/-! ### §1.423 Product corollaries -/

/-- The pair of projections on A×B is the identity. -/
theorem pair_fst_snd {A B : 𝒞} : pair (fst (A := A) (B := B)) snd = Cat.id (prod A B) :=
  (pair_uniq fst snd (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm

/-- Projections fst and snd are jointly monic (§1.423): the product is a table on A, B. -/
theorem fst_snd_jointly_monic {A B : 𝒞} : MonicPair (fst (A := A) (B := B)) snd := by
  intro W f g hf hs
  have hfe : f = pair (f ≫ fst) (f ≫ snd) := pair_uniq _ _ f rfl rfl
  have hge : g = pair (g ≫ fst) (g ≫ snd) := pair_uniq _ _ g rfl rfl
  rw [hfe, hge, hf, hs]

/-- Products (like terminators) are unique up to isomorphism (§1.423).
    Given two product structures on the same pair A, B, the canonical map between them is iso. -/
theorem product_unique_iso {A B : 𝒞} [hp2 : HasBinaryProducts 𝒞]
    (f : prod A B ⟶ hp2.prod A B)
    (g : hp2.prod A B ⟶ prod A B)
    (hf₁ : f ≫ hp2.fst = fst) (hf₂ : f ≫ hp2.snd = snd)
    (hg₁ : g ≫ fst = hp2.fst) (hg₂ : g ≫ snd = hp2.snd) :
    IsIso f := by
  refine ⟨g, ?_, ?_⟩
  · -- f ≫ g = id : suffices pair (f≫g≫fst) (f≫g≫snd) = pair fst snd = id
    have h1 : (f ≫ g) ≫ fst = fst := by rw [Cat.assoc, hg₁, hf₁]
    have h2 : (f ≫ g) ≫ snd = snd := by rw [Cat.assoc, hg₂, hf₂]
    calc f ≫ g = pair ((f ≫ g) ≫ fst) ((f ≫ g) ≫ snd) := pair_uniq _ _ (f ≫ g) rfl rfl
      _ = pair fst snd := by rw [h1, h2]
      _ = Cat.id _ := pair_fst_snd
  · -- g ≫ f = id (using hp2)
    have h1 : (g ≫ f) ≫ hp2.fst = hp2.fst := by rw [Cat.assoc, hf₁, hg₁]
    have h2 : (g ≫ f) ≫ hp2.snd = hp2.snd := by rw [Cat.assoc, hf₂, hg₂]
    have hid1 : (Cat.id (hp2.prod A B)) ≫ hp2.fst = hp2.fst := Cat.id_comp _
    have hid2 : (Cat.id (hp2.prod A B)) ≫ hp2.snd = hp2.snd := Cat.id_comp _
    exact (hp2.pair_uniq hp2.fst hp2.snd (g ≫ f) h1 h2).trans
      (hp2.pair_uniq hp2.fst hp2.snd (Cat.id _) hid1 hid2).symm

/-! ### §1.426 Monic and monic into product -/

/-- §1.426: `x : T → A`, `y : T → B` is a monic pair iff `⟨x,y⟩ : T → A×B` is monic.
    This is the correspondence underlying `Rel(A,B) ≅ Sub(A×B)`. -/
theorem monicPair_iff_monic_pair {T A B : 𝒞} (x : T ⟶ A) (y : T ⟶ B) :
    MonicPair x y ↔ Monic (pair x y) := by
  -- `by` switches to tactic mode: we manipulate the goal step by step instead of
  -- writing the proof term directly. The goal is the `↔` (iff).
  -- `constructor` splits `P ↔ Q` into its two halves: prove `P → Q`, then `Q → P`.
  -- Each `·` below is a "bullet" that focuses on one of those two halves in turn.
  constructor
  -- ── Forward: assuming the pair is jointly monic, show ⟨x,y⟩ is monic. ──
  -- `Monic (pair x y)` unfolds to: for all g, h with g≫⟨x,y⟩ = h≫⟨x,y⟩, we get g = h.
  -- `intro` names the things we're given: the witness object W, the two maps g h,
  -- and the hypothesis `heq : g ≫ pair x y = h ≫ pair x y`. Goal becomes `g = h`.
  · intro hp W g h heq
    -- `hp : MonicPair x y` says: if `g≫x = h≫x` AND `g≫y = h≫y`, then `g = h`.
    -- `apply hp g h` makes `g = h` follow from hp, leaving its two premises as new goals.
    apply hp g h
    -- Premise 1: `g ≫ x = h ≫ x`. Prove it by a chain of equalities (`calc`).
    -- `rw` rewrites the goal using known equations: `Cat.assoc` reassociates
    -- `(g ≫ p) ≫ fst` into `g ≫ (p ≫ fst)`, and `fst_pair` says `⟨x,y⟩ ≫ fst = x`.
    · calc g ≫ x = (g ≫ pair x y) ≫ fst := by rw [Cat.assoc, fst_pair]
        -- swap g≫⟨x,y⟩ for h≫⟨x,y⟩ using our hypothesis `heq`
        _ = (h ≫ pair x y) ≫ fst := by rw [heq]
        -- collapse back the same way: `(h ≫ ⟨x,y⟩) ≫ fst = h ≫ x`
        _ = h ≫ x := by rw [Cat.assoc, fst_pair]
    -- Premise 2: identical argument on the second coordinate, using `snd` / `snd_pair`.
    · calc g ≫ y = (g ≫ pair x y) ≫ snd := by rw [Cat.assoc, snd_pair]
        _ = (h ≫ pair x y) ≫ snd := by rw [heq]
        _ = h ≫ y := by rw [Cat.assoc, snd_pair]
  -- ── Backward: assuming ⟨x,y⟩ is monic, show the pair is jointly monic. ──
  -- `MonicPair x y` unfolds to: given f, g with `f≫x = g≫x` (hx) and `f≫y = g≫y` (hy),
  -- conclude `f = g`. `intro` names all of these; goal becomes `f = g`.
  · intro hm W f g hx hy
    -- `hm : Monic (pair x y)` says `f ≫ ⟨x,y⟩ = g ≫ ⟨x,y⟩` is enough to force `f = g`.
    -- `apply hm f g` reduces the goal `f = g` to proving that single equation.
    apply hm f g
    -- `have` proves a small intermediate fact and names it (`e₁`, `e₂`).
    -- `pair_uniq` is the universal property: any map into A×B equals `⟨its fst part, its snd part⟩`.
    -- The two `(by …)` arguments discharge its side conditions:
    --   `(f ≫ ⟨x,y⟩) ≫ fst = f ≫ x` and `(f ≫ ⟨x,y⟩) ≫ snd = f ≫ y`.
    -- So e₁ rewrites `f ≫ ⟨x,y⟩` into the explicit pair `⟨f≫x, f≫y⟩`.
    have e₁ : f ≫ pair x y = pair (f ≫ x) (f ≫ y) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    -- e₂: the same for g, giving `g ≫ ⟨x,y⟩ = ⟨g≫x, g≫y⟩`.
    have e₂ : g ≫ pair x y = pair (g ≫ x) (g ≫ y) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    -- Goal `f ≫ ⟨x,y⟩ = g ≫ ⟨x,y⟩`. Rewrite both sides via e₁,e₂ to get
    -- `⟨f≫x, f≫y⟩ = ⟨g≫x, g≫y⟩`, then `hx : f≫x = g≫x` and `hy : f≫y = g≫y`
    -- make the two pairs literally identical, closing the goal.
    rw [e₁, e₂, hx, hy]

/-- If `y` is monic then `⟨x,y⟩ : T → A×B` is monic — the clean special case of §1.426
    (a single monic column already makes the pair monic). Used downstream in §1.64. -/
theorem monic_pair_of_monic {T A B : 𝒞} (x : T ⟶ A) (y : T ⟶ B) (hy : Monic y) :
    Monic (pair x y) :=
  (monicPair_iff_monic_pair x y).mp (fun f g _ hyy => hy f g hyy)

/-- §1.426: A monic b : A → B gives a correspondence Sub(A,B) ≅ Sub(A×B).
    The element in Sub(A×B) corresponding to b ∈ Sub(A,B) is pair(id_A, b) : A → A×B.
    Note: this map is monic when b is monic (use `monic_pair_of_monic`).
    The full §1.426 isomorphism of posets is formalized via the monic/subobject infrastructure
    in §1.56; here we record the key arrow: b monic → pair(id,b) monic. -/
theorem monic_id_pair_of_monic {A B : 𝒞} (b : A ⟶ B) (hb : Monic b) :
    Monic (pair (Cat.id A) b) := monic_pair_of_monic _ b hb

/-! ### Product commutativity (§1.42)  A×B ≅ B×A -/

/-- The swap map `A×B → B×A`, `⟨snd, fst⟩`. -/
def prodSwap (A B : 𝒞) : prod A B ⟶ prod B A := pair snd fst

/-- The swap is its own inverse: `(A×B → B×A → A×B)` is the identity. -/
theorem prodSwap_prodSwap {A B : 𝒞} : prodSwap A B ≫ prodSwap B A = Cat.id (prod A B) := by
  calc prodSwap A B ≫ prodSwap B A
      = pair ((prodSwap A B ≫ prodSwap B A) ≫ fst) ((prodSwap A B ≫ prodSwap B A) ≫ snd) :=
        pair_uniq _ _ _ rfl rfl
    _ = pair fst snd := by
        rw [Cat.assoc, show prodSwap B A ≫ fst = snd (A := B) (B := A) from fst_pair _ _,
            show prodSwap A B ≫ snd = fst (A := A) (B := B) from snd_pair _ _,
            Cat.assoc, show prodSwap B A ≫ snd = fst (A := B) (B := A) from snd_pair _ _,
            show prodSwap A B ≫ fst = snd (A := A) (B := B) from fst_pair _ _]
    _ = Cat.id (prod A B) := pair_fst_snd

/-- Product commutativity (§1.42): `A×B ≅ B×A`, witnessed by `prodSwap = ⟨snd, fst⟩`,
    which is its own inverse. -/
theorem prod_comm_iso {A B : 𝒞} : IsIso (prodSwap A B) :=
  ⟨prodSwap B A, prodSwap_prodSwap, prodSwap_prodSwap⟩

end Products

/-! ### Unit laws (§1.42)  1×B ≅ B  and  B×1 ≅ B -/

section Unitors

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-- Left unitor map `B → 1×B`, `⟨term B, id B⟩`. -/
def prodOneLeftInv (B : 𝒞) : B ⟶ prod one B := pair (term B) (Cat.id B)

/-- Round-trip on `1×B`: `(1×B → B → 1×B)` is the identity.
    The `fst` component collapses by `term_uniq` (any two maps into `1` agree). -/
theorem snd_prodOneLeftInv {B : 𝒞} :
    (snd : prod one B ⟶ B) ≫ prodOneLeftInv B = Cat.id (prod one B) := by
  have h1 : (snd ≫ prodOneLeftInv B) ≫ fst = fst (A := one) (B := B) := term_uniq _ _
  have h2 : (snd ≫ prodOneLeftInv B) ≫ snd = snd (A := one) (B := B) := by
    rw [Cat.assoc, show prodOneLeftInv B ≫ snd = Cat.id B from snd_pair _ _, Cat.comp_id]
  exact (pair_uniq fst snd _ h1 h2).trans pair_fst_snd

/-- Left unit law (§1.42): `1×B ≅ B`, witnessed by `snd : 1×B → B`. -/
theorem prod_one_iso_left {B : 𝒞} : IsIso (snd : prod one B ⟶ B) :=
  ⟨prodOneLeftInv B, snd_prodOneLeftInv, snd_pair _ _⟩

/-- Right unitor map `B → B×1`, `⟨id B, term B⟩`. -/
def prodOneRightInv (B : 𝒞) : B ⟶ prod B one := pair (Cat.id B) (term B)

/-- Round-trip on `B×1`: `(B×1 → B → B×1)` is the identity.
    The `snd` component collapses by `term_uniq`. -/
theorem fst_prodOneRightInv {B : 𝒞} :
    (fst : prod B one ⟶ B) ≫ prodOneRightInv B = Cat.id (prod B one) := by
  have h1 : (fst ≫ prodOneRightInv B) ≫ fst = fst (A := B) (B := one) := by
    rw [Cat.assoc, show prodOneRightInv B ≫ fst = Cat.id B from fst_pair _ _, Cat.comp_id]
  have h2 : (fst ≫ prodOneRightInv B) ≫ snd = snd (A := B) (B := one) := term_uniq _ _
  exact (pair_uniq fst snd _ h1 h2).trans pair_fst_snd

/-- Right unit law (§1.42): `B×1 ≅ B`, witnessed by `fst : B×1 → B`. -/
theorem prod_one_iso_right {B : 𝒞} : IsIso (fst : prod B one ⟶ B) :=
  ⟨prodOneRightInv B, fst_prodOneRightInv, fst_pair _ _⟩

end Unitors

/-! ### §1.425 Indexed products -/

/-- An indexed product of a family `{Aᵢ}ᵢ∈I` (§1.425):
    an object `P` with projections `pᵢ : P → Aᵢ` such that for any `X` and family
    `{xᵢ : X → Aᵢ}` there exists a unique `z : X → P` with `z ≫ pᵢ = xᵢ` for all i. -/
structure HasIndexedProduct.{w} {I : Type w} (family : I → 𝒞) where
  prod    : 𝒞
  proj    : (i : I) → prod ⟶ family i
  lift    : {X : 𝒞} → ((i : I) → X ⟶ family i) → (X ⟶ prod)
  lift_π  : ∀ {X : 𝒞} (fs : (i : I) → X ⟶ family i) (i : I), lift fs ≫ proj i = fs i
  lift_uniq : ∀ {X : 𝒞} (fs : (i : I) → X ⟶ family i) (h : X ⟶ prod),
    (∀ i, h ≫ proj i = fs i) → h = lift fs

/-- The empty product is a terminator (§1.425: product of the empty family). -/
def emptyProduct_is_terminator (ep : HasIndexedProduct (𝒞 := 𝒞) (fun i : Empty => i.elim)) :
    HasTerminal 𝒞 where
  one   := ep.prod
  trm   := fun _ => ep.lift (fun i => i.elim)
  uniq  := fun {_} f g =>
    (ep.lift_uniq (fun i => i.elim) f (fun i => i.elim)).trans
    (ep.lift_uniq (fun i => i.elim) g (fun i => i.elim)).symm

/-- §1.425: Finite products reduce to terminal + binary products.
    Any Fin n -indexed product can be built from HasTerminal + HasBinaryProducts.
    Base case n=0: the terminator is the empty product.
    Inductive step: prod(sub.prod, A_last) with proj i = snd (i=last) or fst≫sub.proj i (i<n). -/
def finiteProduct_from_term_binary [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    {n : Nat} (family : Fin n → 𝒞) : HasIndexedProduct family := by
  induction n with
  | zero =>
    exact {
      prod      := one
      proj      := fun i => i.elim0
      lift      := fun _ => term _
      lift_π    := fun _ i => i.elim0
      lift_uniq := fun _ m _ => term_uniq m _
    }
  | succ n ih =>
    -- Product of Fin(n+1)-family = (Product of first n) × A_last.
    -- proj i = if i = last then snd else fst ≫ sub.proj i.
    let sub := ih (family ∘ Fin.castSucc)
    exact {
      prod := prod sub.prod (family (Fin.last n))
      proj := Fin.lastCases snd (fun i => fst ≫ sub.proj i)
      lift := fun fs => pair (sub.lift (fun i => fs i.castSucc)) (fs (Fin.last n))
      lift_π := by
        intro X fs i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.lastCases_last, snd_pair]
        · intro j
          simp only [Fin.lastCases_castSucc]
          rw [← Cat.assoc, fst_pair, sub.lift_π]
      lift_uniq := by
        intro X fs h heq
        apply pair_uniq
        · apply sub.lift_uniq
          intro i
          have hi := heq i.castSucc
          simp only [Fin.lastCases_castSucc] at hi
          rw [← Cat.assoc] at hi
          exact hi
        · have hl := heq (Fin.last n)
          simp only [Fin.lastCases_last] at hl
          exact hl
    }

end Freyd
