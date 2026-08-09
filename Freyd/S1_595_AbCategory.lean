/-
  Freyd & Scedrov, *Categories and Allegories* §1.595
  The category `Ab(𝒞)` of internal abelian group objects.

  §1.59 already builds:
    * `AbelianGroupObject 𝒞`     — internal abelian group objects (carrier + add/zero/neg + axioms);
    * `IsHomAbelianGroupObject`  — the homomorphism predicate `A.add ≫ x = (x×x) ≫ B.add`;
    * `HomAb A B`                — the hom subtype `{ x : A.carrier ⟶ B.carrier // IsHom … }`.

  The comment at S1_59.lean:603 explicitly defers "a `Cat` instance for Ab(A)" to future work.
  This file supplies it, together with the commutative-monoid (in fact abelian-group) structure
  on each hom-set Hom(A,B), which is the genuinely reusable additive content needed by the
  §1.55 / §1.595 exact-representation argument.

  PROVIDED here (all Sorry-free):
    * `instance Cat (AbelianGroupObject 𝒞)`               — identity + composition of group homs;
    * pointwise abelian-group structure on `HomAb A B`     — `add`/`zero`/`neg` via `B.add/zero/neg`,
      with the commutative-monoid + inverse laws and left/right bilinearity of composition.

  NOT provided (and WHY): the `HalfAdditiveCategory` class of S1_59 is *not* the
  "hom-sets are abelian monoids" predicate — it demands that `Ab(𝒞)` ITSELF be an abelian
  category (its field `prod_coprod_coincide` asserts the canonical A+B → A×B is iso, i.e.
  finite products coincide with finite coproducts *in `Ab(𝒞)`*).  That is exactly the
  §1.595 theorem "Ab(A) is abelian", which needs `𝒞` effective regular and the whole §1.594
  machinery — far beyond the group-object structure.  Instantiating it from the bare group
  structure would be vacuous/false, so we honestly stop at `Cat` + the hom-set abelian-group
  structure.  See the residual note at the bottom.
-/

module

public import Freyd.S1_59

open Freyd

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-! ### Product bookkeeping

  A single distributivity fact `g ≫ pair a b = pair (g ≫ a) (g ≫ b)` and the
  functoriality of the "square" `x×y = pair (fst ≫ x) (snd ≫ y)` underlie every proof below.
  We keep them local so this file imports only `S1_59`. -/

/-- The product map `x × y : A×B → C×D`, written `⟨fst ≫ x, snd ≫ y⟩`. -/
private def abSq {A B C D : 𝒞} (x : A ⟶ C) (y : B ⟶ D) : prod A B ⟶ prod C D :=
  pair (fst ≫ x) (snd ≫ y)

/-- Functoriality of the square: `(x×y) ≫ (x'×y') = (x≫x') × (y≫y')`. -/
private theorem abSq_comp {A B C D E F : 𝒞}
    (x : A ⟶ C) (y : B ⟶ D) (x' : C ⟶ E) (y' : D ⟶ F) :
    abSq x y ≫ abSq x' y' = abSq (x ≫ x') (y ≫ y') := by
  unfold abSq
  rw [pair_precomp]
  congr 1
  · rw [← Cat.assoc, fst_pair, Cat.assoc]
  · rw [← Cat.assoc, snd_pair, Cat.assoc]

/-! ### §1.595 The category `Ab(𝒞)`

  `Hom A B := HomAb A B`, identity = `id` of the carrier (a group hom),
  composition = composition of carriers (a composite of group homs is a group hom).
  All three category laws are inherited from `𝒞` via `Subtype.ext` on the carrier. -/

/-- The identity carrier map is a group-object homomorphism. -/
public theorem isHom_id (A : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject A A (Cat.id A.carrier) := by
  unfold IsHomAbelianGroupObject
  -- A.add ≫ id = A.add ;  ⟨fst ≫ id, snd ≫ id⟩ ≫ A.add = ⟨fst, snd⟩ ≫ A.add = id ≫ A.add = A.add
  rw [Cat.comp_id, Cat.comp_id, Cat.comp_id, pair_fst_snd, Cat.id_comp]

/-- A composite of group-object homomorphisms is a group-object homomorphism. -/
public theorem isHom_comp {A B C : AbelianGroupObject 𝒞}
    {x : A.carrier ⟶ B.carrier} {y : B.carrier ⟶ C.carrier}
    (hx : IsHomAbelianGroupObject A B x) (hy : IsHomAbelianGroupObject B C y) :
    IsHomAbelianGroupObject A C (x ≫ y) := by
  unfold IsHomAbelianGroupObject at *
  -- A.add ≫ (x≫y) = (A.add ≫ x) ≫ y = (⟨fst≫x,snd≫x⟩ ≫ B.add) ≫ y
  --              = ⟨fst≫x,snd≫x⟩ ≫ (B.add ≫ y) = ⟨fst≫x,snd≫x⟩ ≫ ⟨fst≫y,snd≫y⟩ ≫ C.add
  --              = (x×x ≫ y×y) ≫ C.add = (x≫y)×(x≫y) ≫ C.add.
  rw [← Cat.assoc, hx, Cat.assoc, hy, ← Cat.assoc]
  -- goal: ⟨fst≫x, snd≫x⟩ ≫ ⟨fst≫y, snd≫y⟩ ≫ C.add = ⟨fst≫(x≫y), snd≫(x≫y)⟩ ≫ C.add
  have : (pair (fst ≫ x) (snd ≫ x)) ≫ (pair (fst ≫ y) (snd ≫ y))
       = pair (fst ≫ x ≫ y) (snd ≫ x ≫ y) := by
    have := abSq_comp x x y y
    unfold abSq at this
    simpa [Cat.assoc] using this
  rw [this]

/-- §1.595: `Ab(𝒞)` is a category.  Hom-sets are the group-homomorphism subtypes;
    identity and composition are those of `𝒞`, restricted to homomorphisms. -/
@[expose] public instance instCatAb : Cat.{v} (AbelianGroupObject 𝒞) where
  Hom A B := HomAb A B
  id A := ⟨Cat.id A.carrier, isHom_id A⟩
  comp f g := ⟨f.val ≫ g.val, isHom_comp f.property g.property⟩
  id_comp f := Subtype.ext (Cat.id_comp f.val)
  comp_id f := Subtype.ext (Cat.comp_id f.val)
  assoc f g h := Subtype.ext (Cat.assoc f.val g.val h.val)

/-- The carrier of an `Ab(𝒞)`-morphism, projecting `Hom A B = HomAb A B` to `A.carrier ⟶ B.carrier`. -/
@[simp] theorem ab_comp_val {A B C : AbelianGroupObject 𝒞}
    (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).val = f.val ≫ g.val := rfl

@[simp] theorem ab_id_val (A : AbelianGroupObject 𝒞) :
    (Cat.id A).val = Cat.id A.carrier := rfl

/-! ### Pointwise abelian-group structure on `HomAb A B`

  `(x + y) := ⟨x, y⟩ ≫ B.add`,  `0 := ! ≫ B.zero`,  `-x := x ≫ B.neg`.
  Each is a group-object homomorphism (proved below), so they stay inside `HomAb`,
  and they satisfy the commutative-monoid + inverse laws plus bilinearity of `≫`.

  This is the additive content the §1.55/§1.595 exact representation consumes:
  the forgetful functor `Ab(𝒞) → 𝒞` is faithful and these operations are its
  preimages of `B`'s structure maps. -/

namespace HomAb

variable {A B C : AbelianGroupObject 𝒞}

/-- Underlying carrier map of a hom-set element. -/
def car (x : HomAb A B) : A.carrier ⟶ B.carrier := x.val

/-- Pointwise addition `⟨x, y⟩ ≫ B.add` at the carrier level. -/
@[expose] public def addCar (x y : HomAb A B) : A.carrier ⟶ B.carrier :=
  pair x.val y.val ≫ B.add

/-- Pointwise zero `! ≫ B.zero` at the carrier level. -/
@[expose] public def zeroCar (A B : AbelianGroupObject 𝒞) : A.carrier ⟶ B.carrier :=
  term A.carrier ≫ B.zero

/-- Pointwise negation `x ≫ B.neg` at the carrier level. -/
@[expose] public def negCar (x : HomAb A B) : A.carrier ⟶ B.carrier :=
  x.val ≫ B.neg

end HomAb

/-! ### Generalized-element arithmetic of a single group object `B`

  For an arbitrary source `T` and maps `f g : T ⟶ B.carrier` write
    `f ⊕ g := ⟨f, g⟩ ≫ B.add`,   `O := term T ≫ B.zero`,   `⊖f := f ≫ B.neg`.
  The group-object axioms (stated on the carrier) lift to these "generalized elements"
  by precomposition; this is the algebra every law below is built from.  All proofs are
  pure rewriting against the four `AbelianGroupObject` axiom fields. -/

namespace GElt

variable {T : 𝒞} (B : AbelianGroupObject 𝒞)

/-- `O ⊕ f = f` (zero is a left unit), from `B.add_zero` precomposed with `f`. -/
public theorem zero_add (f : T ⟶ B.carrier) :
    pair (term T ≫ B.zero) f ≫ B.add = f := by
  have h := congrArg (fun m => f ≫ m) B.add_zero
  simp only at h
  rw [← Cat.assoc, pair_precomp] at h
  -- f ≫ (term ≫ zero) = term_T ≫ zero  and  f ≫ id = f
  rwa [Cat.comp_id, ← Cat.assoc, term_uniq (f ≫ term B.carrier) (term T)] at h

/-- Commutativity `f ⊕ g = g ⊕ f`, from `B.add_comm` (`⟨snd,fst⟩ ≫ add = add`). -/
public theorem add_comm (f g : T ⟶ B.carrier) :
    pair f g ≫ B.add = pair g f ≫ B.add := by
  have h := congrArg (fun m => pair f g ≫ m) B.add_comm
  simp only at h
  rw [← Cat.assoc, pair_precomp, snd_pair, fst_pair] at h
  exact h.symm

/-- `f ⊕ O = f` (zero is a right unit), by commutativity + left unit. -/
public theorem add_zero (f : T ⟶ B.carrier) :
    pair f (term T ≫ B.zero) ≫ B.add = f := by
  rw [add_comm, zero_add]

/-- `(⊖f) ⊕ f = O` (left inverse), from `B.add_neg` precomposed with `f`. -/
public theorem neg_add (f : T ⟶ B.carrier) :
    pair (f ≫ B.neg) f ≫ B.add = term T ≫ B.zero := by
  have h := congrArg (fun m => f ≫ m) B.add_neg
  simp only at h
  rw [← Cat.assoc, pair_precomp, Cat.comp_id, ← Cat.assoc,
      term_uniq (f ≫ term B.carrier) (term T)] at h
  exact h

/-- `f ⊕ (⊖f) = O` (right inverse), by commutativity. -/
public theorem add_neg (f : T ⟶ B.carrier) :
    pair f (f ≫ B.neg) ≫ B.add = term T ≫ B.zero := by
  rw [add_comm, neg_add]

/-- Associativity in generalized-element form:
    `(f ⊕ g) ⊕ h = f ⊕ (g ⊕ h)`, from `B.add_assoc`. -/
public theorem add_assoc (f g h : T ⟶ B.carrier) :
    pair (pair f g ≫ B.add) h ≫ B.add = pair f (pair g h ≫ B.add) ≫ B.add := by
  -- precompose B.add_assoc (a map (B×B)×B → B) with ⟨⟨f,g⟩, h⟩ : T → (B×B)×B.
  have h0 := congrArg (fun m => pair (pair f g) h ≫ m) B.add_assoc
  simp only at h0
  -- Distribute the leading composite ⟨⟨f,g⟩,h⟩ through every pair/projection.
  simp only [← Cat.assoc, fst_pair, snd_pair, pair_precomp] at h0
  exact h0

/-- Composition distributes on the LEFT over `⊕`: `(k ≫ f) ⊕ (k ≫ g) = k ≫ (f ⊕ g)`
    for `k : S ⟶ T`.  (`k` factors out of `⟨k≫f, k≫g⟩ = k ≫ ⟨f,g⟩`.) -/
theorem comp_add {S : 𝒞} (k : S ⟶ T) (f g : T ⟶ B.carrier) :
    pair (k ≫ f) (k ≫ g) ≫ B.add = k ≫ (pair f g ≫ B.add) := by
  rw [← pair_precomp, Cat.assoc]

/-- **Middle-two interchange** `(p ⊕ q) ⊕ (r ⊕ s) = (p ⊕ r) ⊕ (q ⊕ s)`,
    from associativity + commutativity.  This is the Eckmann–Hilton step that makes
    `B`-addition of homs a homomorphism. -/
public theorem middle_two (p q r s : T ⟶ B.carrier) :
    pair (pair p q ≫ B.add) (pair r s ≫ B.add) ≫ B.add
      = pair (pair p r ≫ B.add) (pair q s ≫ B.add) ≫ B.add :=
  calc pair (pair p q ≫ B.add) (pair r s ≫ B.add) ≫ B.add
      = pair p (pair q (pair r s ≫ B.add) ≫ B.add) ≫ B.add := add_assoc B p q _
    _ = pair p (pair (pair q r ≫ B.add) s ≫ B.add) ≫ B.add := by rw [← add_assoc B q r s]
    _ = pair p (pair (pair r q ≫ B.add) s ≫ B.add) ≫ B.add := by rw [add_comm B q r]
    _ = pair p (pair r (pair q s ≫ B.add) ≫ B.add) ≫ B.add := by rw [add_assoc B r q s]
    _ = pair (pair p r ≫ B.add) (pair q s ≫ B.add) ≫ B.add := (add_assoc B p r _).symm

/-- `O ⊕ O = O`: the zero element is idempotent under `⊕` (special case of right unit). -/
public theorem zero_add_zero :
    pair (term T ≫ B.zero) (term T ≫ B.zero) ≫ B.add = term T ≫ B.zero :=
  add_zero B (term T ≫ B.zero)

/-- **Inverse uniqueness**: if `f ⊕ g = O` then `g = ⊖f`.  Standard group argument:
    `g = O ⊕ g = (⊖f ⊕ f) ⊕ g = ⊖f ⊕ (f ⊕ g) = ⊖f ⊕ O = ⊖f`. -/
public theorem neg_unique {f g : T ⟶ B.carrier}
    (h : pair f g ≫ B.add = term T ≫ B.zero) : g = f ≫ B.neg :=
  calc g = pair (term T ≫ B.zero) g ≫ B.add := (zero_add B g).symm
    _ = pair (pair (f ≫ B.neg) f ≫ B.add) g ≫ B.add := by rw [neg_add B f]
    _ = pair (f ≫ B.neg) (pair f g ≫ B.add) ≫ B.add := add_assoc B (f ≫ B.neg) f g
    _ = pair (f ≫ B.neg) (term T ≫ B.zero) ≫ B.add := by rw [h]
    _ = f ≫ B.neg := add_zero B (f ≫ B.neg)

/-- `⊖` distributes over `⊕` (true because `B` is *abelian*): `⊖(f ⊕ g) = (⊖f) ⊕ (⊖g)`.
    Both are the additive inverse of `f ⊕ g`, so they agree by `neg_unique`.  -/
public theorem neg_add_distrib (f g : T ⟶ B.carrier) :
    pair (f ≫ B.neg) (g ≫ B.neg) ≫ B.add = (pair f g ≫ B.add) ≫ B.neg := by
  apply neg_unique B
  -- (f⊕g) ⊕ (⊖f ⊕ ⊖g) = (f ⊕ ⊖f) ⊕ (g ⊕ ⊖g) = O ⊕ O = O
  rw [middle_two B f g (f ≫ B.neg) (g ≫ B.neg), add_neg B f, add_neg B g, zero_add_zero B]

end GElt

/-! ### The pointwise operations are group-object homomorphisms

  `addCar x y`, `zeroCar`, `negCar x` all land back in `HomAb A B`.  These are exactly
  the closure facts that let us put an abelian-group structure on the hom-subtype. -/

namespace HomAb

variable {A B C : AbelianGroupObject 𝒞}

/-- The pointwise sum of two homomorphisms is a homomorphism (middle-two interchange of `B`). -/
public theorem isHom_addCar (x y : HomAb A B) :
    IsHomAbelianGroupObject A B (addCar x y) := by
  unfold IsHomAbelianGroupObject addCar
  -- LHS: A.add ≫ ⟨x,y⟩ ≫ B.add = ⟨A.add≫x, A.add≫y⟩ ≫ B.add
  --    = ⟨⟨fst≫x,snd≫x⟩≫B.add, ⟨fst≫y,snd≫y⟩≫B.add⟩ ≫ B.add        (x,y homs)
  -- RHS: ⟨fst ≫ ⟨x,y⟩≫B.add, snd ≫ ⟨x,y⟩≫B.add⟩ ≫ B.add
  --    = ⟨⟨fst≫x,fst≫y⟩≫B.add, ⟨snd≫x,snd≫y⟩≫B.add⟩ ≫ B.add
  -- equal by middle_two with p=fst≫x, q=snd≫x, r=fst≫y, s=snd≫y.
  rw [← Cat.assoc, pair_precomp, x.property, y.property]
  rw [show pair (fst ≫ (pair x.val y.val ≫ B.add)) (snd ≫ (pair x.val y.val ≫ B.add))
        = pair (pair (fst ≫ x.val) (fst ≫ y.val) ≫ B.add)
               (pair (snd ≫ x.val) (snd ≫ y.val) ≫ B.add) by
      rw [← Cat.assoc, pair_precomp, ← Cat.assoc, pair_precomp]]
  exact GElt.middle_two B (fst ≫ x.val) (snd ≫ x.val) (fst ≫ y.val) (snd ≫ y.val)

/-- The pointwise zero `! ≫ B.zero` is a homomorphism (`O ⊕ O = O`). -/
public theorem isHom_zeroCar (A B : AbelianGroupObject 𝒞) :
    IsHomAbelianGroupObject A B (zeroCar A B) := by
  unfold IsHomAbelianGroupObject zeroCar
  -- LHS: A.add ≫ (term ≫ zero) = term_{A×A} ≫ zero  (term collapses).
  -- RHS: ⟨fst≫term≫zero, snd≫term≫zero⟩ ≫ B.add = ⟨term≫zero, term≫zero⟩ ≫ B.add = O.
  rw [← Cat.assoc, term_uniq (A.add ≫ term A.carrier) (term (prod A.carrier A.carrier)),
      ← Cat.assoc, term_uniq (fst ≫ term A.carrier) (term (prod A.carrier A.carrier)),
      ← Cat.assoc, term_uniq (snd ≫ term A.carrier) (term (prod A.carrier A.carrier))]
  exact (GElt.zero_add_zero B).symm

/-- The pointwise negation `x ≫ B.neg` is a homomorphism (`⊖` distributes, `B` abelian). -/
public theorem isHom_negCar (x : HomAb A B) :
    IsHomAbelianGroupObject A B (negCar x) := by
  unfold IsHomAbelianGroupObject negCar
  -- LHS: A.add ≫ x ≫ neg = (A.add ≫ x) ≫ neg = (⟨fst≫x,snd≫x⟩≫B.add) ≫ neg
  --    = ⟨(fst≫x)≫neg, (snd≫x)≫neg⟩ ≫ B.add                       (neg_add_distrib)
  -- RHS: ⟨fst≫x≫neg, snd≫x≫neg⟩ ≫ B.add  — identical after reassociation.
  rw [← Cat.assoc, x.property, ← Cat.assoc,
      ← GElt.neg_add_distrib B (fst ≫ x.val) (snd ≫ x.val), Cat.assoc, Cat.assoc]

/-! ### Abelian-group structure on the hom-set `HomAb A B`

  The three operations packaged as elements of the subtype, plus the abelian-group laws,
  all reduced to the `GElt` arithmetic.  This is the additive target the §1.55 / §1.595
  representation requires of `Ab(𝒞)`. -/

/-- Sum of homomorphisms, as a hom-set element. -/
@[expose] public def add (x y : HomAb A B) : HomAb A B := ⟨addCar x y, isHom_addCar x y⟩

/-- Zero homomorphism, as a hom-set element. -/
@[expose] public def zero (A B : AbelianGroupObject 𝒞) : HomAb A B := ⟨zeroCar A B, isHom_zeroCar A B⟩

/-- Negation of a homomorphism, as a hom-set element. -/
@[expose] public def neg (x : HomAb A B) : HomAb A B := ⟨negCar x, isHom_negCar x⟩

@[simp] theorem add_val (x y : HomAb A B) : (add x y).val = pair x.val y.val ≫ B.add := rfl
@[simp] theorem zero_val : (zero A B).val = term A.carrier ≫ B.zero := rfl
@[simp] theorem neg_val (x : HomAb A B) : (neg x).val = x.val ≫ B.neg := rfl

theorem add_assoc (x y z : HomAb A B) : add (add x y) z = add x (add y z) :=
  Subtype.ext (GElt.add_assoc B x.val y.val z.val)

theorem add_comm (x y : HomAb A B) : add x y = add y x :=
  Subtype.ext (GElt.add_comm B x.val y.val)

theorem zero_add (x : HomAb A B) : add (zero A B) x = x :=
  Subtype.ext (GElt.zero_add B x.val)

theorem add_zero (x : HomAb A B) : add x (zero A B) = x :=
  Subtype.ext (GElt.add_zero B x.val)

theorem neg_add (x : HomAb A B) : add (neg x) x = zero A B :=
  Subtype.ext (GElt.neg_add B x.val)

public theorem add_neg (x : HomAb A B) : add x (neg x) = zero A B :=
  Subtype.ext (GElt.add_neg B x.val)

/-! The six theorems above (`add_assoc`, `add_comm`, `zero_add`, `add_zero`, `neg_add`,
  `add_neg`) are exactly the abelian-group axioms for `(HomAb A B, add, zero, neg)`.
  The project is mathlib-free, so we record them as standalone lemmas rather than as a
  mathlib `AddCommGroup` instance; a bridge file may package them into one if needed. -/

/-! ### Bilinearity of composition over the hom-set addition

  `Ab(𝒞)`-composition is `≫` on carriers; it distributes over the pointwise `+` on each side.
  These are precisely the `HalfAdditiveCategory`/`Preadditive`-style axioms a downstream
  additive-category packaging of `Ab(𝒞)` would consume. -/

/-- Right distributivity at the carrier level: `(x + y) ≫ z = x ≫ z + y ≫ z`,
    where `z` is itself a homomorphism (so `≫z` commutes with `B.add` via `z.property`). -/
theorem addCar_comp (x y : HomAb A B) (z : HomAb B C) :
    addCar x y ≫ z.val = addCar (⟨x.val ≫ z.val, isHom_comp x.property z.property⟩)
                                (⟨y.val ≫ z.val, isHom_comp y.property z.property⟩) := by
  unfold addCar
  -- ⟨x,y⟩ ≫ B.add ≫ z = ⟨x,y⟩ ≫ ⟨fst≫z, snd≫z⟩ ≫ C.add  (z hom)
  --                   = ⟨x≫z, y≫z⟩ ≫ C.add.
  rw [Cat.assoc, z.property, ← Cat.assoc, pair_precomp]
  simp only [← Cat.assoc, fst_pair, snd_pair]

/-- Left distributivity at the carrier level: `w ≫ (x + y) = w ≫ x + w ≫ y`. -/
theorem comp_addCar {A' : AbelianGroupObject 𝒞} (w : HomAb A' A) (x y : HomAb A B) :
    w.val ≫ addCar x y = addCar (⟨w.val ≫ x.val, isHom_comp w.property x.property⟩)
                                (⟨w.val ≫ y.val, isHom_comp w.property y.property⟩) := by
  unfold addCar
  rw [← Cat.assoc, pair_precomp]

end HomAb

end Freyd
