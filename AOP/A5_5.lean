/-
  Bird & de Moor, *Algebra of Programming* §5.5  Relational catamorphisms
  (the Eilenberg–Wright lemma, book pp. 121–122).

  For a relator `F` on `𝒜` with an initial algebra `α : F t ⟶ t` in the subcategory of
  MAPS of `𝒜`, every algebra `R : F c ⟶ c` (a relation, not necessarily a map) has a
  UNIQUE relational catamorphism `(|R|) : t ⟶ c` characterised by
  `α · X = FX · R ⟺ X = (|R|)`  (5.12, mirrored to diagram order: `α ≫ X = F.map X ≫ R`).

  B&dM's construction: `(|R|) = ∈ · (|Λ(R·F∈)|)`, i.e. transpose the relational algebra
  `R : F c ⟶ c` through the power object of `c` to the MAP algebra
  `Λ(R·F∈) : F [c] ⟶ [c]` (Freyd: `A (F.map (∋ c) ≫ R) : F.obj (powerObj c) ⟶ powerObj c`),
  take the ordinary (map) catamorphism of that, and compose with `∈` to come back down
  to `c`.  All composition is diagram order (Freyd `≫`), mirroring B&dM's `·`.

  Needs Lemma 5.1 ("relators preserve maps": `Map f → Map (F f) ∧ F(f°) = (F f)°`) — its
  canonical home is `A5_1.lean` (added by a parallel wave); a private copy is proved here
  from `recip_of_comp_id` (A4_2) so this file does not block on that landing.
-/
module

public import Freyd.S2_40
public import AOP.A4_6
public import AOP.A4_2
public import AOP.A5_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] (F : Relator 𝒜 𝒜)

-- (Lemma 5.1 "relators preserve maps" now comes from A5_1: `Relator.map_is_map`.)

/-- **B&dM p.121**: `F` has an initial algebra `α : F t ⟶ t` IN THE SUBCATEGORY OF MAPS —
    `α` is a map, and for every MAP algebra `f : F c ⟶ c` there is a unique map
    `cata f hf : t ⟶ c` with `α ≫ cata f hf = F.map (cata f hf) ≫ f`
    (B&dM `cata f hf · α = f · F(cata f hf)`, mirrored). -/
public structure InitialAlgebra (F : Relator 𝒜 𝒜) where
  t : 𝒜
  α : F.obj t ⟶ t
  α_map : Map α
  cata : ∀ {c : 𝒜} (f : F.obj c ⟶ c), Map f → (t ⟶ c)
  cata_map : ∀ {c : 𝒜} (f : F.obj c ⟶ c) (hf : Map f), Map (cata f hf)
  cata_comm : ∀ {c : 𝒜} (f : F.obj c ⟶ c) (hf : Map f), α ≫ cata f hf = F.map (cata f hf) ≫ f
  cata_unique : ∀ {c : 𝒜} (f : F.obj c ⟶ c) (hf : Map f) (h : t ⟶ c), Map h →
    α ≫ h = F.map h ≫ f → h = cata f hf

variable {F}

/-- **B&dM p.121**: the RELATIONAL catamorphism `(|R|) = ∈·(|Λ(R·F∈)|)` (mirrored):
    transpose the algebra `R : F c ⟶ c` to the map algebra `Λ(R·F∈) : F[c] ⟶ [c]`, take
    its (map) catamorphism, and compose back down with `∈`. -/
@[expose] public def relCata (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) : I.t ⟶ c :=
  I.cata (A (F.map (∋ c) ≫ R)) (A_is_map' _) ≫ ∋ c

public theorem relCata_unfold (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    relCata I R = I.cata (A (F.map (∋ c) ≫ R)) (A_is_map' _) ≫ ∋ c := rfl

/-- **Eilenberg–Wright lemma (5.12)**: `α · X = FX · R ⟺ X = (|R|)`, mirrored to
    `α ≫ X = F.map X ≫ R ⟺ X = relCata I R`.  This is the defining universal property
    of the relational catamorphism, characterising `(|R|)` among ALL relations `X : t ⟶ c`
    (not just maps). -/
public theorem relCata_UP (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) (X : I.t ⟶ c) :
    (I.α ≫ X = F.map X ≫ R) ↔ X = relCata I R := by
  constructor
  · intro h
    -- `A X` is a map, so `X = A X ≫ ∋ c`; rewrite both sides of `h` through this map
    -- and transport the equation to `A (F.map (∋ c) ≫ R)` via `A_fusion`.
    have hX_eps : A X ≫ ∋ c = X := A_eps_eq' X
    have hFX : F.map X = F.map (A X) ≫ F.map (∋ c) := by
      -- rewrite the LARGER pattern `A X ≫ ∋ c` (not bare `X`) so the `A X` inside it
      -- does not spuriously get rewritten too.
      have hcomp : F.map (A X ≫ ∋ c) = F.map (A X) ≫ F.map (∋ c) := F.map_comp _ _
      rwa [hX_eps] at hcomp
    have hRHS : A (F.map X ≫ R) = F.map (A X) ≫ A (F.map (∋ c) ≫ R) := by
      rw [hFX, Cat.assoc, A_fusion (F.map_is_map (A_is_map' X))]
    have hLHS : A (I.α ≫ X) = I.α ≫ A X := A_fusion I.α_map X
    have heq : I.α ≫ A X = F.map (A X) ≫ A (F.map (∋ c) ≫ R) := by
      rw [← hLHS, h, hRHS]
    have hAX_eq_u : A X = I.cata (A (F.map (∋ c) ≫ R)) (A_is_map' _) :=
      I.cata_unique _ (A_is_map' _) (A X) (A_is_map' X) heq
    rw [relCata_unfold, ← hAX_eq_u, hX_eps]
  · intro h
    rw [h, relCata_unfold]
    generalize hu_def : I.cata (A (F.map (∋ c) ≫ R)) (A_is_map' _) = u
    have hu_comm : I.α ≫ u = F.map u ≫ A (F.map (∋ c) ≫ R) := by
      rw [← hu_def]; exact I.cata_comm _ _
    calc I.α ≫ (u ≫ ∋ c)
        = (I.α ≫ u) ≫ ∋ c := by rw [Cat.assoc]
      _ = (F.map u ≫ A (F.map (∋ c) ≫ R)) ≫ ∋ c := by rw [hu_comm]
      _ = F.map u ≫ (A (F.map (∋ c) ≫ R) ≫ ∋ c) := by rw [Cat.assoc]
      _ = F.map u ≫ (F.map (∋ c) ≫ R) := by rw [A_eps_eq']
      _ = (F.map u ≫ F.map (∋ c)) ≫ R := by rw [Cat.assoc]
      _ = F.map (u ≫ ∋ c) ≫ R := by rw [F.map_comp]

/-- (5.12), read backwards at `X := (|R|)`: `(|R|)` satisfies its own defining equation. -/
public theorem relCata_cancel (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    I.α ≫ relCata I R = F.map (relCata I R) ≫ R :=
  (relCata_UP I R (relCata I R)).mpr rfl

/-- The relational catamorphism over a MAP algebra is the ordinary (map) catamorphism:
    `(|f|) = cata f hf` when `f` is a map. -/
theorem relCata_map (I : InitialAlgebra F) {c : 𝒜} (f : F.obj c ⟶ c) (hf : Map f) :
    relCata I f = I.cata f hf :=
  ((relCata_UP I f (I.cata f hf)).mp (I.cata_comm f hf)).symm

/-- `Λ(|R|) = (|Λ(R·F∈)|)` (B&dM p.121): the power-transpose of the relational catamorphism
    is exactly the map catamorphism of the transposed algebra it was built from. -/
theorem A_relCata (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    A (relCata I R) = I.cata (A (F.map (∋ c) ≫ R)) (A_is_map' _) := by
  rw [relCata_unfold]
  generalize hu_def : I.cata (A (F.map (∋ c) ≫ R)) (A_is_map' _) = u
  have hu_map : Map u := hu_def ▸ I.cata_map _ _
  exact ((A_UP (u ≫ ∋ c) hu_map).mpr rfl).symm

/-! ## §2.6  Fusion (2.12) and Ex 2.35 (book pp. 46, 49)

  These belong here, not in `AOP.A6_2`: the INCLUSION fusion laws (6.4)/(6.5) there need
  `UnguardedPowerLCDA` because they argue through a least fixed point, whereas the EQUALITY
  fusion below follows from the universal property `relCata_UP` alone and so lives in the
  weaker `UnguardedPowerAllegory` setting of this file. -/

/-- **B&dM (2.12), p.46 — fusion**: `h·(|f|) = (|g|) ⟸ h·f = g·F h`, mirrored to diagram
    order (`h·f ↦ f h`) as `(|R|) S = (|Q|) ⟸ R S = (F S) Q`.

    Unlike the inclusion laws (6.4)/(6.5) of `AOP.A6_2` this needs NO local completeness —
    no `Sup`/`Inf`, no fixed point — only `relCata_UP` and `relCata_cancel`: the composite
    `(|R|) S` is shown to satisfy `Q`'s defining equation, and uniqueness does the rest. -/
public theorem relCata_fusion (I : InitialAlgebra F) {c d : 𝒜} {R : F.obj c ⟶ c}
    {Q : F.obj d ⟶ d} {S : c ⟶ d} (h : R ≫ S = F.map S ≫ Q) :
    relCata I R ≫ S = relCata I Q := by
  apply (relCata_UP I Q (relCata I R ≫ S)).mp
  calc I.α ≫ relCata I R ≫ S
      = (I.α ≫ relCata I R) ≫ S := by rw [Cat.assoc]
    _ = (F.map (relCata I R) ≫ R) ≫ S := by rw [relCata_cancel]
    _ = F.map (relCata I R) ≫ R ≫ S := by rw [Cat.assoc]
    _ = F.map (relCata I R) ≫ F.map S ≫ Q := by rw [h]
    _ = (F.map (relCata I R) ≫ F.map S) ≫ Q := by rw [Cat.assoc]
    _ = F.map (relCata I R ≫ S) ≫ Q := by rw [F.map_comp]

/-- **B&dM Ex 2.35, p.49**, verbatim: "Show that `(|f · g|) = f · (|g · F f|)`", with the
    types the book leaves implicit — `f : A ← X` and `g : X ← F A`, so `f·g : A ← F A` is an
    F-algebra on `A` and `g·F f : X ← F X` one on `X`.  Mirrored to diagram order with
    `f : x ⟶ a` and `g : F.obj a ⟶ x` it reads `(|(F f) g|) f = (|g f|)`.

    This is `relCata_fusion` at `R := (F f) g`, `S := f`, `Q := g f`, whose side condition
    `R S = (F S) Q` is nothing but associativity: both sides are the same three-arrow word
    `(F f) g f`, bracketed `((F f) g) f` on the left and `(F f) (g f)` on the right.

    A one-term theorem, kept despite the repo's no-wrapper rule under its stated exception
    for a statement that is itself a required deliverable — this is a book-numbered exercise. -/
public theorem relCata_of_comp (I : InitialAlgebra F) {a x : 𝒜} (f : x ⟶ a) (g : F.obj a ⟶ x) :
    relCata I (F.map f ≫ g) ≫ f = relCata I (g ≫ f) :=
  relCata_fusion I (Cat.assoc (F.map f) g f)

/-!
  ## Ex 5.19 — dropped

  B&dM's exercise asks to show `Entire R → Entire (|R|)`, hinting "use reflection to show
  `dom (|R|) = id`".  Genuine attempts (3):

  1. `dom (relCata I R) = dom (u ≫ ∋ c) = dom (u ≫ dom (∋ c))` via `dom_comp_dom` (A4_2),
     with `u` the map catamorphism above.  This reduces the goal to `u ≫ dom (∋ c) `
     having full domain, i.e. that `u` (hence, by the same shape of argument, `(|R|)`
     itself) always lands in the coreflexive "nonempty-set" part of `[c]` cut out by
     `dom (∋ c)`.  Proving THAT needs an inductive/fusion argument on `u` as the initial
     map-catamorphism — exactly as hard as the original goal, not a reduction.
  2. Apply `dom`/`congrArg` to `relCata_cancel`'s equation `α ≫ (|R|) = F(|R|) ≫ R` and push
     `dom` through both sides via `dom_comp_dom` + `Entire R` (`dom R = id`, so
     `dom (F(|R|) ≫ R) = dom (F(|R|))`).  This yields `dom (α ≫ dom(|R|)) = dom (F (|R|))`,
     relating `dom(|R|)` to `dom (F.map (relCata I R))` — but nothing here lets us peel
     `dom` through `F.map`, since a bare `Relator` need NOT preserve converse (`°`)
     without the extra `PreservesRecip` hypothesis (Theorem 5.1, tabular-only), so
     `dom (F.map X)` cannot be related to `F.map (dom X)` in general.
  3. Tried to phrase "R entire" as a subalgebra/mono condition on `t` and use
     `cata_unique` as an induction principle (the standard "no-junk" argument for initial
     algebras).  `InitialAlgebra` as specified only bundles the universal property for
     MAPS `t ⟶ c` against a FIXED target `c` (uniqueness of the homomorphism solving
     `α ≫ h = F.map h ≫ f`); it does not give an induction/extremal principle over
     mono-subobjects of `t` needed to transport a pointwise property ("is `R`-entire")
     through `α`.  That principle is extra initial-algebra infrastructure this file's
     `InitialAlgebra` does not carry.

  Conclusion: `Entire R → Entire (relCata I R)` is a genuine wall — it needs either (a) a
  `PreservesRecip`/tabular hypothesis on `F` making route 2 close, or (b) strengthening
  `InitialAlgebra` with an induction/no-junk principle for route 3. Left open here; not
  attempted further per the task's explicit license to drop this item.
-/

end Freyd.Alg
