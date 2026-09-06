/-
  Bird & de Moor, *Algebra of Programming* §5.5  Relational catamorphisms
  (the Eilenberg–Wright lemma, book pp. 121–122).

  For a relator `F` on `𝒜` with an initial algebra `α : F t ⟶ t` in the subcategory of
  MAPS of `𝒜`, every algebra `R : F A ⟶ A` (a relation, not necessarily a map) has a
  UNIQUE relational catamorphism `(|R|) : t ⟶ A` characterised by
  `α · X = FX · R ⟺ X = (|R|)`  (5.12, mirrored to diagram order: `α ≫ X = F.map X ≫ R`).

  B&dM's construction: `(|R|) = ∈ · (|Λ(R·F∈)|)`, i.e. transpose the relational algebra
  `R : F A ⟶ A` through the power object of `A` to the MAP algebra
  `Λ(R·F∈) : F [A] ⟶ [A]` (Freyd: `Λ (F.map (∋ A) ≫ R) : F.obj (powerObj A) ⟶ powerObj A`),
  take the ordinary (map) catamorphism of that, and compose with `∈` to come back down
  to `A`.  All composition is diagram order (Freyd `≫`), mirroring B&dM's `·`.

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
    `α` is a map, and for every MAP algebra `f : F A ⟶ A` there is a unique map
    `cata f hf : t ⟶ A` with `α ≫ cata f hf = F.map (cata f hf) ≫ f`
    (B&dM `cata f hf · α = f · F(cata f hf)`, mirrored). -/
public class InitialAlgebra (F : Relator 𝒜 𝒜) where
  t : 𝒜
  α : F.obj t ⟶ t
  α_map : Map α
  cata : ∀ {A : 𝒜} (f : F.obj A ⟶ A), Map f → (t ⟶ A)
  cata_map : ∀ {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f), Map (cata f hf)
  cata_comm : ∀ {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f), α ≫ cata f hf = F.map (cata f hf) ≫ f
  cata_unique : ∀ {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f) (h : t ⟶ A), Map h →
    α ≫ h = F.map h ≫ f → h = cata f hf

variable {F}

/-- **B&dM p.121**: the RELATIONAL catamorphism `(|R|) = ∈·(|Λ(R·F∈)|)` (mirrored):
    transpose the algebra `R : F A ⟶ A` to the map algebra `Λ(R·F∈) : F[A] ⟶ [A]`, take
    its (map) catamorphism, and compose back down with `∈`. -/
@[expose] public def relCata [I : InitialAlgebra F] {A : 𝒜} (R : F.obj A ⟶ A) : I.t ⟶ A :=
  I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) ≫ ∋ A

/-- The book's banana brackets `(|R|)`.  The ONE global binding: the structural folds `cataR`
    equal `relCata` only propositionally (`cataR_eq_relCata`), so they are spelled by name. -/
notation:max "⦇" R "⦈" => relCata R

public theorem relCata_unfold (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) :
    relCata R = I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) ≫ ∋ A := rfl

/-- **Eilenberg–Wright lemma (5.12)**: `α · X = FX · R ⟺ X = (|R|)`, mirrored to
    `α ≫ X = F.map X ≫ R ⟺ X = relCata I R`.  This is the defining universal property
    of the relational catamorphism, characterising `(|R|)` among ALL relations `X : t ⟶ A`
    (not just maps). -/
public theorem relCata_UP (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) (X : I.t ⟶ A) :
    (I.α ≫ X = F.map X ≫ R) ↔ X = relCata R := by
  constructor
  · intro h
    -- `Λ X` is a map, so `X = Λ X ≫ ∋ A`; rewrite both sides of `h` through this map
    -- and transport the equation to `Λ (F.map (∋ A) ≫ R)` via `Λ_fusion`.
    have hX_eps : Λ X ≫ ∋ A = X := Λ_eps_eq' X
    have hFX : F.map X = F.map (Λ X) ≫ F.map (∋ A) := by
      -- rewrite the LARGER pattern `Λ X ≫ ∋ A` (not bare `X`) so the `Λ X` inside it
      -- does not spuriously get rewritten too.
      have hcomp : F.map (Λ X ≫ ∋ A) = F.map (Λ X) ≫ F.map (∋ A) := F.map_comp _ _
      rwa [hX_eps] at hcomp
    have hRHS : Λ (F.map X ≫ R) = F.map (Λ X) ≫ Λ (F.map (∋ A) ≫ R) := by
      rw [hFX, Cat.assoc, Λ_fusion (F.map_is_map (Λ_is_map' X))]
    have hLHS : Λ (I.α ≫ X) = I.α ≫ Λ X := Λ_fusion I.α_map X
    have heq : I.α ≫ Λ X = F.map (Λ X) ≫ Λ (F.map (∋ A) ≫ R) := by
      rw [← hLHS, h, hRHS]
    have hAX_eq_u : Λ X = I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) :=
      I.cata_unique _ (Λ_is_map' _) (Λ X) (Λ_is_map' X) heq
    rw [relCata_unfold, ← hAX_eq_u, hX_eps]
  · intro h
    rw [h, relCata_unfold]
    generalize hu_def : I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) = u
    have hu_comm : I.α ≫ u = F.map u ≫ Λ (F.map (∋ A) ≫ R) := by
      rw [← hu_def]; exact I.cata_comm _ _
    calc I.α ≫ (u ≫ ∋ A)
        = (I.α ≫ u) ≫ ∋ A := by rw [Cat.assoc]
      _ = (F.map u ≫ Λ (F.map (∋ A) ≫ R)) ≫ ∋ A := by rw [hu_comm]
      _ = F.map u ≫ (Λ (F.map (∋ A) ≫ R) ≫ ∋ A) := by rw [Cat.assoc]
      _ = F.map u ≫ (F.map (∋ A) ≫ R) := by rw [Λ_eps_eq']
      _ = (F.map u ≫ F.map (∋ A)) ≫ R := by rw [Cat.assoc]
      _ = F.map (u ≫ ∋ A) ≫ R := by rw [F.map_comp]

/-- (5.12), read backwards at `X := (|R|)`: `(|R|)` satisfies its own defining equation. -/
public theorem relCata_cancel (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) :
    I.α ≫ relCata R = F.map (relCata R) ≫ R :=
  (relCata_UP I R (relCata R)).mpr rfl

/-- The relational catamorphism over a MAP algebra is the ordinary (map) catamorphism:
    `(|f|) = cata f hf` when `f` is a map. -/
theorem relCata_map (I : InitialAlgebra F) {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f) :
    relCata f = I.cata f hf :=
  ((relCata_UP I f (I.cata f hf)).mp (I.cata_comm f hf)).symm

/-- `Λ(|R|) = (|Λ(R·F∈)|)` (B&dM p.121): the power-transpose of the relational catamorphism
    is exactly the map catamorphism of the transposed algebra it was built from. -/
theorem Λ_relCata (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) :
    Λ (relCata R) = I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) := by
  rw [relCata_unfold]
  generalize hu_def : I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) = u
  have hu_map : Map u := hu_def ▸ I.cata_map _ _
  exact ((Λ_UP (u ≫ ∋ A) hu_map).mpr rfl).symm

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
public theorem relCata_fusion (I : InitialAlgebra F) {A d : 𝒜} {R : F.obj A ⟶ A}
    {Q : F.obj d ⟶ d} {S : A ⟶ d} (h : R ≫ S = F.map S ≫ Q) :
    relCata R ≫ S = relCata Q := by
  apply (relCata_UP I Q (relCata R ≫ S)).mp
  calc I.α ≫ relCata R ≫ S
      = (I.α ≫ relCata R) ≫ S := by rw [Cat.assoc]
    _ = (F.map (relCata R) ≫ R) ≫ S := by rw [relCata_cancel]
    _ = F.map (relCata R) ≫ R ≫ S := by rw [Cat.assoc]
    _ = F.map (relCata R) ≫ F.map S ≫ Q := by rw [h]
    _ = (F.map (relCata R) ≫ F.map S) ≫ Q := by rw [Cat.assoc]
    _ = F.map (relCata R ≫ S) ≫ Q := by rw [F.map_comp]

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
    relCata (F.map f ≫ g) ≫ f = relCata (g ≫ f) :=
  relCata_fusion I (Cat.assoc (F.map f) g f)

/-!
  ## Ex 5.19 — dropped

  B&dM's exercise asks to show `Entire R → Entire (|R|)`, hinting "use reflection to show
  `dom (|R|) = id`".  Genuine attempts (3):

  1. `dom (relCata I R) = dom (u ≫ ∋ A) = dom (u ≫ dom (∋ A))` via `dom_comp_dom` (A4_2),
     with `u` the map catamorphism above.  This reduces the goal to `u ≫ dom (∋ A) `
     having full domain, i.e. that `u` (hence, by the same shape of argument, `(|R|)`
     itself) always lands in the coreflexive "nonempty-set" part of `[A]` cut out by
     `dom (∋ A)`.  Proving THAT needs an inductive/fusion argument on `u` as the initial
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
     MAPS `t ⟶ A` against a FIXED target `A` (uniqueness of the homomorphism solving
     `α ≫ h = F.map h ≫ f`); it does not give an induction/extremal principle over
     mono-subobjects of `t` needed to transport a pointwise property ("is `R`-entire")
     through `α`.  That principle is extra initial-algebra infrastructure this file's
     `InitialAlgebra` does not carry.

  Conclusion: `Entire R → Entire (relCata I R)` is a genuine wall — it needs either (a) a
  `PreservesRecip`/tabular hypothesis on `F` making route 2 close, or (b) strengthening
  `InitialAlgebra` with an induction/no-junk principle for route 3. Left open here; not
  attempted further per the task's explicit license to drop this item.
-/

-- printing-only unexpanders: the note's spelling.  A picture drawn by `diag-export --commutative`
-- takes every label from `Meta.ppExpr`, so what the note calls a thing has to be what Lean PRINTS
-- it as; these change no statement and no `stmt_key`.
-- The carrier and the algebra of an initial algebra are `T` and `α` — the letters `<initial-defn>`
-- and B&dM §2.6 draw them with — and the relator argument is not part of either name.  When that
-- relator is itself a PARTIAL APPLICATION (`F.appl a`, `CL.F Unit A`, …) the initial algebra is one
-- member of a family and its last argument is the index, so it is written back on: `T A`, `α A`.
-- The index is the LAST argument of whichever operand is itself an application: the family `I`
-- taken at `a` (`(I a).t`, how field notation prints it) and the partial relator `F.appl a` are the
-- same indexing, so both spellings answer `a`.  An operand that is not an application is one
-- initial algebra, not a family, and carries no index.
-- Which member of the family, read off whichever operand is an application: `F.appl a`, `(I a)` and
-- `CL.F Unit a` all answer `a`, whether the printer put the relator or the algebra in front.  An
-- operand that is a plain name is one initial algebra, not a family, and has no index.
open Lean in
public meta def lastArg : Term → Option Term
  | `($_ $_ $a) => some a
  | `($_ $a) => some a
  | _ => none

-- A quotation pattern's own brackets are a `paren` node, which a delaborated argument does not
-- carry, so the operand is bound and taken apart on its own rather than matched in place.
open Lean in
public meta def familyIndex : Term → Option Term
  | `($_ $x) => lastArg x
  | _ => none

open Lean PrettyPrinter in
@[app_unexpander InitialAlgebra.t] public meta def unexpandInitialAlgebraT : Unexpander := fun stx =>
  match familyIndex ⟨stx⟩ with
  | some a => `($(mkIdent `T) $a)
  | none => `($(mkIdent `T))

open Lean PrettyPrinter in
@[app_unexpander InitialAlgebra.α] public meta def unexpandInitialAlgebraAlpha : Unexpander :=
  fun stx => match familyIndex ⟨stx⟩ with
  | some a => `($(mkIdent `α) $a)
  | none => `($(mkIdent `α))

end Freyd.Alg
