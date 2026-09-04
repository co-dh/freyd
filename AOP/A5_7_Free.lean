/-
  Bird & de Moor, *Algebra of Programming* §5.7 — the FREE THEOREM for a REIFIED combinator
  language (Wadler, "Theorems for free!"; the §5.7 citation B&dM p.180 attaches to `generate`).

  B&dM p.180: "the type assigned to `generate` is parameterised by `A` … Accordingly,
  `generate` will be a lax natural transformation."  For an arbitrary LEAN term that is not
  provable — Lean's terms are not reified and its type theory has no internal parametricity.
  For a REIFIED term language it is an ordinary theorem, by structural induction on the term:
  `PE.free` below.

  Shape follows `rel/RelInterp.lean`'s `RE`/`eval`: one constructor per operation, interpreted
  through the ALREADY PROVEN lemmas, so the laws hold of interpreted terms by construction.
  The difference is that `RE` is MONOMORPHIC — indexed by two fixed objects — so it cannot type
  a combinator polymorphic in an object.  `PE` is indexed by TYPE EXPRESSIONS `TyE` in one
  variable, and it is the variable that carries the theorem.

  Composition is diagram order (`≫`).  `LaxNatural F G φ` (A5_1) is `G.map R ≫ φ b ⊑ φ a ≫ F.map R`
  for `φ a : G.obj a ⟶ F.obj a`, so a term of type `σ ⟶ τ` is lax natural `⟦σ⟧ ⟶ ⟦τ⟧`.

  Against the standard System F logical-relations recipe (Siek, `SystemF/lean/curry/`), which the
  allegory setting collapses: `Rel A B` (a relation on closed values) is the hom `a ⟶ b` itself;
  the relational substitution is the single `R`, since `TyE` has one variable; the value relation
  `𝒱`, by recursion on the type, is `TyE.rel`'s `map`; the term relation `𝓔` is not needed,
  `PE.eval` being a denotation rather than an operational semantics; the `compat_*` lemma per
  typing rule is the case per `PE` constructor; and `fundamental` is `PE.free`.  Their step 7 —
  instantiate the `∀`-quantified relation at the GRAPH of a function — is `PE.free_on_maps`: at a
  MAP the lax square becomes an equality.  Because `R` here is an arbitrary RELATION and not a
  graph, the general statement is the lax square, and strictness is the special case.

  NOT in the language, and why:
  * CONVERSE.  Lax naturality is not closed under `°`: conversing `G R ≫ φ b ⊑ φ a ≫ F R`
    gives `(φ b)° ≫ (G R)° ⊑ (F R)° ≫ (φ a)°`, which is OPLAX for `φ°` (`recip_oplax`, A5_7),
    not lax.  A `conv` constructor would make `PE.free` false; `∋` already witnesses the gap.
  * `cons`/`nil`.  Their free theorem is the initial algebra's `α : F(A, T A) ⟶ T A` being lax
    natural in `A`, which needs `A5_5_TypeFunctor`'s `typeRelator` and the `⦇·⦈` computation
    law — a coproduct and an initial algebra per object on top of this file's hypotheses.
    The `mem` constructor is the seam where such an already-proved constant enters.

  A6_5's `LaxMembership` BUNDLE is not used here for two independent reasons: it is not `public`,
  so no other module can name it; and it is stated over `UnguardedPowerLCDA`, which does not
  give this file's `TabularUnitaryDivisionAllegory`/`HasRelProd`, so a joint statement would
  carry two unrelated paths to `Allegory 𝒜`.  `comp_mem_lax_free` below therefore derives
  A6_5's `compMembership.lax` over the membership's DATA (`m` and its lax naturality) instead.
-/

module

public import AOP.A5_7

universe v₁ u₁

namespace Freyd.Alg

section Free

variable {𝒜 : Type u₁} [TabularUnitaryDivisionAllegory 𝒜] [HasRelProd 𝒜]

/-! ## Type expressions in one variable

  `TyE` is the syntax of the types a polymorphic combinator can have: the VARIABLE, a CONSTANT
  object, a PRODUCT, and the ACTION OF A RELATOR.  Everything the free theorem needs of a type
  expression is that it denotes a relator, so `TyE.rel` interprets into `Relator 𝒜 𝒜` directly
  and the two interpretations the theorem quantifies over are its two fields:
  `⟦σ⟧ a = σ.rel.obj a` on objects and `⟦σ⟧R R = σ.rel.map R` on relations. -/

/-- TYPE EXPRESSIONS in one object variable. -/
public inductive TyE (𝒜 : Type u₁) [Allegory.{v₁} 𝒜] : Type (max u₁ v₁) where
  /-- The variable — the object the combinator is polymorphic in. -/
  | var
  /-- A constant object, not touched by the substitution. -/
  | const (b : 𝒜)
  /-- Product of two type expressions, on `relProd`'s chosen product. -/
  | prod (σ τ : TyE 𝒜)
  /-- The action of a relator: `F(σ)`. -/
  | app (F : Relator 𝒜 𝒜) (σ : TyE 𝒜)

/-- **The interpretation.**  A type expression denotes a RELATOR, so its action on relations is
    monotone and preserves `𝟙` and `≫` by construction — those are `Relator`'s own fields,
    discharged by `Relator.idRelator`/`const`/`prod`/`comp`, which is the whole reason the
    induction below has nothing to prove about them. -/
@[expose] public def TyE.rel : TyE 𝒜 → Relator 𝒜 𝒜
  | .var => Relator.idRelator 𝒜
  | .const b => Relator.const b
  | .prod σ τ => Relator.prod σ.rel τ.rel
  | .app F σ => Relator.comp σ.rel F

-- The three relator laws for every `⟦σ⟧R`, free from `TyE.rel` landing in `Relator`.
example (σ : TyE 𝒜) (a : 𝒜) : σ.rel.map (𝟙 a) = 𝟙 (σ.rel.obj a) := σ.rel.map_id a

example (σ : TyE 𝒜) {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    σ.rel.map (R ≫ S) = σ.rel.map R ≫ σ.rel.map S := σ.rel.map_comp R S

example (σ : TyE 𝒜) {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : σ.rel.map R ⊑ σ.rel.map S :=
  σ.rel.map_mono h

/-! ## The combinator language -/

/-- POLYMORPHIC COMBINATORS, indexed by source and target type expression.  `mem` is the seam
    through which an already-proved lax constant enters the language — `∋` is `mem` at the
    power relator (`LaxMembership.laxNatural`, A6_5); every other constructor's case of
    `PE.free` is proved. -/
public inductive PE {𝒜 : Type u₁} [Allegory.{v₁} 𝒜] : TyE 𝒜 → TyE 𝒜 → Type (max u₁ v₁) where
  | id (σ : TyE 𝒜) : PE σ σ
  | comp {σ τ υ : TyE 𝒜} : PE σ τ → PE τ υ → PE σ υ
  /-- First projection `π₁`. -/
  | outl {σ τ : TyE 𝒜} : PE (.prod σ τ) σ
  /-- Second projection `π₂`. -/
  | outr {σ τ : TyE 𝒜} : PE (.prod σ τ) τ
  /-- Fork `⟨s,t⟩`. -/
  | pair {σ τ υ : TyE 𝒜} : PE σ τ → PE σ υ → PE σ (.prod τ υ)
  /-- A relator applied to a combinator: `F(t)`. -/
  | map {σ τ : TyE 𝒜} (F : Relator 𝒜 𝒜) : PE σ τ → PE (.app F σ) (.app F τ)
  /-- A membership `m : F ⟶ 𝟙`, i.e. `∋` for `F` — the one constructor that carries its own
      lax naturality, since nothing in the syntax could prove it. -/
  | mem {σ : TyE 𝒜} (F : Relator 𝒜 𝒜) (m : ∀ a : 𝒜, F.obj a ⟶ a)
      (h : LaxNatural (Relator.idRelator 𝒜) F m) : PE (.app F σ) σ

/-- **The interpreter.**  Each constructor is evaluated by the corresponding operation of the
    proven instances, so a term denotes a family of arrows `⟦σ⟧ a ⟶ ⟦τ⟧ a`, one per object. -/
@[expose] public def PE.eval : {σ τ : TyE 𝒜} → PE σ τ → (∀ a : 𝒜, σ.rel.obj a ⟶ τ.rel.obj a)
  | σ, _, .id _, a => 𝟙 (σ.rel.obj a)
  | _, _, .comp s t, a => s.eval a ≫ t.eval a
  | .prod σ τ, _, .outl, a => (relProd (σ.rel.obj a) (τ.rel.obj a)).outl
  | .prod σ τ, _, .outr, a => (relProd (σ.rel.obj a) (τ.rel.obj a)).outr
  | _, .prod τ υ, .pair s t, a =>
      (relProd (τ.rel.obj a) (υ.rel.obj a)).pair (s.eval a) (t.eval a)
  | _, _, .map F t, a => F.map (t.eval a)
  | .app _ σ, _, .mem _ m _, a => m (σ.rel.obj a)

/-! ## The free theorem -/

/-- **THE FREE THEOREM** (Wadler; B&dM §5.7, cited at p.180 for `generate`): a term's TYPE
    alone forces its naturality square.  Written out, for every `t : PE σ τ` and `R : a ⟶ b`,

      `⟦σ⟧R R ≫ ⟦t⟧ b ⊑ ⟦t⟧ a ≫ ⟦τ⟧R R`

    which is `LaxNatural ⟦τ⟧ ⟦σ⟧ ⟦t⟧`.  Proved by structural induction on `t`; the interpreted
    type expressions are relators, so each case is one already-proved slide lemma. -/
public theorem PE.free : ∀ {σ τ : TyE 𝒜} (t : PE σ τ), LaxNatural τ.rel σ.rel t.eval
  | _, _, .id σ => fun R => le_of_eq (by
      show σ.rel.map R ≫ 𝟙 _ = 𝟙 _ ≫ σ.rel.map R
      rw [Cat.comp_id, Cat.id_comp])
  | _, _, .comp s t => fun R => comp_slides (s.free R) (t.free R)
  | _, _, .outl => fun _ => prodMap_outl_le _ _ _ _
  | _, _, .outr => fun _ => prodMap_outr_le _ _ _ _
  | _, _, .pair s t => laxNatural_pair s.free t.free
  | _, _, .map F t => fun R => Relator.map_slides F (t.free R)
  | .app _ σ, _, .mem _ _ h => fun R => h (σ.rel.map R)

/-- The free theorem at the GRAPH of a function: for a MAP `f` the lax square is an EQUALITY,
    `⟦σ⟧R f ≫ ⟦t⟧ b = ⟦t⟧ a ≫ ⟦τ⟧R f` — ordinary naturality.  This is what instantiating the
    `∀`-quantified relation of a System F free theorem at a function's graph buys; here the
    general `R` is already a relation, so the lax square is the general case and this is the
    specialisation. -/
public theorem PE.free_on_maps {σ τ : TyE 𝒜} (t : PE σ τ) {a b : 𝒜} (f : a ⟶ b) (hf : Map f) :
    σ.rel.map f ≫ t.eval b = t.eval a ≫ τ.rel.map f :=
  (laxNatural_iff_strict_on_maps τ.rel σ.rel t.eval).mp t.free f hf

/-! ## Cashing it out: the already-proved instances as corollaries of the induction -/

/-- **B&dM p.133**, `outr_lax_natural` (A5_2) DERIVED: it is `PE.free` at the single term
    `outr : var × var ⟶ var`, whose interpretation is `(relProd a a).outr` and whose source
    type expression interprets as `Δ 𝒜 = Relator.prod (idRelator) (idRelator)`. -/
public theorem outr_lax_natural_free :
    LaxNatural (Relator.idRelator 𝒜) (Δ 𝒜) (fun a => (relProd a a).outr) :=
  PE.free (PE.outr (σ := TyE.var) (τ := TyE.var))

/-- `outl` likewise (`outl_lax_natural`, A5_7). -/
public theorem outl_lax_natural_free :
    LaxNatural (Relator.idRelator 𝒜) (Δ 𝒜) (fun a => (relProd a a).outl) :=
  PE.free (PE.outl (σ := TyE.var) (τ := TyE.var))

/-- **B&dM p.149**, `compMembership`'s `lax` field (A6_5) DERIVED: `member(F·G)` is
    `member(G)·member(F)`.  It is `PE.free` at `mem G ≫ mem F`, typed
    `G(F(var)) ⟶ F(var) ⟶ var`; the composite's lax naturality is the `comp` case, so the
    hand calculation in A6_5 is an instance of the induction. -/
public theorem comp_mem_lax_free {F G : Relator 𝒜 𝒜} {mF : ∀ a : 𝒜, F.obj a ⟶ a}
    {mG : ∀ a : 𝒜, G.obj a ⟶ a} (hF : LaxNatural (Relator.idRelator 𝒜) F mF)
    (hG : LaxNatural (Relator.idRelator 𝒜) G mG) :
    LaxNatural (Relator.idRelator 𝒜) (Relator.comp F G) (fun a => mG (F.obj a) ≫ mF a) :=
  PE.free (PE.comp (PE.mem (σ := TyE.app F TyE.var) G mG hG) (PE.mem (σ := TyE.var) F mF hF))

/-- The `map` case cashed out: `F(π₂)` is lax natural `F·Δ ⟶ F·𝟙`, i.e.
    `F(R×R) ≫ F(outr) ⊑ F(outr) ≫ F(R)`.  `Relator.map_slides` read off the language rather
    than reapplied by hand. -/
public theorem map_outr_lax_natural_free (F : Relator 𝒜 𝒜) :
    LaxNatural (Relator.comp (Relator.idRelator 𝒜) F) (Relator.comp (Δ 𝒜) F)
      (fun a => F.map ((relProd a a).outr)) :=
  PE.free (PE.map F (PE.outr (σ := TyE.var) (τ := TyE.var)))

-- The corollaries are the hand proofs, not merely something like them: proof irrelevance makes
-- these `rfl` iff the two statements are the SAME proposition.
example : @outr_lax_natural 𝒜 _ _ = @outr_lax_natural_free 𝒜 _ _ := rfl
example : @outl_lax_natural 𝒜 _ _ = @outl_lax_natural_free 𝒜 _ _ := rfl

end Free

end Freyd.Alg
