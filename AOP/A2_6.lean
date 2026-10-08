/-
  Bird & de Moor, *Algebra of Programming* §2.6  Initial algebras, p.47: what `h = ⦇c,f⦈` says on
  the naturals.  `Nat ::= zero | succ Nat` declares `α = [zero,succ] : F(Nat) ⟶ Nat` the initial
  algebra of `F(A) = 1+A`, `F(h) = 𝟙+h` (p.46); the book spells the homomorphism condition out:

    αh = F(h)[c,f]  ⟺  zero h = c  and  succ h = h f

  Diagram order throughout: B&dM's `h·α = [c,f]·Fh` is `αh = F(h)[c,f]` here.  The book's chain
  is of equivalences between equations; each of its first four steps rewrites ONE side by an
  equation of arrows, so each is its own `nat_fold_spec_step<k>` equation (the note draws them),
  and the last, cancellation, is the one step that is an `↔` between equations.
-/
module

public import AOP.A6_3

namespace Freyd.Alg

universe u

variable {𝒜 : Type u} [PositiveTabularUnitaryUnguardedDivisionPowerAllegory 𝒜]

/-- B&dM p.46: the functor of `Nat`, `F(A) = 1+A`, `F(h) = 𝟙+h`, on the chosen coproducts. -/
@[expose] public abbrev Nat.F : Relator 𝒜 𝒜 :=
  Relator.sum (Relator.const (UnitaryAllegory.unit_obj (𝒜 := 𝒜))) (Relator.idRelator 𝒜)

/-- The chosen coproduct `1+x`, whose injections are `inl`, `inr`. -/
@[expose] public abbrev natCop (x : 𝒜) :=
  PositiveAllegory.has_coproduct (UnitaryAllegory.unit_obj (𝒜 := 𝒜)) x

variable [I : InitialAlgebra (Nat.F (𝒜 := 𝒜))]

/-- B&dM p.46: `zero = inl α`, the constant the declaration `Nat ::= zero | succ Nat` names. -/
@[expose] public def Nat.zero : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ I.t := (natCop I.t).u₁ ≫ I.α

/-- B&dM p.46: `succ = inr α`. -/
@[expose] public def Nat.succ : I.t ⟶ I.t := (natCop I.t).u₂ ≫ I.α

/-- p.47, step 1 {definition of F}: `F(h)[c,f] = (𝟙+h)[c,f]`. -/
public theorem Nat.nat_fold_spec_step1 {A : 𝒜} (h : I.t ⟶ A)
    (c : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ A) (f : A ⟶ A) :
    Nat.F.map h ≫ junc (natCop A) c f
      = sumMap (natCop I.t) (natCop A) (𝟙 (UnitaryAllegory.unit_obj (𝒜 := 𝒜))) h
          ≫ junc (natCop A) c f := rfl

/-- p.47, step 2 {coproduct}: `(𝟙+h)[c,f] = [c,hf]`. -/
public theorem Nat.nat_fold_spec_step2 {A : 𝒜} (h : I.t ⟶ A)
    (c : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ A) (f : A ⟶ A) :
    sumMap (natCop I.t) (natCop A) (𝟙 (UnitaryAllegory.unit_obj (𝒜 := 𝒜))) h
        ≫ junc (natCop A) c f = junc (natCop I.t) c (h ≫ f) := by
  rw [sumMap_junc, Cat.id_comp]

/-- p.47, step 3 {since α = [zero,succ]}: `αh = [zero,succ]h`. -/
public theorem Nat.nat_fold_spec_step3 {A : 𝒜} (h : I.t ⟶ A) :
    I.α ≫ h = junc (natCop I.t) Nat.zero Nat.succ ≫ h :=
  congrArg (· ≫ h) (junc_unique (natCop I.t) (R := Nat.zero) (S := Nat.succ) rfl rfl)

/-- p.47, step 4 {coproduct}: `[zero,succ]h = [zero h,succ h]`. -/
public theorem Nat.nat_fold_spec_step4 {A : 𝒜} (h : I.t ⟶ A) :
    junc (natCop I.t) Nat.zero Nat.succ ≫ h = junc (natCop I.t) (Nat.zero ≫ h) (Nat.succ ≫ h) :=
  junc_comp (natCop I.t) Nat.zero Nat.succ h

/-- p.47, step 5 {cancellation}: `[zero h,succ h] = [c,hf]` iff the arms agree, since
    `inl[P,Q] = P` and `inr[P,Q] = Q`. -/
public theorem Nat.nat_fold_spec_step5 {A : 𝒜} (h : I.t ⟶ A)
    (c : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ A) (f : A ⟶ A) :
    junc (natCop I.t) (Nat.zero ≫ h) (Nat.succ ≫ h) = junc (natCop I.t) c (h ≫ f)
      ↔ Nat.zero ≫ h = c ∧ Nat.succ ≫ h = h ≫ f := by
  constructor
  · intro e
    exact ⟨(u₁_junc (natCop I.t) _ _).symm.trans (e ▸ u₁_junc (natCop I.t) c (h ≫ f)),
      (u₂_junc (natCop I.t) _ _).symm.trans (e ▸ u₂_junc (natCop I.t) c (h ≫ f))⟩
  · rintro ⟨e₁, e₂⟩; rw [e₁, e₂]

-- The exporter draws arrows, not an `↔` of equations: these two draw step 5's right side, one
-- equation each, and the `⟺` between it and the left is `nat_fold_spec_step5` itself.
/-- p.47, step 5, the `zero` arm of the right side: `zero h = c`. -/
public theorem Nat.nat_fold_spec_step5_zero {A : 𝒜} {h : I.t ⟶ A}
    {c : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ A} {f : A ⟶ A}
    (e : junc (natCop I.t) (Nat.zero ≫ h) (Nat.succ ≫ h) = junc (natCop I.t) c (h ≫ f)) :
    Nat.zero ≫ h = c :=
  ((Nat.nat_fold_spec_step5 h c f).mp e).1

/-- p.47, step 5, the `succ` arm of the right side: `succ h = h f`. -/
public theorem Nat.nat_fold_spec_step5_succ {A : 𝒜} {h : I.t ⟶ A}
    {c : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ A} {f : A ⟶ A}
    (e : junc (natCop I.t) (Nat.zero ≫ h) (Nat.succ ≫ h) = junc (natCop I.t) c (h ≫ f)) :
    Nat.succ ≫ h = h ≫ f :=
  ((Nat.nat_fold_spec_step5 h c f).mp e).2

/-- **B&dM p.47**: `h = ⦇c,f⦈` on the naturals, spelled out — `h` is an F-homomorphism from
    `α = [zero,succ]` to `[c,f]` iff `zero h = c` and `succ h = h f`.  Steps 1–5. -/
public theorem Nat.nat_fold_spec {A : 𝒜} (h : I.t ⟶ A)
    (c : UnitaryAllegory.unit_obj (𝒜 := 𝒜) ⟶ A) (f : A ⟶ A) :
    I.α ≫ h = Nat.F.map h ≫ junc (natCop A) c f ↔ Nat.zero ≫ h = c ∧ Nat.succ ≫ h = h ≫ f := by
  rw [Nat.nat_fold_spec_step1, Nat.nat_fold_spec_step2, Nat.nat_fold_spec_step3, Nat.nat_fold_spec_step4]
  exact Nat.nat_fold_spec_step5 h c f

end Freyd.Alg
