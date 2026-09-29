/-
  Bird & de Moor, *Algebra of Programming* §2.6  Initial algebras, p.47: what `h = ⦇c,f⦈` says on
  the naturals.  `Nat ::= zero | succ Nat` declares `α = [zero,succ] : F(Nat) ⟶ Nat` the initial
  algebra of `F(A) = 1+A`, `F(h) = 𝟙+h`; the book spells the homomorphism condition out:

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

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}
  {one : 𝒜} (C : ∀ x : 𝒜, Coproduct (F.obj x) one x)

/-- p.47, step 1 {definition of F}: `F(h)[c,f] = (𝟙+h)[c,f]`, since `F(h) = 𝟙+h`. -/
public theorem nat_fold_spec_step1
    (hF : ∀ {x y : 𝒜} (X : x ⟶ y), F.map X = sumMap (C x) (C y) (𝟙 one) X)
    {T A : 𝒜} (h : T ⟶ A) (c : one ⟶ A) (f : A ⟶ A) :
    F.map h ≫ junc (C A) c f = sumMap (C T) (C A) (𝟙 one) h ≫ junc (C A) c f := by
  rw [hF h]

/-- p.47, step 2 {coproduct}: `(𝟙+h)[c,f] = [c,hf]`. -/
public theorem nat_fold_spec_step2 {T A : 𝒜} (h : T ⟶ A) (c : one ⟶ A) (f : A ⟶ A) :
    sumMap (C T) (C A) (𝟙 one) h ≫ junc (C A) c f = junc (C T) c (h ≫ f) := by
  rw [sumMap_junc, Cat.id_comp]

/-- p.47, step 3 {since α = [zero,succ]}: `αh = [zero,succ]h`. -/
public theorem nat_fold_spec_step3 [I : InitialAlgebra F] {zero : one ⟶ I.t} {succ : I.t ⟶ I.t}
    (hα : I.α = junc (C I.t) zero succ) {A : 𝒜} (h : I.t ⟶ A) :
    I.α ≫ h = junc (C I.t) zero succ ≫ h := by
  rw [hα]

/-- p.47, step 4 {coproduct}: `[zero,succ]h = [zero h,succ h]`. -/
public theorem nat_fold_spec_step4 {T A : 𝒜} (zero : one ⟶ T) (succ : T ⟶ T) (h : T ⟶ A) :
    junc (C T) zero succ ≫ h = junc (C T) (zero ≫ h) (succ ≫ h) :=
  junc_comp (C T) zero succ h

/-- p.47, step 5 {cancellation}: `[zero h,succ h] = [c,hf]` iff the arms agree, since
    `inl[P,Q] = P` and `inr[P,Q] = Q`. -/
public theorem nat_fold_spec_step5 {T A : 𝒜} (zero : one ⟶ T) (succ : T ⟶ T) (h : T ⟶ A)
    (c : one ⟶ A) (f : A ⟶ A) :
    junc (C T) (zero ≫ h) (succ ≫ h) = junc (C T) c (h ≫ f) ↔ zero ≫ h = c ∧ succ ≫ h = h ≫ f := by
  constructor
  · intro e
    exact ⟨(u₁_junc (C T) _ _).symm.trans (e ▸ u₁_junc (C T) c (h ≫ f)),
      (u₂_junc (C T) _ _).symm.trans (e ▸ u₂_junc (C T) c (h ≫ f))⟩
  · rintro ⟨e₁, e₂⟩; rw [e₁, e₂]

-- The exporter draws arrows, not an `↔` of equations: these two draw step 5's right side, one
-- equation each, and the `⟺` between it and the left is `nat_fold_spec_step5` itself.
/-- p.47, step 5, the `zero` arm of the right side: `zero h = c`. -/
public theorem nat_fold_spec_step5_zero {T A : 𝒜} {zero : one ⟶ T} {succ : T ⟶ T} {h : T ⟶ A}
    {c : one ⟶ A} {f : A ⟶ A} (e : junc (C T) (zero ≫ h) (succ ≫ h) = junc (C T) c (h ≫ f)) :
    zero ≫ h = c :=
  ((nat_fold_spec_step5 C zero succ h c f).mp e).1

/-- p.47, step 5, the `succ` arm of the right side: `succ h = h f`. -/
public theorem nat_fold_spec_step5_succ {T A : 𝒜} {zero : one ⟶ T} {succ : T ⟶ T} {h : T ⟶ A}
    {c : one ⟶ A} {f : A ⟶ A} (e : junc (C T) (zero ≫ h) (succ ≫ h) = junc (C T) c (h ≫ f)) :
    succ ≫ h = h ≫ f :=
  ((nat_fold_spec_step5 C zero succ h c f).mp e).2

/-- **B&dM p.47**: `h = ⦇c,f⦈` on the naturals, spelled out — `h` is an F-homomorphism from
    `α = [zero,succ]` to `[c,f]` iff `zero h = c` and `succ h = h f`.  Steps 1–5. -/
public theorem nat_fold_spec
    (hF : ∀ {x y : 𝒜} (X : x ⟶ y), F.map X = sumMap (C x) (C y) (𝟙 one) X)
    [I : InitialAlgebra F] {zero : one ⟶ I.t} {succ : I.t ⟶ I.t}
    (hα : I.α = junc (C I.t) zero succ) {A : 𝒜} (h : I.t ⟶ A) (c : one ⟶ A) (f : A ⟶ A) :
    I.α ≫ h = F.map h ≫ junc (C A) c f ↔ zero ≫ h = c ∧ succ ≫ h = h ≫ f := by
  rw [nat_fold_spec_step1 C hF, nat_fold_spec_step2 C, nat_fold_spec_step3 C hα,
    nat_fold_spec_step4 C]
  exact nat_fold_spec_step5 C zero succ h c f

end Freyd.Alg
