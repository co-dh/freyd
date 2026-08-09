/-
  Bird & de Moor, *Algebra of Programming* §6.7  Closure (book pp. 157-161).

  The reflexive-transitive closure `R*` of `R : a ⟶ a` is the smallest preorder containing `R`,
  characterised by the universal property `R ⊑ X ↔ R* ⊑ X` for preorders `X` (§6.7), and
  presented explicitly as either of the two least fixed points (6.7)/(6.8).  We also give the
  two `μ`-forms of `S≫R*` and `R*≫S` (B&dM Ex 6.32, needed on p.159 for the θ-recursion) and
  attempt the `(R∪S)*` decomposition (Ex 6.36) and the θ-recursion for computing `S≫R*`
  (pp. 159-161).

  Composition throughout is diagram order (`≫`): B&dM `X·Y` mirrors to `Y ≫ X`.  Book (6.7)
  `R* = (μX : id ∪ X·R)` therefore mirrors to `mu (fun X => Cat.id a ∪ (R ≫ X))` — the book's
  `X·R` (first `R`, then `X`) becomes `R ≫ X`.  Dually (6.8) `R* = (μX : id ∪ R·X)` mirrors to
  `mu (fun X => Cat.id a ∪ (X ≫ R))`.
-/
module

public import AOP.A6_2

universe u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

/- Tasks 1-4 (the `star`/`star'`/closure development) live in their own `section` so the
   `[DivisionLCDA 𝒜]` variable does NOT leak into the θ-stretch `section` below: having BOTH
   `[DivisionLCDA 𝒜]` and `[DivisionBooleanAllegory 𝒜]` simultaneously in scope for the same
   declaration creates a genuine diamond (two non-defeq `LocallyCompleteDistributiveAllegory`
   paths for `𝟘`/`∪`/`≫`), even with a bridge instance available — see the θ-section header. -/
section StarSection

variable {𝒜 : Type u} [DivisionLCDA 𝒜] {a b : 𝒜}

/-! ## §6.7  Definition and basic laws: (6.7) -/

/-- `R* := (μX : id ∪ X·R)` (6.7), mirrored: `mu (fun X => id ∪ R≫X)`. -/
def star {a : 𝒜} (R : a ⟶ a) : a ⟶ a := mu (fun X => Cat.id a ∪ (R ≫ X))

/-- The recursion body of (6.7) is monotonic. -/
theorem star_body_monotonic {a : 𝒜} (R : a ⟶ a) :
    Monotonic (fun X : a ⟶ a => Cat.id a ∪ (R ≫ X)) :=
  fun h => union_mono (le_refl _) (comp_mono_left R h)

/-- `R*` unfolds: `id ∪ R·R* = R*` (Knaster-Tarski applied to (6.7)). -/
theorem star_unfold {a : 𝒜} (R : a ⟶ a) : Cat.id a ∪ (R ≫ star R) = star R :=
  mu_fixed (star_body_monotonic R)

/-- `id ⊑ R*`: `R*` is reflexive. -/
theorem id_le_star {a : 𝒜} (R : a ⟶ a) : Cat.id a ⊑ star R := by
  have h : Cat.id a ⊑ Cat.id a ∪ (R ≫ star R) := le_union_left (Cat.id a) (R ≫ star R)
  rwa [star_unfold R] at h

/-- `R·R* ⊑ R*`. -/
theorem comp_star_le {a : 𝒜} (R : a ⟶ a) : R ≫ star R ⊑ star R := by
  have h : R ≫ star R ⊑ Cat.id a ∪ (R ≫ star R) := le_union_right (Cat.id a) (R ≫ star R)
  rwa [star_unfold R] at h

/-- `R ⊑ R*`. -/
theorem le_star {a : 𝒜} (R : a ⟶ a) : R ⊑ star R := by
  have h : R ≫ Cat.id a ⊑ star R :=
    le_trans (comp_mono_left R (id_le_star R)) (comp_star_le R)
  rwa [Cat.comp_id] at h

/-- **Transitivity of `R*`** (book's division proof, p.157-158). -/
theorem star_trans {a : 𝒜} (R : a ⟶ a) : star R ≫ star R ⊑ star R := by
  have hsub : star R ⊑ star R / star R := by
    refine Sup_le (fun _S hS => hS _ ?_)
    apply (le_div_iff _ _ _).mpr
    rw [union_comp_distrib]
    apply union_lub
    · rw [Cat.id_comp]; exact le_refl (star R)
    · rw [Cat.assoc R (star R / star R) (star R)]
      exact le_trans (comp_mono_left R (div_self_comp_le (star R))) (comp_star_le R)
  exact (le_div_iff _ _ _).mp hsub

/-- `R*` is bounded above by any preorder (`refl` + `trans`) containing `R`. -/
theorem star_le_of_preorder {a : 𝒜} {R X : a ⟶ a} (hrefl : Cat.id a ⊑ X)
    (htrans : X ≫ X ⊑ X) (hR : R ⊑ X) : star R ⊑ X :=
  Sup_le (fun _S hS => hS _ (union_lub hrefl (le_trans (comp_mono_right hR X) htrans)))

/-- **Universal property of `R*`** (§6.7): `R* ` is the SMALLEST preorder containing `R`. -/
theorem star_UP {a : 𝒜} {R X : a ⟶ a} (hrefl : Cat.id a ⊑ X) (htrans : X ≫ X ⊑ X) :
    R ⊑ X ↔ star R ⊑ X :=
  ⟨star_le_of_preorder hrefl htrans, le_trans (le_star R)⟩

/-- `*` is monotone: `R ⊑ S → R* ⊑ S*`. -/
theorem star_mono {a : 𝒜} {R S : a ⟶ a} (h : R ⊑ S) : star R ⊑ star S :=
  star_le_of_preorder (id_le_star S) (star_trans S) (le_trans h (le_star S))

/-! ## §6.7  The (6.8) variant (B&dM Ex 6.31)

  `R* = (μX : id ∪ R·X)` mirrors to `mu (fun X => id ∪ X≫R)`.  We build the mirrored closure
  `star'` from this body, show it is (like `star`) the least preorder containing `R`, and
  conclude `star R = star' R` by mutual leastness — `star_le_of_preorder`/`star'_le_of_preorder`
  applied to each other's preorder-containing-`R` witness. -/

/-- PRIVATE mirror of `star` for the (6.8) body `id ∪ R·X` ↦ `id ∪ X≫R`; used only to prove
    `star_eq_mu'` below (the public statement is in terms of `mu`, not this name). -/
private def star' {a : 𝒜} (R : a ⟶ a) : a ⟶ a := mu (fun X => Cat.id a ∪ (X ≫ R))

private theorem star'_body_monotonic {a : 𝒜} (R : a ⟶ a) :
    Monotonic (fun X : a ⟶ a => Cat.id a ∪ (X ≫ R)) :=
  fun h => union_mono (le_refl _) (comp_mono_right h R)

private theorem star'_unfold {a : 𝒜} (R : a ⟶ a) : Cat.id a ∪ (star' R ≫ R) = star' R :=
  mu_fixed (star'_body_monotonic R)

private theorem id_le_star' {a : 𝒜} (R : a ⟶ a) : Cat.id a ⊑ star' R := by
  have h : Cat.id a ⊑ Cat.id a ∪ (star' R ≫ R) := le_union_left (Cat.id a) (star' R ≫ R)
  rwa [star'_unfold R] at h

private theorem star'_comp_le {a : 𝒜} (R : a ⟶ a) : star' R ≫ R ⊑ star' R := by
  have h : star' R ≫ R ⊑ Cat.id a ∪ (star' R ≫ R) := le_union_right (Cat.id a) (star' R ≫ R)
  rwa [star'_unfold R] at h

private theorem le_star' {a : 𝒜} (R : a ⟶ a) : R ⊑ star' R := by
  have h : Cat.id a ≫ R ⊑ star' R :=
    le_trans (comp_mono_right (id_le_star' R) R) (star'_comp_le R)
  rwa [Cat.id_comp] at h

/-- Transitivity for `star'`, by the MIRRORED division proof (left division this time). -/
private theorem star'_trans {a : 𝒜} (R : a ⟶ a) : star' R ≫ star' R ⊑ star' R := by
  have hsub : star' R ⊑ ((star' R) \ (star' R)) := by
    refine Sup_le (fun _S hS => hS _ ?_)
    apply (le_leftDiv_iff _ _ _).mpr
    rw [DistributiveAllegory.comp_union_distrib]
    apply union_lub
    · rw [Cat.comp_id]; exact le_refl (star' R)
    · rw [← Cat.assoc (star' R) ((star' R) \ (star' R)) R]
      exact le_trans (comp_mono_right (leftDiv_comp_le (star' R) (star' R)) R) (star'_comp_le R)
  exact (le_leftDiv_iff _ _ _).mp hsub

private theorem star'_le_of_preorder {a : 𝒜} {R X : a ⟶ a} (hrefl : Cat.id a ⊑ X)
    (htrans : X ≫ X ⊑ X) (hR : R ⊑ X) : star' R ⊑ X :=
  Sup_le (fun _S hS => hS _ (union_lub hrefl (le_trans (comp_mono_left X hR) htrans)))

/-- **(6.8)**: `R* = (μX : id ∪ R·X)`, mirrored: `star R = mu (fun X => id ∪ X≫R)` (Ex 6.31).
    Proved by mutual leastness: `star R` and `star' R` are each preorders containing `R`, hence
    each is `⊑` the other's least such bound. -/
theorem star_eq_mu' {a : 𝒜} (R : a ⟶ a) :
    star R = mu (fun X : a ⟶ a => Cat.id a ∪ (X ≫ R)) :=
  le_antisymm
    (star_le_of_preorder (id_le_star' R) (star'_trans R) (le_star' R))
    (star'_le_of_preorder (id_le_star R) (star_trans R) (le_star R))

/-- `R*·R ⊑ R*` (the (6.8)-shaped "contains-`R`-on-the-right" law for `star`, derived from
    `star_eq_mu'` and `star'_comp_le`). -/
theorem star_comp_le {a : 𝒜} (R : a ⟶ a) : star R ≫ R ⊑ star R := by
  rw [star_eq_mu']
  exact star'_comp_le R

/-! ## §6.7  Star-composition μ-forms (B&dM Ex 6.32 + p.160)

  `S·R*` and `R*·S` are themselves least fixed points — of the SAME body shape as `star`/`star'`
  but with the base `id` replaced by `S`.  `closureFrom`/`closureFromR` are the two shapes
  (recursion on the left / on the right of the union argument, matching `star'`/`star`
  respectively), used only to prove `comp_star_eq_mu`/`star_comp_eq_mu`. -/

/-- PRIVATE closure-from-`S` body (recursion on the left) `S ∪ X·R` ↦ `S ∪ (X≫R)`; used only to
    prove `comp_star_eq_mu` below. -/
private def closureFrom {a b : 𝒜} (S : b ⟶ a) (R : a ⟶ a) : b ⟶ a :=
  mu (fun X : b ⟶ a => S ∪ (X ≫ R))

private theorem closureFrom_body_monotonic {a b : 𝒜} (S : b ⟶ a) (R : a ⟶ a) :
    Monotonic (fun X : b ⟶ a => S ∪ (X ≫ R)) :=
  fun h => union_mono (le_refl _) (comp_mono_right h R)

private theorem closureFrom_unfold {a b : 𝒜} (S : b ⟶ a) (R : a ⟶ a) :
    S ∪ (closureFrom S R ≫ R) = closureFrom S R :=
  mu_fixed (closureFrom_body_monotonic S R)

private theorem le_closureFrom {a b : 𝒜} (S : b ⟶ a) (R : a ⟶ a) : S ⊑ closureFrom S R := by
  have h : S ⊑ S ∪ (closureFrom S R ≫ R) := le_union_left S (closureFrom S R ≫ R)
  rwa [closureFrom_unfold] at h

private theorem closureFrom_comp_le {a b : 𝒜} (S : b ⟶ a) (R : a ⟶ a) :
    closureFrom S R ≫ R ⊑ closureFrom S R := by
  have h : closureFrom S R ≫ R ⊑ S ∪ (closureFrom S R ≫ R) :=
    le_union_right S (closureFrom S R ≫ R)
  rwa [closureFrom_unfold] at h

private theorem closureFrom_le {a b : 𝒜} {S : b ⟶ a} {R : a ⟶ a} {T : b ⟶ a}
    (hS : S ⊑ T) (hT : T ≫ R ⊑ T) : closureFrom S R ⊑ T :=
  Sup_le (fun _S1 hS1 => hS1 _ (union_lub hS hT))

/-- **B&dM Ex 6.32 / p.160**: `S·R* = (μX : S ∪ R·X)`, mirrored: `S≫R* = μX. S∪(X≫R)`. -/
theorem comp_star_eq_mu {a b : 𝒜} (S : b ⟶ a) (R : a ⟶ a) :
    S ≫ star R = mu (fun X : b ⟶ a => S ∪ (X ≫ R)) := by
  have hMle : closureFrom S R ⊑ S ≫ star R := by
    apply closureFrom_le
    · have h : S ≫ Cat.id a ⊑ S ≫ star R := comp_mono_left S (id_le_star R)
      rwa [Cat.comp_id] at h
    · rw [Cat.assoc S (star R) R]
      exact comp_mono_left S (star_comp_le R)
  have hstep : star R ⊑ (S \ (closureFrom S R)) := by
    rw [star_eq_mu']
    refine Sup_le (fun _S hS => hS _ ?_)
    apply (le_leftDiv_iff _ _ _).mpr
    rw [DistributiveAllegory.comp_union_distrib]
    apply union_lub
    · rw [Cat.comp_id]; exact le_closureFrom S R
    · rw [← Cat.assoc S (S \ (closureFrom S R)) R]
      have h1 : S ≫ (S \ (closureFrom S R)) ⊑ closureFrom S R :=
        leftDiv_comp_le S (closureFrom S R)
      exact le_trans (comp_mono_right h1 R) (closureFrom_comp_le S R)
  have hleM : S ≫ star R ⊑ closureFrom S R :=
    le_trans (comp_mono_left S hstep) (leftDiv_comp_le S (closureFrom S R))
  exact le_antisymm hleM hMle

/-- PRIVATE closure-from-`S` body (recursion on the right) `S ∪ R·X` ↦ `S ∪ (R≫X)`; used only
    to prove `star_comp_eq_mu` below. -/
private def closureFromR {a b : 𝒜} (S : a ⟶ b) (R : a ⟶ a) : a ⟶ b :=
  mu (fun X : a ⟶ b => S ∪ (R ≫ X))

private theorem closureFromR_body_monotonic {a b : 𝒜} (S : a ⟶ b) (R : a ⟶ a) :
    Monotonic (fun X : a ⟶ b => S ∪ (R ≫ X)) :=
  fun h => union_mono (le_refl _) (comp_mono_left R h)

private theorem closureFromR_unfold {a b : 𝒜} (S : a ⟶ b) (R : a ⟶ a) :
    S ∪ (R ≫ closureFromR S R) = closureFromR S R :=
  mu_fixed (closureFromR_body_monotonic S R)

private theorem le_closureFromR {a b : 𝒜} (S : a ⟶ b) (R : a ⟶ a) : S ⊑ closureFromR S R := by
  have h : S ⊑ S ∪ (R ≫ closureFromR S R) := le_union_left S (R ≫ closureFromR S R)
  rwa [closureFromR_unfold] at h

private theorem closureFromR_comp_le {a b : 𝒜} (S : a ⟶ b) (R : a ⟶ a) :
    R ≫ closureFromR S R ⊑ closureFromR S R := by
  have h : R ≫ closureFromR S R ⊑ S ∪ (R ≫ closureFromR S R) :=
    le_union_right S (R ≫ closureFromR S R)
  rwa [closureFromR_unfold] at h

private theorem closureFromR_le {a b : 𝒜} {S : a ⟶ b} {R : a ⟶ a} {T : a ⟶ b}
    (hS : S ⊑ T) (hT : R ≫ T ⊑ T) : closureFromR S R ⊑ T :=
  Sup_le (fun _S1 hS1 => hS1 _ (union_lub hS hT))

/-- The symmetric form (B&dM p.160, "S*·R = (μX : R ∪ S·X)" with roles renamed):
    `R*·S = (μX : S ∪ R·X)`, mirrored: `star R ≫ S = μX. S∪(R≫X)`. -/
theorem star_comp_eq_mu {a b : 𝒜} (R : a ⟶ a) (S : a ⟶ b) :
    star R ≫ S = mu (fun X : a ⟶ b => S ∪ (R ≫ X)) := by
  have hMle : closureFromR S R ⊑ star R ≫ S := by
    apply closureFromR_le
    · have h : Cat.id a ≫ S ⊑ star R ≫ S := comp_mono_right (id_le_star R) S
      rwa [Cat.id_comp] at h
    · rw [← Cat.assoc R (star R) S]
      exact comp_mono_right (comp_star_le R) S
  have hstep : star R ⊑ closureFromR S R / S := by
    refine Sup_le (fun _S hS => hS _ ?_)
    apply (le_div_iff _ _ _).mpr
    rw [union_comp_distrib]
    apply union_lub
    · rw [Cat.id_comp]; exact le_closureFromR S R
    · rw [Cat.assoc R (closureFromR S R / S) S]
      exact le_trans
        (comp_mono_left R (DivisionAllegory.div_comp_le (closureFromR S R) S))
        (closureFromR_comp_le S R)
  have hleM : star R ≫ S ⊑ closureFromR S R :=
    le_trans (comp_mono_right hstep S) (DivisionAllegory.div_comp_le (closureFromR S R) S)
  exact le_antisymm hleM hMle

/-! ## §6.7  Ex 6.36 (partial): `(R∪S)* = R*·(S·R*)*`, mirrored `star(star R≫S)≫star R`

  The `⊒` direction is a clean consequence of monotonicity/idempotence (`star_union_ge` below).
  The `⊑` direction (`star(R∪S) ⊑ star(star R≫S)≫star R`) is the classical Kleene-algebra
  "sliding"/"denesting" identity and genuinely needs more than monotonicity+idempotence of the
  individual stars: by `star_le_of_preorder` it reduces to transitivity of `Z := U≫T`
  (`T := star R`, `U := star(T≫S)`), and expanding `Z≫Z = U≫(T≫U)≫T` via associativity, a
  SUFFICIENT condition `T≫U ⊑ U` is FALSE in general — counterexample: a 3-object category with
  `R : 1⟶2` the only non-identity arrow of `R`, `S := 𝟘`; then `T = id ∪ {1⟶2}`, `T≫S = 𝟘`,
  `U = star 𝟘 = id`, and `T≫U = T ⊄ id = U`.  The correct route (B&dM's own hint) is the
  μ-calculus DIAGONAL rule (Ex 6.35: `mu(fun X => mu(fun Y => φ X Y)) = mu(fun X => φ X X)`),
  applied to a bivariate `φ` whose diagonal is `star'(R∪S)`'s body.  The natural diagonal choice
  `φ(X,Y) := id ∪ X≫R ∪ Y` DOES have the right diagonal (`φ(X,X) = id∪X≫(R∪S)`, matching `star'`'s
  body via `comp_union_distrib`), but its nested-mu unfolding (via `comp_star_eq_mu` applied
  twice, inner-then-outer) produces `star R ≫ star(S≫star R)` — `T` on the LEFT of a
  `star(S≫T)`-shaped factor — NOT the target `star(star R≫S)≫star R`.  The outer/inner variable
  pairing needs a different (Bekić-style) simultaneous-fixed-point arrangement not found within
  the scope of this file; DROPPED per the task's explicit license, with only `star_union_ge`
  (the `⊒` half) proved. -/

/-- The easy (`⊒`) half of B&dM Ex 6.36: both factors of `star(star R≫S)≫star R` are
    `⊑ star(R∪S)`, hence so is their composite (via `star_trans (R∪S)` twice). -/
theorem star_union_ge {a : 𝒜} (R S : a ⟶ a) :
    star (star R ≫ S) ≫ star R ⊑ star (R ∪ S) := by
  have hT : star R ⊑ star (R ∪ S) := star_mono (le_union_left R S)
  have hS : S ⊑ star (R ∪ S) := le_trans (le_union_right R S) (le_star (R ∪ S))
  have hTS : star R ≫ S ⊑ star (R ∪ S) :=
    le_trans (comp_mono_right hT S)
      (le_trans (comp_mono_left (star (R ∪ S)) hS) (star_trans (R ∪ S)))
  have hU : star (star R ≫ S) ⊑ star (R ∪ S) :=
    star_le_of_preorder (id_le_star (R ∪ S)) (star_trans (R ∪ S)) hTS
  exact le_trans (comp_mono_right hU (star R))
    (le_trans (comp_mono_left (star (R ∪ S)) hT) (star_trans (R ∪ S)))

end StarSection

/-! ## §6.7  STRETCH: the θ-recursion for computing `S≫R*` (book pp. 159-161)

  Needs Boolean subtraction (`sub`), hence `DivisionBooleanAllegory` rather than `DivisionLCDA`.
  The two merge classes are siblings, NOT related by `extends` (`AOP.A4_5`'s own diamond note),
  so we bridge with a PRIVATE instance built FROM the given `DivisionBooleanAllegory` data.  This
  bridge is only safe in a section whose ONLY division/completeness hypothesis is
  `[DivisionBooleanAllegory 𝒜]` — mixing it with an ambient `[DivisionLCDA 𝒜]` (as tasks 1-4's
  `StarSection` has) creates a genuine diamond: `𝟘`/`∪`/`≫` would resolve to non-defeq instances
  depending on which path a given subterm's elaboration happens to take (found the hard way: a
  first attempt with both variables live in the SAME section failed to typecheck with
  "synthesized instance is not definitionally equal" errors). Hence the fresh `section` below. -/

section ThetaSection

variable {𝒜 : Type u} [DivisionBooleanAllegory 𝒜] {a b : 𝒜}

-- (The `DivisionBooleanAllegory → DivisionLCDA` bridge instance and `sub_mono_left` now live
-- with the classes in `AOP.A4_5`; the rolling rule `mu_rolling` is `AOP.A6_2`'s — its
-- `MonotonicHom` hypotheses are definitionally `Monotonic` on a single hom-set.)

/-- `θ(P,Q) := P ∪ (μX : Q ∪ (R·X − P))`, mirrored: `P ∪ (μX : Q∪(X≫R − P))`. -/
def theta {a b : 𝒜} (R : a ⟶ a) (P Q : b ⟶ a) : b ⟶ a :=
  P ∪ mu (fun X : b ⟶ a => Q ∪ sub (X ≫ R) P)

/-- **p.160**: `θ(0,S) = R*·S`, mirrored `θ(0,S) = S≫R*` (the θ-recursion computes `S≫R*`). -/
theorem theta_zero_left {a b : 𝒜} (R : a ⟶ a) (S : b ⟶ a) : theta R 𝟘 S = S ≫ star R := by
  show (𝟘 : b ⟶ a) ∪ mu (fun X : b ⟶ a => S ∪ sub (X ≫ R) 𝟘) = S ≫ star R
  simp only [sub_zero, DistributiveAllegory.zero_union]
  exact (comp_star_eq_mu S R).symm

/-- **p.160**: `θ(P,0) = P`. -/
theorem theta_zero_right {a b : 𝒜} (R : a ⟶ a) (P : b ⟶ a) : theta R P 𝟘 = P := by
  show P ∪ mu (fun X : b ⟶ a => 𝟘 ∪ sub (X ≫ R) P) = P
  have hmu : mu (fun X : b ⟶ a => 𝟘 ∪ sub (X ≫ R) P) ⊑ 𝟘 := by
    refine Sup_le (fun _S hS => hS _ ?_)
    show 𝟘 ∪ sub (𝟘 ≫ R) P ⊑ 𝟘
    rw [show (𝟘 : b ⟶ a) ≫ R = 𝟘 from DistributiveAllegory.zero_comp R]
    exact union_lub (le_refl 𝟘) (inter_lb_left 𝟘 (∼P))
  exact le_antisymm (union_lub (le_refl P) (le_trans hmu (zero_le P))) (le_union_left P _)

/-- **p.160 recursion step** (B&dM's five-step derivation: subtraction, rolling, subtraction ×2,
    definition of `θ`): `θ(P,Q) = θ(P∪Q, Q·R−P−Q)`, mirrored `θ(P,Q) = θ(P∪Q, (Q≫R−P)−Q)`. -/
theorem theta_step {a b : 𝒜} (R : a ⟶ a) (P Q : b ⟶ a) :
    theta R P Q = theta R (P ∪ Q) (sub (sub (Q ≫ R) P) Q) := by
  show P ∪ mu (fun X : b ⟶ a => Q ∪ sub (X ≫ R) P)
     = (P ∪ Q) ∪ mu (fun X : b ⟶ a => sub (sub (Q ≫ R) P) Q ∪ sub (X ≫ R) (P ∪ Q))
  have step1 : mu (fun X : b ⟶ a => Q ∪ sub (X ≫ R) P)
             = mu (fun X : b ⟶ a => Q ∪ sub (sub (X ≫ R) P) Q) :=
    mu_congr (fun X => (union_sub_absorb Q (sub (X ≫ R) P)).symm)
  have hφ₀ : Monotonic (fun Y : b ⟶ a => Q ∪ Y) := fun h => union_mono (le_refl Q) h
  have hψ₀ : Monotonic (fun X : b ⟶ a => sub (sub (X ≫ R) P) Q) :=
    fun h => sub_mono_left (sub_mono_left (comp_mono_right h R) P) Q
  have step2 : mu (fun X : b ⟶ a => Q ∪ sub (sub (X ≫ R) P) Q)
             = Q ∪ mu (fun X : b ⟶ a => sub (sub ((Q ∪ X) ≫ R) P) Q) :=
    mu_rolling hφ₀ hψ₀
  have step3 : mu (fun X : b ⟶ a => sub (sub ((Q ∪ X) ≫ R) P) Q)
             = mu (fun X : b ⟶ a => sub (sub (Q ≫ R) P) Q ∪ sub (sub (X ≫ R) P) Q) := by
    apply mu_congr
    intro X
    rw [union_comp_distrib, union_sub_distrib, union_sub_distrib]
  have step4 : mu (fun X : b ⟶ a => sub (sub (Q ≫ R) P) Q ∪ sub (sub (X ≫ R) P) Q)
             = mu (fun X : b ⟶ a => sub (sub (Q ≫ R) P) Q ∪ sub (X ≫ R) (P ∪ Q)) :=
    mu_congr (fun X => by rw [sub_union])
  rw [step1, step2, step3, step4, DistributiveAllegory.union_assoc]

end ThetaSection

end Freyd.Alg
