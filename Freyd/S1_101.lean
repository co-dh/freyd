/-
  Freyd & Scedrov, *Categories and Allegories* §1.(10)  SCONING

  §1.(10)1  SCONE of a category A with terminal 1: objects ⟨S,A,f⟩ where S is
             a set, A ∈ |𝐀|, f : S → Γ(A).  A is a retract of its scone.
             A is EXACTING if Γ=(1,-) preserves all finite colimits that exist.
  §1.(10)11 Terminal in the scone; proper sub-terminator M = ⟨∅,1⟩; 1 is coprime.
  §1.(10)12 The scone Â is exacting.
  §1.(10)13 Â → Â/M → A has both adjoints; preserves all limits and colimits.
  §1.(10)14 Additional structure on Â (exponentials, power-objects, NNO) from A.
  §1.(10)2  Sconing for Heyting algebras: S(X̂) from S(X) by adding a focal point.
  §1.(10)3  Free categories are retracts of their scone, hence exacting.
  §1.(10)31 A retract of an exacting category is exacting.
  §1.(10)32 Various free categories are exacting.
  §1.(10)4  SMALL PROJECTIVE in a cocomplete abelian category.
  §1.(10)41 Connected projective in a Grothendieck topos ⟹ (A,-) preserves all
             small colimits.
-/

module

public import Freyd.S1_10
public import Freyd.S1_90
public import Freyd.S1_72
public import Freyd.S1_84
public import Freyd.S1_97

universe v u

namespace Freyd

/-! ## §1.(10)  Exacting categories and the scone construction

  A category with a terminator is EXACTING if the functor Γ = (1,-) is exact,
  i.e. preserves any finite colimits that exist.

  The SCONE of A is the category  Â  defined in §1.21.22 whose objects are
  triples ⟨S, A, f : S → Γ(A)⟩.  Morphisms ⟨S,A⟩ → ⟨S',A'⟩ are pairs
  ⟨g : S → S', x : A → A'⟩ such that f ≫ Γ(x) = g ≫ f'.

  NOTE: Formalizing these requires a notion of "functor preserves colimits"
  that is not yet built in this repo (the repo uses hand-built Cat, not
  Mathlib's CategoryTheory, and has no `PreservesColimits` predicate).
  All propositions in this chapter are therefore recorded as BOOK stubs. -/

-- BOOK §1.(10)1: Every category A with a terminator is a slice of an exacting
-- category Â (its scone).  If A is regular / a pre-logos / a pre-topos / a
-- logos / cartesian-closed / a topos / a Grothendieck topos / a category with
-- a natural number object, then so is Â.
-- (Requires: scone construction + "exacting" predicate on functors.)

-- BOOK §1.(10)11: ⟨Γ(1),1⟩ is a terminator in the scone.  It has a proper
-- subobject M = ⟨∅,1⟩, and all proper sub-terminators are included in M.
-- In particular, 1 is coprime in Â.  The slice Â/M is equivalent to A.

-- BOOK §1.(10)12: The scone is exacting.  In fact Γ : Â → S preserves any
-- small colimits that exist (because Γ has a right adjoint given by
-- ⟨ΓA, A⟩ and a left adjoint given by ⟨∅, A⟩).

-- BOOK §1.(10)13: Â → Â/M → A has both a left adjoint (⟨∅,A⟩) and a right
-- adjoint (⟨ΓA,A⟩), so it preserves any limits and colimits that exist.

-- BOOK §1.(10)14: Additional structure on Â is determined by A via:
--   ⟨f,x⟩^## ⟨S,A⟩ = ⟨f^## S, x^## A⟩
--   ⟨T,B⟩^⟨S,A⟩   = ⟨Â(⟨S,A⟩, ⟨T,B⟩), B^A⟩
--   [⟨S,A⟩]        = ⟨Sub_Â⟨S,A⟩, [A]⟩
--   N_Â             = ⟨N_S, N_A⟩
-- If C ⊂ |A| is a generating set for A then {⟨1,C⟩ : C ∈ C} generates Â.

/-! ## §1.(10)3  Free categories are exacting

  A free category A embeds as a retract of Â (the composite A → Â → Â/M → A
  is the identity).  A retract of an exacting category is exacting [1.(10)31].
  Hence free logoi, topoi, etc. are exacting [1.(10)32]. -/

-- BOOK §1.(10)31: A retract of an exacting category is exacting.
-- Proof sketch: Γ_A : A → S is a retract of Γ_Â : Â → S.  A retract of a
-- weak-colimit-preserving functor is again such.

-- BOOK §1.(10)32: Various free categories are exacting.
-- (Formal proof requires §1.(10)31 + the retract property §1.(10)3.)

/-! ## §1.(10)4  Small projectives in a Grothendieck topos -/

-- BOOK §1.(10)41: Let E be a Grothendieck topos and A ∈ |E| a connected
-- projective.  Then the representable functor (A,-) : E → S preserves all
-- small colimits.
-- Proof sketch: (A,-) preserves finite coproducts (disjoint in E) and hence
-- all coproducts.  Since A is projective, (A,-) preserves images and hence
-- all unions.  It therefore preserves equivalence closures [§1.775, §1.846]
-- and hence equalizers, giving all finite colimits; together with coproducts
-- this gives all small colimits.
-- (Requires: "connected projective" predicate + "preserves small colimits".)

end Freyd
