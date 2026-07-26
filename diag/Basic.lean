/-
  `diag` — the diagrammatic-calculus tower over `Rel(Set)`.
  Plan: `diag/PLAN.md`; assessment: `Freyd/note/diagrams-for-aop.md`.

  Layers (each keeps the one below):
    diag.CB    cartesian bicategory — `;`, `∩`, `°`, `⊤`  functorialSemanticsForRelationalTheories.pdf
    diag.Tape  fb-cb rig category — `∪`, `⊥`               TapeDiagrams.pdf Def. 7.1
    diag.FO    fo-bicategory — complement, residuals      DiagrammaticAlgebraOfFirstOrderLogic.pdf §5–6

  This file: the poset enrichment all three layers share.  The hom order is PRIMITIVE here —
  unlike the allegory's derived order `R ⊑ S := R ∩ S = R` (`Freyd/S2_10.lean`) — because in the
  diagrammatic presentation `∩` is not a generator: it is the derived meet `Δ;(R ⊗ S);∇`
  (functorialSemanticsForRelationalTheories.pdf p. 22), and the inequational axioms (37)–(43)
  mention `≤` before `∩` exists.
-/
import Freyd.S1_10

universe v u

namespace Freyd.Diag

/-- The hom order, carried on its own so that the `LE` instance below — hence Lean's own `≤` — is in
    scope for the LAWS about it, which are the whole point: this theory is inequational, and its
    axioms should read on the page the way the paper prints them.  Core's `Preorder extends LE` is
    the same split, one relation per type instead of one per hom-set. -/
class HomLE (𝒞 : Type u) [Cat.{v} 𝒞] where
  le {a b : 𝒞} (R S : a ⟶ b) : Prop

instance {𝒞 : Type u} [Cat.{v} 𝒞] [HomLE.{v} 𝒞] {a b : 𝒞} : LE (a ⟶ b) := ⟨HomLE.le⟩

/-- A poset-enriched category (functorialSemanticsForRelationalTheories.pdf, Def. 4.1
    preamble: "a poset enriched category that
    is symmetric monoidal"; the symmetric monoidal part is layered on in `diag.CB`): every
    hom-set is a partial order and composition is monotone in both arguments. -/
class OrderedCat (𝒞 : Type u) extends Cat.{v} 𝒞, HomLE.{v} 𝒞 where
  le_refl {a b : 𝒞} (R : a ⟶ b) : R ≤ R
  le_trans {a b : 𝒞} {R S T : a ⟶ b} : R ≤ S → S ≤ T → R ≤ T
  le_antisymm {a b : 𝒞} {R S : a ⟶ b} : R ≤ S → S ≤ R → R = S
  /-- Poset enrichment of `≫`: composition is monotone in both arguments. -/
  comp_mono {a b c : 𝒞} {R R' : a ⟶ b} {S S' : b ⟶ c} :
    R ≤ R' → S ≤ S' → R ≫ S ≤ R' ≫ S'

end Freyd.Diag
