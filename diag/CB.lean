/-
  `diag.CB` — cartesian bicategories of relations.

  functorialSemanticsForRelationalTheories.pdf Definition 4.1 (pp. 17–18), stated field for field:

    1. every object `n` carries `Δ_n : n → n ⊗ n`, `!_n : n → I` forming a cocommutative comonoid;
    2. every object `n` carries `∇_n : n ⊗ n → n`, `?_n : I → n` forming a commutative monoid;
    3. the inequations (37)–(41);
    4. every arrow is a lax comonoid homomorphism — (42), (43).

  (37)/(38) say `Δ ⊣ ∇`, (39)/(40) say `! ⊣ ?` (p. 18, and the adjunction form is (35), p. 17).
  The comonoid/monoid equations are (8)–(10) of Example 2.3(b) and (5)–(7) of Example 2.3(a).

  NOT a field: the special law `Δ;∇ = 𝟙`.  The paper derives it (p. 18): "The other equation (12)
  holds in any Cartesian bicategory of relations: one direction is given by (38) and the other is
  proved as follows."  It is `special` below.

  DEFERRED, and recorded here so it is not mistaken for an oversight: Carboni & Walters additionally
  require the Frobenius structure to be the *unique* comonoid on each object (`Frobenius.pdf` Def. 1,
  clause 2, "and this is the only such comonoid structure on X"), which equationally means
  `Δ_{a⊗b}` and `!_{a⊗b}` are built from `Δ_a, Δ_b, !_a, !_b` by a shuffle.  Def. 4.1 as printed does
  not state it, and nothing below needs it; the first proof that needs `Δ` at a composite object must
  add it, with the shuffle written out.
-/
import diag.Monoidal

universe v u

namespace Freyd.Diag

open Freyd
open scoped SymMonCat

/-- A CARTESIAN BICATEGORY OF RELATIONS (functorialSemanticsForRelationalTheories.pdf Def. 4.1). -/
class CartBicat (𝒞 : Type u) extends SymMonCat.{v} 𝒞 where
  /-- `Δ_n : n ⟶ n ⊗ n`, the copy (Def. 4.1.1). -/
  delta (n : 𝒞) : n ⟶ n ⊗ n
  /-- `!_n : n ⟶ I`, the discard (Def. 4.1.1). -/
  bang (n : 𝒞) : n ⟶ 𝕀
  /-- `∇_n : n ⊗ n ⟶ n`, the merge (Def. 4.1.2). -/
  nabla (n : 𝒞) : n ⊗ n ⟶ n
  /-- `?_n : I ⟶ n`, the unit (Def. 4.1.2). -/
  unitR (n : 𝒞) : 𝕀 ⟶ n

  /-- Coassociativity of `Δ`; Example 2.3(b) eq. (8). -/
  delta_assoc (n : 𝒞) :
    delta n ≫ (delta n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n = delta n ≫ (𝟙 n ⊗ₕ delta n)
  /-- Cocommutativity of `Δ`; eq. (9). -/
  delta_comm (n : 𝒞) : delta n ≫ SymMonCat.swap n n = delta n
  /-- Counit law for `(Δ, !)`; eq. (10). -/
  delta_counit (n : 𝒞) : delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.runit n = 𝟙 n

  /-- Associativity of `∇`; Example 2.3(a) eq. (5). -/
  nabla_assoc (n : 𝒞) :
    (nabla n ⊗ₕ 𝟙 n) ≫ nabla n = SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ nabla n) ≫ nabla n
  /-- Commutativity of `∇`; eq. (6). -/
  nabla_comm (n : 𝒞) : SymMonCat.swap n n ≫ nabla n = nabla n
  /-- Unit law for `(∇, ?)`; eq. (7). -/
  nabla_unit (n : 𝒞) : SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n = 𝟙 n

  /-- (37): `∇;Δ ≤ 𝟙`.  With (38), `Δ ⊣ ∇`. -/
  ineq_37 (n : 𝒞) : (nabla n ≫ delta n) ≤ (𝟙 (n ⊗ n))
  /-- (38): `𝟙 ≤ Δ;∇`.  With (37), `Δ ⊣ ∇`. -/
  ineq_38 (n : 𝒞) : (𝟙 n) ≤ (delta n ≫ nabla n)
  /-- (39): `?;! ≤ 𝟙_I`.  With (40), `! ⊣ ?`. -/
  ineq_39 (n : 𝒞) : (unitR n ≫ bang n) ≤ (𝟙 (𝕀 : 𝒞))
  /-- (40): `𝟙 ≤ !;?`.  With (39), `! ⊣ ?`. -/
  ineq_40 (n : 𝒞) : (𝟙 n) ≤ (bang n ≫ unitR n)

  /-- (41), left form: `(𝟙 ⊗ Δ);α⁻¹;(∇ ⊗ 𝟙) = ∇;Δ`. -/
  frob_left (n : 𝒞) :
    (𝟙 n ⊗ₕ delta n) ≫ SymMonCat.tensAssocInv n n n ≫ (nabla n ⊗ₕ 𝟙 n) = nabla n ≫ delta n
  /-- (41), right form: `(Δ ⊗ 𝟙);α;(𝟙 ⊗ ∇) = ∇;Δ`. -/
  frob_right (n : 𝒞) :
    (delta n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ nabla n) = nabla n ≫ delta n

  /-- (42): every arrow is lax for the comultiplication — `R;Δ ≤ Δ;(R ⊗ R)`.  This is eq. (3),
      p. 4; Freyd has it product-free as §2.136's `R(S ∩ T) ⊑ RS ∩ RT` at `S := π₁°, T := π₂°`. -/
  lax_delta {m n : 𝒞} (R : m ⟶ n) : (R ≫ delta n) ≤ (delta m ≫ (R ⊗ₕ R))
  /-- (43): every arrow is lax for the counit — `R;! ≤ !`.  Freyd: §2.152's step "`p_α` is maximal
      in `(α,λ)`, hence `R p_β ⊆ p_α`". -/
  lax_bang {m n : 𝒞} (R : m ⟶ n) : (R ≫ bang n) ≤ (bang m)

namespace CartBicat

variable {𝒞 : Type u} [CartBicat.{v} 𝒞]

/-- The SPECIAL law `Δ;∇ = 𝟙` (functorialSemanticsForRelationalTheories.pdf p. 18, eq. (12)).
    Not an axiom: `𝟙 ≤ Δ;∇` is (38), and
    the reverse is the paper's displayed derivation — weaken the identity on one strand of the
    bubble to `!;?` by (40), then collapse with the counit and unit laws. -/
theorem special (n : 𝒞) : delta n ≫ nabla n = 𝟙 n := by
  refine OrderedCat.le_antisymm ?_ (ineq_38 n)
  -- `Δ;∇ ≤ Δ;(𝟙 ⊗ (!;?));∇`, by (40) under `⊗` and then under `;`.
  have hstep : (delta n ≫ nabla n) ≤ (delta n ≫ (𝟙 n ⊗ₕ (bang n ≫ unitR n)) ≫ nabla n) := by
    have h : ((𝟙 n ⊗ₕ 𝟙 n) ≫ nabla n) ≤ ((𝟙 n ⊗ₕ (bang n ≫ unitR n)) ≫ nabla n) :=
      OrderedCat.comp_mono
        (SymMonCat.tensHom_mono (OrderedCat.le_refl _) (ineq_40 n)) (OrderedCat.le_refl _)
    rw [SymMonCat.tensHom_id, Cat.id_comp] at h
    exact OrderedCat.comp_mono (OrderedCat.le_refl _) h
  -- The right-hand side is `𝟙`: split the `⊗`, insert `runit ≫ runitInv = 𝟙`, then use the
  -- counit law (10) on the left half and the unit law (7) on the right half.
  have hcollapse : delta n ≫ (𝟙 n ⊗ₕ (bang n ≫ unitR n)) ≫ nabla n = 𝟙 n := by
    have hsplit : (𝟙 n ⊗ₕ (bang n ≫ unitR n)) = (𝟙 n ⊗ₕ bang n) ≫ (𝟙 n ⊗ₕ unitR n) := by
      rw [← SymMonCat.tensHom_comp, Cat.id_comp]
    calc delta n ≫ (𝟙 n ⊗ₕ (bang n ≫ unitR n)) ≫ nabla n
        = delta n ≫ ((𝟙 n ⊗ₕ bang n) ≫ (𝟙 n ⊗ₕ unitR n)) ≫ nabla n := by rw [hsplit]
      _ = delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ 𝟙 (n ⊗ 𝕀) ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n := by
            rw [Cat.id_comp, Cat.assoc]
      _ = delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ (SymMonCat.runit n ≫ SymMonCat.runitInv n)
            ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n := by rw [SymMonCat.runit_inv]
      _ = (delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.runit n)
            ≫ (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n) := by
            simp only [Cat.assoc]
      _ = 𝟙 n ≫ 𝟙 n := by rw [delta_counit, nabla_unit]
      _ = 𝟙 n := Cat.id_comp _
  rw [← hcollapse]
  exact hstep

/-- The counit law (10) read on the LEFT strand: `Δ;(! ⊗ 𝟙);λ = 𝟙`.  Only the right-hand form is a
    field, since cocommutativity (9) plus the unitor–symmetry coherence gives this one. -/
theorem delta_counit_left (n : 𝒞) :
    delta n ≫ (bang n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n = 𝟙 n := by
  calc delta n ≫ (bang n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n
      = (delta n ≫ SymMonCat.swap n n) ≫ (bang n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n := by rw [delta_comm]
    _ = delta n ≫ (SymMonCat.swap n n ≫ (bang n ⊗ₕ 𝟙 n)) ≫ SymMonCat.lunit n := by
          simp only [Cat.assoc]
    _ = delta n ≫ ((𝟙 n ⊗ₕ bang n) ≫ SymMonCat.swap n 𝕀) ≫ SymMonCat.lunit n := by
          rw [← SymMonCat.swap_nat]
    _ = delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.swap n 𝕀 ≫ SymMonCat.lunit n := by
          simp only [Cat.assoc]
    _ = delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.runit n := by rw [SymMonCat.swap_lunit]
    _ = 𝟙 n := delta_counit n

/-- The unit law (7) read on the LEFT strand: `λ⁻¹;(? ⊗ 𝟙);∇ = 𝟙`, dual to `delta_counit_left`. -/
theorem nabla_unit_left (n : 𝒞) :
    SymMonCat.lunitInv n ≫ (unitR n ⊗ₕ 𝟙 n) ≫ nabla n = 𝟙 n := by
  calc SymMonCat.lunitInv n ≫ (unitR n ⊗ₕ 𝟙 n) ≫ nabla n
      = SymMonCat.lunitInv n ≫ (unitR n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n ≫ nabla n := by rw [nabla_comm]
    _ = SymMonCat.lunitInv n ≫ ((unitR n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n) ≫ nabla n := by
          simp only [Cat.assoc]
    _ = SymMonCat.lunitInv n ≫ (SymMonCat.swap (𝕀 : 𝒞) n ≫ (𝟙 n ⊗ₕ unitR n)) ≫ nabla n := by
          rw [SymMonCat.swap_nat]
    _ = (SymMonCat.lunitInv n ≫ SymMonCat.swap (𝕀 : 𝒞) n) ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n := by
          simp only [Cat.assoc]
    _ = SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n := by rw [lunitInv_swap]
    _ = 𝟙 n := nabla_unit n

/-- The CUP `? ; Δ : I ⟶ n ⊗ n` — in `Rel`, `• ↦ (x,x)` for every `x`.  The compact-closed
    structure the Frobenius equations induce (functorialSemanticsForRelationalTheories.pdf p. 19). -/
def cup (n : 𝒞) : (𝕀 : 𝒞) ⟶ n ⊗ n := unitR n ≫ delta n

/-- The CAP `∇ ; ! : n ⊗ n ⟶ I` — in `Rel`, `(x,y) ↦ •` exactly when `x = y`. -/
def cap (n : 𝒞) : n ⊗ n ⟶ (𝕀 : 𝒞) := nabla n ≫ bang n

/-- The SNAKE (yanking) equation: a wire bent down by a cup and back up by a cap is straight.
    This is where the Frobenius equation (41) earns its place — the middle three factors are
    literally the left-hand side of `frob_left`, which collapses them to `∇;Δ`, and then the monoid
    unit law (7) and the left counit law finish it. -/
theorem snake (n : 𝒞) :
    SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ cup n) ≫ SymMonCat.tensAssocInv n n n
      ≫ (cap n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n = 𝟙 n := by
  have hcup : (𝟙 n ⊗ₕ cup n) = (𝟙 n ⊗ₕ unitR n) ≫ (𝟙 n ⊗ₕ delta n) := by
    dsimp [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (cap n ⊗ₕ 𝟙 n) = (nabla n ⊗ₕ 𝟙 n) ≫ (bang n ⊗ₕ 𝟙 n) := by
    dsimp [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  calc SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ cup n) ≫ SymMonCat.tensAssocInv n n n
        ≫ (cap n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n
      = SymMonCat.runitInv n ≫ ((𝟙 n ⊗ₕ unitR n) ≫ (𝟙 n ⊗ₕ delta n)) ≫ SymMonCat.tensAssocInv n n n
          ≫ ((nabla n ⊗ₕ 𝟙 n) ≫ (bang n ⊗ₕ 𝟙 n)) ≫ SymMonCat.lunit n := by rw [hcup, hcap]
    _ = (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ unitR n))
          ≫ ((𝟙 n ⊗ₕ delta n) ≫ SymMonCat.tensAssocInv n n n ≫ (nabla n ⊗ₕ 𝟙 n))
          ≫ (bang n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n := by simp only [Cat.assoc]
    _ = (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ unitR n)) ≫ (nabla n ≫ delta n)
          ≫ (bang n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n := by rw [frob_left]
    _ = (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ unitR n) ≫ nabla n)
          ≫ (delta n ≫ (bang n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n) := by simp only [Cat.assoc]
    _ = 𝟙 n ≫ 𝟙 n := by rw [nabla_unit, delta_counit_left]
    _ = 𝟙 n := Cat.id_comp _

/-- The mirror snake, bending the other way.  Same shape as `snake` with `frob_right` in place of
    `frob_left` and the left/right unit laws exchanged. -/
theorem snake' (n : 𝒞) :
    SymMonCat.lunitInv n ≫ (cup n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n
      ≫ (𝟙 n ⊗ₕ cap n) ≫ SymMonCat.runit n = 𝟙 n := by
  have hcup : (cup n ⊗ₕ 𝟙 n) = (unitR n ⊗ₕ 𝟙 n) ≫ (delta n ⊗ₕ 𝟙 n) := by
    dsimp [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (𝟙 n ⊗ₕ cap n) = (𝟙 n ⊗ₕ nabla n) ≫ (𝟙 n ⊗ₕ bang n) := by
    dsimp [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  calc SymMonCat.lunitInv n ≫ (cup n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n
        ≫ (𝟙 n ⊗ₕ cap n) ≫ SymMonCat.runit n
      = SymMonCat.lunitInv n ≫ ((unitR n ⊗ₕ 𝟙 n) ≫ (delta n ⊗ₕ 𝟙 n)) ≫ SymMonCat.tensAssoc n n n
          ≫ ((𝟙 n ⊗ₕ nabla n) ≫ (𝟙 n ⊗ₕ bang n)) ≫ SymMonCat.runit n := by rw [hcup, hcap]
    _ = (SymMonCat.lunitInv n ≫ (unitR n ⊗ₕ 𝟙 n))
          ≫ ((delta n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ nabla n))
          ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.runit n := by simp only [Cat.assoc]
    _ = (SymMonCat.lunitInv n ≫ (unitR n ⊗ₕ 𝟙 n)) ≫ (nabla n ≫ delta n)
          ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.runit n := by rw [frob_right]
    _ = (SymMonCat.lunitInv n ≫ (unitR n ⊗ₕ 𝟙 n) ≫ nabla n)
          ≫ (delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ SymMonCat.runit n) := by simp only [Cat.assoc]
    _ = 𝟙 n ≫ 𝟙 n := by rw [nabla_unit_left, delta_counit]
    _ = 𝟙 n := Cat.id_comp _

/-- UNBEND: straighten `S : b ⟶ a` into its `I`-valued form `(𝟙_a ⊗ S);cap_a : a ⊗ b ⟶ I`.  This
    is the right-hand picture of the `†` notation on functorialSemanticsForRelationalTheories.pdf
    p. 19, read as an operation rather than as a definition. -/
def unbend {a b : 𝒞} (S : b ⟶ a) : a ⊗ b ⟶ (𝕀 : 𝒞) := (𝟙 a ⊗ₕ S) ≫ cap a

/-- BEND: the inverse operation, wrapping an `I`-valued `k : a ⊗ b ⟶ I` around a cup to get
    `b ⟶ a`.  `bend` and `unbend` are mutually inverse (`bend_unbend`, `unbend_bend`); that
    bijection is what makes the converse well behaved, and it is the "snake lemma" the paper
    appeals to for Lemma 4.2. -/
def bend {a b : 𝒞} (k : a ⊗ b ⟶ (𝕀 : 𝒞)) : b ⟶ a :=
  SymMonCat.lunitInv b ≫ (cup a ⊗ₕ 𝟙 b) ≫ SymMonCat.tensAssoc a a b
    ≫ (𝟙 a ⊗ₕ k) ≫ SymMonCat.runit a

/-- The CONVERSE `R†`, by bending both of `R`'s wires around
    (functorialSemanticsForRelationalTheories.pdf p. 19, "`R†` is just the opposite relation").
    In `Rel` this reads `y ↦ x` exactly when `x R y`.

    NOTE the symbol: this is the paper's `(−)†` and Freyd's `R°`.  The paper's own `(−)°` is the
    colour swap of its §7 and is NOT order-reversing — never conflate the two. -/
def conv {a b : 𝒞} (R : a ⟶ b) : b ⟶ a := bend ((R ⊗ₕ 𝟙 b) ≫ cap b)

/-- `𝟙† = 𝟙`, which is exactly the mirror snake once `𝟙 ⊗ 𝟙` is collapsed. -/
theorem conv_id (a : 𝒞) : conv (𝟙 a) = 𝟙 a := by
  dsimp [conv, bend]
  rw [SymMonCat.tensHom_id, Cat.id_comp]
  exact snake' a

/-- The converse is monotone: it is built only from `≫` and `⊗`, both of which are. -/
theorem conv_mono {a b : 𝒞} {R S : a ⟶ b} (h : R ≤ S) :
    (conv R) ≤ (conv S) := by
  dsimp [conv, bend]
  refine OrderedCat.comp_mono (OrderedCat.le_refl _) (OrderedCat.comp_mono (OrderedCat.le_refl _)
    (OrderedCat.comp_mono (OrderedCat.le_refl _) (OrderedCat.comp_mono ?_ (OrderedCat.le_refl _))))
  exact SymMonCat.tensHom_mono (OrderedCat.le_refl _)
    (OrderedCat.comp_mono (SymMonCat.tensHom_mono h (OrderedCat.le_refl _)) (OrderedCat.le_refl _))

section Bending

open SymMonCat

/-- The cap is symmetric: `γ;cap = cap`.  Immediate from commutativity (6) of the merge, and the
    reason the two ways of capping a pair of `a`-wires agree. -/
theorem swap_cap (n : 𝒞) : swap n n ≫ cap n = cap n := by
  dsimp [cap]; rw [← Cat.assoc, nabla_comm]

/-- The cup is symmetric: `cup;γ = cup`, dual to `swap_cap`, from cocommutativity (9). -/
theorem cup_swap (n : 𝒞) : cup n ≫ swap n n = cup n := by
  dsimp [cup]; rw [Cat.assoc, delta_comm]

/-- `bend` undoes `unbend`.  Distribute `𝟙_a ⊗ −` over the composite, push the re-bracketing past
    `(𝟙 ⊗ 𝟙) ⊗ S` with `tensAssoc_nat`, fuse the cup with `S` into `cup ⊗ S`, and then
    `lunitInv_nat` pulls `S` out to the front — what is left is exactly `snake'`. -/
theorem bend_unbend {a b : 𝒞} (S : b ⟶ a) : bend (unbend S) = S := by
  have hsplit : (𝟙 a ⊗ₕ ((𝟙 a ⊗ₕ S) ≫ cap a))
      = (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap a) := by
    rw [← tensHom_comp, Cat.id_comp]
  have hfuse : (cup a ⊗ₕ 𝟙 b) ≫ tensAssoc a a b ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S))
      = (𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ (cup a ⊗ₕ 𝟙 a) ≫ tensAssoc a a a := by
    calc (cup a ⊗ₕ 𝟙 b) ≫ tensAssoc a a b ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S))
        = (cup a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ 𝟙 a) ⊗ₕ S) ≫ tensAssoc a a a := by rw [← tensAssoc_nat]
      _ = (cup a ⊗ₕ 𝟙 b) ≫ (𝟙 (a ⊗ a) ⊗ₕ S) ≫ tensAssoc a a a := by rw [tensHom_id]
      _ = ((cup a ⊗ₕ 𝟙 b) ≫ (𝟙 (a ⊗ a) ⊗ₕ S)) ≫ tensAssoc a a a := by simp only [Cat.assoc]
      _ = (cup a ⊗ₕ S) ≫ tensAssoc a a a := by rw [tensHom_split]
      _ = ((𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ (cup a ⊗ₕ 𝟙 a)) ≫ tensAssoc a a a := by rw [tensHom_split']
      _ = (𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ (cup a ⊗ₕ 𝟙 a) ≫ tensAssoc a a a := by simp only [Cat.assoc]
  calc bend (unbend S)
      = lunitInv b ≫ (cup a ⊗ₕ 𝟙 b) ≫ tensAssoc a a b
          ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap a) ≫ runit a := by
        dsimp [bend, unbend]; rw [hsplit]; simp only [Cat.assoc]
    _ = lunitInv b ≫ ((cup a ⊗ₕ 𝟙 b) ≫ tensAssoc a a b ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S)))
          ≫ (𝟙 a ⊗ₕ cap a) ≫ runit a := by simp only [Cat.assoc]
    _ = lunitInv b ≫ ((𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ (cup a ⊗ₕ 𝟙 a) ≫ tensAssoc a a a)
          ≫ (𝟙 a ⊗ₕ cap a) ≫ runit a := by rw [hfuse]
    _ = (lunitInv b ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ S))
          ≫ (cup a ⊗ₕ 𝟙 a) ≫ tensAssoc a a a ≫ (𝟙 a ⊗ₕ cap a) ≫ runit a := by
        simp only [Cat.assoc]
    _ = (S ≫ lunitInv a)
          ≫ (cup a ⊗ₕ 𝟙 a) ≫ tensAssoc a a a ≫ (𝟙 a ⊗ₕ cap a) ≫ runit a := by rw [lunitInv_nat]
    _ = S ≫ (lunitInv a ≫ (cup a ⊗ₕ 𝟙 a) ≫ tensAssoc a a a
          ≫ (𝟙 a ⊗ₕ cap a) ≫ runit a) := by simp only [Cat.assoc]
    _ = S ≫ 𝟙 a := by rw [snake']
    _ = S := Cat.comp_id _

/-- The triangle read with both unitors inverted: `(𝟙_a ⊗ λ⁻¹_b);α⁻¹ = ρ⁻¹_a ⊗ 𝟙_b`.  Both sides
    are inverse to `ρ_a ⊗ 𝟙_b`, which the triangle identifies with `α;(𝟙_a ⊗ λ_b)`. -/
theorem runitInv_tens_triangle (a b : 𝒞) :
    (𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b = (runitInv a ⊗ₕ 𝟙 b) := by
  have hrr : (runit a ⊗ₕ 𝟙 b) ≫ (runitInv a ⊗ₕ 𝟙 b) = 𝟙 ((a ⊗ (𝕀 : 𝒞)) ⊗ b) := by
    rw [← tensHom_comp, runit_inv, Cat.id_comp, tensHom_id]
  have hL : ((𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b) ≫ (runit a ⊗ₕ 𝟙 b)
      = 𝟙 (a ⊗ b) := by
    calc ((𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b) ≫ (runit a ⊗ₕ 𝟙 b)
        = ((𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b)
            ≫ tensAssoc a (𝕀 : 𝒞) b ≫ (𝟙 a ⊗ₕ lunit b) := by rw [triangle]
      _ = (𝟙 a ⊗ₕ lunitInv b) ≫ (tensAssocInv a (𝕀 : 𝒞) b ≫ tensAssoc a (𝕀 : 𝒞) b)
            ≫ (𝟙 a ⊗ₕ lunit b) := by simp only [Cat.assoc]
      _ = (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ lunit b) := by rw [inv_tensAssoc, Cat.id_comp]
      _ = 𝟙 (a ⊗ b) := by rw [← tensHom_comp, Cat.comp_id, inv_lunit, tensHom_id]
  calc (𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b
      = (((𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b) ≫ (runit a ⊗ₕ 𝟙 b))
          ≫ (runitInv a ⊗ₕ 𝟙 b) := by rw [Cat.assoc, hrr, Cat.comp_id]
    _ = 𝟙 (a ⊗ b) ≫ (runitInv a ⊗ₕ 𝟙 b) := by rw [hL]
    _ = (runitInv a ⊗ₕ 𝟙 b) := Cat.id_comp _

/-- The pentagon rearranged so that the re-bracketing `𝟙_a ⊗ α` can be traded for one that keeps
    the passenger wire `b` on the outside.  Stated already fused with the trailing `α⁻¹`, because
    `≫` is `infixr` and an unfused `(X ≫ Y)` never appears as a subterm of `X ≫ Y ≫ Z`. -/
theorem pentagon_slide (a b : 𝒞) :
    (𝟙 a ⊗ₕ tensAssoc a a b) ≫ tensAssocInv a a (a ⊗ b)
      = tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b := by
  have hPinv : (tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b))
      ≫ ((tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b) = 𝟙 (a ⊗ ((a ⊗ a) ⊗ b)) := by
    calc (tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b))
          ≫ ((tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b)
        = tensAssocInv a (a ⊗ a) b
            ≫ ((tensAssocInv a a a ≫ tensAssoc a a a) ⊗ₕ (𝟙 b ≫ 𝟙 b))
            ≫ tensAssoc a (a ⊗ a) b := by rw [tensHom_comp]; simp only [Cat.assoc]
      _ = 𝟙 (a ⊗ ((a ⊗ a) ⊗ b)) := by
          rw [inv_tensAssoc, Cat.id_comp, tensHom_id, Cat.id_comp, inv_tensAssoc]
  have hp2 : (tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
        ≫ tensAssocInv a a (a ⊗ b)
      = tensAssoc (a ⊗ a) a b := by
    calc (tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
          ≫ tensAssocInv a a (a ⊗ b)
        = ((tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b ≫ (𝟙 a ⊗ₕ tensAssoc a a b))
            ≫ tensAssocInv a a (a ⊗ b) := by simp only [Cat.assoc]
      _ = (tensAssoc (a ⊗ a) a b ≫ tensAssoc a a (a ⊗ b)) ≫ tensAssocInv a a (a ⊗ b) := by
          rw [pentagon]
      _ = tensAssoc (a ⊗ a) a b := by rw [Cat.assoc, tensAssoc_inv, Cat.comp_id]
  calc (𝟙 a ⊗ₕ tensAssoc a a b) ≫ tensAssocInv a a (a ⊗ b)
      = 𝟙 (a ⊗ ((a ⊗ a) ⊗ b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b) ≫ tensAssocInv a a (a ⊗ b) :=
        (Cat.id_comp _).symm
    _ = ((tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b))
          ≫ ((tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b))
          ≫ (𝟙 a ⊗ₕ tensAssoc a a b) ≫ tensAssocInv a a (a ⊗ b) := by rw [hPinv]
    _ = (tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b))
          ≫ (tensAssoc a a a ⊗ₕ 𝟙 b) ≫ tensAssoc a (a ⊗ a) b
          ≫ (𝟙 a ⊗ₕ tensAssoc a a b) ≫ tensAssocInv a a (a ⊗ b) := by simp only [Cat.assoc]
    _ = (tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b)) ≫ tensAssoc (a ⊗ a) a b := by
        rw [hp2]
    _ = tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b := by
        simp only [Cat.assoc]

/-- `unbend` undoes `bend` — the snake with a PASSENGER wire.  This is the direction that needs
    Kelly's coherence lemmas: the cap creates a unit object right next to the untouched `b` strand,
    and `lunit_tens`/`runit_tens`/`lunit_unit` are exactly what lets `b` ride past it.  Modulo that
    bookkeeping the proof is `snake` tensored with `𝟙 b`. -/
theorem unbend_bend {a b : 𝒞} (k : a ⊗ b ⟶ (𝕀 : 𝒞)) : unbend (bend k) = k := by
  -- (1) `𝟙_a ⊗ −` distributes over the five factors of `bend k`.
  have hdistrib : (𝟙 a ⊗ₕ bend k)
      = (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
          ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) ≫ (𝟙 a ⊗ₕ runit a) := by
    dsimp [bend]; simp only [← tensHom_comp, Cat.id_comp]
  -- (2) the tail: `k` slides out to the far right, leaving a cap and a left unitor.
  have hru : (𝟙 a ⊗ₕ runit a) = tensAssocInv a a (𝕀 : 𝒞) ≫ runit (a ⊗ a) := by
    rw [← runit_tens, ← Cat.assoc, inv_tensAssoc, Cat.id_comp]
  have htail : (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) ≫ (𝟙 a ⊗ₕ runit a) ≫ cap a
      = tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) ≫ k := by
    calc (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) ≫ (𝟙 a ⊗ₕ runit a) ≫ cap a
        = (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) ≫ (tensAssocInv a a (𝕀 : 𝒞) ≫ runit (a ⊗ a)) ≫ cap a := by
          rw [hru]
      _ = ((𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) ≫ tensAssocInv a a (𝕀 : 𝒞)) ≫ runit (a ⊗ a) ≫ cap a := by
          simp only [Cat.assoc]
      _ = (tensAssocInv a a (a ⊗ b) ≫ ((𝟙 a ⊗ₕ 𝟙 a) ⊗ₕ k)) ≫ runit (a ⊗ a) ≫ cap a := by
          rw [tensAssocInv_nat]
      _ = (tensAssocInv a a (a ⊗ b) ≫ (𝟙 (a ⊗ a) ⊗ₕ k)) ≫ runit (a ⊗ a) ≫ cap a := by
          rw [tensHom_id]
      _ = (tensAssocInv a a (a ⊗ b) ≫ (𝟙 (a ⊗ a) ⊗ₕ k))
            ≫ (cap a ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit (𝕀 : 𝒞) := by rw [← runit_nat]
      _ = tensAssocInv a a (a ⊗ b) ≫ ((𝟙 (a ⊗ a) ⊗ₕ k) ≫ (cap a ⊗ₕ 𝟙 (𝕀 : 𝒞)))
            ≫ runit (𝕀 : 𝒞) := by simp only [Cat.assoc]
      _ = tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ k) ≫ runit (𝕀 : 𝒞) := by rw [tensHom_split']
      _ = tensAssocInv a a (a ⊗ b) ≫ ((cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ k))
            ≫ runit (𝕀 : 𝒞) := by rw [tensHom_split]
      _ = tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ k)
            ≫ lunit (𝕀 : 𝒞) := by rw [← lunit_unit]; simp only [Cat.assoc]
      _ = tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) ≫ k := by
          rw [lunit_nat]
  -- (3) what is left of the structure is `snake` with `b` carried along.
  have hcapslide : tensAssoc (a ⊗ a) a b ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b))
      = ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ tensAssoc (𝕀 : 𝒞) a b := by
    rw [tensAssoc_nat, tensHom_id]
  have hcollapse : ((runitInv a ≫ (𝟙 a ⊗ₕ cup a) ≫ tensAssocInv a a a
        ≫ (cap a ⊗ₕ 𝟙 a) ≫ lunit a) ⊗ₕ 𝟙 b)
      = (runitInv a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b)
          ≫ ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ (lunit a ⊗ₕ 𝟙 b) := by
    simp only [← tensHom_comp, Cat.id_comp]
  have hstruct : (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
        ≫ tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b)
      = 𝟙 (a ⊗ b) := by
    calc (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
          ≫ tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b)
        = (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b))
            ≫ ((𝟙 a ⊗ₕ tensAssoc a a b) ≫ tensAssocInv a a (a ⊗ b))
            ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) := by simp only [Cat.assoc]
      _ = (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b))
            ≫ (tensAssocInv a (a ⊗ a) b ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b)
            ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) := by rw [pentagon_slide]
      _ = (𝟙 a ⊗ₕ lunitInv b)
            ≫ ((𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ tensAssocInv a (a ⊗ a) b)
            ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b
            ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) := by simp only [Cat.assoc]
      _ = (𝟙 a ⊗ₕ lunitInv b)
            ≫ (tensAssocInv a (𝕀 : 𝒞) b ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b))
            ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b
            ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) := by rw [← tensAssocInv_nat]
      _ = ((𝟙 a ⊗ₕ lunitInv b) ≫ tensAssocInv a (𝕀 : 𝒞) b)
            ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b)
            ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b
            ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) := by simp only [Cat.assoc]
      _ = (runitInv a ⊗ₕ 𝟙 b)
            ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b)
            ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b) ≫ tensAssoc (a ⊗ a) a b
            ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) := by rw [runitInv_tens_triangle]
      _ = (runitInv a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b)
            ≫ (tensAssoc (a ⊗ a) a b ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b))) ≫ lunit (a ⊗ b) := by
          simp only [Cat.assoc]
      _ = (runitInv a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b)
            ≫ (((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ tensAssoc (𝕀 : 𝒞) a b) ≫ lunit (a ⊗ b) := by
          rw [hcapslide]
      _ = (runitInv a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b)
            ≫ ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ (tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b)) := by
          simp only [Cat.assoc]
      _ = (runitInv a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (tensAssocInv a a a ⊗ₕ 𝟙 b)
            ≫ ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ (lunit a ⊗ₕ 𝟙 b) := by rw [lunit_tens]
      _ = ((runitInv a ≫ (𝟙 a ⊗ₕ cup a) ≫ tensAssocInv a a a
            ≫ (cap a ⊗ₕ 𝟙 a) ≫ lunit a) ⊗ₕ 𝟙 b) := hcollapse.symm
      _ = (𝟙 a ⊗ₕ 𝟙 b) := by rw [snake]
      _ = 𝟙 (a ⊗ b) := tensHom_id a b
  calc unbend (bend k)
      = (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
          ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) ≫ (𝟙 a ⊗ₕ runit a) ≫ cap a := by
        dsimp only [unbend]; rw [hdistrib]; simp only [Cat.assoc]
    _ = (𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
          ≫ (tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b) ≫ k) := by
        rw [htail]
    _ = ((𝟙 a ⊗ₕ lunitInv b) ≫ (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ tensAssoc a a b)
          ≫ tensAssocInv a a (a ⊗ b) ≫ (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ lunit (a ⊗ b)) ≫ k := by
        simp only [Cat.assoc]
    _ = 𝟙 (a ⊗ b) ≫ k := by rw [hstruct]
    _ = k := Cat.id_comp _

/-- SLIDING a box around the cap: `(𝟙_a ⊗ R†);cap_a = (R ⊗ 𝟙_b);cap_b`.  This is `unbend_bend`
    read at `R`'s own unbending — `R†` is by definition the bending of `(R ⊗ 𝟙);cap`, so straightening
    it again returns what we started from.  Every converse law below is one application of this. -/
theorem conv_slide {a b : 𝒞} (R : a ⟶ b) :
    (𝟙 a ⊗ₕ conv R) ≫ cap a = (R ⊗ₕ 𝟙 b) ≫ cap b := unbend_bend _

/-- Capping a box on the left is capping it on the right, past a symmetry — the cap does not care
    which strand the box sits on (`swap_cap`). -/
theorem tens_cap_swap {a b : 𝒞} (S : b ⟶ a) :
    (S ⊗ₕ 𝟙 a) ≫ cap a = swap b a ≫ (𝟙 a ⊗ₕ S) ≫ cap a := by
  calc (S ⊗ₕ 𝟙 a) ≫ cap a
      = (S ⊗ₕ 𝟙 a) ≫ swap a a ≫ cap a := by rw [swap_cap]
    _ = ((S ⊗ₕ 𝟙 a) ≫ swap a a) ≫ cap a := by simp only [Cat.assoc]
    _ = (swap b a ≫ (𝟙 a ⊗ₕ S)) ≫ cap a := by rw [swap_nat]
    _ = swap b a ≫ (𝟙 a ⊗ₕ S) ≫ cap a := by simp only [Cat.assoc]

/-- UNIQUENESS of the converse: an arrow that unbends to `(R ⊗ 𝟙);cap` IS `R†`.  `bend` inverts
    `unbend` (`bend_unbend`), so `unbend` is injective — this is that injectivity, packaged. -/
theorem conv_unique {a b : 𝒞} {R : a ⟶ b} {S : b ⟶ a}
    (h : (𝟙 a ⊗ₕ S) ≫ cap a = (R ⊗ₕ 𝟙 b) ≫ cap b) : S = conv R := by
  calc S = bend (unbend S) := (bend_unbend S).symm
    _ = bend ((R ⊗ₕ 𝟙 b) ≫ cap b) := by dsimp only [unbend]; rw [h]
    _ = conv R := rfl

/-- INVOLUTIVITY, `R†† = R` — Freyd's `recip_recip` (§2.11).  By uniqueness it is enough to unbend
    `R` itself and recognise `R†`'s unbending, which `tens_cap_swap` supplies once the two symmetries
    cancel. -/
theorem conv_conv {a b : 𝒞} (R : a ⟶ b) : conv (conv R) = R := by
  refine (conv_unique ?_).symm
  calc (𝟙 b ⊗ₕ R) ≫ cap b
      = (swap b a ≫ swap a b) ≫ (𝟙 b ⊗ₕ R) ≫ cap b := by rw [swap_swap, Cat.id_comp]
    _ = swap b a ≫ swap a b ≫ (𝟙 b ⊗ₕ R) ≫ cap b := by simp only [Cat.assoc]
    _ = swap b a ≫ (R ⊗ₕ 𝟙 b) ≫ cap b := by rw [← tens_cap_swap]
    _ = swap b a ≫ (𝟙 a ⊗ₕ conv R) ≫ cap a := by rw [conv_slide]
    _ = (conv R ⊗ₕ 𝟙 a) ≫ cap a := (tens_cap_swap (conv R)).symm

/-- CONTRAVARIANT FUNCTORIALITY, `(R;S)† = S†;R†` — Lemma 4.2 (ii)
    (functorialSemanticsForRelationalTheories.pdf p. 19) and Freyd's `recip_comp` (§2.11).  Unbend
    `S†;R†` one factor at a time: `conv_slide` turns the inner `R†` into `R`, `tensHom_split` walks
    `S†` across to the other strand, and a second `conv_slide` turns it into `S`. -/
theorem conv_comp {a b c : 𝒞} (R : a ⟶ b) (S : b ⟶ c) :
    conv (R ≫ S) = conv S ≫ conv R := by
  refine (conv_unique ?_).symm
  have hs : (𝟙 a ⊗ₕ (conv S ≫ conv R)) = (𝟙 a ⊗ₕ conv S) ≫ (𝟙 a ⊗ₕ conv R) := by
    rw [← tensHom_comp, Cat.id_comp]
  calc (𝟙 a ⊗ₕ (conv S ≫ conv R)) ≫ cap a
      = (𝟙 a ⊗ₕ conv S) ≫ (𝟙 a ⊗ₕ conv R) ≫ cap a := by rw [hs]; simp only [Cat.assoc]
    _ = (𝟙 a ⊗ₕ conv S) ≫ (R ⊗ₕ 𝟙 b) ≫ cap b := by rw [conv_slide]
    _ = ((𝟙 a ⊗ₕ conv S) ≫ (R ⊗ₕ 𝟙 b)) ≫ cap b := by simp only [Cat.assoc]
    _ = (R ⊗ₕ conv S) ≫ cap b := by rw [tensHom_split']
    _ = ((R ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ conv S)) ≫ cap b := by rw [tensHom_split]
    _ = (R ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ conv S) ≫ cap b := by simp only [Cat.assoc]
    _ = (R ⊗ₕ 𝟙 c) ≫ (S ⊗ₕ 𝟙 c) ≫ cap c := by rw [conv_slide]
    _ = ((R ⊗ₕ 𝟙 c) ≫ (S ⊗ₕ 𝟙 c)) ≫ cap c := by simp only [Cat.assoc]
    _ = ((R ≫ S) ⊗ₕ 𝟙 c) ≫ cap c := by rw [← tensHom_comp, Cat.comp_id]

/-! ### Towards the modular law

  The three results below are everything the modular law needs.  `nabla_of_cap` is the only Frobenius
  computation in the group: it says the merge can be rebuilt from a copy and a cap.  `cap_tens_nabla`
  is that fact with a box riding on the bent strand, and `nabla_slide_conv` is the modular law with
  its two outer factors stripped off — the step where the lax inequation (42) duplicates `S`. -/

/-- The MERGE rebuilt from a copy and a cap: `(Δ ⊗ 𝟙);α;(𝟙 ⊗ cap);ρ = ∇`.  Unfold `cap = ∇;!` and
    the three middle factors become the left-hand side of `frob_right`, collapsing to `∇;Δ`; the
    counit law (10) then eats the `Δ`.  This single equation is the whole Frobenius content of the
    modular law. -/
theorem nabla_of_cap (n : 𝒞) :
    (delta n ⊗ₕ 𝟙 n) ≫ tensAssoc n n n ≫ (𝟙 n ⊗ₕ cap n) ≫ runit n = nabla n := by
  have hcap : (𝟙 n ⊗ₕ cap n) = (𝟙 n ⊗ₕ nabla n) ≫ (𝟙 n ⊗ₕ bang n) := by
    dsimp [cap]; rw [← tensHom_comp, Cat.id_comp]
  calc (delta n ⊗ₕ 𝟙 n) ≫ tensAssoc n n n ≫ (𝟙 n ⊗ₕ cap n) ≫ runit n
      = ((delta n ⊗ₕ 𝟙 n) ≫ tensAssoc n n n ≫ (𝟙 n ⊗ₕ nabla n))
          ≫ (𝟙 n ⊗ₕ bang n) ≫ runit n := by rw [hcap]; simp only [Cat.assoc]
    _ = (nabla n ≫ delta n) ≫ (𝟙 n ⊗ₕ bang n) ≫ runit n := by rw [frob_right]
    _ = nabla n ≫ delta n ≫ (𝟙 n ⊗ₕ bang n) ≫ runit n := by simp only [Cat.assoc]
    _ = nabla n ≫ 𝟙 n := by rw [delta_counit]
    _ = nabla n := Cat.comp_id _

/-- `nabla_of_cap` with a box on the bent strand: `(Δ ⊗ 𝟙);α;(𝟙 ⊗ ((𝟙 ⊗ T);cap));ρ = (𝟙 ⊗ T);∇`.
    `tensAssoc_nat` and the two splittings pull `T` out to the front, after which the box-free
    `nabla_of_cap` closes it. -/
theorem cap_tens_nabla {b c : 𝒞} (T : c ⟶ b) :
    (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ T) ≫ cap b)) ≫ runit b
      = (𝟙 b ⊗ₕ T) ≫ nabla b := by
  have hsplit : (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ T) ≫ cap b))
      = (𝟙 b ⊗ₕ (𝟙 b ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ cap b) := by rw [← tensHom_comp, Cat.id_comp]
  calc (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ T) ≫ cap b)) ≫ runit b
      = (delta b ⊗ₕ 𝟙 c) ≫ (tensAssoc b b c ≫ (𝟙 b ⊗ₕ (𝟙 b ⊗ₕ T)))
          ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by rw [hsplit]; simp only [Cat.assoc]
    _ = (delta b ⊗ₕ 𝟙 c) ≫ (((𝟙 b ⊗ₕ 𝟙 b) ⊗ₕ T) ≫ tensAssoc b b b)
          ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by rw [← tensAssoc_nat]
    _ = (delta b ⊗ₕ 𝟙 c) ≫ ((𝟙 (b ⊗ b) ⊗ₕ T) ≫ tensAssoc b b b)
          ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by rw [tensHom_id]
    _ = ((delta b ⊗ₕ 𝟙 c) ≫ (𝟙 (b ⊗ b) ⊗ₕ T)) ≫ tensAssoc b b b
          ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by simp only [Cat.assoc]
    _ = (delta b ⊗ₕ T) ≫ tensAssoc b b b ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by rw [tensHom_split]
    _ = ((𝟙 b ⊗ₕ T) ≫ (delta b ⊗ₕ 𝟙 b)) ≫ tensAssoc b b b
          ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by rw [tensHom_split']
    _ = (𝟙 b ⊗ₕ T) ≫ (delta b ⊗ₕ 𝟙 b) ≫ tensAssoc b b b
          ≫ (𝟙 b ⊗ₕ cap b) ≫ runit b := by simp only [Cat.assoc]
    _ = (𝟙 b ⊗ₕ T) ≫ nabla b := by rw [nabla_of_cap]

/-- THE HEART OF THE MODULAR LAW: `(S ⊗ 𝟙);∇ ≤ (𝟙 ⊗ S†);∇;S`.

    Read relationally, the left-hand side sends `(y, z)` to `z` when `S y z`, and the right-hand
    side sends it to any `z'` with `S y z`; so `S` occurs once on the left and twice on the right.
    That is the tell: the lax copy inequation (42) — the ONLY place a box may be duplicated — has to
    be the inequality step, and it is.  `nabla_of_cap` puts the left-hand side into the shape `(S;Δ) ⊗ 𝟙`
    that (42) applies to, and `conv_slide` turns the surviving duplicate into `S†`. -/
theorem nabla_slide_conv {b c : 𝒞} (S : b ⟶ c) :
    ((S ⊗ₕ 𝟙 c) ≫ nabla c) ≤ ((𝟙 b ⊗ₕ conv S) ≫ nabla b ≫ S) := by
  have hL : ((S ≫ delta c) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c
      = (S ⊗ₕ 𝟙 c) ≫ nabla c := by
    calc ((S ≫ delta c) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c
        = ((S ⊗ₕ 𝟙 c) ≫ (delta c ⊗ₕ 𝟙 c)) ≫ tensAssoc c c c
            ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c := by rw [← tensHom_comp, Cat.comp_id]
      _ = (S ⊗ₕ 𝟙 c) ≫ (delta c ⊗ₕ 𝟙 c) ≫ tensAssoc c c c
            ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c := by simp only [Cat.assoc]
      _ = (S ⊗ₕ 𝟙 c) ≫ nabla c := by rw [nabla_of_cap]
  have hR : ((delta b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c
      = (𝟙 b ⊗ₕ conv S) ≫ nabla b ≫ S := by
    calc ((delta b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c
        = ((delta b ⊗ₕ 𝟙 c) ≫ ((S ⊗ₕ S) ⊗ₕ 𝟙 c)) ≫ tensAssoc c c c
            ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c := by rw [← tensHom_comp, Cat.comp_id]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ (((S ⊗ₕ S) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c)
            ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c := by simp only [Cat.assoc]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ (tensAssoc b b c ≫ (S ⊗ₕ (S ⊗ₕ 𝟙 c)))
            ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c := by rw [tensAssoc_nat]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ ((S ⊗ₕ (S ⊗ₕ 𝟙 c)) ≫ (𝟙 c ⊗ₕ cap c))
            ≫ runit c := by simp only [Cat.assoc]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (S ⊗ₕ ((S ⊗ₕ 𝟙 c) ≫ cap c))
            ≫ runit c := by rw [← tensHom_comp, Cat.comp_id]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (S ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b))
            ≫ runit c := by rw [conv_slide]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c
            ≫ ((𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b)) ≫ (S ⊗ₕ 𝟙 (𝕀 : 𝒞)))
            ≫ runit c := by rw [tensHom_split']
      _ = (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b))
            ≫ (S ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit c := by simp only [Cat.assoc]
      _ = (delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b))
            ≫ runit b ≫ S := by rw [runit_nat]
      _ = ((delta b ⊗ₕ 𝟙 c) ≫ tensAssoc b b c ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b))
            ≫ runit b) ≫ S := by simp only [Cat.assoc]
      _ = ((𝟙 b ⊗ₕ conv S) ≫ nabla b) ≫ S := by rw [cap_tens_nabla]
      _ = (𝟙 b ⊗ₕ conv S) ≫ nabla b ≫ S := by simp only [Cat.assoc]
  -- Spelled as a THREE-LINK `calc` rather than `rw [← hL, ← hR]; exact …`, so that the argument sits
  -- in the proof TERM where `diag-export --proof` can draw it: reshape, the one inequality, reshape
  -- back.  `hL` and `hR` are the reshaping and are stated at `=`, so the drawn chain shows exactly
  -- one `≤`, which is `lax_delta` — the whole of the mathematics.
  calc (S ⊗ₕ 𝟙 c) ≫ nabla c
      = ((S ≫ delta c) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c := hL.symm
    _ ≤ ((delta b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) ≫ tensAssoc c c c ≫ (𝟙 c ⊗ₕ cap c) ≫ runit c :=
        OrderedCat.comp_mono (tensHom_mono (lax_delta S) (OrderedCat.le_refl _))
          (OrderedCat.le_refl _)
    _ = (𝟙 b ⊗ₕ conv S) ≫ nabla b ≫ S := hR

end Bending

end CartBicat

end Freyd.Diag
