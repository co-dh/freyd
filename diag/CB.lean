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
  cop (n : 𝒞) : n ⟶ n ⊗ n
  /-- `!_n : n ⟶ I`, the discard (Def. 4.1.1). -/
  dis (n : 𝒞) : n ⟶ 𝕀
  /-- `∇_n : n ⊗ n ⟶ n`, the merge (Def. 4.1.2). -/
  mer (n : 𝒞) : n ⊗ n ⟶ n
  /-- `?_n : I ⟶ n`, the unit (Def. 4.1.2). -/
  un (n : 𝒞) : 𝕀 ⟶ n

  /-- Coassociativity of `Δ`; Example 2.3(b) eq. (8). -/
  cop_assoc (n : 𝒞) :
    cop n ≫ (cop n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n = cop n ≫ (𝟙 n ⊗ₕ cop n)
  /-- Cocommutativity of `Δ`; eq. (9). -/
  cop_comm (n : 𝒞) : cop n ≫ SymMonCat.swap n n = cop n
  /-- Counit law for `(Δ, !)`; eq. (10). -/
  cop_counit (n : 𝒞) : cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.runit n = 𝟙 n

  /-- Associativity of `∇`; Example 2.3(a) eq. (5). -/
  mer_assoc (n : 𝒞) :
    (mer n ⊗ₕ 𝟙 n) ≫ mer n = SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ mer n) ≫ mer n
  /-- Commutativity of `∇`; eq. (6). -/
  mer_comm (n : 𝒞) : SymMonCat.swap n n ≫ mer n = mer n
  /-- Unit law for `(∇, ?)`; eq. (7). -/
  mer_unit (n : 𝒞) : SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ un n) ≫ mer n = 𝟙 n

  /-- (37): `∇;Δ ≤ 𝟙`.  With (38), `Δ ⊣ ∇`. -/
  ineq_37 (n : 𝒞) : le (mer n ≫ cop n) (𝟙 (n ⊗ n))
  /-- (38): `𝟙 ≤ Δ;∇`.  With (37), `Δ ⊣ ∇`. -/
  ineq_38 (n : 𝒞) : le (𝟙 n) (cop n ≫ mer n)
  /-- (39): `?;! ≤ 𝟙_I`.  With (40), `! ⊣ ?`. -/
  ineq_39 (n : 𝒞) : le (un n ≫ dis n) (𝟙 (𝕀 : 𝒞))
  /-- (40): `𝟙 ≤ !;?`.  With (39), `! ⊣ ?`. -/
  ineq_40 (n : 𝒞) : le (𝟙 n) (dis n ≫ un n)

  /-- (41), left form: `(𝟙 ⊗ Δ);α⁻¹;(∇ ⊗ 𝟙) = ∇;Δ`. -/
  frob_left (n : 𝒞) :
    (𝟙 n ⊗ₕ cop n) ≫ SymMonCat.tensAssocInv n n n ≫ (mer n ⊗ₕ 𝟙 n) = mer n ≫ cop n
  /-- (41), right form: `(Δ ⊗ 𝟙);α;(𝟙 ⊗ ∇) = ∇;Δ`. -/
  frob_right (n : 𝒞) :
    (cop n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ mer n) = mer n ≫ cop n

  /-- (42): every arrow is lax for the comultiplication — `R;Δ ≤ Δ;(R ⊗ R)`.  This is eq. (3),
      p. 4; Freyd has it product-free as §2.136's `R(S ∩ T) ⊑ RS ∩ RT` at `S := π₁°, T := π₂°`. -/
  lax_cop {m n : 𝒞} (R : m ⟶ n) : le (R ≫ cop n) (cop m ≫ (R ⊗ₕ R))
  /-- (43): every arrow is lax for the counit — `R;! ≤ !`.  Freyd: §2.152's step "`p_α` is maximal
      in `(α,λ)`, hence `R p_β ⊆ p_α`". -/
  lax_dis {m n : 𝒞} (R : m ⟶ n) : le (R ≫ dis n) (dis m)

namespace CartBicat

variable {𝒞 : Type u} [CartBicat.{v} 𝒞]

/-- The SPECIAL law `Δ;∇ = 𝟙` (functorialSemanticsForRelationalTheories.pdf p. 18, eq. (12)).
    Not an axiom: `𝟙 ≤ Δ;∇` is (38), and
    the reverse is the paper's displayed derivation — weaken the identity on one strand of the
    bubble to `!;?` by (40), then collapse with the counit and unit laws. -/
theorem special (n : 𝒞) : cop n ≫ mer n = 𝟙 n := by
  refine OrderedCat.le_antisymm ?_ (ineq_38 n)
  -- `Δ;∇ ≤ Δ;(𝟙 ⊗ (!;?));∇`, by (40) under `⊗` and then under `;`.
  have hstep : OrderedCat.le (cop n ≫ mer n) (cop n ≫ (𝟙 n ⊗ₕ (dis n ≫ un n)) ≫ mer n) := by
    have h : OrderedCat.le ((𝟙 n ⊗ₕ 𝟙 n) ≫ mer n) ((𝟙 n ⊗ₕ (dis n ≫ un n)) ≫ mer n) :=
      OrderedCat.comp_mono
        (SymMonCat.tensHom_mono (OrderedCat.le_refl _) (ineq_40 n)) (OrderedCat.le_refl _)
    rw [SymMonCat.tensHom_id, Cat.id_comp] at h
    exact OrderedCat.comp_mono (OrderedCat.le_refl _) h
  -- The right-hand side is `𝟙`: split the `⊗`, insert `runit ≫ runitInv = 𝟙`, then use the
  -- counit law (10) on the left half and the unit law (7) on the right half.
  have hcollapse : cop n ≫ (𝟙 n ⊗ₕ (dis n ≫ un n)) ≫ mer n = 𝟙 n := by
    have hsplit : (𝟙 n ⊗ₕ (dis n ≫ un n)) = (𝟙 n ⊗ₕ dis n) ≫ (𝟙 n ⊗ₕ un n) := by
      rw [← SymMonCat.tensHom_comp, Cat.id_comp]
    calc cop n ≫ (𝟙 n ⊗ₕ (dis n ≫ un n)) ≫ mer n
        = cop n ≫ ((𝟙 n ⊗ₕ dis n) ≫ (𝟙 n ⊗ₕ un n)) ≫ mer n := by rw [hsplit]
      _ = cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ 𝟙 (n ⊗ 𝕀) ≫ (𝟙 n ⊗ₕ un n) ≫ mer n := by
            rw [Cat.id_comp, Cat.assoc]
      _ = cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ (SymMonCat.runit n ≫ SymMonCat.runitInv n)
            ≫ (𝟙 n ⊗ₕ un n) ≫ mer n := by rw [SymMonCat.runit_inv]
      _ = (cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.runit n)
            ≫ (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ un n) ≫ mer n) := by
            simp only [Cat.assoc]
      _ = 𝟙 n ≫ 𝟙 n := by rw [cop_counit, mer_unit]
      _ = 𝟙 n := Cat.id_comp _
  rw [← hcollapse]
  exact hstep

/-- The counit law (10) read on the LEFT strand: `Δ;(! ⊗ 𝟙);λ = 𝟙`.  Only the right-hand form is a
    field, since cocommutativity (9) plus the unitor–symmetry coherence gives this one. -/
theorem cop_counit_left (n : 𝒞) :
    cop n ≫ (dis n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n = 𝟙 n := by
  calc cop n ≫ (dis n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n
      = (cop n ≫ SymMonCat.swap n n) ≫ (dis n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n := by rw [cop_comm]
    _ = cop n ≫ (SymMonCat.swap n n ≫ (dis n ⊗ₕ 𝟙 n)) ≫ SymMonCat.lunit n := by
          simp only [Cat.assoc]
    _ = cop n ≫ ((𝟙 n ⊗ₕ dis n) ≫ SymMonCat.swap n 𝕀) ≫ SymMonCat.lunit n := by
          rw [← SymMonCat.swap_nat]
    _ = cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.swap n 𝕀 ≫ SymMonCat.lunit n := by
          simp only [Cat.assoc]
    _ = cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.runit n := by rw [SymMonCat.swap_lunit]
    _ = 𝟙 n := cop_counit n

/-- The unit law (7) read on the LEFT strand: `λ⁻¹;(? ⊗ 𝟙);∇ = 𝟙`, dual to `cop_counit_left`. -/
theorem mer_unit_left (n : 𝒞) :
    SymMonCat.lunitInv n ≫ (un n ⊗ₕ 𝟙 n) ≫ mer n = 𝟙 n := by
  calc SymMonCat.lunitInv n ≫ (un n ⊗ₕ 𝟙 n) ≫ mer n
      = SymMonCat.lunitInv n ≫ (un n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n ≫ mer n := by rw [mer_comm]
    _ = SymMonCat.lunitInv n ≫ ((un n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n) ≫ mer n := by
          simp only [Cat.assoc]
    _ = SymMonCat.lunitInv n ≫ (SymMonCat.swap (𝕀 : 𝒞) n ≫ (𝟙 n ⊗ₕ un n)) ≫ mer n := by
          rw [SymMonCat.swap_nat]
    _ = (SymMonCat.lunitInv n ≫ SymMonCat.swap (𝕀 : 𝒞) n) ≫ (𝟙 n ⊗ₕ un n) ≫ mer n := by
          simp only [Cat.assoc]
    _ = SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ un n) ≫ mer n := by rw [lunitInv_swap]
    _ = 𝟙 n := mer_unit n

/-- The CUP `? ; Δ : I ⟶ n ⊗ n` — in `Rel`, `• ↦ (x,x)` for every `x`.  The compact-closed
    structure the Frobenius equations induce (functorialSemanticsForRelationalTheories.pdf p. 19). -/
def cup (n : 𝒞) : (𝕀 : 𝒞) ⟶ n ⊗ n := un n ≫ cop n

/-- The CAP `∇ ; ! : n ⊗ n ⟶ I` — in `Rel`, `(x,y) ↦ •` exactly when `x = y`. -/
def cap (n : 𝒞) : n ⊗ n ⟶ (𝕀 : 𝒞) := mer n ≫ dis n

/-- The SNAKE (yanking) equation: a wire bent down by a cup and back up by a cap is straight.
    This is where the Frobenius equation (41) earns its place — the middle three factors are
    literally the left-hand side of `frob_left`, which collapses them to `∇;Δ`, and then the monoid
    unit law (7) and the left counit law finish it. -/
theorem snake (n : 𝒞) :
    SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ cup n) ≫ SymMonCat.tensAssocInv n n n
      ≫ (cap n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n = 𝟙 n := by
  have hcup : (𝟙 n ⊗ₕ cup n) = (𝟙 n ⊗ₕ un n) ≫ (𝟙 n ⊗ₕ cop n) := by
    dsimp [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (cap n ⊗ₕ 𝟙 n) = (mer n ⊗ₕ 𝟙 n) ≫ (dis n ⊗ₕ 𝟙 n) := by
    dsimp [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  calc SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ cup n) ≫ SymMonCat.tensAssocInv n n n
        ≫ (cap n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n
      = SymMonCat.runitInv n ≫ ((𝟙 n ⊗ₕ un n) ≫ (𝟙 n ⊗ₕ cop n)) ≫ SymMonCat.tensAssocInv n n n
          ≫ ((mer n ⊗ₕ 𝟙 n) ≫ (dis n ⊗ₕ 𝟙 n)) ≫ SymMonCat.lunit n := by rw [hcup, hcap]
    _ = (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ un n))
          ≫ ((𝟙 n ⊗ₕ cop n) ≫ SymMonCat.tensAssocInv n n n ≫ (mer n ⊗ₕ 𝟙 n))
          ≫ (dis n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n := by simp only [Cat.assoc]
    _ = (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ un n)) ≫ (mer n ≫ cop n)
          ≫ (dis n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n := by rw [frob_left]
    _ = (SymMonCat.runitInv n ≫ (𝟙 n ⊗ₕ un n) ≫ mer n)
          ≫ (cop n ≫ (dis n ⊗ₕ 𝟙 n) ≫ SymMonCat.lunit n) := by simp only [Cat.assoc]
    _ = 𝟙 n ≫ 𝟙 n := by rw [mer_unit, cop_counit_left]
    _ = 𝟙 n := Cat.id_comp _

/-- The mirror snake, bending the other way.  Same shape as `snake` with `frob_right` in place of
    `frob_left` and the left/right unit laws exchanged. -/
theorem snake' (n : 𝒞) :
    SymMonCat.lunitInv n ≫ (cup n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n
      ≫ (𝟙 n ⊗ₕ cap n) ≫ SymMonCat.runit n = 𝟙 n := by
  have hcup : (cup n ⊗ₕ 𝟙 n) = (un n ⊗ₕ 𝟙 n) ≫ (cop n ⊗ₕ 𝟙 n) := by
    dsimp [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (𝟙 n ⊗ₕ cap n) = (𝟙 n ⊗ₕ mer n) ≫ (𝟙 n ⊗ₕ dis n) := by
    dsimp [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  calc SymMonCat.lunitInv n ≫ (cup n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n
        ≫ (𝟙 n ⊗ₕ cap n) ≫ SymMonCat.runit n
      = SymMonCat.lunitInv n ≫ ((un n ⊗ₕ 𝟙 n) ≫ (cop n ⊗ₕ 𝟙 n)) ≫ SymMonCat.tensAssoc n n n
          ≫ ((𝟙 n ⊗ₕ mer n) ≫ (𝟙 n ⊗ₕ dis n)) ≫ SymMonCat.runit n := by rw [hcup, hcap]
    _ = (SymMonCat.lunitInv n ≫ (un n ⊗ₕ 𝟙 n))
          ≫ ((cop n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ mer n))
          ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.runit n := by simp only [Cat.assoc]
    _ = (SymMonCat.lunitInv n ≫ (un n ⊗ₕ 𝟙 n)) ≫ (mer n ≫ cop n)
          ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.runit n := by rw [frob_right]
    _ = (SymMonCat.lunitInv n ≫ (un n ⊗ₕ 𝟙 n) ≫ mer n)
          ≫ (cop n ≫ (𝟙 n ⊗ₕ dis n) ≫ SymMonCat.runit n) := by simp only [Cat.assoc]
    _ = 𝟙 n ≫ 𝟙 n := by rw [mer_unit_left, cop_counit]
    _ = 𝟙 n := Cat.id_comp _

/-- The CONVERSE `R†`, by bending both of `R`'s wires around
    (functorialSemanticsForRelationalTheories.pdf p. 19, "`R†` is just the opposite relation").
    In `Rel` this reads `y ↦ x` exactly when `x R y`.

    NOTE the symbol: this is the paper's `(−)†` and Freyd's `R°`.  The paper's own `(−)°` is the
    colour swap of its §7 and is NOT order-reversing — never conflate the two. -/
def conv {a b : 𝒞} (R : a ⟶ b) : b ⟶ a :=
  SymMonCat.lunitInv b ≫ (cup a ⊗ₕ 𝟙 b) ≫ SymMonCat.tensAssoc a a b
    ≫ (𝟙 a ⊗ₕ ((R ⊗ₕ 𝟙 b) ≫ cap b)) ≫ SymMonCat.runit a

/-- `𝟙† = 𝟙`, which is exactly the mirror snake once `𝟙 ⊗ 𝟙` is collapsed. -/
theorem conv_id (a : 𝒞) : conv (𝟙 a) = 𝟙 a := by
  dsimp [conv]
  rw [SymMonCat.tensHom_id, Cat.id_comp]
  exact snake' a

/-- The converse is monotone: it is built only from `≫` and `⊗`, both of which are. -/
theorem conv_mono {a b : 𝒞} {R S : a ⟶ b} (h : OrderedCat.le R S) :
    OrderedCat.le (conv R) (conv S) := by
  dsimp [conv]
  refine OrderedCat.comp_mono (OrderedCat.le_refl _) (OrderedCat.comp_mono (OrderedCat.le_refl _)
    (OrderedCat.comp_mono (OrderedCat.le_refl _) (OrderedCat.comp_mono ?_ (OrderedCat.le_refl _))))
  exact SymMonCat.tensHom_mono (OrderedCat.le_refl _)
    (OrderedCat.comp_mono (SymMonCat.tensHom_mono h (OrderedCat.le_refl _)) (OrderedCat.le_refl _))

end CartBicat

end Freyd.Diag
