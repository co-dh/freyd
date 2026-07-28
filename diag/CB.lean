/-
  `diag.CB` — cartesian bicategories of relations.

  functorialSemanticsForRelationalTheories.pdf Definition 4.1 (pp. 17–18), stated field for field:

    1. every object `n` carries `Δ_n : n → n ⊗ n`, `!_n : n → I` forming a cocommutative comonoid;
    2. every object `n` carries `∇_n : n ⊗ n → n`, `?_n : I → n` forming a commutative monoid;
    3. the inequations (37)–(41);
    4. every arrow is a lax comonoid homomorphism — (42), (43).

  (37)/(38) say `Δ ⊣ ∇`, (39)/(40) say `! ⊣ ?` (p. 18, and the adjunction form is (35), p. 17).
  The comonoid/monoid equations are (8)–(10) of Example 2.3(b) and (5)–(7) of Example 2.3(a).

  STRICT.  `diag.Monoidal` on this branch has no associator and no unitors, so the (co)monoid laws
  are stated the way the paper prints them — `Δ;(Δ ⊗ 𝟙) = Δ;(𝟙 ⊗ Δ)`, `Δ;(𝟙 ⊗ !) = 𝟙` — with no
  coherence arrow anywhere in a field, and the wire-bending section below spends no coherence
  lemmas at all.

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
open scoped Word SymMonCat

/-- A CARTESIAN BICATEGORY OF RELATIONS (functorialSemanticsForRelationalTheories.pdf Def. 4.1). -/
class CartBicat (O : Type u) extends SymMonCat.{v} O where
  Δ (n : Word O) : n ⟶ n ⊗ n     --copy
  «!» (n : Word O) : n ⟶ 𝕀       --discard
  «∇» (n : Word O) : n ⊗ n ⟶ n   --merge
  «?» (n : Word O) : 𝕀 ⟶ n       --unit

  /-- Coassociativity of `Δ`; eq. (8).  With `α = 𝟙` the two copy trees are compared directly. -/
  Δ_assoc (n : Word O) : Δ n ≫ (Δ n ⊗ₕ 𝟙 n) = (Δ n ≫ (𝟙 n ⊗ₕ Δ n) : _)
  /-- Cocommutativity of `Δ`; eq. (9). -/
  Δ_comm (n : Word O) : Δ n ≫ SymMonCat.swap n n = Δ n
  /-- Counit law for `(Δ, !)`; eq. (10). -/
  Δ_counit (n : Word O) : Δ n ≫ (𝟙 n ⊗ₕ «!» n) = 𝟙 n

  /-- Associativity of `∇`; Example 2.3(a) eq. (5). -/
  «∇_assoc» (n : Word O) : («∇» n ⊗ₕ 𝟙 n) ≫ «∇» n = ((𝟙 n ⊗ₕ «∇» n) ≫ «∇» n : _)
  /-- Commutativity of `∇`; eq. (6). -/
  «∇_comm» (n : Word O) : SymMonCat.swap n n ≫ «∇» n = «∇» n
  /-- Unit law for `(∇, ?)`; eq. (7). -/
  «∇_unit» (n : Word O) : (𝟙 n ⊗ₕ «?» n) ≫ «∇» n = 𝟙 n

  /-- (37): `∇;Δ ≤ 𝟙`.  With (38), `Δ ⊣ ∇`. -/
  «∇Δ_≤_𝟙» (n : Word O) : («∇» n ≫ Δ n) ≤ (𝟙 (n ⊗ n))
  /-- (38): `𝟙 ≤ Δ;∇`.  With (37), `Δ ⊣ ∇`. -/
  «𝟙_≤_Δ∇» (n : Word O) : (𝟙 n) ≤ (Δ n ≫ «∇» n)
  /-- (39): `?;! ≤ 𝟙_I`.  With (40), `! ⊣ ?`. -/
  «?!_≤_𝟙» (n : Word O) : («?» n ≫ «!» n) ≤ (𝟙 (𝕀 : Word O))
  /-- (40): `𝟙 ≤ !;?`.  With (39), `! ⊣ ?`. -/
  «𝟙_≤_!?» (n : Word O) : (𝟙 n) ≤ («!» n ≫ «?» n)

  /-- (41), left form: `(𝟙 ⊗ Δ);(∇ ⊗ 𝟙) = ∇;Δ`. -/
  frob_left (n : Word O) : (𝟙 n ⊗ₕ Δ n) ≫ («∇» n ⊗ₕ 𝟙 n) = («∇» n ≫ Δ n : _)
  /-- (41), right form: `(Δ ⊗ 𝟙);(𝟙 ⊗ ∇) = ∇;Δ`. -/
  frob_right (n : Word O) : (Δ n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ «∇» n) = («∇» n ≫ Δ n : _)

  /-- (42): every arrow is lax for the comultiplication — `R;Δ ≤ Δ;(R ⊗ R)`.  This is eq. (3),
      p. 4; Freyd has it product-free as §2.136's `R(S ∩ T) ⊑ RS ∩ RT` at `S := π₁°, T := π₂°`. -/
  lax_Δ {m n : Word O} (R : m ⟶ n) : (R ≫ Δ n) ≤ (Δ m ≫ (R ⊗ₕ R))
  /-- (43): every arrow is lax for the counit — `R;! ≤ !`.  Freyd: §2.152's step "`p_α` is maximal
      in `(α,λ)`, hence `R p_β ⊆ p_α`". -/
  lax_! {m n : Word O} (R : m ⟶ n) : (R ≫ «!» n) ≤ («!» m)

namespace CartBicat

/-- `∇` at the USE sites, so the merge reads as the paper draws it rather than as `∇`.  The field
    itself has to keep the guillemets — U+2207 is a mathematical operator, outside Lean's
    letterlike whitelist (`Init/Meta/Defs.lean:100`), so it is not a legal bare identifier — and the
    class body above is elaborated before this line, so it keeps them too.

    Only the merge gets this.  `!` loses to core's Bool negation even at `priority := high`, and `?`
    is read as a metavariable before notation is consulted; both stay `«!»` and `«?»` throughout. -/
scoped notation "∇" => CartBicat.«∇»

variable {O : Type u} [CartBicat.{v} O]

/-- The SPECIAL law `Δ;∇ = 𝟙` (functorialSemanticsForRelationalTheories.pdf p. 18, eq. (12)).
    Not an axiom: `𝟙 ≤ Δ;∇` is (38), and
    the reverse is the paper's displayed derivation — weaken the identity on one strand of the
    bubble to `!;?` by (40), then collapse with the counit and unit laws. -/
theorem special (n : Word O) : Δ n ≫ ∇ n = 𝟙 n := by
  refine OrderedCat.«≤_antisymm» ?_ («𝟙_≤_Δ∇» n)
  -- `Δ;∇ ≤ Δ;(𝟙 ⊗ (!;?));∇`, by (40) under `⊗` and then under `;`.
  have hstep : (Δ n ≫ ∇ n) ≤ (Δ n ≫ (𝟙 n ⊗ₕ («!» n ≫ «?» n)) ≫ ∇ n) := by
    have h : ((𝟙 n ⊗ₕ 𝟙 n) ≫ ∇ n) ≤ ((𝟙 n ⊗ₕ («!» n ≫ «?» n)) ≫ ∇ n) :=
      OrderedCat.comp_mono
        (SymMonCat.tensHom_mono (OrderedCat.«≤_refl» _) («𝟙_≤_!?» n)) (OrderedCat.«≤_refl» _)
    rw [SymMonCat.tensHom_id, Cat.id_comp] at h
    exact OrderedCat.comp_mono (OrderedCat.«≤_refl» _) h
  -- The right-hand side is `𝟙`: split the `⊗`, then use the counit law (10) on the left half and
  -- the unit law (7) on the right half.  In the non-strict tower this step also had to insert
  -- `ρ ; ρ⁻¹ = 𝟙` between the halves; with `ρ = 𝟙` there is nothing between them.
  have hcollapse : Δ n ≫ (𝟙 n ⊗ₕ («!» n ≫ «?» n)) ≫ ∇ n = 𝟙 n := by
    have hsplit : (𝟙 n ⊗ₕ («!» n ≫ «?» n)) = (𝟙 n ⊗ₕ «!» n) ≫ (𝟙 n ⊗ₕ «?» n) := by
      rw [← SymMonCat.tensHom_comp, Cat.id_comp]
    calc Δ n ≫ (𝟙 n ⊗ₕ («!» n ≫ «?» n)) ≫ ∇ n
        = Δ n ≫ ((𝟙 n ⊗ₕ «!» n) ≫ (𝟙 n ⊗ₕ «?» n)) ≫ ∇ n := by rw [hsplit]
      _ = (Δ n ≫ (𝟙 n ⊗ₕ «!» n)) ≫ (𝟙 n ⊗ₕ «?» n) ≫ ∇ n := by simp only [Cat.assoc]
      _ = 𝟙 n ≫ 𝟙 n := by rw [Δ_counit, «∇_unit»]
      _ = 𝟙 n := Cat.id_comp _
  rw [← hcollapse]
  exact hstep

/-- The counit law (10) read on the LEFT strand: `Δ;(! ⊗ 𝟙) = 𝟙`.  Only the right-hand form is a
    field, since cocommutativity (9) plus `swap_unit_right` gives this one. -/
theorem Δ_counit_left (n : Word O) : Δ n ≫ («!» n ⊗ₕ 𝟙 n) = 𝟙 n := by
  have h : SymMonCat.swap n n ≫ («!» n ⊗ₕ 𝟙 n) = (𝟙 n ⊗ₕ «!» n) := by
    calc SymMonCat.swap n n ≫ («!» n ⊗ₕ 𝟙 n)
        = (𝟙 n ⊗ₕ «!» n) ≫ SymMonCat.swap n (𝕀 : Word O) :=
          (SymMonCat.swap_nat (𝟙 n) («!» n)).symm
      _ = (𝟙 n ⊗ₕ «!» n) ≫ 𝟙 n := by rw [swap_unit_right]
      _ = (𝟙 n ⊗ₕ «!» n) := Cat.comp_id _
  calc Δ n ≫ («!» n ⊗ₕ 𝟙 n)
      = (Δ n ≫ SymMonCat.swap n n) ≫ («!» n ⊗ₕ 𝟙 n) := by rw [Δ_comm]
    _ = Δ n ≫ SymMonCat.swap n n ≫ («!» n ⊗ₕ 𝟙 n) := Cat.assoc _ _ _
    _ = Δ n ≫ (𝟙 n ⊗ₕ «!» n) := by rw [h]
    _ = 𝟙 n := Δ_counit n

/-- The unit law (7) read on the LEFT strand: `(? ⊗ 𝟙);∇ = 𝟙`, dual to `Δ_counit_left`. -/
theorem «∇_unit_left» (n : Word O) : («?» n ⊗ₕ 𝟙 n) ≫ ∇ n = 𝟙 n := by
  have h : («?» n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n = (𝟙 n ⊗ₕ «?» n) := by
    calc («?» n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n
        = SymMonCat.swap (𝕀 : Word O) n ≫ (𝟙 n ⊗ₕ «?» n) :=
          SymMonCat.swap_nat («?» n) (𝟙 n)
      _ = 𝟙 n ≫ (𝟙 n ⊗ₕ «?» n) := by rw [swap_unit_left]
      _ = (𝟙 n ⊗ₕ «?» n) := Cat.id_comp _
  calc («?» n ⊗ₕ 𝟙 n) ≫ ∇ n
      = («?» n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n ≫ ∇ n := by rw [«∇_comm»]
    _ = ((«?» n ⊗ₕ 𝟙 n) ≫ SymMonCat.swap n n) ≫ ∇ n := (Cat.assoc _ _ _).symm
    _ = (𝟙 n ⊗ₕ «?» n) ≫ ∇ n := by rw [h]
    _ = 𝟙 n := «∇_unit» n

/-- The CUP `? ; Δ : I ⟶ n ⊗ n` — in `Rel`, `• ↦ (x,x)` for every `x`.  The compact-closed
    structure the Frobenius equations induce (functorialSemanticsForRelationalTheories.pdf p. 19). -/
def cup (n : Word O) : (𝕀 : Word O) ⟶ n ⊗ n := «?» n ≫ Δ n

/-- The CAP `∇ ; ! : n ⊗ n ⟶ I` — in `Rel`, `(x,y) ↦ •` exactly when `x = y`. -/
def cap (n : Word O) : n ⊗ n ⟶ (𝕀 : Word O) := ∇ n ≫ «!» n

/-- The SNAKE (yanking) equation: a wire bent down by a cup and back up by a cap is straight.
    This is where the Frobenius equation (41) earns its place — the two middle factors are
    literally the left-hand side of `frob_left`, which collapses them to `∇;Δ`, and then the monoid
    unit law (7) and the left counit law finish it. -/
theorem snake (n : Word O) : (𝟙 n ⊗ₕ cup n) ≫ (cap n ⊗ₕ 𝟙 n) = 𝟙 n := by
  have hcup : (𝟙 n ⊗ₕ cup n) = (𝟙 n ⊗ₕ «?» n) ≫ (𝟙 n ⊗ₕ Δ n) := by
    dsimp [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (cap n ⊗ₕ 𝟙 n) = (∇ n ⊗ₕ 𝟙 n) ≫ («!» n ⊗ₕ 𝟙 n) := by
    dsimp [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  calc (𝟙 n ⊗ₕ cup n) ≫ (cap n ⊗ₕ 𝟙 n)
      = ((𝟙 n ⊗ₕ «?» n) ≫ (𝟙 n ⊗ₕ Δ n)) ≫ (∇ n ⊗ₕ 𝟙 n) ≫ («!» n ⊗ₕ 𝟙 n) := by
        rw [hcup, hcap]
    _ = (𝟙 n ⊗ₕ «?» n) ≫ ((𝟙 n ⊗ₕ Δ n) ≫ (∇ n ⊗ₕ 𝟙 n)) ≫ («!» n ⊗ₕ 𝟙 n) := by
        simp only [Cat.assoc]
    _ = (𝟙 n ⊗ₕ «?» n) ≫ (∇ n ≫ Δ n) ≫ («!» n ⊗ₕ 𝟙 n) := by rw [frob_left]
    _ = ((𝟙 n ⊗ₕ «?» n) ≫ ∇ n) ≫ Δ n ≫ («!» n ⊗ₕ 𝟙 n) := by simp only [Cat.assoc]
    _ = 𝟙 n ≫ 𝟙 n := by rw [«∇_unit», Δ_counit_left]
    _ = 𝟙 n := Cat.id_comp _

/-- The mirror snake, bending the other way.  Same shape as `snake` with `frob_right` in place of
    `frob_left` and the left/right unit laws exchanged. -/
theorem snake' (n : Word O) : (cup n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ cap n) = 𝟙 n := by
  have hcup : (cup n ⊗ₕ 𝟙 n) = («?» n ⊗ₕ 𝟙 n) ≫ (Δ n ⊗ₕ 𝟙 n) := by
    dsimp [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (𝟙 n ⊗ₕ cap n) = (𝟙 n ⊗ₕ ∇ n) ≫ (𝟙 n ⊗ₕ «!» n) := by
    dsimp [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  calc (cup n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ cap n)
      = ((«?» n ⊗ₕ 𝟙 n) ≫ (Δ n ⊗ₕ 𝟙 n)) ≫ (𝟙 n ⊗ₕ ∇ n) ≫ (𝟙 n ⊗ₕ «!» n) := by
        rw [hcup, hcap]
    _ = («?» n ⊗ₕ 𝟙 n) ≫ ((Δ n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ ∇ n)) ≫ (𝟙 n ⊗ₕ «!» n) := by
        simp only [Cat.assoc]
    _ = («?» n ⊗ₕ 𝟙 n) ≫ (∇ n ≫ Δ n) ≫ (𝟙 n ⊗ₕ «!» n) := by rw [frob_right]
    _ = ((«?» n ⊗ₕ 𝟙 n) ≫ ∇ n) ≫ Δ n ≫ (𝟙 n ⊗ₕ «!» n) := by simp only [Cat.assoc]
    _ = 𝟙 n ≫ 𝟙 n := by rw [«∇_unit_left», Δ_counit]
    _ = 𝟙 n := Cat.id_comp _

/-- UNBEND: straighten `S : b ⟶ a` into its `I`-valued form `(𝟙_a ⊗ S);cap_a : a ⊗ b ⟶ I`.  This
    is the right-hand picture of the `†` notation on functorialSemanticsForRelationalTheories.pdf
    p. 19, read as an operation rather than as a definition. -/
def unbend {a b : Word O} (S : b ⟶ a) : a ⊗ b ⟶ (𝕀 : Word O) := (𝟙 a ⊗ₕ S) ≫ cap a

/-- BEND: the inverse operation, wrapping an `I`-valued `k : a ⊗ b ⟶ I` around a cup to get
    `b ⟶ a`.  `bend` and `unbend` are mutually inverse (`bend_unbend`, `unbend_bend`); that
    bijection is what makes the converse well behaved, and it is the "snake lemma" the paper
    appeals to for Lemma 4.2. -/
def bend {a b : Word O} (k : a ⊗ b ⟶ (𝕀 : Word O)) : b ⟶ a :=
  (cup a ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ k)

/-- The CONVERSE `R°`, by bending both of `R`'s wires around
    (functorialSemanticsForRelationalTheories.pdf p. 19, "`R†` is just the opposite relation").
    In `Rel` this reads `y ↦ x` exactly when `x R y`.

    ONE SYMBOL: `R°`, the book's.  The paper writes this same operation `R†` and reserves `(−)°` for
    the colour swap of its §7 — but §7 is a worked example in OTHER models, as the paper says itself:
    only the black fragment `⊤, ∩, (−)†, ; , id` coincides with the calculus of relations there,
    "`⊥` is not the empty relation and `>` is not the union".  Nothing in this repo formalises it.
    Everything here is `Rel(Set)`, where `†` and `°` name the one operation, so there is no clash to
    protect against and the reader is never asked to match two symbols. -/
def conv {a b : Word O} (R : a ⟶ b) : b ⟶ a := bend ((R ⊗ₕ 𝟙 b) ≫ cap b)

/-- `𝟙° = 𝟙`, which is exactly the mirror snake once `𝟙 ⊗ 𝟙` is collapsed. -/
theorem conv_id (a : Word O) : conv (𝟙 a) = 𝟙 a := by
  dsimp [conv, bend]
  rw [SymMonCat.tensHom_id, Cat.id_comp]
  exact snake' a

/-- The converse is monotone: it is built only from `≫` and `⊗`, both of which are. -/
theorem conv_mono {a b : Word O} {R S : a ⟶ b} (h : R ≤ S) : (conv R) ≤ (conv S) := by
  dsimp [conv, bend]
  refine OrderedCat.comp_mono (OrderedCat.«≤_refl» _) ?_
  exact SymMonCat.tensHom_mono (OrderedCat.«≤_refl» _)
    (OrderedCat.comp_mono (SymMonCat.tensHom_mono h (OrderedCat.«≤_refl» _))
      (OrderedCat.«≤_refl» _))

section Bending

open SymMonCat

/-- The cap is symmetric: `γ;cap = cap`.  Immediate from commutativity (6) of the merge, and the
    reason the two ways of capping a pair of `a`-wires agree. -/
theorem swap_cap (n : Word O) : swap n n ≫ cap n = cap n := by
  dsimp [cap]; rw [← Cat.assoc, «∇_comm»]

/-- The cup is symmetric: `cup;γ = cup`, dual to `swap_cap`, from cocommutativity (9). -/
theorem cup_swap (n : Word O) : cup n ≫ swap n n = cup n := by
  dsimp [cup]; rw [Cat.assoc, Δ_comm]

/-- `bend` undoes `unbend`.  Distribute `𝟙_a ⊗ −` over the composite, fuse the cup with `S` into
    `cup ⊗ S`, and the strict left unit pulls `S` out to the front — what is left is `snake'`.
    In the non-strict tower this proof also had to push a re-bracketing past `(𝟙 ⊗ 𝟙) ⊗ S` with
    `tensAssoc_nat` and pull `S` out with `lunitInv_nat`. -/
theorem bend_unbend {a b : Word O} (S : b ⟶ a) : bend (unbend S) = S := by
  have hsplit : (𝟙 a ⊗ₕ ((𝟙 a ⊗ₕ S) ≫ cap a))
      = (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap a) := by
    rw [← tensHom_comp, Cat.id_comp]
  have hfuse : (cup a ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S)) = S ≫ (cup a ⊗ₕ 𝟙 a) := by
    calc (cup a ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S))
        = (cup a ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ 𝟙 a) ⊗ₕ S) := by rw [← tensHom_assoc]
      _ = (cup a ⊗ₕ 𝟙 b) ≫ (𝟙 (a ⊗ a) ⊗ₕ S) := by rw [tensHom_id]
      _ = (cup a ⊗ₕ S) := tensHom_split _ _
      _ = (𝟙 (𝕀 : Word O) ⊗ₕ S) ≫ (cup a ⊗ₕ 𝟙 a) := (tensHom_split' _ _).symm
      _ = S ≫ (cup a ⊗ₕ 𝟙 a) := by rw [tensHom_lunit]
  calc bend (unbend S)
      = (cup a ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap a) := by
        dsimp only [bend, unbend]; rw [hsplit]
    _ = ((cup a ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ S))) ≫ (𝟙 a ⊗ₕ cap a) := (Cat.assoc _ _ _).symm
    _ = (S ≫ (cup a ⊗ₕ 𝟙 a)) ≫ (𝟙 a ⊗ₕ cap a) := by rw [hfuse]
    _ = S ≫ (cup a ⊗ₕ 𝟙 a) ≫ (𝟙 a ⊗ₕ cap a) := Cat.assoc _ _ _
    _ = S ≫ 𝟙 a := by rw [snake']
    _ = S := Cat.comp_id _

/-- `unbend` undoes `bend` — the snake with a PASSENGER wire.  In the non-strict tower this is the
    direction that needs all three of Kelly's coherence lemmas, because the cap creates a unit
    object next to the untouched `b` strand and `b` has to ride past it; with `λ = ρ = 𝟙` there is
    no unit object to ride past, and the proof is `snake` tensored with `𝟙 b`. -/
theorem unbend_bend {a b : Word O} (k : a ⊗ b ⟶ (𝕀 : Word O)) : unbend (bend k) = k := by
  -- (1) `𝟙_a ⊗ −` distributes over `bend k`, and re-brackets onto the `b` strand.
  -- `← tensHom_comp` can only FUSE two factors that split the word the same way, so the
  -- distribution has to happen before the re-bracketing, not in one `rw` chain with it.
  have hdistrib : (𝟙 a ⊗ₕ bend k)
      = ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (𝟙 (a ⊗ a) ⊗ₕ k) := by
    have h1 : (𝟙 a ⊗ₕ bend k) = (𝟙 a ⊗ₕ (cup a ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ (𝟙 a ⊗ₕ k)) := by
      dsimp only [bend]; rw [← tensHom_comp, Cat.id_comp]
    rw [h1, ← tensHom_assoc, ← tensHom_assoc, tensHom_id]
  -- (2) the tail: `k` slides out to the far right, leaving a cap.
  have htail : (𝟙 (a ⊗ a) ⊗ₕ k) ≫ cap a = ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ k := by
    calc (𝟙 (a ⊗ a) ⊗ₕ k) ≫ cap a
        = (𝟙 (a ⊗ a) ⊗ₕ k) ≫ (cap a ⊗ₕ 𝟙 (𝕀 : Word O)) := by rw [tensHom_runit]
      _ = (cap a ⊗ₕ k) := tensHom_split' _ _
      _ = (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ (𝟙 (𝕀 : Word O) ⊗ₕ k) := (tensHom_split _ _).symm
      _ = (cap a ⊗ₕ 𝟙 (a ⊗ b)) ≫ k := by rw [tensHom_lunit]
      _ = (cap a ⊗ₕ (𝟙 a ⊗ₕ 𝟙 b)) ≫ k := by rw [tensHom_id]
      _ = ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ k := by rw [tensHom_assoc]
  calc unbend (bend k)
      = (((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (𝟙 (a ⊗ a) ⊗ₕ k)) ≫ cap a := by
        dsimp only [unbend]; rw [hdistrib]
    _ = ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ (𝟙 (a ⊗ a) ⊗ₕ k) ≫ cap a := Cat.assoc _ _ _
    _ = ((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ k := by rw [htail]
    _ = (((𝟙 a ⊗ₕ cup a) ⊗ₕ 𝟙 b) ≫ ((cap a ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b)) ≫ k := (Cat.assoc _ _ _).symm
    _ = (((𝟙 a ⊗ₕ cup a) ≫ (cap a ⊗ₕ 𝟙 a)) ⊗ₕ (𝟙 b ≫ 𝟙 b)) ≫ k := by rw [← tensHom_comp]
    _ = (𝟙 a ⊗ₕ 𝟙 b) ≫ k := by rw [snake, Cat.id_comp]
    _ = 𝟙 (a ⊗ b) ≫ k := by rw [tensHom_id]
    _ = k := Cat.id_comp _

/-- SLIDING a box around the cap: `(𝟙_a ⊗ R°);cap_a = (R ⊗ 𝟙_b);cap_b`.  This is `unbend_bend`
    read at `R`'s own unbending — `R°` is by definition the bending of `(R ⊗ 𝟙);cap`, so straightening
    it again returns what we started from.  Every converse law below is one application of this. -/
theorem conv_slide {a b : Word O} (R : a ⟶ b) :
    (𝟙 a ⊗ₕ conv R) ≫ cap a = (R ⊗ₕ 𝟙 b) ≫ cap b := unbend_bend _

/-- Capping a box on the left is capping it on the right, past a symmetry — the cap does not care
    which strand the box sits on (`swap_cap`). -/
theorem tens_cap_swap {a b : Word O} (S : b ⟶ a) :
    (S ⊗ₕ 𝟙 a) ≫ cap a = swap b a ≫ (𝟙 a ⊗ₕ S) ≫ cap a := by
  calc (S ⊗ₕ 𝟙 a) ≫ cap a
      = (S ⊗ₕ 𝟙 a) ≫ swap a a ≫ cap a := by rw [swap_cap]
    _ = ((S ⊗ₕ 𝟙 a) ≫ swap a a) ≫ cap a := by simp only [Cat.assoc]
    _ = (swap b a ≫ (𝟙 a ⊗ₕ S)) ≫ cap a := by rw [swap_nat]
    _ = swap b a ≫ (𝟙 a ⊗ₕ S) ≫ cap a := by simp only [Cat.assoc]

/-- UNIQUENESS of the converse: an arrow that unbends to `(R ⊗ 𝟙);cap` IS `R°`.  `bend` inverts
    `unbend` (`bend_unbend`), so `unbend` is injective — this is that injectivity, packaged. -/
theorem conv_unique {a b : Word O} {R : a ⟶ b} {S : b ⟶ a}
    (h : (𝟙 a ⊗ₕ S) ≫ cap a = (R ⊗ₕ 𝟙 b) ≫ cap b) : S = conv R := by
  calc S = bend (unbend S) := (bend_unbend S).symm
    _ = bend ((R ⊗ₕ 𝟙 b) ≫ cap b) := by dsimp only [unbend]; rw [h]
    _ = conv R := rfl

/-- INVOLUTIVITY, `R°° = R` — Freyd's `recip_recip` (§2.11).  By uniqueness it is enough to unbend
    `R` itself and recognise `R°`'s unbending, which `tens_cap_swap` supplies once the two symmetries
    cancel. -/
theorem conv_conv {a b : Word O} (R : a ⟶ b) : conv (conv R) = R := by
  refine (conv_unique ?_).symm
  calc (𝟙 b ⊗ₕ R) ≫ cap b
      = (swap b a ≫ swap a b) ≫ (𝟙 b ⊗ₕ R) ≫ cap b := by rw [swap_swap, Cat.id_comp]
    _ = swap b a ≫ swap a b ≫ (𝟙 b ⊗ₕ R) ≫ cap b := by simp only [Cat.assoc]
    _ = swap b a ≫ (R ⊗ₕ 𝟙 b) ≫ cap b := by rw [← tens_cap_swap]
    _ = swap b a ≫ (𝟙 a ⊗ₕ conv R) ≫ cap a := by rw [conv_slide]
    _ = (conv R ⊗ₕ 𝟙 a) ≫ cap a := (tens_cap_swap (conv R)).symm

/-- CONTRAVARIANT FUNCTORIALITY, `(R;S)° = S°;R°` — Lemma 4.2 (ii)
    (functorialSemanticsForRelationalTheories.pdf p. 19) and Freyd's `recip_comp` (§2.11).  Unbend
    `S°;R°` one factor at a time: `conv_slide` turns the inner `R°` into `R`, `tensHom_split` walks
    `S°` across to the other strand, and a second `conv_slide` turns it into `S`. -/
theorem conv_comp {a b c : Word O} (R : a ⟶ b) (S : b ⟶ c) :
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

  The three results below are everything the modular law needs.  `«∇_of_cap»` is the only Frobenius
  computation in the group: it says the merge can be rebuilt from a copy and a cap.  `«cap_tens_∇»`
  is that fact with a box riding on the bent strand, and `«∇_slide_conv»` is the modular law with
  its two outer factors stripped off — the step where the lax inequation (42) duplicates `S`. -/

/-- The MERGE rebuilt from a copy and a cap: `(Δ ⊗ 𝟙);(𝟙 ⊗ cap) = ∇`.  Unfold `cap = ∇;!` and
    the two middle factors become the left-hand side of `frob_right`, collapsing to `∇;Δ`; the
    counit law (10) then eats the `Δ`.  This single equation is the whole Frobenius content of the
    modular law. -/
theorem «∇_of_cap» (n : Word O) : (Δ n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ cap n) = ∇ n := by
  have hcap : (𝟙 n ⊗ₕ cap n) = (𝟙 n ⊗ₕ ∇ n) ≫ (𝟙 n ⊗ₕ «!» n) := by
    dsimp [cap]; rw [← tensHom_comp, Cat.id_comp]
  calc (Δ n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ cap n)
      = ((Δ n ⊗ₕ 𝟙 n) ≫ (𝟙 n ⊗ₕ ∇ n)) ≫ (𝟙 n ⊗ₕ «!» n) := by
        rw [hcap]; simp only [Cat.assoc]
    _ = (∇ n ≫ Δ n) ≫ (𝟙 n ⊗ₕ «!» n) := by rw [frob_right]
    _ = ∇ n ≫ Δ n ≫ (𝟙 n ⊗ₕ «!» n) := Cat.assoc _ _ _
    _ = ∇ n ≫ 𝟙 n := by rw [Δ_counit]
    _ = ∇ n := Cat.comp_id _

/-- `«∇_of_cap»` with a box on the bent strand: `(Δ ⊗ 𝟙);(𝟙 ⊗ ((𝟙 ⊗ T);cap)) = (𝟙 ⊗ T);∇`.
    Strict associativity and the two splittings pull `T` out to the front, after which the box-free
    `«∇_of_cap»` closes it. -/
theorem «cap_tens_∇» {b c : Word O} (T : c ⟶ b) :
    (Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ T) ≫ cap b)) = (𝟙 b ⊗ₕ T) ≫ ∇ b := by
  have hsplit : (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ T) ≫ cap b))
      = (𝟙 b ⊗ₕ (𝟙 b ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ cap b) := by rw [← tensHom_comp, Cat.id_comp]
  calc (Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ T) ≫ cap b))
      = ((Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ (𝟙 b ⊗ₕ T))) ≫ (𝟙 b ⊗ₕ cap b) := by
        rw [hsplit]; simp only [Cat.assoc]
    _ = ((Δ b ⊗ₕ 𝟙 c) ≫ ((𝟙 b ⊗ₕ 𝟙 b) ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ cap b) := by rw [← tensHom_assoc]
    _ = ((Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 (b ⊗ b) ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ cap b) := by rw [tensHom_id]
    _ = (Δ b ⊗ₕ T) ≫ (𝟙 b ⊗ₕ cap b) := by rw [tensHom_split]
    _ = ((𝟙 b ⊗ₕ T) ≫ (Δ b ⊗ₕ 𝟙 b)) ≫ (𝟙 b ⊗ₕ cap b) := by rw [tensHom_split']
    _ = (𝟙 b ⊗ₕ T) ≫ (Δ b ⊗ₕ 𝟙 b) ≫ (𝟙 b ⊗ₕ cap b) := Cat.assoc _ _ _
    _ = (𝟙 b ⊗ₕ T) ≫ ∇ b := by rw [«∇_of_cap»]

/-- THE HEART OF THE MODULAR LAW: `(S ⊗ 𝟙);∇ ≤ (𝟙 ⊗ S°);∇;S`.

    Read relationally, the left-hand side sends `(y, z)` to `z` when `S y z`, and the right-hand
    side sends it to any `z'` with `S y z`; so `S` occurs once on the left and twice on the right.
    That is the tell: the lax copy inequation (42) — the ONLY place a box may be duplicated — has to
    be the inequality step, and it is.  `«∇_of_cap»` puts the left-hand side into the shape
    `(S;Δ) ⊗ 𝟙` that (42) applies to, and `conv_slide` turns the surviving duplicate into `S°`. -/
theorem «∇_slide_conv» {b c : Word O} (S : b ⟶ c) :
    ((S ⊗ₕ 𝟙 c) ≫ ∇ c) ≤ ((𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S) := by
  have hfacL : ((S ≫ Δ c) ⊗ₕ 𝟙 c) = (S ⊗ₕ 𝟙 c) ≫ (Δ c ⊗ₕ 𝟙 c) := by
    rw [← tensHom_comp, Cat.comp_id]
  have hfacR : ((Δ b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) = (Δ b ⊗ₕ 𝟙 c) ≫ ((S ⊗ₕ S) ⊗ₕ 𝟙 c) := by
    rw [← tensHom_comp, Cat.comp_id]
  have hL : ((S ≫ Δ c) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c) = (S ⊗ₕ 𝟙 c) ≫ ∇ c := by
    calc ((S ≫ Δ c) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c)
        = ((S ⊗ₕ 𝟙 c) ≫ (Δ c ⊗ₕ 𝟙 c)) ≫ (𝟙 c ⊗ₕ cap c) := by rw [hfacL]
      _ = (S ⊗ₕ 𝟙 c) ≫ (Δ c ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c) := Cat.assoc _ _ _
      _ = (S ⊗ₕ 𝟙 c) ≫ ∇ c := by rw [«∇_of_cap»]
  have hR : ((Δ b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c) = (𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S := by
    have hslide : ((S ⊗ₕ S) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c)
        = (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b)) ≫ (S ⊗ₕ 𝟙 (𝕀 : Word O)) := by
      calc ((S ⊗ₕ S) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c)
          = (S ⊗ₕ (S ⊗ₕ 𝟙 c)) ≫ (𝟙 c ⊗ₕ cap c) := by rw [tensHom_assoc]
        _ = (S ⊗ₕ ((S ⊗ₕ 𝟙 c) ≫ cap c)) := by rw [← tensHom_comp, Cat.comp_id]
        _ = (S ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b)) := by rw [conv_slide]
        _ = (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b)) ≫ (S ⊗ₕ 𝟙 (𝕀 : Word O)) := by
              rw [tensHom_split']
    calc ((Δ b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c)
        = ((Δ b ⊗ₕ 𝟙 c) ≫ ((S ⊗ₕ S) ⊗ₕ 𝟙 c)) ≫ (𝟙 c ⊗ₕ cap c) := by rw [hfacR]
      _ = (Δ b ⊗ₕ 𝟙 c) ≫ ((S ⊗ₕ S) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c) := Cat.assoc _ _ _
      _ = (Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b)) ≫ (S ⊗ₕ 𝟙 (𝕀 : Word O)) := by
            rw [hslide]
      _ = (Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b)) ≫ S := by rw [tensHom_runit]
      _ = ((Δ b ⊗ₕ 𝟙 c) ≫ (𝟙 b ⊗ₕ ((𝟙 b ⊗ₕ conv S) ≫ cap b))) ≫ S := (Cat.assoc _ _ _).symm
      _ = ((𝟙 b ⊗ₕ conv S) ≫ ∇ b) ≫ S := by rw [«cap_tens_∇»]
      _ = (𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S := Cat.assoc _ _ _
  -- Spelled as a THREE-LINK `calc` rather than `rw [← hL, ← hR]; exact …`, so that the argument sits
  -- in the proof TERM where `diag-export --proof` can draw it: reshape, the one inequality, reshape
  -- back.  `hL` and `hR` are the reshaping and are stated at `=`, so the drawn chain shows exactly
  -- one `≤`, which is `lax_Δ` — the whole of the mathematics.
  calc (S ⊗ₕ 𝟙 c) ≫ ∇ c
      = ((S ≫ Δ c) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c) := hL.symm
    _ ≤ ((Δ b ≫ (S ⊗ₕ S)) ⊗ₕ 𝟙 c) ≫ (𝟙 c ⊗ₕ cap c) :=
        OrderedCat.comp_mono (tensHom_mono (lax_Δ S) (OrderedCat.«≤_refl» _))
          (OrderedCat.«≤_refl» _)
    _ = (𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S := hR

end Bending

end CartBicat

end Freyd.Diag
