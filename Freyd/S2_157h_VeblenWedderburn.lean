/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 — the PAYOFF (p. 15):
  a concrete NON-DESARGUESIAN projective plane, hence a finitely-presented one-object
  allegory violating the Desargues Horn sentence that `Rel(S)` satisfies.

  The plane is the translation plane over the Veblen–Wedderburn RIGHT NEAR-FIELD `J₉`
  of order 9 (Veblen–Wedderburn 1907; the Hall plane of order 9).  `J₉` is `GF(9)`
  with its addition, but multiplication twisted through the Frobenius (Dickson's
  construction): `x ∘ y = x·y` when `y` is a square in `GF(9)`, `x³·y` when not.
  All near-field laws hold EXCEPT left distributivity — and that failure propagates
  to a concrete ten-point Desargues violation in the plane built from it.

  Formalised here:
  · `VW.add`/`VW.neg`/`VW.mul` — `J₉` as `Fin 9` (element `a + 3b` codes `a + b·i`,
    `i² = -1` in `GF(9) = 𝔽₃[i]`) with EXPLICIT 9×9 operation tables; the near-field
    laws (abelian group `+`, two-sided unit, associativity of `∘`, RIGHT
    distributivity, no zero divisors, left/right solvability) all by kernel `decide`,
    plus `not_left_distrib` — the twist is genuine.
  · `VW : ProjectivePlane` — points `(J₉ × J₉) ⊕ J₉ ⊕ Unit` (affine, slope,
    vertical direction `∞`), lines `(J₉ × J₉) ⊕ J₉ ⊕ Unit` (`y = x∘m + b` coded
    `(m,b)`, verticals `x = c`, the line at infinity); the three plane axioms by
    symbolic case analysis over the near-field laws.  `VW_interesting`.
  · `VW_not_desargues` — THE CORE: a concrete violating ten-point configuration
    (found by random search over the coded coordinates, verified here by `decide`).
  · `VW_not_desarguesHorn` — via §2.157g `desarguesND_iff_desarguesHorn`: the
    associated one-object allegory `LMonObj (PElem VW)` violates the Desargues
    Horn sentence.
-/
module

public import Freyd.S2_157g_ConverseHeadline

namespace Freyd.Alg

namespace VW

/-! ## §2.157h  The right near-field `J₉` (Veblen–Wedderburn 1907)

  Elements are `Fin 9`; the index `a + 3b` (`a, b ∈ {0,1,2}`) codes `a + b·i ∈ GF(9)`,
  where `i² = -1` (so `0..2 = 0,1,2`, `3 = i`, `4 = 1+i`, `5 = 2+i`, `6 = 2i`,
  `7 = 1+2i`, `8 = 2+2i`).  The nonzero squares of `GF(9)` are `{1, 2, i, 2i}` =
  indices `{1, 2, 3, 6}`; the Frobenius `x ↦ x³` is conjugation `a + bi ↦ a - bi`. -/

/-- `J₉`, the carrier: `Fin 9`. -/
@[expose] public abbrev J9 := Fin 9

/-- Table row: a function `J9 → J9` from nine literals. -/
@[expose] public def row (a0 a1 a2 a3 a4 a5 a6 a7 a8 : J9) : J9 → J9
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4
  | 5 => a5 | 6 => a6 | 7 => a7 | 8 => a8

/-- ADDITION: `GF(9)` addition, componentwise mod 3 in the coding `a + 3b ↔ a + b·i`. -/
@[expose] public def add : J9 → J9 → J9
  | 0 => row 0 1 2 3 4 5 6 7 8
  | 1 => row 1 2 0 4 5 3 7 8 6
  | 2 => row 2 0 1 5 3 4 8 6 7
  | 3 => row 3 4 5 6 7 8 0 1 2
  | 4 => row 4 5 3 7 8 6 1 2 0
  | 5 => row 5 3 4 8 6 7 2 0 1
  | 6 => row 6 7 8 0 1 2 3 4 5
  | 7 => row 7 8 6 1 2 0 4 5 3
  | 8 => row 8 6 7 2 0 1 5 3 4

/-- Additive INVERSE: `-(a + bi) = (3-a) + (3-b)i`. -/
@[expose] public def neg : J9 → J9 := row 0 2 1 6 8 7 3 5 4

/-- Subtraction, as `x + (-y)`. -/
@[expose] public def sub (x y : J9) : J9 := add x (neg y)

/-- MULTIPLICATION `x ∘ y`, the Dickson twist of `GF(9)` multiplication:
    `x·y` when `y` is a square in `GF(9)` (indices `{0,1,2,3,6}`), `x³·y` when not
    (`x³` = conjugation).  Tabulated directly; e.g. row 4 (`x = 1+i`):
    `(1+i)∘(1+i) = (1-i)(1+i) = 2` (twisted), `(1+i)∘i = (1+i)i = -1+i = 2+i = 5`. -/
@[expose] public def mul : J9 → J9 → J9
  | 0 => row 0 0 0 0 0 0 0 0 0
  | 1 => row 0 1 2 3 4 5 6 7 8
  | 2 => row 0 2 1 6 8 7 3 5 4
  | 3 => row 0 3 6 2 7 4 1 8 5
  | 4 => row 0 4 8 5 2 6 7 3 1
  | 5 => row 0 5 7 8 3 2 4 1 6
  | 6 => row 0 6 3 1 5 8 2 4 7
  | 7 => row 0 7 5 4 6 1 8 2 3
  | 8 => row 0 8 4 7 1 3 5 6 2

/-! ### The near-field laws, each by kernel `decide` (9³ = 729 table lookups max) -/

/-- `(J₉, +)` is commutative. -/
theorem add_comm : ∀ x y : J9, add x y = add y x := by decide

/-- `(J₉, +)` is associative. -/
theorem add_assoc : ∀ x y z : J9, add (add x y) z = add x (add y z) := by decide

/-- `0` is the additive unit. -/
theorem zero_add : ∀ x : J9, add 0 x = x := by decide

theorem add_zero : ∀ x : J9, add x 0 = x := by decide

/-- Additive inverses: `(J₉, +, 0, neg)` is an abelian group. -/
theorem add_neg : ∀ x : J9, add x (neg x) = 0 := by decide

/-- `1` is a two-sided unit for `∘`. -/
theorem one_mul : ∀ x : J9, mul 1 x = x := by decide

theorem mul_one : ∀ x : J9, mul x 1 = x := by decide

/-- `∘` is ASSOCIATIVE (on all of `J₉`, zero included). -/
theorem mul_assoc : ∀ x y z : J9, mul (mul x y) z = mul x (mul y z) := by decide

/-- RIGHT distributivity `(a + b) ∘ c = a∘c + b∘c` — the near-field's one
    distributive law (each `· ∘ c` is `·(c)` or `(·)³(c)`, both additive). -/
theorem add_mul : ∀ a b c : J9, mul (add a b) c = add (mul a c) (mul b c) := by decide

theorem zero_mul : ∀ x : J9, mul 0 x = 0 := by decide

theorem mul_zero : ∀ x : J9, mul x 0 = 0 := by decide

/-- No zero divisors. -/
theorem no_zero_divisors : ∀ x y : J9, mul x y = 0 → x = 0 ∨ y = 0 := by decide

/-- LEFT solvability, uniquely: `a ≠ 0 → ∃! x, a ∘ x = b` (spelled out; `∃!` is
    not in Lean core). -/
theorem left_solvable : ∀ a b : J9, a ≠ 0 →
    ∃ x, mul a x = b ∧ ∀ y, mul a y = b → y = x := by decide

/-- RIGHT solvability, uniquely: `a ≠ 0 → ∃! y, y ∘ a = b`. -/
theorem right_solvable : ∀ a b : J9, a ≠ 0 →
    ∃ y, mul y a = b ∧ ∀ z, mul z a = b → z = y := by decide

/-- Left cancellation (the uniqueness in `left_solvable`, in applicable form). -/
theorem mul_left_cancel : ∀ a x y : J9, a ≠ 0 → mul a x = mul a y → x = y := by decide

/-- Right cancellation. -/
theorem mul_right_cancel : ∀ a x y : J9, a ≠ 0 → mul x a = mul y a → x = y := by decide

/-- LEFT distributivity FAILS: `J₉` is a genuine near-field, not a field —
    `(1+i) ∘ (1 + i) ≠ (1+i)∘1 + (1+i)∘i` (indices: `4∘(1+3) ≠ 4∘1 + 4∘3`). -/
theorem not_left_distrib : ¬ ∀ a b c : J9, mul a (add b c) = add (mul a b) (mul a c) :=
  fun h => absurd (h 4 1 3) (by decide)

/-! ## §2.157h  The Veblen–Wedderburn plane over `J₉`

  The projective completion of the affine translation plane coordinatised by `J₉`:
  · POINTS — affine `(x, y)`; one ideal point per slope `m`; one ideal point `∞`
    for the vertical direction.
  · LINES — `y = x∘m + b`, coded `(m, b)` (carrying the ideal point `m`);
    verticals `x = c` (carrying `∞`); the line at infinity (all ideal points). -/

/-- Points: affine `(x, y)` ⊕ slope `m` ⊕ `∞`. -/
@[expose] public abbrev Point9 : Type := (J9 × J9) ⊕ (J9 ⊕ Unit)

/-- Lines: `y = x∘m + b` coded `(m, b)` ⊕ vertical `x = c` ⊕ the line at infinity. -/
@[expose] public abbrev Line9 : Type := (J9 × J9) ⊕ (J9 ⊕ Unit)

/-- The affine point `(x, y)`. -/
@[expose] public abbrev aff (x y : J9) : Point9 := Sum.inl (x, y)
/-- The ideal point of slope `m`. -/
@[expose] public abbrev slopePt (m : J9) : Point9 := Sum.inr (Sum.inl m)
/-- The ideal point `∞` of the vertical direction. -/
@[expose] public abbrev infPt : Point9 := Sum.inr (Sum.inr ())
/-- The line `y = x∘m + b`. -/
@[expose] public abbrev lineMB (m b : J9) : Line9 := Sum.inl (m, b)
/-- The vertical line `x = c`. -/
@[expose] public abbrev vert (c : J9) : Line9 := Sum.inr (Sum.inl c)
/-- The line at infinity. -/
@[expose] public abbrev infLine : Line9 := Sum.inr (Sum.inr ())

/-- INCIDENCE.  Affine `(x,y) ∈ (m,b)` iff `y = x∘m + b`; `(x,y) ∈ [x = c]` iff
    `x = c`; the ideal point `m` lies on every line of slope `m` and on the line
    at infinity; `∞` lies on the verticals and the line at infinity. -/
@[expose] public def incid : Point9 → Line9 → Prop
  | .inl (x, y), .inl (m, b) => y = add (mul x m) b
  | .inl (x, _), .inr (.inl c) => x = c
  | .inl _,      .inr (.inr _) => False
  | .inr (.inl s), .inl (m, _) => s = m
  | .inr (.inl _), .inr (.inl _) => False
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inl _ => False
  | .inr (.inr _), .inr (.inl _) => True
  | .inr (.inr _), .inr (.inr _) => True

@[expose] public instance : ∀ (p : Point9) (l : Line9), Decidable (incid p l)
  | .inl (_, _), .inl (_, _) => inferInstanceAs (Decidable (_ = _))
  | .inl (_, _), .inr (.inl _) => inferInstanceAs (Decidable (_ = _))
  | .inl _,      .inr (.inr _) => inferInstanceAs (Decidable False)
  | .inr (.inl _), .inl (_, _) => inferInstanceAs (Decidable (_ = _))
  | .inr (.inl _), .inr (.inl _) => inferInstanceAs (Decidable False)
  | .inr (.inl _), .inr (.inr _) => inferInstanceAs (Decidable True)
  | .inr (.inr _), .inl _ => inferInstanceAs (Decidable False)
  | .inr (.inr _), .inr (.inl _) => inferInstanceAs (Decidable True)
  | .inr (.inr _), .inr (.inr _) => inferInstanceAs (Decidable True)

/-! ### The geometric solvability lemmas (kernel `decide`, ≤ 9⁴·9 lookups)

  Only RIGHT distributivity is available, so the two affine existence problems are
  genuinely one-sided:
  · JOIN of `(x₁,y₁)`, `(x₂,y₂)` with `x₁ ≠ x₂`: the slope `m` solves
    `(x₁ - x₂)∘m = y₁ - y₂` (left solvability); with `b := y₁ - x₁∘m` both
    incidences hold.
  · MEET of `(m₁,b₁)`, `(m₂,b₂)` with `m₁ ≠ m₂`: `x ↦ x∘m₁ - x∘m₂` is additive
    (RIGHT distributivity) with trivial kernel (left cancellation), hence bijective;
    solve `x∘m₁ - x∘m₂ = b₂ - b₁`. -/

/-- `v + (u - v) = u` — the additive rearrangement used to check incidences. -/
public theorem sub_add_cancel : ∀ u v : J9, add v (sub u v) = u := by decide

/-- JOIN solvability, packaged in incidence shape: for `x₁ ≠ x₂` there is a slope
    `m` putting `(x₂,y₂)` on the line through `(x₁,y₁)` of slope `m`. -/
public theorem join_slope_exists : ∀ x₁ y₁ x₂ y₂ : J9, x₁ ≠ x₂ →
    ∃ m, y₂ = add (mul x₂ m) (sub y₁ (mul x₁ m)) := by decide

/-- MEET solvability: two line codes of distinct slopes agree at some abscissa. -/
public theorem meet_mb_exists : ∀ m₁ b₁ m₂ b₂ : J9, m₁ ≠ m₂ →
    ∃ x, add (mul x m₁) b₁ = add (mul x m₂) b₂ := by decide

/-- Additive cancellation, for uniqueness of the `b`-code. -/
public theorem add_left_cancel : ∀ v b₁ b₂ : J9, add v b₁ = add v b₂ → b₁ = b₂ := by decide

/-- Cross-subtraction: `X₁ + b₁ = X₂ + b₂ → X₁ - X₂ = b₂ - b₁`. -/
public theorem cross_sub : ∀ X₁ b₁ X₂ b₂ : J9, add X₁ b₁ = add X₂ b₂ →
    sub X₁ X₂ = sub b₂ b₁ := by decide

/-- For `m₁ ≠ m₂` the map `x ↦ x∘m₁ - x∘m₂` is INJECTIVE — two lines of distinct
    slopes meet in at most one affine point. -/
public theorem slope_inj : ∀ m₁ m₂ x x' : J9, m₁ ≠ m₂ →
    sub (mul x m₁) (mul x m₂) = sub (mul x' m₁) (mul x' m₂) → x = x' := by decide

/-! ### The three projective-plane axioms -/

/-- AXIOM 1: any two points lie on a common line.  Affine–affine splits on
    `x₁ = x₂` (vertical) vs. `x₁ ≠ x₂` (`join_slope_exists`); a slope point rides
    every line of its slope; ideal points join along the line at infinity. -/
public theorem join_exists9 : ∀ x y : Point9, ∃ A : Line9, incid x A ∧ incid y A := by
  rintro (⟨x₁, y₁⟩ | s₁ | ⟨⟩) (⟨x₂, y₂⟩ | s₂ | ⟨⟩)
  · by_cases h : x₁ = x₂
    · exact ⟨vert x₁, rfl, h.symm⟩
    · obtain ⟨m, hm⟩ := join_slope_exists x₁ y₁ x₂ y₂ h
      exact ⟨lineMB m (sub y₁ (mul x₁ m)), (sub_add_cancel y₁ (mul x₁ m)).symm, hm⟩
  · exact ⟨lineMB s₂ (sub y₁ (mul x₁ s₂)), (sub_add_cancel y₁ (mul x₁ s₂)).symm, rfl⟩
  · exact ⟨vert x₁, rfl, trivial⟩
  · exact ⟨lineMB s₁ (sub y₂ (mul x₂ s₁)), rfl, (sub_add_cancel y₂ (mul x₂ s₁)).symm⟩
  · exact ⟨infLine, trivial, trivial⟩
  · exact ⟨infLine, trivial, trivial⟩
  · exact ⟨vert x₂, trivial, rfl⟩
  · exact ⟨infLine, trivial, trivial⟩
  · exact ⟨infLine, trivial, trivial⟩

/-- AXIOM 2: any two lines meet.  Same slope meets at the slope's ideal point;
    distinct slopes meet affinely (`meet_mb_exists`); a slope line meets a vertical
    at the obvious affine point; verticals and the line at infinity share `∞`. -/
public theorem meet_exists9 : ∀ A B : Line9, ∃ x : Point9, incid x A ∧ incid x B := by
  rintro (⟨m₁, b₁⟩ | c₁ | ⟨⟩) (⟨m₂, b₂⟩ | c₂ | ⟨⟩)
  · by_cases h : m₁ = m₂
    · exact ⟨slopePt m₁, rfl, h⟩
    · obtain ⟨x, hx⟩ := meet_mb_exists m₁ b₁ m₂ b₂ h
      exact ⟨aff x (add (mul x m₁) b₁), rfl, hx⟩
  · exact ⟨aff c₂ (add (mul c₂ m₁) b₁), rfl, rfl⟩
  · exact ⟨slopePt m₁, rfl, trivial⟩
  · exact ⟨aff c₁ (add (mul c₁ m₂) b₂), rfl, rfl⟩
  · exact ⟨infPt, trivial, trivial⟩
  · exact ⟨infPt, trivial, trivial⟩
  · exact ⟨slopePt m₂, trivial, rfl⟩
  · exact ⟨infPt, trivial, trivial⟩
  · exact ⟨infPt, trivial, trivial⟩

/-- AXIOM 3: two points on two common lines force equal points or equal lines.
    After the constructor split, all mixed-sort cases die on a `False` incidence or
    close by transitivity; the one substantive case — two affine points on two
    slope-coded lines — is `slope_inj` (distinct slopes meet in ≤ 1 affine point)
    plus `add_left_cancel` (same slope forces the same `b`-code). -/
public theorem unique9 : ∀ {x y : Point9} {A B : Line9},
    incid x A → incid x B → incid y A → incid y B → x = y ∨ A = B := by
  rintro (⟨x₁, y₁⟩ | s₁ | ⟨⟩) (⟨x₂, y₂⟩ | s₂ | ⟨⟩) (⟨m₁, b₁⟩ | c₁ | ⟨⟩)
    (⟨m₂, b₂⟩ | c₂ | ⟨⟩) hxA hxB hyA hyB <;>
    first
    | exact hxA.elim | exact hxB.elim | exact hyA.elim | exact hyB.elim
    | exact Or.inl rfl | exact Or.inr rfl
    | skip
  -- aff, aff on (m₁,b₁), (m₂,b₂): equal slopes force equal `b` (cancellation);
  -- distinct slopes meet in ≤ 1 affine point (`slope_inj` via `cross_sub`)
  · by_cases hm : m₁ = m₂
    · subst hm
      have hb : b₁ = b₂ := add_left_cancel _ _ _ (hxA.symm.trans hxB)
      subst hb; exact Or.inr rfl
    · have hx : x₁ = x₂ := slope_inj m₁ m₂ x₁ x₂ hm
        ((cross_sub _ _ _ _ (hxA.symm.trans hxB)).trans
          (cross_sub _ _ _ _ (hyA.symm.trans hyB)).symm)
      subst hx
      have hy : y₁ = y₂ := hxA.trans hyA.symm
      subst hy; exact Or.inl rfl
  -- aff, aff on (m₁,b₁), vert c₂: both abscissae are `c₂`
  · have hx : x₁ = x₂ := hxB.trans hyB.symm
    subst hx
    have hy : y₁ = y₂ := hxA.trans hyA.symm
    subst hy; exact Or.inl rfl
  -- aff, aff on vert c₁, (m₂,b₂)
  · have hx : x₁ = x₂ := hxA.trans hyA.symm
    subst hx
    have hy : y₁ = y₂ := hxB.trans hyB.symm
    subst hy; exact Or.inl rfl
  -- aff, aff on vert c₁, vert c₂: both verticals pass through `x₁`
  · have hc : c₁ = c₂ := hxA.symm.trans hxB
    subst hc; exact Or.inr rfl
  -- aff, slopePt s₂ on (m₁,b₁), (m₂,b₂): the ideal point forces `m₁ = m₂`
  · have hm : m₁ = m₂ := hyA.symm.trans hyB
    subst hm
    have hb : b₁ = b₂ := add_left_cancel _ _ _ (hxA.symm.trans hxB)
    subst hb; exact Or.inr rfl
  -- aff, ∞ on vert c₁, vert c₂
  · have hc : c₁ = c₂ := hxA.symm.trans hxB
    subst hc; exact Or.inr rfl
  -- slopePt s₁, aff on (m₁,b₁), (m₂,b₂)
  · have hm : m₁ = m₂ := hxA.symm.trans hxB
    subst hm
    have hb : b₁ = b₂ := add_left_cancel _ _ _ (hyA.symm.trans hyB)
    subst hb; exact Or.inr rfl
  -- slopePt, slopePt on (m₁,b₁), (m₂,b₂): both are the ideal point of `m₁`
  · have hs : s₁ = s₂ := hxA.trans hyA.symm
    subst hs; exact Or.inl rfl
  -- slopePt, slopePt on (m₁,b₁), infLine
  · have hs : s₁ = s₂ := hxA.trans hyA.symm
    subst hs; exact Or.inl rfl
  -- slopePt, slopePt on infLine, (m₂,b₂)
  · have hs : s₁ = s₂ := hxB.trans hyB.symm
    subst hs; exact Or.inl rfl
  -- ∞, aff on vert c₁, vert c₂
  · have hc : c₁ = c₂ := hyA.symm.trans hyB
    subst hc; exact Or.inr rfl

/-! ### Interestingness helpers -/

/-- The horizontal line `y = b` passes through `(x, b)`: `b = x∘0 + b`. -/
theorem incid_slope_zero : ∀ x y : J9, y = add (mul x 0) y := by decide

/-- The line of slope `1` through `(x, y)`: `y = x∘1 + (y - x)`. -/
theorem incid_slope_one : ∀ x y : J9, y = add (mul x 1) (sub y x) := by decide

end VW

/-- **THE VEBLEN–WEDDERBURN PLANE** (§2.157, the p. 15 payoff): the projective
    completion of the translation plane coordinatised by the right near-field `J₉`
    — the Hall plane of order 9.  91 points, 91 lines, 10 points a line.
    (`@[reducible]` so that `VW.Point`/`VW.incid` stay transparent to typeclass
    search — `decide` needs the `Decidable` instances through the projections.) -/
@[reducible, expose] public def VW : ProjectivePlane.{0} where
  Point := VW.Point9
  Line := VW.Line9
  incid := VW.incid
  join_exists := VW.join_exists9
  meet_exists := VW.meet_exists9
  unique := VW.unique9

/-- `VW` is an INTERESTING projective plane (§2.157): three distinct lines through
    every point, three distinct points on every line (each carries ten). -/
theorem VW_interesting : VW.Interesting := by
  constructor
  · rintro (⟨x, y⟩ | s | ⟨⟩)
    · -- affine `(x,y)`: the slope-0 and slope-1 lines through it, and its vertical
      exact ⟨VW.lineMB 0 y, VW.lineMB 1 (VW.sub y x), VW.vert x,
        by decide +revert, by decide +revert, by decide +revert,
        VW.incid_slope_zero x y, VW.incid_slope_one x y, rfl⟩
    · -- ideal point `s`: two lines of slope `s` and the line at infinity
      exact ⟨VW.lineMB s 0, VW.lineMB s 1, VW.infLine,
        by decide +revert, by decide +revert, by decide +revert,
        rfl, rfl, trivial⟩
    · -- `∞`: two verticals and the line at infinity
      exact ⟨VW.vert 0, VW.vert 1, VW.infLine,
        by decide, by decide, by decide, trivial, trivial, trivial⟩
  · rintro (⟨m, b⟩ | c | ⟨⟩)
    · -- line `(m,b)`: its points at abscissae 0 and 1, and its ideal point
      exact ⟨VW.aff 0 (VW.add (VW.mul 0 m) b), VW.aff 1 (VW.add (VW.mul 1 m) b),
        VW.slopePt m, by decide +revert, by decide +revert, by decide +revert,
        rfl, rfl, rfl⟩
    · -- vertical `x = c`: two affine points and `∞`
      exact ⟨VW.aff c 0, VW.aff c 1, VW.infPt,
        by decide +revert, by decide +revert, by decide +revert,
        rfl, rfl, trivial⟩
    · -- line at infinity: two ideal points and `∞`
      exact ⟨VW.slopePt 0, VW.slopePt 1, VW.infPt,
        by decide, by decide, by decide, trivial, trivial, trivial⟩

/-! ## §2.157h  VW is NOT Desarguesian

  The violating ten-point configuration (found by exhaustive search over the coded
  coordinates, verified below by `decide`; recall index `a + 3b` = `a + b·i`):

    centre `p = (5,4)`, perspective lines `y = x∘6 + 0`, `y = x∘0 + 4`, `y = x∘4 + 1`;
    triangle 1: `a₁ = ⟨slope 6⟩` (ideal!), `b₁ = (7,4)`, `c₁ = (8,2)`;
    triangle 2: `a₂ = (8,5)`,               `b₂ = (4,4)`, `c₂ = (6,3)`;
    sides: `a₁c₁ = (6,6)`, `a₂c₂ = (1,6)` meeting in `u = (0,6)`;
           `c₁b₁ = (7,5)`, `c₂b₂ = (5,7)` meeting in `v = (1,0)`;
           `a₁b₁ = (6,8)`, `a₂b₂ = (8,3)` meeting in `w = (5,0)`.

  The triangles are in perspective from `p`, all nine premises of `DesarguesND`
  hold — yet `u`, `v`, `w` are NOT colinear: the line through `u = (0,6)` and
  `v = (1,0)` is `y = x∘3 + 6`, and `w = (5,0)` misses it (`5∘3 + 6 = 8 + 6 = 5 ≠ 0`).
  Left distributivity fails in exactly the right place. -/

/-- The meets `u = (0,6)`, `v = (1,0)`, `w = (5,0)` of corresponding sides are NOT
    colinear: slope-coded lines force `b = 6`, `m = 3` from `u`, `v`, but then `w`
    misses; the abscissae `0, 1` rule out verticals; affine points miss infinity. -/
public theorem VW_uvw_not_colinear :
    ¬ VW.Colinear (VW.aff 0 6) (VW.aff 1 0) (VW.aff 5 0) := by
  rintro ⟨(⟨m, b⟩ | c | ⟨⟩), hu, hv, hw⟩
  · exact absurd ⟨hu, hv, hw⟩
      ((by decide : ∀ m b : VW.J9,
          ¬(6 = VW.add (VW.mul 0 m) b ∧ 0 = VW.add (VW.mul 1 m) b ∧
            0 = VW.add (VW.mul 5 m) b)) m b)
  · exact absurd (hu.trans hv.symm) (by decide)
  · exact hu.elim

/-- **§2.157 (p. 15 payoff), THE CORE: `VW` violates the theorem of Desargues** —
    the concrete configuration above satisfies all nine colinearity premises and all
    nine side conditions of the honest ten-point statement `DesarguesND`, but its
    side-meets `u`, `v`, `w` are not colinear. -/
public theorem VW_not_desargues : ¬ VW.DesarguesND := by
  intro h
  -- the six side-lines ARE the `lineThrough`s of the corresponding vertex pairs
  have e_ab1 : VW.lineMB 6 8 = VW.lineThrough (VW.slopePt 6) (VW.aff 7 4) :=
    ProjectivePlane.lineThrough_eq (P := VW) (x := VW.slopePt 6) (y := VW.aff 7 4)
      (A := VW.lineMB 6 8) (by decide) (by decide) (by decide)
  have e_ab2 : VW.lineMB 8 3 = VW.lineThrough (VW.aff 8 5) (VW.aff 4 4) :=
    ProjectivePlane.lineThrough_eq (P := VW) (x := VW.aff 8 5) (y := VW.aff 4 4)
      (A := VW.lineMB 8 3) (by decide) (by decide) (by decide)
  have e_ac1 : VW.lineMB 6 6 = VW.lineThrough (VW.slopePt 6) (VW.aff 8 2) :=
    ProjectivePlane.lineThrough_eq (P := VW) (x := VW.slopePt 6) (y := VW.aff 8 2)
      (A := VW.lineMB 6 6) (by decide) (by decide) (by decide)
  have e_ac2 : VW.lineMB 1 6 = VW.lineThrough (VW.aff 8 5) (VW.aff 6 3) :=
    ProjectivePlane.lineThrough_eq (P := VW) (x := VW.aff 8 5) (y := VW.aff 6 3)
      (A := VW.lineMB 1 6) (by decide) (by decide) (by decide)
  have e_cb1 : VW.lineMB 7 5 = VW.lineThrough (VW.aff 8 2) (VW.aff 7 4) :=
    ProjectivePlane.lineThrough_eq (P := VW) (x := VW.aff 8 2) (y := VW.aff 7 4)
      (A := VW.lineMB 7 5) (by decide) (by decide) (by decide)
  have e_cb2 : VW.lineMB 5 7 = VW.lineThrough (VW.aff 6 3) (VW.aff 4 4) :=
    ProjectivePlane.lineThrough_eq (P := VW) (x := VW.aff 6 3) (y := VW.aff 4 4)
      (A := VW.lineMB 5 7) (by decide) (by decide) (by decide)
  refine VW_uvw_not_colinear
    (h (VW.aff 5 4) (VW.slopePt 6) (VW.aff 8 5) (VW.aff 7 4) (VW.aff 4 4)
       (VW.aff 8 2) (VW.aff 6 3) (VW.aff 0 6) (VW.aff 1 0) (VW.aff 5 0)
      ⟨VW.lineMB 6 0, by decide, by decide, by decide⟩  -- p, a₁, a₂
      ⟨VW.lineMB 0 4, by decide, by decide, by decide⟩  -- p, b₁, b₂
      ⟨VW.lineMB 4 1, by decide, by decide, by decide⟩  -- p, c₁, c₂
      ⟨VW.lineMB 6 6, by decide, by decide, by decide⟩  -- a₁, c₁, u
      ⟨VW.lineMB 1 6, by decide, by decide, by decide⟩  -- a₂, c₂, u
      ⟨VW.lineMB 7 5, by decide, by decide, by decide⟩  -- b₁, c₁, v
      ⟨VW.lineMB 5 7, by decide, by decide, by decide⟩  -- b₂, c₂, v
      ⟨VW.lineMB 6 8, by decide, by decide, by decide⟩  -- a₁, b₁, w
      ⟨VW.lineMB 8 3, by decide, by decide, by decide⟩  -- a₂, b₂, w
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ?_ ?_ ?_)
  · rw [← e_ab1, ← e_ab2]; decide
  · rw [← e_ac1, ← e_ac2]; decide
  · rw [← e_cb1, ← e_cb2]; decide

/-! ## §2.157h  The Horn-sentence payoff (p. 15)

  Freyd's point in §2.157: the Desargues Horn sentence "is easily verified for
  Rel(S)" (`desarguesHorn_binRel`), yet here is a finite one-object allegory —
  the modular lattice 𝓛(VW) of the Veblen–Wedderburn plane, viewed through
  §2.156/§2.113 — that VIOLATES it.  Horn sentences do not axiomatise the
  representable allegories, and (p. 15) "the theory of allegories in which
  Desargues's theorem is false" is consistent. -/

/-- **§2.157 payoff: the allegory of the Veblen–Wedderburn plane violates the
    Desargues Horn sentence** — immediately from the §2.157g equivalence
    `desarguesND_iff_desarguesHorn` and `VW_not_desargues`. -/
public theorem VW_not_desarguesHorn : ¬ DesarguesHorn (LMonObj (PElem VW)) :=
  fun h => VW_not_desargues (desarguesND_iff_desarguesHorn.mpr h)

/-! ### The non-representability corollary (DONE — see `S2_157i_NotRepresentable`)

  The intended p. 15 consequence — `LMonObj (PElem VW)` admits NO faithful
  representation in `Rel(Set)` (nor in any power of it) — is proved in
  `Freyd/S2_157i_NotRepresentable.lean` from the two transfer facts:

  1. `desarguesHorn_relObj` / `desarguesHorn_relObjPower`: the Horn sentence for
     the honest `Allegory` instance on `RelObj (Type u)` / `RelObj (I → Type u)`
     (the element chase `desarguesHorn_binRel` wired through the `setRel`/`powRel`
     computation rules for `≫`/`∩`/`°`/`⊑`).
  2. `desarguesHorn_reflect`: for a faithful `F : AllegoryFunctor 𝒜 ℬ` (§2.148),
     `DesarguesHorn ℬ → DesarguesHorn 𝒜` — `F` preserves `≫`/`°`/`∩` by its
     fields, and faithful + `map_inter` reflects `⊑` (`R ⊑ S ↔ R ∩ S = R`).

  Together with `VW_not_desarguesHorn` these give `VW_not_representable` and
  `VW_not_representable_in_power`. -/

end Freyd.Alg
