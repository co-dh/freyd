/-
  Bird & de Moor, *Algebra of Programming* §5.4  The power relator.

  Composition throughout is diagram order (`≫`), matching Freyd's convention (the book's
  `X·Y` is `Y ≫ X` here — already applied to every formula transcribed below).

  `powerRel R : [a] ⟶ [b]` is B&dM's `PR` (p.119): the Egli–Milner lifting of `R : a ⟶ b`
  to the power objects.  It is built from the two division operations of `Freyd.S2_3`
  (`/`, right division, and `\` = `leftDiv`, left division) applied to the membership `∋`
  of `Freyd.S2_4`.  Only the hard direction of functoriality (`powerRel_comp`) needs a
  tabulation; every other fact holds in a bare `UnguardedPowerAllegory`.

  Ex 5.16 (`powerRel (dom R) ≫ existsImage R ⊑ powerRel R`) is DROPPED — see the report;
  the natural attempt needs `R` a map to shunt, which it is not in general.
-/

import Freyd.S2_04
import AOP.A4_6
import AOP.A4_2
import Freyd.S2_41b

universe u

namespace Freyd.Alg

-- (`div_mono_left`/`leftDiv_mono_right` were hoisted into S2_3 at collection.)

/-! ## §5.4  Definition and elementary calculus of the power relator -/

section PowerRelDef

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- **B&dM §5.4 p.119** (the POWER RELATOR `PR`, mirrored to Freyd's diagram order): for
    `R : a ⟶ b`, `powerRel R : [a] ⟶ [b]` relates `X` to `Y` (the Egli–Milner order) when
    EVERY element of `X` `R`-reaches into `Y` (term₁, via left division `\`: "each element
    of the input set `R`-reaches into the output set") AND every element of `Y` is
    `R`-reachable from some element of `X` (term₂, via right division `/`: "each element of
    the output set is `R`-reachable from the input set").

    Universal properties used to verify the definition (`le_leftDiv_iff`/`le_div_iff`):
    `X ⊑ ((∋a)° \ (R≫(∋b)°)) ↔ (∋a)°≫X ⊑ R≫(∋b)°` (term₁) and
    `X ⊑ (∋a≫R)/∋b ↔ X≫∋b ⊑ ∋a≫R` (term₂). -/
def powerRel {a b : 𝒜} (R : a ⟶ b) :
    PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj b :=
  ((∋ a)° \ (R ≫ (∋ b)°)) ∩ ((∋ a ≫ R) / ∋ b)

/-- Term₂ cancellation (the "output-reachable" half): `powerRel R ≫ ∋ b ⊑ ∋ a ≫ R`.
    This is B&dM p.133's example that `∈` is LAX NATURAL along the power relator
    (used again, unnamed, in `AOP.A5_7`). -/
theorem powerRel_eps_lax {a b : 𝒜} (R : a ⟶ b) : powerRel R ≫ ∋ b ⊑ ∋ a ≫ R :=
  le_trans (comp_mono_right (inter_lb_right _ _) _) (DivisionAllegory.div_comp_le _ _)

/-- Term₁ cancellation (the "input-reaches" half): `(∋ a)° ≫ powerRel R ⊑ R ≫ (∋ b)°`. -/
theorem powerRel_term1_cancel {a b : 𝒜} (R : a ⟶ b) :
    (∋ a)° ≫ powerRel R ⊑ R ≫ (∋ b)° :=
  (le_leftDiv_iff _ _ _).mp (inter_lb_left _ _)

/-- **B&dM §5.4** (`powerRel` is monotone): `R ⊑ S → powerRel R ⊑ powerRel S`.  Both
    divisions are monotone in the numerator position (`div_mono_left`/`leftDiv_mono_right`),
    applied after composing `h` with the fixed `∋`-factors. -/
theorem powerRel_mono {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : powerRel R ⊑ powerRel S :=
  le_inter
    (le_trans (inter_lb_left _ _) (leftDiv_mono_right _ (comp_mono_right h _)))
    (le_trans (inter_lb_right _ _) (div_mono_left (comp_mono_left _ h) _))

/-- **B&dM §5.4** (`powerRel` preserves identities): `powerRel 1_a = 1_{[a]}`.  B&dM's
    "`Pid = id` is the antisymmetry of subset" — here it is definitional via `symmDiv` plus
    Freyd's `A_eps_reflection` (§2.412 reflection law `A(∋) = id`).  With `R = id_a` the
    definition collapses to `((∋a)° \ (∋a)°) ∩ (∋a/∋a)`; the first term equals
    `powerOrder°` on the nose (`(S \ R)` unfolds to `(R° / S°)°`, and `(∋a)°° = ∋a`), so the
    whole meet is `powerOrder° ∩ powerOrder = powerOrder ∩ powerOrder°`, which is exactly
    the unfolding of `A (∋ a) = ∋a /ₛ ∋a`. -/
theorem powerRel_id {a : 𝒜} : powerRel (Cat.id a) = Cat.id (PowerAllegory.powerObj a) := by
  have hterm1 : ((∋ a)° \ (Cat.id a ≫ (∋ a)°)) = (powerOrder (a := a))° := by
    have e : Cat.id a ≫ (∋ a)° = (∋ a)° := Cat.id_comp _
    rw [e]
    show ((((∋ a)°)°) / (((∋ a)°)°))° = (powerOrder (a := a))°
    rw [Allegory.recip_recip]
    rfl
  show ((∋ a)° \ (Cat.id a ≫ (∋ a)°)) ∩ ((∋ a ≫ Cat.id a) / ∋ a)
      = Cat.id (PowerAllegory.powerObj a)
  rw [hterm1, Cat.comp_id]
  show (powerOrder (a := a))° ∩ powerOrder (a := a) = Cat.id (PowerAllegory.powerObj a)
  rw [Allegory.inter_comm]
  exact A_eps_reflection

/-- **B&dM §5.4 p.119 top** (`P` and `E` agree on maps): for a map `f`, `powerRel f`
    coincides with the existential image `existsImage f` of `AOP.A4_6`.  The term₂
    components already match on the nose (both are `(∋a≫f)/∋b`); the term₁ component is
    identified with the reciprocal of the OTHER division component of `existsImage f`'s
    `symmDiv` unfolding via an indirect (Yoneda-style) argument using `map_shunt_left`. -/
theorem powerRel_map {a b : 𝒜} {f : a ⟶ b} (hf : Map f) : powerRel f = existsImage f := by
  have hterm1 : ((∋ a)° \ (f ≫ (∋ b)°)) = (∋ b / (∋ a ≫ f))° := by
    have dir1 : ((∋ a)° \ (f ≫ (∋ b)°)) ⊑ (∋ b / (∋ a ≫ f))° := by
      have step1 : (∋ a)° ≫ ((∋ a)° \ (f ≫ (∋ b)°)) ⊑ f ≫ (∋ b)° := leftDiv_comp_le _ _
      have step2 : f° ≫ ((∋ a)° ≫ ((∋ a)° \ (f ≫ (∋ b)°))) ⊑ (∋ b)° :=
        (map_shunt_left hf _ _).mpr step1
      have step3 : (∋ a ≫ f)° ≫ ((∋ a)° \ (f ≫ (∋ b)°)) ⊑ (∋ b)° := by
        have e : (∋ a ≫ f)° = f° ≫ (∋ a)° := Allegory.recip_comp _ _
        rw [e, Cat.assoc]; exact step2
      have step4 := recip_mono step3
      simp only [Allegory.recip_comp, Allegory.recip_recip] at step4
      have step5 : ((∋ a)° \ (f ≫ (∋ b)°))° ⊑ ∋ b / (∋ a ≫ f) := (le_div_iff _ _ _).mpr step4
      have step6 := recip_mono step5
      rwa [Allegory.recip_recip] at step6
    have dir2 : (∋ b / (∋ a ≫ f))° ⊑ ((∋ a)° \ (f ≫ (∋ b)°)) := by
      have step1 : (∋ b / (∋ a ≫ f)) ≫ (∋ a ≫ f) ⊑ ∋ b := DivisionAllegory.div_comp_le _ _
      have step2 := recip_mono step1
      simp only [Allegory.recip_comp] at step2
      have step3 : f° ≫ ((∋ a)° ≫ (∋ b / (∋ a ≫ f))°) ⊑ (∋ b)° := by
        rw [Cat.assoc] at step2; exact step2
      have step4 : (∋ a)° ≫ (∋ b / (∋ a ≫ f))° ⊑ f ≫ (∋ b)° :=
        (map_shunt_left hf _ _).mp step3
      exact (le_leftDiv_iff _ _ _).mpr step4
    exact le_antisymm dir1 dir2
  show ((∋ a)° \ (f ≫ (∋ b)°)) ∩ ((∋ a ≫ f) / ∋ b)
      = ((∋ a ≫ f) / ∋ b) ∩ ((∋ b / (∋ a ≫ f))°)
  rw [hterm1]
  exact Allegory.inter_comm _ _

end PowerRelDef

/-! ## §5.4  Functoriality of the power relator (`powerRel (R ≫ S) = powerRel R ≫ powerRel S`)

  The `⊒` direction (`powerRel_comp_le`) needs only the two universal properties, so it is
  proved under a bare `[UnguardedPowerAllegory 𝒜]`.  The `⊑` direction needs a TABULATION of
  `powerRel (R ≫ S)`, so it is proved under the merged class `TabularUnitaryUnguardedPowerAllegory`
  (`Freyd.S2_41b`) — the smallest existing class combining `TabularAllegory`-strength
  tabulation with the `A4_6` power-allegory calculus over a single shared `Allegory` base. -/

section PowerRelCompEasy

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- **B&dM §5.4** (functoriality, easy direction): `powerRel R ≫ powerRel S ⊑ powerRel (R ≫ S)`.
    Both obligations chain the term₁/term₂ cancellations of `powerRel R` and `powerRel S`. -/
theorem powerRel_comp_le {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    powerRel R ≫ powerRel S ⊑ powerRel (R ≫ S) := by
  apply le_inter
  · apply (le_leftDiv_iff _ _ _).mpr
    have part1 : (∋ a)° ≫ (powerRel R ≫ powerRel S) ⊑ R ≫ ((∋ b)° ≫ powerRel S) := by
      calc (∋ a)° ≫ (powerRel R ≫ powerRel S)
          = ((∋ a)° ≫ powerRel R) ≫ powerRel S := (Cat.assoc _ _ _).symm
        _ ⊑ (R ≫ (∋ b)°) ≫ powerRel S := comp_mono_right (powerRel_term1_cancel R) _
        _ = R ≫ ((∋ b)° ≫ powerRel S) := Cat.assoc _ _ _
    have part2 : R ≫ ((∋ b)° ≫ powerRel S) ⊑ (R ≫ S) ≫ (∋ c)° := by
      calc R ≫ ((∋ b)° ≫ powerRel S)
          ⊑ R ≫ (S ≫ (∋ c)°) := comp_mono_left _ (powerRel_term1_cancel S)
        _ = (R ≫ S) ≫ (∋ c)° := (Cat.assoc _ _ _).symm
    exact le_trans part1 part2
  · apply (le_div_iff _ _ _).mpr
    have part1 : (powerRel R ≫ powerRel S) ≫ ∋ c ⊑ (powerRel R ≫ ∋ b) ≫ S := by
      calc (powerRel R ≫ powerRel S) ≫ ∋ c
          = powerRel R ≫ (powerRel S ≫ ∋ c) := Cat.assoc _ _ _
        _ ⊑ powerRel R ≫ (∋ b ≫ S) := comp_mono_left _ (powerRel_eps_lax S)
        _ = (powerRel R ≫ ∋ b) ≫ S := (Cat.assoc _ _ _).symm
    have part2 : (powerRel R ≫ ∋ b) ≫ S ⊑ ∋ a ≫ (R ≫ S) := by
      calc (powerRel R ≫ ∋ b) ≫ S
          ⊑ (∋ a ≫ R) ≫ S := comp_mono_right (powerRel_eps_lax R) _
        _ = ∋ a ≫ (R ≫ S) := Cat.assoc _ _ _
    exact le_trans part1 part2

end PowerRelCompEasy

section PowerRelLegBound

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- **Reusable core of the hard functoriality obligations** (both `powerRel_comp`'s term₁-for-`x`
    and term₂-for-`z` obligations instantiate this ONE lemma — the latter after a `°`-flip).

    Setting: `W = (p ≫ ∋ a' ≫ bookRel) ∩ (q ≫ ∋ b'' ≫ bookRel')` (a meet of two "reachability"
    relations through legs `p, q` of a tabulation), `h = A W` the classifying map of `W`.  Given
    the CROSS fact `(∋a')°≫p°≫q ⊑ (bookRel≫bookRel'°)≫(∋b'')°` (extracted from the membership
    of the tabulated relation itself), we get `(∋a')°≫(p°≫h) ⊑ bookRel≫(∋d)°`.

    Proof: shunt `h` (a map, `A_is_map'`) to reduce to `S' ⊑ bookRel ≫ W°` where
    `S' := (∋a')°≫p°`; compute `W° = (bookRel°≫S') ∩ (bookRel'°≫S'')` with `S'' := (∋b'')°≫q°`;
    shunt `q` (a map) in the cross fact to get the "easy" bound `S' ⊑ bookRel≫(bookRel'°≫S'')`;
    combine with the trivial `S' ⊑ S'` via the (right) modular law `modular_le_right` to land
    inside `bookRel ≫ W°`. -/
private theorem powerRel_leg_bound {w a' b'' d : 𝒜}
    {p : w ⟶ PowerAllegory.powerObj a'} {q : w ⟶ PowerAllegory.powerObj b''}
    (hq : Map q)
    {bookRel : a' ⟶ d} {bookRel' : b'' ⟶ d}
    {W : w ⟶ d} (hWdef : W = (p ≫ ∋ a' ≫ bookRel) ∩ (q ≫ ∋ b'' ≫ bookRel'))
    {h : w ⟶ PowerAllegory.powerObj d} (hh : Map h) (hheps : h ≫ ∋ d = W)
    (fact : (∋ a')° ≫ p° ≫ q ⊑ (bookRel ≫ bookRel'°) ≫ (∋ b'')°) :
    (∋ a')° ≫ (p° ≫ h) ⊑ bookRel ≫ (∋ d)° := by
  have hstep : ((∋ a')° ≫ p°) ≫ h ⊑ bookRel ≫ (∋ d)° := by
    apply (map_shunt_right hh _ _).mpr
    have hQ : (bookRel ≫ (∋ d)°) ≫ h° = bookRel ≫ W° := by
      rw [Cat.assoc, ← Allegory.recip_comp, hheps]
    rw [hQ, hWdef, Allegory.recip_inter]
    have e1 : (p ≫ ∋ a' ≫ bookRel)° = bookRel° ≫ ((∋ a')° ≫ p°) := by
      simp only [Allegory.recip_comp, Cat.assoc]
    have e2 : (q ≫ ∋ b'' ≫ bookRel')° = bookRel'° ≫ ((∋ b'')° ≫ q°) := by
      simp only [Allegory.recip_comp, Cat.assoc]
    rw [e1, e2]
    have hfact' : ((∋ a')° ≫ p°) ≫ q ⊑ bookRel ≫ (bookRel'° ≫ (∋ b'')°) := by
      have hf := fact; simp only [Cat.assoc] at hf ⊢; exact hf
    have heasy : (∋ a')° ≫ p° ⊑ bookRel ≫ (bookRel'° ≫ ((∋ b'')° ≫ q°)) := by
      have hshunt := (map_shunt_right hq _ _).mp hfact'
      simpa only [Cat.assoc] using hshunt
    have hstep_a : (∋ a')° ≫ p°
        ⊑ (bookRel ≫ (bookRel'° ≫ ((∋ b'')° ≫ q°))) ∩ ((∋ a')° ≫ p°) :=
      le_inter heasy (le_refl _)
    have hstep_b : (bookRel ≫ (bookRel'° ≫ ((∋ b'')° ≫ q°))) ∩ ((∋ a')° ≫ p°)
        ⊑ bookRel ≫ ((bookRel'° ≫ ((∋ b'')° ≫ q°)) ∩ (bookRel° ≫ ((∋ a')° ≫ p°))) :=
      modular_le_right bookRel _ _
    have hcomb := le_trans hstep_a hstep_b
    rw [Allegory.inter_comm] at hcomb
    exact hcomb
  simpa only [Cat.assoc] using hstep

end PowerRelLegBound

section PowerRelCompHard

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerAllegory 𝒜]

/-- **B&dM §5.4** (functoriality, THE HARD direction): `powerRel (R ≫ S) ⊑ powerRel R ≫ powerRel S`.
    Tabulate `powerRel (R≫S)` as `x°≫z` (a jointly-monic pair of maps `x : w⟶[a]`, `z : w⟶[c]`).
    Set `W := (x≫∋a≫R) ∩ (z≫∋c≫S°)` and `h := A W : w⟶[b]`.  The two "cross facts"
    `(∋a)°≫x°≫z ⊑ (R≫S)≫(∋c)°` (from term₁-membership of `powerRel(R≫S)` itself) and its
    `°`-flip `(∋c)°≫z°≫x ⊑ (S°≫R°)≫(∋a)°` (from term₂-membership) feed `powerRel_leg_bound`
    (applied to the `x`-leg and, after a flip, the `z`-leg) to give `x°≫h ⊑ powerRel R` and
    `h°≫z ⊑ powerRel S`.  Since `h` is entire, `x°≫z ⊑ x°≫(h≫h°)≫z = (x°≫h)≫(h°≫z) ⊑
    powerRel R ≫ powerRel S`. -/
theorem powerRel_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    powerRel (R ≫ S) = powerRel R ≫ powerRel S := by
  apply le_antisymm _ (powerRel_comp_le R S)
  obtain ⟨w, x, z, hxmap, hzmap, hxz, _hjoint⟩ :=
    TabularAllegory.tabular (𝒜 := 𝒜) (powerRel (R ≫ S))
  let W : w ⟶ b := (x ≫ ∋ a ≫ R) ∩ (z ≫ ∋ c ≫ S°)
  let h : w ⟶ PowerAllegory.powerObj b := A W
  have hWdef : W = (x ≫ ∋ a ≫ R) ∩ (z ≫ ∋ c ≫ S°) := rfl
  have hhmap : Map h := A_is_map' W
  have hheps : h ≫ ∋ b = W := A_eps_eq' W
  -- Term₁/term₂ membership of the ORIGINAL tabulated relation `powerRel (R ≫ S) = x° ≫ z`.
  have factI : (∋ a)° ≫ x° ≫ z ⊑ (R ≫ S) ≫ (∋ c)° := by
    have hmem : x° ≫ z ⊑ ((∋ a)° \ ((R ≫ S) ≫ (∋ c)°)) := by
      rw [← hxz]; exact inter_lb_left _ _
    exact (le_leftDiv_iff _ _ _).mp hmem
  have factII : (x° ≫ z) ≫ ∋ c ⊑ ∋ a ≫ (R ≫ S) := by
    have hmem : x° ≫ z ⊑ (∋ a ≫ (R ≫ S)) / ∋ c := by
      rw [← hxz]; exact inter_lb_right _ _
    exact (le_div_iff _ _ _).mp hmem
  have factI' : (∋ a)° ≫ x° ≫ z ⊑ (R ≫ (S°)°) ≫ (∋ c)° := by
    rw [Allegory.recip_recip]; exact factI
  have factII' : (∋ c)° ≫ z° ≫ x ⊑ (S° ≫ R°) ≫ (∋ a)° := by
    have hr := recip_mono factII
    simp only [Allegory.recip_comp, Allegory.recip_recip] at hr
    exact hr
  have hWdef' : W = (z ≫ ∋ c ≫ S°) ∩ (x ≫ ∋ a ≫ R) := hWdef.trans (Allegory.inter_comm _ _)
  -- `x`-leg: term₁ (hard) via `powerRel_leg_bound`, term₂ (easy) directly.
  have hxh_le : x° ≫ h ⊑ powerRel R := by
    apply le_inter
    · exact (le_leftDiv_iff _ _ _).mpr (powerRel_leg_bound hzmap hWdef hhmap hheps factI')
    · apply (le_div_iff _ _ _).mpr
      have part1 : (x° ≫ h) ≫ ∋ b ⊑ (x° ≫ x) ≫ ∋ a ≫ R := by
        calc (x° ≫ h) ≫ ∋ b
            = x° ≫ (h ≫ ∋ b) := Cat.assoc _ _ _
          _ = x° ≫ W := by rw [hheps]
          _ ⊑ x° ≫ (x ≫ ∋ a ≫ R) := comp_mono_left _ (by rw [hWdef]; exact inter_lb_left _ _)
          _ = (x° ≫ x) ≫ ∋ a ≫ R := (Cat.assoc _ _ _).symm
      have part2 : (x° ≫ x) ≫ ∋ a ≫ R ⊑ ∋ a ≫ R := by
        calc (x° ≫ x) ≫ ∋ a ≫ R
            ⊑ Cat.id (PowerAllegory.powerObj a) ≫ ∋ a ≫ R := comp_mono_right hxmap.2 _
          _ = ∋ a ≫ R := Cat.id_comp _
      exact le_trans part1 part2
  -- `z`-leg: term₁ (easy) directly, term₂ (hard) via `powerRel_leg_bound` + a `°`-flip.
  have hhz_le : h° ≫ z ⊑ powerRel S := by
    apply le_inter
    · apply (le_leftDiv_iff _ _ _).mpr
      have hraw : z° ≫ (h ≫ ∋ b) ⊑ ∋ c ≫ S° := by
        have part1 : z° ≫ (h ≫ ∋ b) ⊑ (z° ≫ z) ≫ ∋ c ≫ S° := by
          calc z° ≫ (h ≫ ∋ b) = z° ≫ W := by rw [hheps]
            _ ⊑ z° ≫ (z ≫ ∋ c ≫ S°) := comp_mono_left _ (by rw [hWdef]; exact inter_lb_right _ _)
            _ = (z° ≫ z) ≫ ∋ c ≫ S° := (Cat.assoc _ _ _).symm
        have part2 : (z° ≫ z) ≫ ∋ c ≫ S° ⊑ ∋ c ≫ S° := by
          calc (z° ≫ z) ≫ ∋ c ≫ S°
              ⊑ Cat.id (PowerAllegory.powerObj c) ≫ ∋ c ≫ S° := comp_mono_right hzmap.2 _
            _ = ∋ c ≫ S° := Cat.id_comp _
        exact le_trans part1 part2
      have hr := recip_mono hraw
      simp only [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc] at hr
      exact hr
    · apply (le_div_iff _ _ _).mpr
      have hz_term1 : (∋ c)° ≫ (z° ≫ h) ⊑ S° ≫ (∋ b)° :=
        powerRel_leg_bound hxmap hWdef' hhmap hheps factII'
      have hr := recip_mono hz_term1
      simp only [Allegory.recip_comp, Allegory.recip_recip] at hr
      exact hr
  rw [hxz]
  have hent : Cat.id w ⊑ h ≫ h° := entire_id_le hhmap.1
  have p1 : x° ≫ z ⊑ (x° ≫ h) ≫ (h° ≫ z) := by
    calc x° ≫ z
        = x° ≫ (Cat.id w ≫ z) := by rw [Cat.id_comp]
      _ ⊑ x° ≫ ((h ≫ h°) ≫ z) := comp_mono_left _ (comp_mono_right hent _)
      _ = (x° ≫ h) ≫ (h° ≫ z) := by simp only [Cat.assoc]
  have p2 : (x° ≫ h) ≫ (h° ≫ z) ⊑ powerRel R ≫ (h° ≫ z) := comp_mono_right hxh_le _
  have p3 : powerRel R ≫ (h° ≫ z) ⊑ powerRel R ≫ powerRel S := comp_mono_left _ hhz_le
  exact le_trans p1 (le_trans p2 p3)

end PowerRelCompHard

end Freyd.Alg
