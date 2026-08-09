/-
  §1.532  `Δ : 𝒞 → Over B` is a representation of cartesian categories.

  Freyd & Scedrov factor `(B×−)` in DIAGRAM ORDER as `𝒞 →[Δ] Over B →[Σ] 𝒞`, i.e.
  `(B×−) = ΔΣ`, with `Σ = SliceForget` (forgetful) and `Δ = deltaFunctor` (diagonal),
  `Δ Y = ⟨Y×B, snd⟩` (`S1_85`; Σ ⊣ Δ is `sigma_adj_delta`).

  §1.437: a functor is a REPRESENTATION OF CARTESIAN CATEGORIES iff it preserves pullbacks
  and the terminator.  §1.532 gets this for `Δ` by the [1.442] cancellation, in diagram order:
  `ΔΣ = (−×B)` preserves pullbacks and `Σ` reflects them (`sliceForget_reflects_isPullback`,
  i.e. cancel the right factor `Σ`), so `Δ` preserves pullbacks; and `Δ` preserves the
  terminator directly (`Δ 1 = ⟨1×B, snd⟩ ≅ (B →[1] B)`, the slice's distinguished terminator).

  (`Σ` cannot be a Lean identifier — it is the reserved `Σ`-type binder — hence `sliceForget`;
  `Δ` is a legal identifier, so the book names are kept on the `Δ` side.)
-/
module

public import Freyd.S1_85
public import Freyd.S1_53_SliceRegular

universe v u

namespace Freyd

-- `deltaObj`/`deltaMap` (S1_85) are defined under `HasExponentials`, so we inherit that binder
-- (it `extends HasBinaryProducts`, so the product API still resolves).  §1.532 itself only needs
-- finite products; generalising `deltaObj` to `HasBinaryProducts` would be a separate S1_85 refactor.
variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasExponentials 𝒞]

/-- `g ≫ ⟨p,q⟩ = ⟨g≫p, g≫q⟩`. -/
private theorem comp_pair {W X A B : 𝒞} (g : W ⟶ X) (p : X ⟶ A) (q : X ⟶ B) :
    g ≫ pair p q = pair (g ≫ p) (g ≫ q) :=
  pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])

/-- `Δ`'s underlying map composes as `(h×1) ≫ (k×1) = (h≫k)×1` (in `pair (fst ≫ ·) snd` form). -/
private theorem pm_comp {X Y Z : 𝒞} (B : 𝒞) (h : X ⟶ Y) (k : Y ⟶ Z) :
    pair (fst ≫ h) (snd : prod X B ⟶ B) ≫ pair (fst ≫ k) snd = pair (fst ≫ (h ≫ k)) snd := by
  rw [comp_pair, snd_pair, ← Cat.assoc, fst_pair, Cat.assoc]

section Pullback
variable [HasPullbacks 𝒞]

/-- The `Δ`-image of a base cone over `(f,g)`: a slice cone over `(Δf, Δg)` in `Over B`. -/
def deltaCone (B : 𝒞) {Y₁ Y₂ Y₀ : 𝒞} {f : Y₁ ⟶ Y₀} {g : Y₂ ⟶ Y₀} (c : Cone f g) :
    Cone (𝒞 := Over B) (deltaMap B f) (deltaMap B g) where
  pt := deltaObj B c.pt
  π₁ := deltaMap B c.π₁
  π₂ := deltaMap B c.π₂
  w := OverHom.ext <| by
    show pair (fst ≫ c.π₁) snd ≫ pair (fst ≫ f) snd
       = pair (fst ≫ c.π₂) snd ≫ pair (fst ≫ g) snd
    rw [pm_comp, pm_comp, c.w]

/-- **`ΔΣ = (−×B)` preserves pullbacks** — the `Σ`-image of the `Δ`-cone is a base pullback.
    Lift of a test cone `d` is `⟨w, d.π₁≫snd⟩`, with `w` from `c.IsPullback` on the `fst`-parts. -/
theorem forget_deltaCone_isPullback (B : 𝒞) {Y₁ Y₂ Y₀ : 𝒞} {f : Y₁ ⟶ Y₀} {g : Y₂ ⟶ Y₀}
    (c : Cone f g) (hc : c.IsPullback) : (sliceConeForget (deltaCone B c)).IsPullback := by
  intro d
  have hsnd : d.π₁ ≫ snd = d.π₂ ≫ snd := by
    simpa [deltaMap, deltaCone, sliceConeForget, Cat.assoc, snd_pair] using congrArg (· ≫ snd) d.w
  have hbw : (d.π₁ ≫ fst) ≫ f = (d.π₂ ≫ fst) ≫ g := by
    simpa [deltaMap, deltaCone, sliceConeForget, Cat.assoc, fst_pair] using congrArg (· ≫ fst) d.w
  obtain ⟨w, ⟨hw₁, hw₂⟩, hwuniq⟩ := hc ⟨d.pt, d.π₁ ≫ fst, d.π₂ ≫ fst, hbw⟩
  refine ⟨pair w (d.π₁ ≫ snd), ⟨?_, ?_⟩, ?_⟩
  · show pair w (d.π₁ ≫ snd) ≫ pair (fst ≫ c.π₁) snd = d.π₁
    rw [comp_pair, snd_pair, ← Cat.assoc, fst_pair, hw₁]
    exact (pair_uniq _ _ d.π₁ rfl rfl).symm
  · show pair w (d.π₁ ≫ snd) ≫ pair (fst ≫ c.π₂) snd = d.π₂
    rw [comp_pair, snd_pair, hsnd, ← Cat.assoc, fst_pair, hw₂]
    exact (pair_uniq _ _ d.π₂ rfl rfl).symm
  · intro v hv₁ hv₂
    have hvsnd : v ≫ snd = d.π₁ ≫ snd := by
      simpa [deltaMap, deltaCone, sliceConeForget, Cat.assoc, snd_pair] using congrArg (· ≫ snd) hv₁
    have hvfst : v ≫ fst = w := by
      apply hwuniq
      · simpa [deltaMap, deltaCone, sliceConeForget, Cat.assoc, fst_pair] using congrArg (· ≫ fst) hv₁
      · simpa [deltaMap, deltaCone, sliceConeForget, Cat.assoc, fst_pair] using congrArg (· ≫ fst) hv₂
    rw [pair_uniq _ _ v rfl rfl, hvfst, hvsnd]

/-- **§1.532 — `Δ` preserves pullbacks.**  The [1.442] cancellation in diagram order: `ΔΣ = (−×B)`
    preserves pullbacks (`forget_deltaCone_isPullback`) and `Σ` reflects them, so `Δ` preserves them.

    The `Σ`-reflection step is inlined (lift the base solution `u` to the over-hom `⟨u, uw⟩`): the
    general `sliceForget_reflects_isPullback` lives in `SliceTopos` with a spurious topos hypothesis;
    consolidating it into `SliceRegular` (see `TODO.md`) would let this be a one-liner. -/
theorem Δ_preserves_pullback (B : 𝒞) {Y₁ Y₂ Y₀ : 𝒞} {f : Y₁ ⟶ Y₀} {g : Y₂ ⟶ Y₀}
    (c : Cone f g) (hc : c.IsPullback) : (deltaCone B c).IsPullback := by
  intro d
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := forget_deltaCone_isPullback B c hc (sliceConeForget d)
  have hu₁' : u ≫ (deltaCone B c).π₁.f = d.π₁.f := hu₁
  have hu₂' : u ≫ (deltaCone B c).π₂.f = d.π₂.f := hu₂
  have uw : u ≫ (deltaCone B c).pt.hom = d.pt.hom := by
    have h1 : u ≫ ((deltaCone B c).π₁.f ≫ (deltaObj B Y₁).hom) = d.π₁.f ≫ (deltaObj B Y₁).hom := by
      rw [← Cat.assoc, hu₁']
    rwa [(deltaCone B c).π₁.w, d.π₁.w] at h1
  exact ⟨⟨u, uw⟩, ⟨OverHom.ext hu₁', OverHom.ext hu₂'⟩,
    fun v hv₁ hv₂ => OverHom.ext (huniq v.f (congrArg OverHom.f hv₁) (congrArg OverHom.f hv₂))⟩

end Pullback

/-- The `Δ`-image of the terminator, as an over-map onto the slice terminator `B →[1] B`. -/
def deltaTerminalHom [HasTerminal 𝒞] (B : 𝒞) : OverHom (deltaObj B (one : 𝒞)) (overTerm B) :=
  ⟨snd, by simp [overTerm, deltaObj, Cat.comp_id]⟩

/-- **§1.532 — `Δ` preserves the terminator.**  `Δ 1 = ⟨1×B, snd⟩ ≅ (B →[1] B)`, the distinguished
    terminator of `Over B`; the witnessing iso is `snd : 1×B → B` (inverse `⟨!, 1_B⟩`). -/
theorem Δ_preserves_terminal [HasTerminal 𝒞] (B : 𝒞) : OverIso (deltaTerminalHom B) := by
  apply overIso_of_underlying
  show IsIso (snd : prod (one : 𝒞) B ⟶ B)
  refine ⟨pair (term B) (Cat.id B), ?_, snd_pair _ _⟩
  calc snd ≫ pair (term B) (Cat.id B)
      = pair (snd ≫ term B) (snd ≫ Cat.id B) := comp_pair _ _ _
    _ = pair fst snd := by rw [Cat.comp_id, term_uniq (snd ≫ term B) fst]
    _ = Cat.id (prod (one : 𝒞) B) := pair_fst_snd

end Freyd
