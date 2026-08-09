/-
  Freyd & Scedrov, *Categories and Allegories* — §2.168 (discharging the §2.161 headline):
  the allegory of Z-valued sets over a locale is TABULAR.

  §2.161: "Recall [2.14] that the allegory composed of Z-valued relations [2.111] is not
  tabular if 𝒱 is a connected locale.  For any locale, however, the allegory composed of
  Z-valued relations may be extended to a tabular allegory [2.168]."

  The extension is the allegory OSet(F) of F-valued sets (§2.16(12), built in
  `Freyd/S1_723_Locale.lean` as `instOSetAllegory`).  Here we prove it TABULAR
  (`instTabularOSet`): every `R : ⟨I,E⟩ → ⟨J,S⟩` is tabulated from the apex `I × J` with
  the F-valued equality  `W (i,j) (i',j') = (E i i' ∧ S j j') ∧ (iRj ∧ i'Rj')`  and legs
  `f (i,j) i' = E i i' ∧ iRj`,  `g (i,j) j' = S j j' ∧ iRj`.

  §2.168: "A coreflexive Z-valued relation is a diagonal matrix.  The objects in the
  tabular reflection may be redescribed as pairs ⟨I,∃⟩ where ∃ is a function from I to 𝒱.
  We read ∃ᵢ as 'the extent to which i exists'.  The source-target predicate is
  R : ⟨I,∃⟩ → ⟨J,∃⟩ iff iRj ≤ ∃ᵢ ∧ ∃ⱼ.  R is entire iff ∃ᵢ = ⋁ⱼ iRj for all i, and simple
  iff iRj ∧ iRj' = 0 for all i,j,j', j ≠ j'.  R is a map, therefore, iff for each i the
  i-th row of R partitions ∃ᵢ."

  We realize the ⟨I,∃⟩ objects as the DIAGONAL F-valued sets (`Diagonal`, `ExtObj`,
  `extObjMk`), a full sub-allegory of OSet(F) closed under the tabulation above
  (`instTabularExtObj`), and prove the book's entire/simple/map characterizations
  (`extObj_entire_iff`, `extObj_simple_iff`, `extObj_map_iff`).

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/
module

public import Freyd.S1_723_Locale

universe u

namespace Freyd

open Freyd.Alg

/-! ## Frame meet/sSup helpers

  Small projection/distributivity lemmas used throughout (the Locale file keeps its
  versions `private`, so we re-derive what we need). -/

section FrameHelpers

variable {F : Frame.{u}}

/-- `a = b ⟹ a ≤ b`. -/
private theorem le_of_eq {a b : F.carrier} (h : a = b) : F.le a b := h ▸ F.le_refl a

/-- Project a meet through its LEFT component: `a ≤ c ⟹ a ⊓ b ≤ c`. -/
public theorem mll {a b c : F.carrier} (h : F.le a c) : F.le (F.meet a b) c :=
  F.le_trans (F.meet_le_left _ _) h

/-- Project a meet through its RIGHT component: `b ≤ c ⟹ a ⊓ b ≤ c`. -/
public theorem mlr {a b c : F.carrier} (h : F.le b c) : F.le (F.meet a b) c :=
  F.le_trans (F.meet_le_right _ _) h

/-- Bound a meet whose LEFT factor is a `sSup`, generator-wise (frame distributivity). -/
private theorem sSup_meet_le {S : F.carrier → Prop} {t b : F.carrier}
    (h : ∀ s, S s → F.le (F.meet s t) b) : F.le (F.meet (F.sSup S) t) b := by
  rw [F.meet_comm, F.meet_sSup_distrib]
  exact F.sSup_le _ _ (fun x ⟨s, hs, hx⟩ =>
    hx ▸ F.le_trans (le_of_eq (F.meet_comm t s)) (h s hs))

end FrameHelpers

/-! ## §2.161/[2.168]  The tabulation of an arbitrary F-valued relation

  Given `R : ⟨I,E⟩ → ⟨J,S⟩` in OSet(F), the tabulating apex is the F-valued set on
  `I × J` whose equality `W` records "both coordinates are equal AND both pairs are
  R-related"; the legs project onto the two coordinates, cut down by `R` itself. -/

namespace OSetHom

variable {F : Frame.{u}} {A B : OValuedSet F}

/-- The TABULATION APEX of `R : ⟨I,E⟩ → ⟨J,S⟩` (§2.168): carrier `I × J` with
    `W (i,j) (i',j') = (E i i' ∧ S j j') ∧ (iRj ∧ i'Rj')`.  Symmetry is component-wise;
    transitivity composes the two `E`-components and keeps the outer `R`-components. -/
@[expose] public def tabApex (R : OSetHom A B) : OValuedSet F where
  carrier := A.carrier × B.carrier
  E p q := F.meet (F.meet (A.E p.1 q.1) (B.E p.2 q.2))
                  (F.meet (R.rel p.1 p.2) (R.rel q.1 q.2))
  symm p q := by
    show F.meet (F.meet (A.E p.1 q.1) (B.E p.2 q.2))
                (F.meet (R.rel p.1 p.2) (R.rel q.1 q.2))
       = F.meet (F.meet (A.E q.1 p.1) (B.E q.2 p.2))
                (F.meet (R.rel q.1 q.2) (R.rel p.1 p.2))
    rw [A.symm p.1 q.1, B.symm p.2 q.2, F.meet_comm (R.rel p.1 p.2) (R.rel q.1 q.2)]
  trans p q r := by
    show F.le (F.meet
        (F.meet (F.meet (A.E p.1 q.1) (B.E p.2 q.2))
                (F.meet (R.rel p.1 p.2) (R.rel q.1 q.2)))
        (F.meet (F.meet (A.E q.1 r.1) (B.E q.2 r.2))
                (F.meet (R.rel q.1 q.2) (R.rel r.1 r.2))))
      (F.meet (F.meet (A.E p.1 r.1) (B.E p.2 r.2))
              (F.meet (R.rel p.1 p.2) (R.rel r.1 r.2)))
    exact F.le_meet
      (F.le_meet
        (F.le_trans
          (F.le_meet (mll (mll (F.meet_le_left _ _))) (mlr (mll (F.meet_le_left _ _))))
          (A.trans p.1 q.1 r.1))
        (F.le_trans
          (F.le_meet (mll (mll (F.meet_le_right _ _))) (mlr (mll (F.meet_le_right _ _))))
          (B.trans p.2 q.2 r.2)))
      (F.le_meet (mll (mlr (F.meet_le_left _ _))) (mlr (mlr (F.meet_le_right _ _))))

/-- LEFT LEG of the tabulation, `f : W → ⟨I,E⟩`, `f (i,j) i' = E i i' ∧ iRj`. -/
public def tabLeft (R : OSetHom A B) : OSetHom (tabApex R) A where
  rel p i' := F.meet (A.E p.1 i') (R.rel p.1 p.2)
  dom_bound p i' :=
    F.le_meet
      (F.le_meet (mll (A.E_le_extent_left p.1 i')) (mlr (R.cod_bound p.1 p.2)))
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_right _ _))
  cod_bound p i' := mll (A.E_le_extent_right p.1 i')
  natural p q i₁ i₂ := by
    refine F.le_meet
      (F.le_trans
        (F.le_meet
          (F.le_trans (F.le_meet ?hqp ?hp1) (A.trans q.1 p.1 i₁)) ?h12)
        (A.trans q.1 i₁ i₂))
      ?hRq
    case hqp => exact mll (mll (F.le_trans (mll (F.meet_le_left _ _))
      (le_of_eq (A.symm p.1 q.1))))
    case hp1 => exact mlr (F.meet_le_left _ _)
    case h12 => exact mll (F.meet_le_right _ _)
    case hRq => exact mll (mll (mlr (F.meet_le_right _ _)))

/-- RIGHT LEG of the tabulation, `g : W → ⟨J,S⟩`, `g (i,j) j' = S j j' ∧ iRj`. -/
public def tabRight (R : OSetHom A B) : OSetHom (tabApex R) B where
  rel p j' := F.meet (B.E p.2 j') (R.rel p.1 p.2)
  dom_bound p j' :=
    F.le_meet
      (F.le_meet (mlr (R.dom_bound p.1 p.2)) (mll (B.E_le_extent_left p.2 j')))
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_right _ _))
  cod_bound p j' := mll (B.E_le_extent_right p.2 j')
  natural p q j₁ j₂ := by
    refine F.le_meet
      (F.le_trans
        (F.le_meet
          (F.le_trans (F.le_meet ?hqp ?hp2) (B.trans q.2 p.2 j₁)) ?h12)
        (B.trans q.2 j₁ j₂))
      ?hRq
    case hqp => exact mll (mll (F.le_trans (mll (F.meet_le_right _ _))
      (le_of_eq (B.symm p.2 q.2))))
    case hp2 => exact mlr (F.meet_le_left _ _)
    case h12 => exact mll (F.meet_le_right _ _)
    case hRq => exact mll (mll (mlr (F.meet_le_right _ _)))

/-- The apex equality bounds the `f ≫ f°` composite pointwise (witness the middle index
    at `q.1`).  Used for both `dom (tabLeft R) = 1` and `ff° ∩ gg° = 1`. -/
public theorem tabApex_le_ff (R : OSetHom A B) (p q : A.carrier × B.carrier) :
    F.le ((tabApex R).E p q)
      ((comp (tabLeft R) (recip (tabLeft R))).rel p q) := by
  show F.le ((tabApex R).E p q)
    (F.sSup (fun v => ∃ i'' : A.carrier,
      v = F.meet (F.meet (A.E p.1 i'') (R.rel p.1 p.2))
                 (F.meet (A.E q.1 i'') (R.rel q.1 q.2))))
  refine F.le_trans ?_ (F.le_sSup _ _ ⟨q.1, rfl⟩)
  exact F.le_meet
    (F.le_meet (mll (F.meet_le_left _ _)) (mlr (F.meet_le_left _ _)))
    (F.le_meet
      (F.le_trans (mll (F.meet_le_left _ _)) (A.E_le_extent_right p.1 q.1))
      (mlr (F.meet_le_right _ _)))

/-- The apex equality bounds the `g ≫ g°` composite pointwise (witness at `q.2`). -/
public theorem tabApex_le_gg (R : OSetHom A B) (p q : A.carrier × B.carrier) :
    F.le ((tabApex R).E p q)
      ((comp (tabRight R) (recip (tabRight R))).rel p q) := by
  show F.le ((tabApex R).E p q)
    (F.sSup (fun v => ∃ j'' : B.carrier,
      v = F.meet (F.meet (B.E p.2 j'') (R.rel p.1 p.2))
                 (F.meet (B.E q.2 j'') (R.rel q.1 q.2))))
  refine F.le_trans ?_ (F.le_sSup _ _ ⟨q.2, rfl⟩)
  exact F.le_meet
    (F.le_meet (mll (F.meet_le_right _ _)) (mlr (F.meet_le_left _ _)))
    (F.le_meet
      (F.le_trans (mll (F.meet_le_right _ _)) (B.E_le_extent_right p.2 q.2))
      (mlr (F.meet_le_right _ _)))

/-- `f ≫ f°` is bounded by the A-equality and the two `R`-components (E-transitivity
    across the middle index). -/
public theorem ff_le (R : OSetHom A B) (p q : A.carrier × B.carrier) :
    F.le ((comp (tabLeft R) (recip (tabLeft R))).rel p q)
      (F.meet (A.E p.1 q.1) (F.meet (R.rel p.1 p.2) (R.rel q.1 q.2))) := by
  show F.le (F.sSup (fun v => ∃ i'' : A.carrier,
      v = F.meet (F.meet (A.E p.1 i'') (R.rel p.1 p.2))
                 (F.meet (A.E q.1 i'') (R.rel q.1 q.2)))) _
  apply F.sSup_le
  intro v ⟨i'', hv⟩
  subst hv
  exact F.le_meet
    (F.le_trans
      (F.le_meet (mll (F.meet_le_left _ _))
        (F.le_trans (mlr (F.meet_le_left _ _)) (le_of_eq (A.symm q.1 i''))))
      (A.trans p.1 i'' q.1))
    (F.le_meet (mll (F.meet_le_right _ _)) (mlr (F.meet_le_right _ _)))

/-- `g ≫ g°` is bounded by the B-equality and the two `R`-components. -/
public theorem gg_le (R : OSetHom A B) (p q : A.carrier × B.carrier) :
    F.le ((comp (tabRight R) (recip (tabRight R))).rel p q)
      (F.meet (B.E p.2 q.2) (F.meet (R.rel p.1 p.2) (R.rel q.1 q.2))) := by
  show F.le (F.sSup (fun v => ∃ j'' : B.carrier,
      v = F.meet (F.meet (B.E p.2 j'') (R.rel p.1 p.2))
                 (F.meet (B.E q.2 j'') (R.rel q.1 q.2)))) _
  apply F.sSup_le
  intro v ⟨j'', hv⟩
  subst hv
  exact F.le_meet
    (F.le_trans
      (F.le_meet (mll (F.meet_le_left _ _))
        (F.le_trans (mlr (F.meet_le_left _ _)) (le_of_eq (B.symm q.2 j''))))
      (B.trans p.2 j'' q.2))
    (F.le_meet (mll (F.meet_le_right _ _)) (mlr (F.meet_le_right _ _)))

/-- `R = f° ≫ g` (§2.14 first tabulation equation, stated as `f° ≫ g = R`):
    `⨆_{(i,j)} (E i i' ∧ iRj) ∧ (S j j' ∧ iRj) = i'Rj'` — `≤` by naturality of `R`,
    `≥` by instantiating the middle pair at `(i',j')` and the extent bounds. -/
public theorem tab_factor (R : OSetHom A B) :
    comp (recip (tabLeft R)) (tabRight R) = R := by
  ext i' j'
  show F.sSup (fun v => ∃ p : A.carrier × B.carrier,
      v = F.meet (F.meet (A.E p.1 i') (R.rel p.1 p.2))
                 (F.meet (B.E p.2 j') (R.rel p.1 p.2)))
    = R.rel i' j'
  apply F.le_antisymm
  · apply F.sSup_le
    intro v ⟨p, hv⟩
    subst hv
    exact F.le_trans
      (F.le_meet
        (F.le_meet (mll (F.meet_le_left _ _)) (mlr (F.meet_le_left _ _)))
        (mll (F.meet_le_right _ _)))
      (R.natural p.1 i' p.2 j')
  · refine F.le_trans ?_ (F.le_sSup _ _ ⟨(i', j'), rfl⟩)
    exact F.le_meet
      (F.le_meet (R.dom_bound i' j') (F.le_refl _))
      (F.le_meet (R.cod_bound i' j') (F.le_refl _))

/-- `f ≫ f° ∩ g ≫ g° = 1` (§2.14 second tabulation equation): pointwise both sides
    equal the apex equality `W`. -/
public theorem tab_inter_id (R : OSetHom A B) :
    inter (comp (tabLeft R) (recip (tabLeft R)))
          (comp (tabRight R) (recip (tabRight R)))
      = id (tabApex R) := by
  ext p q
  show F.meet ((comp (tabLeft R) (recip (tabLeft R))).rel p q)
              ((comp (tabRight R) (recip (tabRight R))).rel p q)
      = (tabApex R).E p q
  apply F.le_antisymm
  · exact F.le_meet
      (F.le_meet (mll (F.le_trans (ff_le R p q) (F.meet_le_left _ _)))
                 (mlr (F.le_trans (gg_le R p q) (F.meet_le_left _ _))))
      (mll (F.le_trans (ff_le R p q) (F.meet_le_right _ _)))
  · exact F.le_meet (tabApex_le_ff R p q) (tabApex_le_gg R p q)

/-- `tabLeft R` is ENTIRE: `dom f = 1` on the apex (raw form `1 ∩ ff° = 1`). -/
public theorem tabLeft_dom (R : OSetHom A B) :
    inter (id (tabApex R)) (comp (tabLeft R) (recip (tabLeft R))) = id (tabApex R) := by
  ext p q
  show F.meet ((tabApex R).E p q)
              ((comp (tabLeft R) (recip (tabLeft R))).rel p q)
      = (tabApex R).E p q
  exact F.le_antisymm (F.meet_le_left _ _)
    (F.le_meet (F.le_refl _) (tabApex_le_ff R p q))

/-- `tabRight R` is ENTIRE: `dom g = 1` on the apex. -/
public theorem tabRight_dom (R : OSetHom A B) :
    inter (id (tabApex R)) (comp (tabRight R) (recip (tabRight R))) = id (tabApex R) := by
  ext p q
  show F.meet ((tabApex R).E p q)
              ((comp (tabRight R) (recip (tabRight R))).rel p q)
      = (tabApex R).E p q
  exact F.le_antisymm (F.meet_le_left _ _)
    (F.le_meet (F.le_refl _) (tabApex_le_gg R p q))

/-- `tabLeft R` is SIMPLE: `f° ≫ f ⊑ 1` (raw form `f°f ∩ 1 = f°f`), by E-symmetry
    and E-transitivity across the middle pair. -/
public theorem tabLeft_simple (R : OSetHom A B) :
    inter (comp (recip (tabLeft R)) (tabLeft R)) (id A)
      = comp (recip (tabLeft R)) (tabLeft R) := by
  apply (inter_eq_left_iff _ _).mpr
  intro i₁ i₂
  show F.le (F.sSup (fun v => ∃ p : A.carrier × B.carrier,
      v = F.meet (F.meet (A.E p.1 i₁) (R.rel p.1 p.2))
                 (F.meet (A.E p.1 i₂) (R.rel p.1 p.2))))
    (A.E i₁ i₂)
  apply F.sSup_le
  intro v ⟨p, hv⟩
  subst hv
  exact F.le_trans
    (F.le_meet
      (F.le_trans (mll (F.meet_le_left _ _)) (le_of_eq (A.symm p.1 i₁)))
      (mlr (F.meet_le_left _ _)))
    (A.trans i₁ p.1 i₂)

/-- `tabRight R` is SIMPLE: `g° ≫ g ⊑ 1`. -/
public theorem tabRight_simple (R : OSetHom A B) :
    inter (comp (recip (tabRight R)) (tabRight R)) (id B)
      = comp (recip (tabRight R)) (tabRight R) := by
  apply (inter_eq_left_iff _ _).mpr
  intro j₁ j₂
  show F.le (F.sSup (fun v => ∃ p : A.carrier × B.carrier,
      v = F.meet (F.meet (B.E p.2 j₁) (R.rel p.1 p.2))
                 (F.meet (B.E p.2 j₂) (R.rel p.1 p.2))))
    (B.E j₁ j₂)
  apply F.sSup_le
  intro v ⟨p, hv⟩
  subst hv
  exact F.le_trans
    (F.le_meet
      (F.le_trans (mll (F.meet_le_left _ _)) (le_of_eq (B.symm p.2 j₁)))
      (mlr (F.meet_le_left _ _)))
    (B.trans j₁ p.2 j₂)

end OSetHom

/-- **§2.161/[2.168] HEADLINE.**  For any locale (frame) `F`, the allegory OSet(F) of
    F-valued sets — the natural extension of the allegory of Z-valued relations [2.111]
    — is TABULAR: "For any locale, however, the allegory composed of Z-valued relations
    may be extended to a tabular allegory [2.168]."  Every `R : ⟨I,E⟩ → ⟨J,S⟩` is
    tabulated by the two projection legs from the apex `⟨I × J, W⟩`. -/
@[expose] public instance instTabularOSet (F : Frame.{u}) : TabularAllegory (OValuedSet F) :=
  { instOSetAllegory F with
    tabular := fun R =>
      ⟨OSetHom.tabApex R, OSetHom.tabLeft R, OSetHom.tabRight R,
        ⟨OSetHom.tabLeft_dom R, OSetHom.tabLeft_simple R⟩,
        ⟨OSetHom.tabRight_dom R, OSetHom.tabRight_simple R⟩,
        (OSetHom.tab_factor R).symm, OSetHom.tab_inter_id R⟩ }

/-! ## §2.168  The ⟨I,∃⟩ presentation: diagonal F-valued sets

  "A coreflexive Z-valued relation is a diagonal matrix.  The objects in the tabular
  reflection may be redescribed as pairs ⟨I,∃⟩ where ∃ is a function from I to 𝒱."
  A DIAGONAL F-valued set is one whose equality matrix is diagonal; it carries exactly
  the data ⟨I,∃⟩ with `∃ᵢ = E i i` the "extent to which i exists". -/

/-- An F-valued set is DIAGONAL (§2.168) when its equality is a diagonal matrix:
    all off-diagonal entries are `⊥`. -/
@[expose] public def Diagonal {F : Frame.{u}} (A : OValuedSet F) : Prop :=
  ∀ i j, i ≠ j → A.E i j = F.bot

/-- The §2.168 objects ⟨I,∃⟩: the full sub-allegory of OSet(F) on the DIAGONAL
    F-valued sets. -/
@[expose] public def ExtObj (F : Frame.{u}) : Type (u + 1) := { A : OValuedSet F // Diagonal A }

namespace ExtObj

variable {F : Frame.{u}}

/-- Category structure on `ExtObj F`: full subcategory of OSet(F) — homs, identity and
    composition are those of the underlying F-valued sets. -/
@[expose] public instance instCatExtObj : Cat.{u} (ExtObj F) where
  Hom A B := OSetHom A.val B.val
  id A    := OSetHom.id A.val
  comp    := OSetHom.comp
  id_comp R     := oset_id_comp R
  comp_id R     := oset_comp_id R
  assoc R S T   := oset_comp_assoc R S T

/-- Allegory structure on `ExtObj F`: reciprocation and intersection inherited from
    OSet(F); every law is the corresponding OSet(F) law on the underlying homs. -/
@[expose] public instance instAllegoryExtObj : Allegory (ExtObj F) where
  recip             := OSetHom.recip
  inter             := OSetHom.inter
  recip_recip R     := OSetHom.recip_recip R
  recip_comp R S    := OSetHom.recip_comp R S
  recip_inter R S   := OSetHom.recip_inter R S
  inter_idem R      := OSetHom.inter_idem R
  inter_comm R S    := OSetHom.inter_comm R S
  inter_assoc R S T := OSetHom.inter_assoc R S T
  semidistrib R S T := OSetHom.osetAlleg_semidistrib R S T
  modular R S T     := OSetHom.osetAlleg_modular R S T

end ExtObj

/-- Build a §2.168 object from the book's data ⟨I,∃⟩: carrier `I`, extent function
    `ex : I → 𝒱`, equality `E i j = ⨆ {ex i | i = j}` — the constructive encoding of
    "if i = j then ∃ᵢ else ⊥" (no decidable equality on `I` needed). -/
def extObjMk {F : Frame.{u}} (I : Type u) (ex : I → F.carrier) : ExtObj F :=
  ⟨{ carrier := I
     E := fun i j => F.sSup (fun x => i = j ∧ x = ex i)
     symm := fun i j => F.le_antisymm
       (F.sSup_le _ _ (fun x ⟨hij, hx⟩ => F.le_sSup _ _ ⟨hij.symm, hij ▸ hx⟩))
       (F.sSup_le _ _ (fun x ⟨hji, hx⟩ => F.le_sSup _ _ ⟨hji.symm, hji ▸ hx⟩))
     trans := fun i j k => by
       refine sSup_meet_le (fun s hs => ?_)
       obtain ⟨hij, -⟩ := hs
       subst hij
       exact F.meet_le_right _ _ },
   fun i j hne => F.le_antisymm
     (F.sSup_le _ _ (fun x ⟨hij, _⟩ => absurd hij hne))
     (F.bot_le _)⟩

/-- The diagonal entry of `extObjMk I ex` is the extent: `E i i = ∃ᵢ`. -/
theorem extObjMk_E_self {F : Frame.{u}} (I : Type u) (ex : I → F.carrier) (i : I) :
    (extObjMk I ex).val.E i i = ex i :=
  F.le_antisymm
    (F.sSup_le _ _ (fun _ ⟨_, hx⟩ => le_of_eq hx))
    (F.le_sSup _ _ ⟨rfl, rfl⟩)

namespace OSetHom

variable {F : Frame.{u}} {A B : OValuedSet F}

/-- The tabulation apex of a relation between DIAGONAL F-valued sets is again
    diagonal: if `(i,j) ≠ (i',j')` then one coordinate pair differs, so the
    corresponding E-component of `W` is `⊥`.  (The coordinate split `¬(x ∧ y) ⟹
    ¬x ∨ ¬y` is the one classical step in the file.) -/
public theorem tabApex_diagonal (hA : Diagonal A) (hB : Diagonal B) (R : OSetHom A B) :
    Diagonal (tabApex R) := by
  intro p q hne
  refine F.le_antisymm ?_ (F.bot_le _)
  rcases Classical.em (p.1 = q.1) with h1 | h1
  · have h2 : p.2 ≠ q.2 := by
      intro h2
      apply hne
      cases p; cases q; cases h1; cases h2; rfl
    exact mll (F.le_trans (F.meet_le_right _ _) (le_of_eq (hB _ _ h2)))
  · exact mll (F.le_trans (F.meet_le_left _ _) (le_of_eq (hA _ _ h1)))

end OSetHom

/-- **§2.168**: the ⟨I,∃⟩ allegory — the full sub-allegory of OSet(F) on diagonal
    objects — is TABULAR, tabulating with the SAME apex and legs as `instTabularOSet`
    (the apex stays diagonal by `tabApex_diagonal`).  This makes `ExtObj F` the tabular
    reflection promised by §2.161: it extends the allegory of Z-valued relations [2.111]
    (the objects `⟨I, ∃ = ⊤⟩`, see `sharpHom`) to a tabular allegory. -/
@[expose] public instance instTabularExtObj (F : Frame.{u}) : TabularAllegory (ExtObj F) :=
  { ExtObj.instAllegoryExtObj with
    tabular := fun {A B} R =>
      ⟨⟨OSetHom.tabApex R, OSetHom.tabApex_diagonal A.2 B.2 R⟩,
        OSetHom.tabLeft R, OSetHom.tabRight R,
        ⟨OSetHom.tabLeft_dom R, OSetHom.tabLeft_simple R⟩,
        ⟨OSetHom.tabRight_dom R, OSetHom.tabRight_simple R⟩,
        (OSetHom.tab_factor R).symm, OSetHom.tab_inter_id R⟩ }

/-! ## §2.168  Entire / simple / map characterizations

  "R is entire iff ∃ᵢ = ⋁ⱼ iRj for all i, and simple iff iRj ∧ iRj' = 0 for all
  i,j,j', j ≠ j'."  We prove the raw pointwise forms once at the `OSetHom` level and
  read them off in both OSet(F) and its diagonal sub-allegory `ExtObj F`. -/

namespace OSetHom

variable {F : Frame.{u}} {A B : OValuedSet F}

/-- Raw pointwise form of ENTIRE (`1 ∩ RR° = 1`): each row of `R` joins to the full
    extent, `E i i = ⋁ⱼ iRj`.  (The join is always `≤ E i i` by the domain bound, so
    only the `≤` direction is substantive.) -/
theorem entire_raw_iff (R : OSetHom A B) :
    inter (id A) (comp R (recip R)) = id A
      ↔ ∀ i, A.E i i = F.sSup (fun x => ∃ j, x = R.rel i j) := by
  constructor
  · intro h i
    apply F.le_antisymm
    · have hp : F.meet (A.E i i) ((comp R (recip R)).rel i i) = A.E i i :=
        congrArg (fun T => T.rel i i) h
      have h1 : F.le (A.E i i) ((comp R (recip R)).rel i i) := by
        rw [← hp]; exact F.meet_le_right _ _
      refine F.le_trans h1 ?_
      show F.le (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (R.rel i j))) _
      apply F.sSup_le
      intro v ⟨j, hv⟩
      subst hv
      exact F.le_trans (F.meet_le_left _ _) (F.le_sSup _ _ ⟨j, rfl⟩)
    · exact F.sSup_le _ _ (fun x ⟨j, hx⟩ => hx ▸ R.dom_bound i j)
  · intro h
    ext i i'
    show F.meet (A.E i i') ((comp R (recip R)).rel i i') = A.E i i'
    refine F.le_antisymm (F.meet_le_left _ _) (F.le_meet (F.le_refl _) ?_)
    show F.le (A.E i i') (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (R.rel i' j)))
    refine F.le_trans (F.le_meet (F.le_refl _)
      (F.le_trans (A.E_le_extent_left i i') (le_of_eq (h i)))) ?_
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨s, ⟨j, hs⟩, hv⟩
    subst hs; subst hv
    refine F.le_trans ?_ (F.le_sSup _ _ ⟨j, rfl⟩)
    refine F.le_meet (F.meet_le_right _ _) (F.le_trans ?_ (R.natural i i' j j))
    exact F.le_meet (F.le_meet (F.meet_le_left _ _) (mlr (R.cod_bound i j)))
      (F.meet_le_right _ _)

/-- Raw pointwise form of SIMPLE (`R°R ⊑ 1`): any two entries in a row meet inside
    the codomain equality, `iRj ∧ iRj' ≤ E j j'`. -/
theorem simple_raw_iff (R : OSetHom A B) :
    inter (comp (recip R) R) (id B) = comp (recip R) R
      ↔ ∀ i j j', F.le (F.meet (R.rel i j) (R.rel i j')) (B.E j j') := by
  rw [inter_eq_left_iff]
  constructor
  · intro h i j j'
    exact F.le_trans (F.le_sSup _ _ ⟨i, rfl⟩) (h j j')
  · intro h j j'
    exact F.sSup_le _ _ (fun v ⟨i, hv⟩ => hv ▸ h i j j')

end OSetHom

/-- §2.168 in OSet(F): `R` is ENTIRE iff "∃ᵢ = ⋁ⱼ iRj for all i". -/
theorem oset_entire_iff {F : Frame.{u}} {A B : OValuedSet F} (R : A ⟶ B) :
    Alg.Entire R ↔ ∀ i, A.E i i = F.sSup (fun x => ∃ j, x = R.rel i j) :=
  OSetHom.entire_raw_iff R

/-- §2.168 in OSet(F): `R` is SIMPLE iff row entries meet inside the codomain
    equality (for diagonal codomains this becomes disjointness, `extObj_simple_iff`). -/
theorem oset_simple_iff {F : Frame.{u}} {A B : OValuedSet F} (R : A ⟶ B) :
    Alg.Simple R ↔ ∀ i j j', F.le (F.meet (R.rel i j) (R.rel i j')) (B.E j j') :=
  OSetHom.simple_raw_iff R

/-- **§2.168**: on the ⟨I,∃⟩ objects, `R` is ENTIRE iff "∃ᵢ = ⋁ⱼ iRj for all i". -/
theorem extObj_entire_iff {F : Frame.{u}} {A B : ExtObj F} (R : A ⟶ B) :
    Alg.Entire R ↔ ∀ i, A.val.E i i = F.sSup (fun x => ∃ j, x = R.rel i j) :=
  OSetHom.entire_raw_iff R

/-- **§2.168**: on the ⟨I,∃⟩ objects, `R` is SIMPLE iff "iRj ∧ iRj' = 0 for all
    i,j,j', j ≠ j'" — distinct row entries are disjoint. -/
theorem extObj_simple_iff {F : Frame.{u}} {A B : ExtObj F} (R : A ⟶ B) :
    Alg.Simple R ↔ ∀ i j j', j ≠ j' → F.meet (R.rel i j) (R.rel i j') = F.bot := by
  constructor
  · intro h i j j' hne
    refine F.le_antisymm ?_ (F.bot_le _)
    have hb := (OSetHom.simple_raw_iff R).mp h i j j'
    rw [B.2 j j' hne] at hb
    exact hb
  · intro h
    refine (OSetHom.simple_raw_iff R).mpr (fun i j j' => ?_)
    rcases Classical.em (j = j') with heq | hne
    · subst heq
      exact F.le_trans (F.meet_le_left _ _) (R.cod_bound i j)
    · rw [h i j j' hne]
      exact F.bot_le _

/-- **§2.168**: "R is a map, therefore, iff for each i the i-th row of R partitions
    ∃ᵢ" — the row joins to the whole extent (`entire`) and distinct entries are
    disjoint (`simple`). -/
theorem extObj_map_iff {F : Frame.{u}} {A B : ExtObj F} (R : A ⟶ B) :
    Alg.Map R ↔ ((∀ i, A.val.E i i = F.sSup (fun x => ∃ j, x = R.rel i j)) ∧
             ∀ i j j', j ≠ j' → F.meet (R.rel i j) (R.rel i j') = F.bot) :=
  ⟨fun ⟨he, hs⟩ => ⟨(extObj_entire_iff R).mp he, (extObj_simple_iff R).mp hs⟩,
   fun ⟨he, hs⟩ => ⟨(extObj_entire_iff R).mpr he, (extObj_simple_iff R).mpr hs⟩⟩

/-! ## The Z-valued relations inside the tabular extension (§2.111 / §2.161)

  The original Z-valued-relation allegory [2.111] sits inside `ExtObj F` as the objects
  `⟨I, ∃ = ⊤⟩`: between them, morphisms are ARBITRARY `I × J` matrices of F-values.
  Thus `ExtObj F` is literally the promised tabular EXTENSION of the allegory of
  Z-valued relations. -/

/-- The SHARP object on a set `I`: the ⟨I,∃⟩ object with `∃ᵢ = ⊤` — a set of the
    original Z-valued-relation allegory [2.111]. -/
def sharp (F : Frame.{u}) (I : Type u) : ExtObj F := extObjMk I (fun _ => F.top)

/-- Between sharp objects ANY matrix `M : I → J → 𝒱` is a morphism — the source-target
    predicate `iMj ≤ ∃ᵢ ∧ ∃ⱼ = ⊤` and naturality are vacuous.  These are exactly the
    Z-VALUED RELATIONS of §2.111. -/
def sharpHom {F : Frame.{u}} {I J : Type u} (M : I → J → F.carrier) :
    sharp F I ⟶ sharp F J where
  rel := M
  dom_bound i _ :=
    F.le_trans (F.le_top _) (le_of_eq (extObjMk_E_self I (fun _ => F.top) i).symm)
  cod_bound _ j :=
    F.le_trans (F.le_top _) (le_of_eq (extObjMk_E_self J (fun _ => F.top) j).symm)
  natural i i' j j' := by
    refine F.le_trans (le_of_eq (F.meet_assoc _ _ _)) (sSup_meet_le (fun s hs => ?_))
    obtain ⟨hii, -⟩ := hs
    subst hii
    refine F.le_trans (F.meet_le_right _ _) (sSup_meet_le (fun s' hs' => ?_))
    obtain ⟨hjj, -⟩ := hs'
    subst hjj
    exact F.meet_le_right _ _

/-- Every morphism between sharp objects IS its matrix; with `sharpHom` this identifies
    `sharp F I ⟶ sharp F J` with the `I × J` matrices over `𝒱` (§2.111). -/
theorem eq_sharpHom {F : Frame.{u}} {I J : Type u} (R : sharp F I ⟶ sharp F J) :
    R = sharpHom R.rel :=
  OSetHom.ext rfl

end Freyd
