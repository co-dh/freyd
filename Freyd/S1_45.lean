/-
  Freyd & Scedrov, *Categories and Allegories* §1.45  Pullbacks and kernel pairs.

  Cone: a cone over a cospan A—f→C←g—B.
  HasPullback: a pullback (cone + universal property).  §1.454
  HasPullbacks: the category has all pullbacks.
  kernelPair f: pullback of f along f (§1.454).
  monic_iff_kp_diag_iso: f monic ↔ kp_diag f iso (§1.453).
  mono_pullback: pullback of a monic is monic (§1.45).
  invImg: inverse image f# : Sub(B) → Sub(A) (§1.451).
  Sub.inter: intersection of subobjects via pullback (§1.452).
  pullback_faithful_iff_preserves_properness: §1.453 Lemma.
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_33
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_51


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-- A cone over the cospan `A —f→ C ←g— B` (§1.454). -/
structure Cone {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  pt : 𝒞
  π₁ : pt ⟶ A
  π₂ : pt ⟶ B
  w  : π₁ ≫ f = π₂ ≫ g

/-- A pullback of the cospan `A —f→ C ←g— B`: a distinguished `cone` and
    universal lift.  §1.454 -/
class HasPullback {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) where
  cone : Cone f g
  lift      (c : Cone f g) : c.pt ⟶ cone.pt
  lift_fst  (c : Cone f g) : lift c ≫ cone.π₁ = c.π₁
  lift_snd  (c : Cone f g) : lift c ≫ cone.π₂ = c.π₂
  lift_uniq (c : Cone f g) (u : c.pt ⟶ cone.pt)
    (h₁ : u ≫ cone.π₁ = c.π₁) (h₂ : u ≫ cone.π₂ = c.π₂) : u = lift c

/-- The category has all pullbacks. -/
class HasPullbacks (𝒞 : Type u) [Cat.{v} 𝒞] where
  has {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g

/-- A cone is a PULLBACK if every cone over the same cospan factors uniquely
    through it (§1.454).  Predicate form, for stating that a given square is a
    pullback without fixing a choice of pullbacks. -/
def Cone.IsPullback {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} (c : Cone f g) : Prop :=
  ∀ d : Cone f g, ∃ u : d.pt ⟶ c.pt, (u ≫ c.π₁ = d.π₁ ∧ u ≫ c.π₂ = d.π₂) ∧
    ∀ v : d.pt ⟶ c.pt, v ≫ c.π₁ = d.π₁ → v ≫ c.π₂ = d.π₂ → v = u

/-- The chosen cone of a pullback is a pullback. -/
theorem HasPullback.cone_isPullback {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    (hp : HasPullback f g) : hp.cone.IsPullback := λ d =>
  ⟨hp.lift d, ⟨⟨hp.lift_fst d, hp.lift_snd d⟩, λ v h₁ h₂ => hp.lift_uniq d v h₁ h₂⟩⟩

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

/-- The kernel pair of `f` : pullback of `f` along itself.  §1.454 -/
def kernelPair {A B : 𝒞} (f : A ⟶ B) : 𝒞 := (hpull.has f f).cone.pt

section
variable {A B X : 𝒞} {f : A ⟶ B}

def kp₁ : kernelPair f ⟶ A := (hpull.has f f).cone.π₁
def kp₂ : kernelPair f ⟶ A := (hpull.has f f).cone.π₂

theorem kp_sq : kp₁ (f:=f) ≫ f = kp₂ (f:=f) ≫ f := (hpull.has f f).cone.w

/-- The diagonal cone `(A, 1_A, 1_A)` over the cospan `(f, f)`. -/
def diagCone : Cone f f := ⟨A, Cat.id A, Cat.id A, rfl⟩

def kp_diag : A ⟶ kernelPair f := (hpull.has f f).lift diagCone

/-- Spec of `kp_diag` (kept, not inlined): the stated type `= Cat.id A` pins `diagCone`'s cospan,
    which a bare `(hpull.has f f).lift_fst diagCone` inline cannot recover in the functor-category
    instance (`diagCone (f := α)` elaborates to `Cone ?m ?m`). -/
theorem kp_diag_p₁ : kp_diag (f:=f) ≫ kp₁ (f:=f) = Cat.id A := (hpull.has f f).lift_fst diagCone
theorem kp_diag_p₂ : kp_diag (f:=f) ≫ kp₂ (f:=f) = Cat.id A := (hpull.has f f).lift_snd diagCone

theorem kp_lift_p₁ (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ ≫ kp₁ (f:=f) = x₁ := (hpull.has f f).lift_fst _

theorem kp_lift_p₂ (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f) :
    (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ ≫ kp₂ (f:=f) = x₂ := (hpull.has f f).lift_snd _

theorem kp_lift_uniq (x₁ x₂ : X ⟶ A) (h : x₁ ≫ f = x₂ ≫ f)
    (g : X ⟶ kernelPair f) (h₁ : g ≫ kp₁ (f:=f) = x₁) (h₂ : g ≫ kp₂ (f:=f) = x₂) :
    g = (hpull.has f f).lift ⟨_, x₁, x₂, h⟩ := (hpull.has f f).lift_uniq ⟨_, x₁, x₂, h⟩ g h₁ h₂

/-- Lemma from §1.453: f is monic iff the diagonal into its kernel pair is iso. -/
theorem monic_iff_kp_diag_iso : Monic f ↔ IsIso (kp_diag (f:=f)) := by
  constructor
  · intro hm
    have h_eq : kp₁ (f:=f) = kp₂ (f:=f) := hm _ _ kp_sq
    refine ⟨kp₁ (f:=f), (hpull.has f f).lift_fst diagCone, ?_⟩
    have h_id : (hpull.has f f).lift ⟨_, kp₁ (f:=f), kp₂ (f:=f), kp_sq⟩ = Cat.id (kernelPair f) :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq (Cat.id (kernelPair f))
        (Cat.id_comp _) (Cat.id_comp _)).symm
    have h_comp : (kp₁ (f:=f)) ≫ kp_diag (f:=f) =
        (hpull.has f f).lift ⟨_, kp₁ (f:=f), kp₂ (f:=f), kp_sq⟩ :=
      (kp_lift_uniq (kp₁ (f:=f)) (kp₂ (f:=f)) kp_sq ((kp₁ (f:=f)) ≫ kp_diag (f:=f))
        (by rw [Cat.assoc, show kp_diag (f:=f) ≫ kp₁ (f:=f) = Cat.id A from
              (hpull.has f f).lift_fst diagCone, Cat.comp_id])
        (by rw [Cat.assoc, show kp_diag (f:=f) ≫ kp₂ (f:=f) = Cat.id A from
              (hpull.has f f).lift_snd diagCone, Cat.comp_id, h_eq]))
    rw [h_comp, h_id]
  · intro hiso
    obtain ⟨inv, _diag_inv, inv_diag⟩ := hiso
    intro X x₁ x₂ h
    let hpair : X ⟶ kernelPair f := (hpull.has f f).lift ⟨_, x₁, x₂, h⟩
    let t : X ⟶ A := hpair ≫ inv
    have ht : hpair = t ≫ kp_diag (f:=f) := by
      dsimp [t]; rw [Cat.assoc, inv_diag]; rw [Cat.comp_id]
    calc
      x₁ = hpair ≫ kp₁ (f:=f) := by rw [kp_lift_p₁ x₁ x₂ h]
      _ = (t ≫ kp_diag (f:=f)) ≫ kp₁ (f:=f) := by rw [ht]
      _ = t ≫ (kp_diag (f:=f) ≫ kp₁ (f:=f)) := by rw [Cat.assoc]
      _ = t ≫ Cat.id A := by
          rw [show kp_diag (f:=f) ≫ kp₁ (f:=f) = Cat.id A from (hpull.has f f).lift_fst diagCone]
      _ = t := by rw [Cat.comp_id]
      _ = t ≫ Cat.id A := by rw [Cat.comp_id]
      _ = t ≫ (kp_diag (f:=f) ≫ kp₂ (f:=f)) := by
          rw [show kp_diag (f:=f) ≫ kp₂ (f:=f) = Cat.id A from (hpull.has f f).lift_snd diagCone]
      _ = (t ≫ kp_diag (f:=f)) ≫ kp₂ (f:=f) := by rw [← Cat.assoc]
      _ = hpair ≫ kp₂ (f:=f) := by rw [ht]
      _ = x₂ := by rw [kp_lift_p₂ x₁ x₂ h]

end

/-! ## §1.45 Pullbacks transfer monics

  If `m : B → C` is monic and we pull it back along `f : A → C`, the resulting
  projection `π₁ : P → A` (where `P` is the pullback of `f` and `m`) is monic. -/

/-- §1.45: The pullback of a monic along any map is monic.
    Given the cospan `A —f→ C ←m— B` with `m` monic and `hp : HasPullback f m`,
    the first projection `hp.cone.π₁ : hp.cone.pt → A` is monic. -/
theorem mono_pullback {A B C : 𝒞} (f : A ⟶ C) (m : B ⟶ C) (hm : Monic m)
    (hp : HasPullback f m) : Monic hp.cone.π₁ := by
  intro W g h heq
  -- Derive g ≫ π₂ = h ≫ π₂ using m monic and the cone square π₁ ≫ f = π₂ ≫ m
  have hm2 : g ≫ hp.cone.π₂ = h ≫ hp.cone.π₂ := hm _ _ (by
    -- (x ≫ π₂) ≫ m = (x ≫ π₁) ≫ f  [by Cat.assoc + cone.w]
    -- so g ≫ π₁ = h ≫ π₁ (heq) gives equality
    rw [show (g ≫ hp.cone.π₂) ≫ m = (g ≫ hp.cone.π₁) ≫ f from by
          rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
        show (h ≫ hp.cone.π₂) ≫ m = (h ≫ hp.cone.π₁) ≫ f from by
          rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
        heq])
  -- g and h induce the same cone, so lift uniqueness gives g = h
  have hw : (g ≫ hp.cone.π₁) ≫ f = (g ≫ hp.cone.π₂) ≫ m := by
    simp only [Cat.assoc, hp.cone.w]
  have hlg : g = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
    hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ g rfl rfl
  have hlh : h = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
    hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ h heq.symm hm2.symm
  rw [hlg, hlh]

/-! ## §1.451 Inverse image f# : Sub(B) → Sub(A)

  Given `f : A → B` and a subobject `m : B' → B`, the INVERSE IMAGE `f# m` is the
  pullback of `m` along `f`, which lands as a subobject of `A`.  It is order-preserving
  and makes `Sub(−)` a contravariant functor. -/

/-- The inverse image of a subobject `S` of `B` along `f : A → B`,
    defined as the pullback of `S.arr` along `f`.  (Freyd §1.451, f#) -/
noncomputable def invImg {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 B)
    (hp : HasPullback f S.arr) : Subobject 𝒞 A where
  dom   := hp.cone.pt
  arr   := hp.cone.π₁
  monic := mono_pullback f S.arr S.monic hp

/-- §1.451: inverse image is order-preserving: if `S ≤ T` in `Sub(B)`, then
    `f# S ≤ f# T` in `Sub(A)`. -/
theorem invImg_le {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
    (hS : HasPullback f S.arr) (hT : HasPullback f T.arr)
    (hle : S.le T) : (invImg f S hS).le (invImg f T hT) := by
  obtain ⟨k, hk⟩ := hle
  -- π₂_S ≫ k : hS.cone.pt → T.dom satisfies (π₂_S ≫ k) ≫ T.arr = π₁_S ≫ f
  have hw : hS.cone.π₁ ≫ f = (hS.cone.π₂ ≫ k) ≫ T.arr := by
    rw [Cat.assoc, hk, ← hS.cone.w]
  exact ⟨hT.lift ⟨hS.cone.pt, hS.cone.π₁, hS.cone.π₂ ≫ k, hw⟩, hT.lift_fst _⟩

/-- §1.451: `Sub(−)` is a contravariant functor: `f# ∘ g# = (f ≫ g)#` up to ≅.
    Pullback pasting: the composite pullback of S along g then along f equals
    the pullback of S along (f ≫ g). -/
theorem invImg_comp {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (S : Subobject 𝒞 C)
    (hfg : HasPullback (f ≫ g) S.arr)
    (hg  : HasPullback g S.arr)
    (hf  : HasPullback f (invImg g S hg).arr) :
    (invImg (f ≫ g) S hfg).le (invImg f (invImg g S hg) hf) ∧
    (invImg f (invImg g S hg) hf).le (invImg (f ≫ g) S hfg) := by
  -- invImg g S hg : dom = hg.cone.pt, arr = hg.cone.π₁
  -- invImg f (invImg g S hg) hf : dom = hf.cone.pt, arr = hf.cone.π₁
  -- hf is pullback of f along hg.cone.π₁
  -- hfg is pullback of (f≫g) along S.arr
  -- Forward: from hfg.cone.pt we build a map to hf.cone.pt
  --   Step 1: hfg.cone.π₁ ≫ f lands in hg via: (hfg.π₁ ≫ f) ≫ g = hfg.π₂ ≫ S.arr
  --   Step 2: lift to hf.cone.pt via f and above map into hg.cone.pt
  constructor
  · -- (f≫g)#S ≤ f#(g#S)
    -- u : hfg.cone.pt → hg.cone.pt with u ≫ hg.cone.π₁ = hfg.cone.π₁ ≫ f
    have hw_g : (hfg.cone.π₁ ≫ f) ≫ g = hfg.cone.π₂ ≫ S.arr := by
      rw [Cat.assoc]; exact hfg.cone.w
    let u := hg.lift ⟨hfg.cone.pt, hfg.cone.π₁ ≫ f, hfg.cone.π₂, hw_g⟩
    have hu_π₁ : u ≫ hg.cone.π₁ = hfg.cone.π₁ ≫ f := hg.lift_fst _
    -- v : hfg.cone.pt → hf.cone.pt with v ≫ hf.cone.π₁ = hfg.cone.π₁
    -- hf is the pullback of f along hg.cone.π₁ = (invImg g S hg).arr
    have hw_f : hfg.cone.π₁ ≫ f = u ≫ hg.cone.π₁ := hu_π₁.symm
    let v := hf.lift ⟨hfg.cone.pt, hfg.cone.π₁, u, hw_f⟩
    exact ⟨v, hf.lift_fst _⟩
  · -- f#(g#S) ≤ (f≫g)#S
    -- From hf.cone.pt we map to hfg.cone.pt
    -- hf.cone: π₁ : hf.cone.pt → A, π₂ : hf.cone.pt → hg.cone.pt
    --   with hf.cone.π₁ ≫ f = hf.cone.π₂ ≫ hg.cone.π₁
    -- hg.cone: π₁ : hg.cone.pt → B, π₂ : hg.cone.pt → S.dom
    --   with hg.cone.π₁ ≫ g = hg.cone.π₂ ≫ S.arr
    -- So hf.cone.π₁ ≫ (f≫g) = hf.cone.π₂ ≫ (hg.cone.π₁ ≫ g)
    --                          = hf.cone.π₂ ≫ hg.cone.π₂ ≫ S.arr
    -- (invImg g S hg).arr = hg.cone.π₁ by def; hf.cone.w says π₁ ≫ f = π₂ ≫ (invImg g S hg).arr
    have hf_w : hf.cone.π₁ ≫ f = hf.cone.π₂ ≫ hg.cone.π₁ := hf.cone.w
    have hw : hf.cone.π₁ ≫ (f ≫ g) = (hf.cone.π₂ ≫ hg.cone.π₂) ≫ S.arr := by
      rw [← Cat.assoc, hf_w, Cat.assoc, hg.cone.w, Cat.assoc]
    let w := hfg.lift ⟨hf.cone.pt, hf.cone.π₁, hf.cone.π₂ ≫ hg.cone.π₂, hw⟩
    exact ⟨w, hfg.lift_fst _⟩

/-! ## §1.49(10) Pullback pasting lemma

  Two-square horizontal diagram:
  ```
  A --h--> B --k--> C
  |        |        |
  a        b        c
  v        v        v
  D --i--> E --j--> F
  ```
  `pullback_paste`:   left-square pb + right-square pb  ⟹  outer rectangle pb.
  `pullback_cancel`:  right-square pb + outer rectangle pb  ⟹  left-square pb.

  We use `Cone.IsPullback` (the predicate form) because the square apexes `A`, `B` are fixed
  objects whereas `HasPullback` wraps a *chosen* cone and the apex can differ. -/

/-- §1.49(10) PASTE: the outer rectangle is a pullback whenever both inner squares are.

    ```
    A --h--> B --k--> C
    |        |        |
    a        b        c
    v        v        v
    D --i--> E --j--> F
    ```
    Given: left-square cone `cL = ⟨A, h, a, w_L⟩` over `(b,i)` is a pullback,
           right-square cone `cR = ⟨B, k, b, w_R⟩` over `(c,j)` is a pullback.
    Produces: rectangle cone `⟨A, h≫k, a, _⟩` over `(c, i≫j)` is a pullback. -/
theorem pullback_paste
    {A B C D E F : 𝒞}
    {h : A ⟶ B} {k : B ⟶ C} {a : A ⟶ D} {b : B ⟶ E} {c : C ⟶ F}
    {i : D ⟶ E} {j : E ⟶ F}
    (w_L : h ≫ b = a ≫ i) (w_R : k ≫ c = b ≫ j)
    (hL : (Cone.mk A h a w_L).IsPullback)
    (hR : (Cone.mk B k b w_R).IsPullback) :
    (Cone.mk A (h ≫ k) a (by rw [Cat.assoc, w_R, ← Cat.assoc, w_L, Cat.assoc])).IsPullback := by
  intro d
  -- d : Cone c (i ≫ j), d.w : d.π₁ ≫ c = d.π₂ ≫ (i ≫ j)
  -- Step 1: lift into B via right pullback (right cospan: c, j)
  have hw_R : d.π₁ ≫ c = (d.π₂ ≫ i) ≫ j := by rw [Cat.assoc]; exact d.w
  obtain ⟨eR, ⟨heR_k, heR_b⟩, heR_uniq⟩ := hR ⟨d.pt, d.π₁, d.π₂ ≫ i, hw_R⟩
  -- eR : d.pt ⟶ B, eR ≫ k = d.π₁, eR ≫ b = d.π₂ ≫ i  (definitionally)
  -- Step 2: lift into A via left pullback (left cospan: b, i)
  obtain ⟨eL, ⟨heL_h, heL_a⟩, heL_uniq⟩ := hL ⟨d.pt, eR, d.π₂, heR_b⟩
  -- eL : d.pt ⟶ A, eL ≫ h = eR, eL ≫ a = d.π₂  (definitionally)
  refine ⟨eL, ⟨?_, heL_a⟩, ?_⟩
  · -- eL ≫ (h ≫ k) = d.π₁
    show eL ≫ h ≫ k = d.π₁
    rw [← Cat.assoc, heL_h, heR_k]
  · -- uniqueness: any v with v ≫ (h≫k) = d.π₁ and v ≫ a = d.π₂ equals eL
    intro v hv_hk hv_a
    -- The goals hv_hk, hv_a reduce definitionally:
    --   hv_hk : v ≫ (h ≫ k) = d.π₁
    --   hv_a  : v ≫ a = d.π₂
    -- v ≫ h is a cone over (c, j) with legs (v ≫ h) ≫ k = d.π₁ and (v ≫ h) ≫ b = d.π₂ ≫ i
    have hw_v_R : (v ≫ h) ≫ k = d.π₁ := by rw [Cat.assoc]; exact hv_hk
    have hw_v_b : (v ≫ h) ≫ b = d.π₂ ≫ i :=
      calc (v ≫ h) ≫ b = v ≫ h ≫ b     := Cat.assoc _ _ _
        _ = v ≫ a ≫ i                    := congrArg (v ≫ ·) w_L
        _ = (v ≫ a) ≫ i                  := (Cat.assoc _ _ _).symm
        _ = d.π₂ ≫ i                     := congrArg (· ≫ i) hv_a
    -- eR is unique in the right pb for cone (d.π₁, d.π₂ ≫ i), so v ≫ h = eR
    have heq_R : v ≫ h = eR := heR_uniq (v ≫ h) hw_v_R hw_v_b
    -- v and eL are both lifts into A with same projections, unique in left pb
    exact heL_uniq v heq_R hv_a

/-- §1.49(10) CANCEL (right-paste converse): if the right square is a pullback and the outer
    rectangle is a pullback, then the left square is a pullback.

    ```
    A --h--> B --k--> C
    |        |        |
    a        b        c
    v        v        v
    D --i--> E --j--> F
    ```
    Given: right-square cone `cR = ⟨B, k, b, w_R⟩` over `(c,j)` is a pullback,
           rectangle cone `⟨A, h≫k, a, _⟩` over `(c, i≫j)` is a pullback.
    Produces: left-square cone `cL = ⟨A, h, a, w_L⟩` over `(b,i)` is a pullback. -/
theorem pullback_cancel
    {A B C D E F : 𝒞}
    {h : A ⟶ B} {k : B ⟶ C} {a : A ⟶ D} {b : B ⟶ E} {c : C ⟶ F}
    {i : D ⟶ E} {j : E ⟶ F}
    (w_L : h ≫ b = a ≫ i) (w_R : k ≫ c = b ≫ j)
    (hR   : (Cone.mk B k b w_R).IsPullback)
    (hRect : (Cone.mk A (h ≫ k) a (by rw [Cat.assoc, w_R, ← Cat.assoc, w_L, Cat.assoc])).IsPullback) :
    (Cone.mk A h a w_L).IsPullback := by
  intro d
  -- d : Cone b i, d.w : d.π₁ ≫ b = d.π₂ ≫ i
  -- Form a cone over (c, i≫j) with apex d.pt via the rectangle:
  --   π₁ = d.π₁ ≫ k,  π₂ = d.π₂
  have hw_rect : (d.π₁ ≫ k) ≫ c = d.π₂ ≫ i ≫ j := by
    rw [Cat.assoc, w_R, ← Cat.assoc, d.w, Cat.assoc]
  obtain ⟨eA, ⟨heA_hk, heA_a⟩, heA_uniq⟩ := hRect ⟨d.pt, d.π₁ ≫ k, d.π₂, hw_rect⟩
  -- eA : d.pt ⟶ A, eA ≫ (h ≫ k) = d.π₁ ≫ k, eA ≫ a = d.π₂  (definitionally)
  -- Show eA ≫ h = d.π₁ using uniqueness of the right pullback.
  -- Both (eA ≫ h) and d.π₁ map into B and lift the cone (d.π₁ ≫ k, d.π₁ ≫ b) over (c,j):
  have hw_dR : (d.π₁ ≫ k) ≫ c = (d.π₁ ≫ b) ≫ j := by rw [Cat.assoc, Cat.assoc, w_R]
  obtain ⟨eB, ⟨heB_k, heB_b⟩, heB_uniq⟩ := hR ⟨d.pt, d.π₁ ≫ k, d.π₁ ≫ b, hw_dR⟩
  -- d.π₁ lifts trivially:
  have hd_eq : d.π₁ = eB := heB_uniq d.π₁ rfl rfl
  -- eA ≫ h lifts: (eA ≫ h) ≫ k = eA ≫ (h ≫ k) = d.π₁ ≫ k
  have heAh_k : (eA ≫ h) ≫ k = d.π₁ ≫ k := by rw [Cat.assoc]; exact heA_hk
  -- (eA ≫ h) ≫ b = eA ≫ (h ≫ b) = eA ≫ (a ≫ i) = (eA ≫ a) ≫ i = d.π₂ ≫ i = d.π₁ ≫ b
  have heAh_b : (eA ≫ h) ≫ b = d.π₁ ≫ b :=
    calc (eA ≫ h) ≫ b = eA ≫ h ≫ b   := Cat.assoc _ _ _
      _ = eA ≫ a ≫ i                   := congrArg (eA ≫ ·) w_L
      _ = (eA ≫ a) ≫ i                 := (Cat.assoc _ _ _).symm
      _ = d.π₂ ≫ i                     := congrArg (· ≫ i) heA_a
      _ = d.π₁ ≫ b                     := d.w.symm
  have heA_h : eA ≫ h = d.π₁ :=
    (heB_uniq (eA ≫ h) heAh_k heAh_b).trans hd_eq.symm
  refine ⟨eA, ⟨heA_h, heA_a⟩, ?_⟩
  -- uniqueness: any v with v ≫ h = d.π₁ and v ≫ a = d.π₂ equals eA
  intro v hv_h hv_a
  apply heA_uniq
  · -- v ≫ (h ≫ k) = d.π₁ ≫ k
    show v ≫ h ≫ k = d.π₁ ≫ k
    rw [← Cat.assoc, hv_h]
  · exact hv_a

/-- The intersection of two subobjects of `A` via the pullback of their monics.
    §1.452: the resulting subobject is the glb of `S` and `T` in `Sub(A)`. -/
noncomputable def Sub.inter {A : 𝒞} (S T : Subobject 𝒞 A)
    (hp : HasPullback S.arr T.arr) : Subobject 𝒞 A where
  dom   := hp.cone.pt
  arr   := hp.cone.π₁ ≫ S.arr
  monic := by
    -- π₁ ≫ S.arr is monic: if g ≫ (π₁ ≫ S.arr) = h ≫ (π₁ ≫ S.arr), derive g = h.
    -- Step 1: S.arr monic → g ≫ π₁ = h ≫ π₁.
    -- Step 2: cone square + T.arr monic → g ≫ π₂ = h ≫ π₂.
    -- Step 3: lift uniqueness → g = h.
    intro W g h heq
    have hπ₁ : g ≫ hp.cone.π₁ = h ≫ hp.cone.π₁ :=
      S.monic _ _ (by rw [Cat.assoc, Cat.assoc]; exact heq)
    have hπ₂ : g ≫ hp.cone.π₂ = h ≫ hp.cone.π₂ := T.monic _ _ (by
      -- (x ≫ π₂) ≫ T.arr = (x ≫ π₁) ≫ S.arr  [Cat.assoc + cone.w symm]
      rw [show (g ≫ hp.cone.π₂) ≫ T.arr = (g ≫ hp.cone.π₁) ≫ S.arr from by
            rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
          show (h ≫ hp.cone.π₂) ≫ T.arr = (h ≫ hp.cone.π₁) ≫ S.arr from by
            rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc],
          hπ₁])
    have hw : (g ≫ hp.cone.π₁) ≫ S.arr = (g ≫ hp.cone.π₂) ≫ T.arr := by
      simp only [Cat.assoc, hp.cone.w]
    have hlg : g = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
      hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ g rfl rfl
    have hlh : h = hp.lift ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ :=
      hp.lift_uniq ⟨W, g ≫ hp.cone.π₁, g ≫ hp.cone.π₂, hw⟩ h hπ₁.symm hπ₂.symm
    rw [hlg, hlh]

/-- §1.452: the intersection is a lower bound: `S ∩ T ≤ S`. -/
theorem Sub.inter_le_left {A : 𝒞} (S T : Subobject 𝒞 A) (hp : HasPullback S.arr T.arr) :
    (Sub.inter S T hp).le S :=
  ⟨hp.cone.π₁, rfl⟩

/-- §1.452: the intersection is a lower bound: `S ∩ T ≤ T`. -/
theorem Sub.inter_le_right {A : 𝒞} (S T : Subobject 𝒞 A) (hp : HasPullback S.arr T.arr) :
    (Sub.inter S T hp).le T :=
  ⟨hp.cone.π₂, hp.cone.w.symm⟩

/-- §1.452: the intersection is the greatest lower bound: any common lower bound
    factors through it. -/
theorem Sub.inter_glb {A : 𝒞} (S T U : Subobject 𝒞 A) (hp : HasPullback S.arr T.arr)
    (hS : U.le S) (hT : U.le T) : U.le (Sub.inter S T hp) := by
  obtain ⟨ks, hks⟩ := hS
  obtain ⟨kt, hkt⟩ := hT
  have hw : ks ≫ S.arr = kt ≫ T.arr := by rw [hks, hkt]
  let u := hp.lift ⟨U.dom, ks, kt, hw⟩
  refine ⟨u, ?_⟩
  -- (Sub.inter S T hp).arr = hp.cone.π₁ ≫ S.arr; u ≫ π₁ = ks; ks ≫ S.arr = U.arr
  show u ≫ hp.cone.π₁ ≫ S.arr = U.arr
  rw [← Cat.assoc, hp.lift_fst _, hks]

/-- §1.452: inverse image `f#` preserves intersections: `f#(S ∩ T) ≅ f#S ∩ f#T`. -/
theorem invImg_preserves_inter {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
    (hST   : HasPullback S.arr T.arr)
    (hfST  : HasPullback f (Sub.inter S T hST).arr)
    (hfS   : HasPullback f S.arr)
    (hfT   : HasPullback f T.arr)
    (hfSfT : HasPullback (invImg f S hfS).arr (invImg f T hfT).arr) :
    (invImg f (Sub.inter S T hST) hfST).le
      (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT) ∧
    (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT).le
      (invImg f (Sub.inter S T hST) hfST) := by
  -- Extract cone equations as plain Prop values, avoiding rewrites that change types of local vars.
  -- (Sub.inter S T hST).arr = hST.cone.π₁ ≫ S.arr  (definitionally)
  -- (invImg f S hfS).arr = hfS.cone.π₁              (definitionally)
  -- (invImg f T hfT).arr = hfT.cone.π₁              (definitionally)
  -- hfST.cone.w : π₁ ≫ f = π₂ ≫ (hST.cone.π₁ ≫ S.arr)  — but Lean sees (Sub.inter).arr
  -- We extract these using type ascription to force unfolding:
  have hfST_w : hfST.cone.π₁ ≫ f = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr :=
    show hfST.cone.π₁ ≫ f = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr from hfST.cone.w
  have hfS_w  : hfS.cone.π₁  ≫ f = hfS.cone.π₂  ≫ S.arr              := hfS.cone.w
  have hfT_w  : hfT.cone.π₁  ≫ f = hfT.cone.π₂  ≫ T.arr              := hfT.cone.w
  have hST_w  : hST.cone.π₁  ≫ S.arr = hST.cone.π₂ ≫ T.arr          := hST.cone.w
  have hfSfT_w : hfSfT.cone.π₁ ≫ hfS.cone.π₁ = hfSfT.cone.π₂ ≫ hfT.cone.π₁ :=
    show hfSfT.cone.π₁ ≫ hfS.cone.π₁ = hfSfT.cone.π₂ ≫ hfT.cone.π₁ from hfSfT.cone.w
  constructor
  · -- f#(S∩T) ≤ f#S ∩ f#T
    -- u_S : hfST.cone.pt → hfS.cone.pt
    have hw_S : hfST.cone.π₁ ≫ f = (hfST.cone.π₂ ≫ hST.cone.π₁) ≫ S.arr :=
      hfST_w.trans (Cat.assoc _ _ _).symm
    let u_S := hfS.lift ⟨hfST.cone.pt, hfST.cone.π₁, hfST.cone.π₂ ≫ hST.cone.π₁, hw_S⟩
    have hu_S : u_S ≫ hfS.cone.π₁ = hfST.cone.π₁ := hfS.lift_fst _
    -- u_T : hfST.cone.pt → hfT.cone.pt
    have hw_T : hfST.cone.π₁ ≫ f = (hfST.cone.π₂ ≫ hST.cone.π₂) ≫ T.arr :=
      calc hfST.cone.π₁ ≫ f
          = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr  := hfST_w
        _ = (hfST.cone.π₂ ≫ hST.cone.π₁) ≫ S.arr := (Cat.assoc _ _ _).symm
        _ = (hfST.cone.π₂ ≫ hST.cone.π₁) ≫ S.arr := rfl
        _ = hfST.cone.π₂ ≫ hST.cone.π₁ ≫ S.arr   := Cat.assoc _ _ _
        _ = hfST.cone.π₂ ≫ hST.cone.π₂ ≫ T.arr   := by rw [hST_w]
        _ = (hfST.cone.π₂ ≫ hST.cone.π₂) ≫ T.arr := (Cat.assoc _ _ _).symm
    let u_T := hfT.lift ⟨hfST.cone.pt, hfST.cone.π₁, hfST.cone.π₂ ≫ hST.cone.π₂, hw_T⟩
    have hu_T : u_T ≫ hfT.cone.π₁ = hfST.cone.π₁ := hfT.lift_fst _
    -- u_S and u_T agree → lift into hfSfT
    have hw_SfT : u_S ≫ hfS.cone.π₁ = u_T ≫ hfT.cone.π₁ := by rw [hu_S, hu_T]
    -- need the cone equation for hfSfT: (invImg f S hfS).arr = hfS.cone.π₁  definitionally
    have hw_SfT' : u_S ≫ (invImg f S hfS).arr = u_T ≫ (invImg f T hfT).arr := hw_SfT
    let v := hfSfT.lift ⟨hfST.cone.pt, u_S, u_T, hw_SfT'⟩
    refine ⟨v, ?_⟩
    -- goal: v ≫ (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT).arr = hfST.cone.π₁
    -- .arr = hfSfT.cone.π₁ ≫ (invImg f S hfS).arr = hfSfT.cone.π₁ ≫ hfS.cone.π₁  (def)
    show v ≫ hfSfT.cone.π₁ ≫ hfS.cone.π₁ = hfST.cone.π₁
    rw [← Cat.assoc, hfSfT.lift_fst _, hu_S]
  · -- f#S ∩ f#T ≤ f#(S∩T)
    -- Step 1: map hfSfT.cone.pt → hST.cone.pt
    have hw_ST : (hfSfT.cone.π₁ ≫ hfS.cone.π₂) ≫ S.arr = (hfSfT.cone.π₂ ≫ hfT.cone.π₂) ≫ T.arr :=
      calc (hfSfT.cone.π₁ ≫ hfS.cone.π₂) ≫ S.arr
          = hfSfT.cone.π₁ ≫ hfS.cone.π₂ ≫ S.arr   := Cat.assoc _ _ _
        _ = hfSfT.cone.π₁ ≫ hfS.cone.π₁ ≫ f       := by rw [← hfS_w]
        _ = hfSfT.cone.π₂ ≫ hfT.cone.π₁ ≫ f       := by rw [← Cat.assoc, hfSfT_w, Cat.assoc]
        _ = hfSfT.cone.π₂ ≫ hfT.cone.π₂ ≫ T.arr   := by rw [← hfT_w]
        _ = (hfSfT.cone.π₂ ≫ hfT.cone.π₂) ≫ T.arr := (Cat.assoc _ _ _).symm
    let u_ST := hST.lift ⟨hfSfT.cone.pt, hfSfT.cone.π₁ ≫ hfS.cone.π₂,
                                           hfSfT.cone.π₂ ≫ hfT.cone.π₂, hw_ST⟩
    have hu_ST_π₁ : u_ST ≫ hST.cone.π₁ = hfSfT.cone.π₁ ≫ hfS.cone.π₂ := hST.lift_fst _
    -- Step 2: map hfSfT.cone.pt → hfST.cone.pt
    -- need: (hfSfT.cone.π₁ ≫ hfS.cone.π₁) ≫ f = u_ST ≫ (Sub.inter S T hST).arr
    have hw_fST : (hfSfT.cone.π₁ ≫ hfS.cone.π₁) ≫ f = u_ST ≫ (Sub.inter S T hST).arr :=
      calc (hfSfT.cone.π₁ ≫ hfS.cone.π₁) ≫ f
          = hfSfT.cone.π₁ ≫ hfS.cone.π₁ ≫ f           := Cat.assoc _ _ _
        _ = hfSfT.cone.π₁ ≫ hfS.cone.π₂ ≫ S.arr       := by rw [← hfS_w]
        _ = (hfSfT.cone.π₁ ≫ hfS.cone.π₂) ≫ S.arr     := (Cat.assoc _ _ _).symm
        _ = (u_ST ≫ hST.cone.π₁) ≫ S.arr               := congrArg (· ≫ S.arr) hu_ST_π₁.symm
        _ = u_ST ≫ hST.cone.π₁ ≫ S.arr                 := Cat.assoc _ _ _
        _ = u_ST ≫ (Sub.inter S T hST).arr              := rfl
    let w := hfST.lift ⟨hfSfT.cone.pt, hfSfT.cone.π₁ ≫ hfS.cone.π₁, u_ST, hw_fST⟩
    refine ⟨w, ?_⟩
    -- goal: w ≫ (invImg f (Sub.inter S T hST) hfST).arr = (Sub.inter (invImg f S hfS) (invImg f T hfT) hfSfT).arr
    -- .arr on left = hfST.cone.π₁, .arr on right = hfSfT.cone.π₁ ≫ hfS.cone.π₁  (def)
    show w ≫ hfST.cone.π₁ = hfSfT.cone.π₁ ≫ hfS.cone.π₁
    exact hfST.lift_fst _

/-! ## §1.453 (abstract) monic ↔ diagonal-of-level iso, for an arbitrary pullback cone

  `monic_iff_kp_diag_iso` is stated for the *chosen* kernel pair, which needs
  `HasPullbacks`.  The §1.453 lemma below applies it in the target category `ℬ`,
  where we have only a single concrete pullback cone (the `T`-image of the level
  of `f`) and *no* `HasPullbacks ℬ`.  This abstract version takes the pullback
  cone and a diagonal as data, mirroring `monic_iff_kp_diag_iso` verbatim. -/

-- The abstract facts below must NOT drag in the Cartesian instances of `𝒞`: they are
-- reused in the target category `ℬ` (the `T`-image of a level), where we have no
-- `HasTerminal/HasBinaryProducts/HasPullbacks`.  (`Level` is fine: its fields fix no
-- such dependency; the `omit … in` guards the theorems.)
/-- A "level" of `f`: a pullback cone over the cospan `(f, f)` together with a
    diagonal `δ` (the comparison `A → c.pt` induced by `(1_A, 1_A)`). -/
structure Level {A B : 𝒞} (f : A ⟶ B) where
  c : Cone f f
  hpb : c.IsPullback
  δ : A ⟶ c.pt
  δ₁ : δ ≫ c.π₁ = Cat.id A
  δ₂ : δ ≫ c.π₂ = Cat.id A

omit ht hp hpull in
/-- §1.453 / §1.454: `f` is monic iff its diagonal `δ : A → L` into a level `L`
    is an isomorphism.  Abstracted away from `HasPullbacks` so it can be reused
    in any target category for the image of a level. -/
theorem mono_iff_level_diag_iso {A B : 𝒞} {f : A ⟶ B} (L : Level f) :
    Monic f ↔ IsIso L.δ := by
  obtain ⟨c, hpb, δ, δ₁, δ₂⟩ := L
  constructor
  · intro hm
    -- f monic ⇒ π₁ = π₂, so π₁ is a two-sided inverse of δ.
    have h_eq : c.π₁ = c.π₂ := hm _ _ c.w
    refine ⟨c.π₁, δ₁, ?_⟩
    -- π₁ ≫ δ = id : both are the unique lift of the cone (π₁, π₂) into the pullback.
    obtain ⟨lift_pp, ⟨hpp₁, hpp₂⟩, huniq⟩ := hpb c
    have h_id : Cat.id c.pt = lift_pp := huniq _ (Cat.id_comp _) (Cat.id_comp _)
    have h_comp : c.π₁ ≫ δ = lift_pp := huniq _
      (by rw [Cat.assoc, δ₁, Cat.comp_id])
      (by rw [Cat.assoc, δ₂, Cat.comp_id, h_eq])
    rw [h_comp, ← h_id]
  · intro hiso
    obtain ⟨inv, _diag_inv, inv_diag⟩ := hiso
    intro X x₁ x₂ h
    -- (x₁, x₂) is a cone over (f,f); let p be its lift into the pullback.
    obtain ⟨p, ⟨hp₁, hp₂⟩, _⟩ := hpb ⟨X, x₁, x₂, h⟩
    let t : X ⟶ A := p ≫ inv
    have ht : p = t ≫ δ := by dsimp only [t]; rw [Cat.assoc, inv_diag, Cat.comp_id]
    calc
      x₁ = p ≫ c.π₁ := hp₁.symm
      _ = (t ≫ δ) ≫ c.π₁ := by rw [ht]
      _ = t ≫ δ ≫ c.π₁ := Cat.assoc _ _ _
      _ = t ≫ Cat.id A := by rw [δ₁]
      _ = t := Cat.comp_id _
      _ = t ≫ Cat.id A := (Cat.comp_id _).symm
      _ = t ≫ δ ≫ c.π₂ := by rw [δ₂]
      _ = (t ≫ δ) ≫ c.π₂ := (Cat.assoc _ _ _).symm
      _ = p ≫ c.π₂ := by rw [ht]
      _ = x₂ := hp₂

/-! ## §1.453 LEMMA: pullback-preserving functor faithful ↔ preserves properness

  A functor `T : A → B` that preserves pullbacks is faithful if and only if it
  preserves *properness* of subobjects: i.e. a non-iso mono maps to a non-iso mono. -/

/-- T PRESERVES PULLBACKS: for every pullback cone in `𝒜`, the image cone in `ℬ`
    is also a pullback. -/
def PreservesPullbacks {𝒜 : Type u₁} {ℬ : Type u₂} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ) : Prop :=
  ∀ {A B C : 𝒜} (f : A ⟶ C) (g : B ⟶ C) (c : Cone f g),
    c.IsPullback →
    (Cone.mk (T.obj c.pt) (T.map c.π₁) (T.map c.π₂)
      (by rw [← T.map_comp, ← T.map_comp, c.w])).IsPullback

/-- T PRESERVES PROPERNESS: a non-iso monic maps to a non-iso monic (§1.453). -/
def PreservesProperness {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ) : Prop :=
  ∀ {A' A : 𝒜} (m : A' ⟶ A), Monic m → ¬IsIso m → ¬IsIso (T.map m)

/-- T PRESERVES PRODUCT-MONICITY: the image projections `T fst, T snd` remain a
    monic pair (jointly left-cancellable), so a map into `T(A×B)` is determined by
    its two legs.  This is the product-half of Freyd's "representation of a
    Cartesian category" (§1.472), stated in the only form available when the
    codomain `ℬ` need not have its own products (unlike the §1.437
    `PreservesBinaryProducts`, which asks the comparison `T(A×B) → TA×TB` to be
    iso and hence requires `HasBinaryProducts ℬ`).  `PreservesPullbacks` alone does
    NOT supply this — `(T fst, T snd)` need not stay jointly monic — which is the
    genuine gap in the `Faithful` direction; adding it makes §1.453 true as stated. -/
def PreservesProductMonic {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [HasBinaryProducts 𝒜] (T : Functor 𝒜 ℬ) : Prop :=
  ∀ {A B : 𝒜}, MonicPair (T.map (fst (A := A) (B := B))) (T.map snd)

/-- The canonical level of `f`, built from the chosen kernel pair. -/
noncomputable def canonicalLevel {A B : 𝒞} (f : A ⟶ B) : Level f where
  c := (hpull.has f f).cone
  hpb := (hpull.has f f).cone_isPullback
  δ := kp_diag (f := f)
  δ₁ := (hpull.has f f).lift_fst diagCone
  δ₂ := (hpull.has f f).lift_snd diagCone

omit ht hp hpull in
/-- The diagonal of a level is a split mono (`δ ≫ π₁ = id`), hence monic. -/
theorem Level.diag_mono {A B : 𝒞} {f : A ⟶ B} (L : Level f) : Monic L.δ := by
  intro W g h heq
  have heq2 : g ≫ Cat.id A = h ≫ Cat.id A := by
    rw [← L.δ₁, ← Cat.assoc, ← Cat.assoc, heq]
  rw [Cat.comp_id, Cat.comp_id] at heq2
  exact heq2

/-- The `T`-image of a level of `f` is a level of `T f` (T preserves the level
    pullback; the diagonal equations are functorial). -/
noncomputable def Level.map {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ) (hpb : PreservesPullbacks T)
    {A B : 𝒜} {f : A ⟶ B} (L : Level f) : Level (T.map f) where
  c := Cone.mk (T.obj L.c.pt) (T.map L.c.π₁) (T.map L.c.π₂)
        (by rw [← T.map_comp, ← T.map_comp, L.c.w])
  hpb := hpb f f L.c L.hpb
  δ := T.map L.δ
  δ₁ := by rw [show T.map L.δ ≫ T.map L.c.π₁ = T.map (L.δ ≫ L.c.π₁) from
              (T.map_comp _ _).symm, L.δ₁, T.map_id]
  δ₂ := by rw [show T.map L.δ ≫ T.map L.c.π₂ = T.map (L.δ ≫ L.c.π₂) from
              (T.map_comp _ _).symm, L.δ₂, T.map_id]

/-- §1.453: a pullback-preserving, properness-preserving functor REFLECTS MONICS.
    This is the explicit content of Freyd's argument: `f` monic ⟺ its diagonal is
    iso; properness (contrapositive, classically) propagates non-iso of the
    diagonal through `T`; so `T f` monic forces `f` monic. -/
theorem reflectsMono {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [HasTerminal 𝒜] [HasBinaryProducts 𝒜] [HasPullbacks 𝒜]
    (T : Functor 𝒜 ℬ) (hpb : PreservesPullbacks T)
    (hprop : PreservesProperness T) {A B : 𝒜} (f : A ⟶ B) (hm : Monic (T.map f)) :
    Monic f := by
  -- Classical contrapositive: if f not monic, the level diagonal δ is a non-iso mono,
  -- so T δ is non-iso (properness), so T f is not monic — contradiction.
  by_cases hnm : Monic f
  · exact hnm
  · exfalso
    let L := canonicalLevel f
    have hδ_niso : ¬IsIso L.δ := fun h => hnm ((mono_iff_level_diag_iso L).2 h)
    have hTδ_niso : ¬IsIso (T.map L.δ) := hprop L.δ L.diag_mono hδ_niso
    -- T δ is the diagonal of the image level of T f; T f monic ⇒ that diagonal iso.
    exact hTδ_niso ((mono_iff_level_diag_iso (L.map T hpb)).1 hm)

/-- §1.453 LEMMA: if `𝒜` is Cartesian and `T : 𝒜 → ℬ` preserves pullbacks, then
    `T` is faithful iff it preserves properness of subobjects.

    Freyd's argument:
    - (⇒) T faithful ⇒ T reflects isos ⇒ non-iso mono stays non-iso under T.
    - (⇐) Given `f` not monic, its kernel pair diagonal `A → kp(f)` is not iso
      (§1.453 / `monic_iff_kp_diag_iso`); T preserves this pullback so `T(diag)` is
      the diagonal for `T(f)`'s kernel pair; T preserves properness so `T(diag)` is
      not iso; hence `T(f)` is not monic.  Contrapositive: T reflects monics.
      For faithfulness, Freyd equates "reflects monics" (when pullbacks are preserved)
      with hom-injectivity.

    The `Faithful` direction additionally needs `T` to preserve binary products
    (Freyd's §1.472 "representation of a Cartesian category"): `PreservesPullbacks`
    alone leaves `(T fst, T snd)` possibly non–jointly-monic, so it cannot force
    `T⟨1,f⟩ = T⟨1,g⟩` from `T f = T g`.  We therefore take `PreservesProductMonic T`
    as a hypothesis, making the statement true as written. -/
theorem pullback_faithful_iff_preserves_properness
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [HasTerminal 𝒜] [HasBinaryProducts 𝒜] [HasPullbacks 𝒜]
    (T : Functor 𝒜 ℬ)
    (hpb : PreservesPullbacks T) (hpbp : PreservesProductMonic T) :
    Faithful T ↔ PreservesProperness T := by
  constructor
  · -- (⇒) Faithful T → PreservesProperness T
    -- T faithful → T reflects isomorphisms → non-iso mono stays non-iso.
    intro ⟨_, hRefl⟩ A' A m _ hniso hTiso
    exact hniso (hRefl m hTiso)
  · -- (⇐) PreservesProperness T → Faithful T (§1.453).
    -- The substantive book content — "Hence T reflects monics" — is DISCHARGED as
    -- `reflectsMono` above.  `Faithful = Embedding ∧ (reflects isos)`; we prove both.
    intro hprop
    -- Reflecting isos first: it is reused inside the embedding step.
    have hRefl : ∀ {A B : 𝒜} (f : A ⟶ B), IsIso (T.map f) → IsIso f := by
      intro A B f hiso
      -- IsIso (T f) ⇒ Monic (T f) ⇒ Monic f (reflectsMono).
      have hmono : Monic f :=
        reflectsMono T hpb hprop f
          (by obtain ⟨i, h1, _⟩ := hiso; intro W p q hpq;
              have := congrArg (· ≫ i) hpq; simp only [Cat.assoc, h1, Cat.comp_id] at this;
              exact this)
      -- f mono; if f were not iso it would be a proper mono, so T f non-iso — contradiction.
      by_cases hf : IsIso f
      · exact hf
      · exact absurd hiso (hprop f hmono hf)
    refine ⟨?emb, hRefl⟩
    -- Embedding: T f = T g → f = g.
    intro A B f g hTfg
    -- The equalizer of `f, g` is the pullback of `⟨1,f⟩, ⟨1,g⟩ : A → A×B`:
    -- a cone `(x,y)` with `x≫⟨1,f⟩ = y≫⟨1,g⟩` forces `x = y` (post `fst`) and
    -- `x≫f = x≫g` (post `snd`); so the apex equalizes `f, g`.
    -- (`set` is a Mathlib tactic, unavailable here; use plain `let`s — `u`, `v` unfold
    --  definitionally so `fst_pair`/`snd_pair` fire directly.)
    let u : A ⟶ prod A B := pair (Cat.id A) f
    let v : A ⟶ prod A B := pair (Cat.id A) g
    let P : HasPullback u v := HasPullbacks.has u v
    let e : P.cone.pt ⟶ A := P.cone.π₁
    -- The two pullback projections agree (both equal after postcomposing fst).
    have hπeq : P.cone.π₁ = P.cone.π₂ := by
      have hw : P.cone.π₁ ≫ u = P.cone.π₂ ≫ v := P.cone.w
      have h := congrArg (· ≫ fst) hw
      simpa [u, v, Cat.assoc, fst_pair, Cat.comp_id] using h
    -- e equalizes f, g.
    have heq : e ≫ f = e ≫ g := by
      have hw : P.cone.π₁ ≫ u = P.cone.π₂ ≫ v := P.cone.w
      have h := congrArg (· ≫ snd) hw
      simp only [u, v, Cat.assoc, snd_pair] at h
      -- h : P.cone.π₁ ≫ f = P.cone.π₂ ≫ g  ; rewrite π₂ = π₁
      show P.cone.π₁ ≫ f = P.cone.π₁ ≫ g
      rw [← hπeq] at h; exact h
    -- u is split mono (`u ≫ fst = 1`).
    have hu_split : u ≫ fst = Cat.id A := fst_pair _ _
    -- e is monic: both pullback projections coincide, and a cone is determined by its lift.
    have he_mono : Monic e := by
      intro W p q hpq
      -- hpq : p ≫ e = q ≫ e, i.e. p ≫ π₁ = q ≫ π₁; since π₂ = π₁ also p ≫ π₂ = q ≫ π₂.
      have hpq1 : p ≫ P.cone.π₁ = q ≫ P.cone.π₁ := hpq
      have hpq2 : p ≫ P.cone.π₂ = q ≫ P.cone.π₂ := by rw [← hπeq]; exact hpq1
      -- (p ≫ π₁, p ≫ π₂) is a cone over (u,v); p and q both lift it; uniqueness ⇒ p = q.
      have hcone : (p ≫ P.cone.π₁) ≫ u = (p ≫ P.cone.π₂) ≫ v := by
        rw [Cat.assoc, Cat.assoc, P.cone.w]
      have hp_uniq := P.lift_uniq ⟨W, p ≫ P.cone.π₁, p ≫ P.cone.π₂, hcone⟩ p rfl rfl
      have hq_uniq := P.lift_uniq ⟨W, p ≫ P.cone.π₁, p ≫ P.cone.π₂, hcone⟩ q hpq1.symm hpq2.symm
      rw [hp_uniq, hq_uniq]
    -- Now show `T e` is iso.  T f = T g ⇒ T u = T v (joint-monicity of T fst, T snd).
    have hTuv : T.map u = T.map v := by
      apply hpbp
      · -- post T fst : both = T(1_A)
        rw [← T.map_comp, ← T.map_comp, show u ≫ fst = Cat.id A from fst_pair _ _,
            show v ≫ fst = Cat.id A from fst_pair _ _]
      · -- post T snd : T f = T g
        rw [← T.map_comp, ← T.map_comp, show u ≫ snd = f from snd_pair _ _,
            show v ≫ snd = g from snd_pair _ _, hTfg]
    -- T carries the pullback to a pullback in ℬ; with T u = T v it is the KERNEL PAIR of T u.
    -- `T u` is split mono (T of split mono), hence monic; so the diagonal is iso, so T e iso.
    -- The image cone over the cospan (T u, T v).  Rewriting `T v = T u` (hTuv) turns it into a
    -- cone over (T u, T u) — a *level* of `T u` — and `PreservesPullbacks` makes it a pullback.
    -- Build that level by transporting along `hTuv`.
    have hTu_split : T.map u ≫ T.map (fst (A := A) (B := B)) = Cat.id (T.obj A) := by
      rw [← T.map_comp, hu_split, T.map_id]
    have hTu_mono : Monic (T.map u) := mono_of_retraction _ _ hTu_split
    -- The level of `T u`: cone (T pt, T π₁, T π₂) over (T u, T u), pullback, diagonal 1_{TA}.
    -- The image of P's cone is a pullback over the cospan (T u, T v).
    have himg : (Cone.mk (T.obj P.cone.pt) (T.map P.cone.π₁) (T.map P.cone.π₂)
        (show T.map P.cone.π₁ ≫ T.map u = T.map P.cone.π₂ ≫ T.map v by
          rw [← T.map_comp, ← T.map_comp, P.cone.w])).IsPullback :=
      hpb u v P.cone P.cone_isPullback
    -- A cone over (T u, T u) is a cone over (T u, T v) (the `w` data differs only by hTuv),
    -- so `himg`'s universal property transfers verbatim; this makes cTu a level of `T u`.
    let cTu : Cone (T.map u) (T.map u) :=
      Cone.mk (T.obj P.cone.pt) (T.map P.cone.π₁) (T.map P.cone.π₂)
        (calc T.map P.cone.π₁ ≫ T.map u
              = T.map (P.cone.π₁ ≫ u) := (T.map_comp _ _).symm
            _ = T.map (P.cone.π₂ ≫ v) := by rw [P.cone.w]
            _ = T.map P.cone.π₂ ≫ T.map v := T.map_comp _ _
            _ = T.map P.cone.π₂ ≫ T.map u := (congrArg (T.map P.cone.π₂ ≫ ·) hTuv).symm)
    have hcTu_pb : cTu.IsPullback := by
      intro d
      -- reinterpret d as a cone over (T u, T v) (legs identical; w via hTuv)
      have hdw : d.π₁ ≫ T.map u = d.π₂ ≫ T.map v :=
        d.w.trans (congrArg (d.π₂ ≫ ·) hTuv)
      obtain ⟨l, ⟨hl₁, hl₂⟩, hluniq⟩ := himg ⟨d.pt, d.π₁, d.π₂, hdw⟩
      exact ⟨l, ⟨hl₁, hl₂⟩, hluniq⟩
    obtain ⟨δ, ⟨hδ₁, hδ₂⟩, _⟩ := hcTu_pb
      ⟨T.obj A, Cat.id (T.obj A), Cat.id (T.obj A), (Cat.id_comp _).trans (Cat.id_comp _).symm⟩
    -- Assemble the level and invoke `mono_iff_level_diag_iso` in ℬ.
    have hδ_iso : IsIso δ :=
      (mono_iff_level_diag_iso (⟨cTu, hcTu_pb, δ, hδ₁, hδ₂⟩ : Level (T.map u))).1 hTu_mono
    -- δ ≫ (T π₁) = 1 with δ iso ⇒ T π₁ iso ⇒ T e iso.
    have hTe_iso : IsIso (T.map e) := by
      obtain ⟨δi, hδi1, hδi2⟩ := hδ_iso  -- hδi1 : δ ≫ δi = id ; hδi2 : δi ≫ δ = id
      -- hδ₁ : δ ≫ T e = 1.  Cancel δ on the left (δ split epi via δi): T e = δi.
      have hTe_eq : T.map e = δi := by
        calc T.map e = (δi ≫ δ) ≫ T.map e := by rw [hδi2, Cat.id_comp]
          _ = δi ≫ (δ ≫ T.map e) := Cat.assoc _ _ _
          _ = δi ≫ Cat.id _ := by rw [hδ₁]
          _ = δi := Cat.comp_id _
      -- e = P.cone.π₁ definitionally; T e = δi, δ ≫ δi = id, δi ≫ δ = id.
      exact ⟨δ, by show T.map P.cone.π₁ ≫ δ = _; rw [show T.map P.cone.π₁ = δi from hTe_eq, hδi2],
                by show δ ≫ T.map P.cone.π₁ = _; exact hδ₁⟩
    -- Finally: e monic and T e iso ⇒ (properness contrapositive) e iso; then cancel e on heq.
    have he_iso : IsIso e := by
      by_cases h : IsIso e
      · exact h
      · exact absurd hTe_iso (hprop e he_mono h)
    -- e iso ⇒ e is epi ⇒ cancel from e≫f = e≫g.
    obtain ⟨ei, hei1, hei2⟩ := he_iso
    calc f = (ei ≫ e) ≫ f := by rw [hei2, Cat.id_comp]
      _ = ei ≫ (e ≫ f) := Cat.assoc _ _ _
      _ = ei ≫ (e ≫ g) := by rw [heq]
      _ = (ei ≫ e) ≫ g := (Cat.assoc _ _ _).symm
      _ = g := by rw [hei2, Cat.id_comp]

end Freyd
