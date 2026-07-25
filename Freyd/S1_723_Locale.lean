/-
  Freyd & Scedrov, *Categories and Allegories* §1.723, §2.227, §2.331.

  FRAME / LOCALE foundation.

  A FRAME (= complete Heyting algebra) is a complete lattice in which finite
  meets distribute over arbitrary joins.  Every frame is a Heyting algebra
  (§1.723): define  a → b := sSup {c | a ⊓ c ≤ b}  and prove the adjunction
  c ≤ a → b ↔ a ⊓ c ≤ b.

  The canonical example: for a topological space X, the lattice O(X) of open
  sets (modelled here as a predicate  IsOpen : (X → Prop) → Prop) is a frame
  (arbitrary unions and finite intersections of opens are open).

  A frame homomorphism preserves finite meets and arbitrary joins.

  The sheaf / O(X)-valued-set content of §2.227/§2.331 requires sheaf
  infrastructure not yet in the repo; those goals are recorded as
  precise  -- BOOK §  TODO comments below.

  Build target: lake build Freyd.Locale
  Axioms (post-build): propext, Classical.choice, Quot.sound only.
-/

import Freyd.S1_72
import Freyd.S2_10

open Freyd

universe u

namespace Freyd

/-! ## §1.723 Frame (self-contained, not subobject-based)

  A FRAME is a complete lattice with finite-meet / arbitrary-join
  distributivity.  We give it its own bundled structure (not the
  Subobject-based `Locale` of S1_72) so that concrete carriers such
  as `Opens X` can instantiate it directly. -/

/-- A FRAME: complete lattice in which `a ⊓ (⨆ S) = ⨆ {a ⊓ s | s ∈ S}`.
    Extends `MeetLattice` (§1.85) — the carrier, order, and meet fields are
    inherited rather than duplicated. -/
structure Frame extends MeetLattice where
  /-- Top element. -/
  top   : carrier
  le_top : ∀ a, le a top
  /-- Bottom element. -/
  bot   : carrier
  bot_le : ∀ a, le bot a
  /-- Arbitrary join (⨆). -/
  sSup   : (carrier → Prop) → carrier
  le_sSup : ∀ (S : carrier → Prop) a, S a → le a (sSup S)
  sSup_le : ∀ (S : carrier → Prop) b, (∀ a, S a → le a b) → le (sSup S) b
  /-- **Frame distributivity**: `a ⊓ (⨆ S) = ⨆ {a ⊓ s | s ∈ S}`. -/
  meet_sSup_distrib : ∀ (a : carrier) (S : carrier → Prop),
    meet a (sSup S) = sSup (fun x => ∃ s, S s ∧ x = meet a s)

namespace Frame

variable (F : Frame.{u})

/-! ### Basic order facts -/

/-- Equals are comparable. -/
theorem le_of_eq {F : Frame.{u}} {a b : F.carrier} (h : a = b) : F.le a b := h ▸ F.le_refl a

/-- `sSup ∅ = bot` (join of empty family = bottom). -/
theorem sSup_empty : F.sSup (fun _ => False) = F.bot :=
  F.le_antisymm
    (F.sSup_le _ _ (fun _ h => h.elim))
    (F.bot_le _)

/-- `sSup {a} = a`. -/
theorem sSup_singleton (a : F.carrier) : F.sSup (fun x => x = a) = a :=
  F.le_antisymm
    (F.sSup_le _ _ (fun _ h => h ▸ F.le_refl _))
    (F.le_sSup _ a rfl)

/-- Binary join via sSup. -/
def join (a b : F.carrier) : F.carrier :=
  F.sSup (fun x => x = a ∨ x = b)

theorem le_join_left (a b : F.carrier) : F.le a (F.join a b) :=
  F.le_sSup _ a (Or.inl rfl)

theorem le_join_right (a b : F.carrier) : F.le b (F.join a b) :=
  F.le_sSup _ b (Or.inr rfl)

theorem join_le {a b c : F.carrier} (ha : F.le a c) (hb : F.le b c) : F.le (F.join a b) c :=
  F.sSup_le _ c (fun _ h => h.elim (· ▸ ha) (· ▸ hb))

/-! ### Derived meets: top and meet are correct -/

/-- `meet a top = a`. -/
theorem meet_top (a : F.carrier) : F.meet a F.top = a :=
  F.le_antisymm (F.meet_le_left a F.top)
    (F.le_meet (F.le_refl _) (F.le_top _))

/-- `meet a bot = bot`. -/
theorem meet_bot (a : F.carrier) : F.meet a F.bot = F.bot :=
  F.le_antisymm (F.meet_le_right a F.bot) (F.bot_le _)

/-- Meet is idempotent: `a ⊓ a = a`. -/
theorem meet_idem (a : F.carrier) : F.meet a a = a :=
  F.le_antisymm (F.meet_le_left a a) (F.le_meet (F.le_refl a) (F.le_refl a))

/-- Meet is commutative. -/
theorem meet_comm (a b : F.carrier) : F.meet a b = F.meet b a :=
  F.le_antisymm
    (F.le_meet (F.meet_le_right a b) (F.meet_le_left a b))
    (F.le_meet (F.meet_le_right b a) (F.meet_le_left b a))

/-- Meet is associative. -/
theorem meet_assoc (a b c : F.carrier) : F.meet (F.meet a b) c = F.meet a (F.meet b c) :=
  F.le_antisymm
    (F.le_meet (F.le_trans (F.meet_le_left _ c) (F.meet_le_left a b))
      (F.le_meet (F.le_trans (F.meet_le_left _ c) (F.meet_le_right a b)) (F.meet_le_right _ c)))
    (F.le_meet (F.le_meet (F.meet_le_left a _) (F.le_trans (F.meet_le_right a _) (F.meet_le_left b c)))
      (F.le_trans (F.meet_le_right a _) (F.meet_le_right b c)))

/-- `sSup` of the whole carrier = top. -/
theorem sSup_univ : F.sSup (fun _ => True) = F.top :=
  F.le_antisymm (F.sSup_le _ _ (fun _ _ => F.le_top _))
    (F.le_sSup _ F.top trivial)

/-! ### §1.723 Frame ⟹ Heyting algebra

  Define `a → b := sSup {c | a ⊓ c ≤ b}` and prove the adjunction
  `c ≤ a → b ↔ a ⊓ c ≤ b`. -/

/-- Heyting implication derived from frame structure: `a → b = ⨆ {c | a ⊓ c ≤ b}`. -/
noncomputable def himp (a b : F.carrier) : F.carrier :=
  F.sSup (fun c => F.le (F.meet a c) b)

/-- **Adjunction** `c ≤ (a → b) ↔ a ⊓ c ≤ b`  (§1.723). -/
theorem himp_adjunction (a b c : F.carrier) :
    F.le c (F.himp a b) ↔ F.le (F.meet a c) b := by
  constructor
  · -- c ≤ ⨆{z | a⊓z ≤ b} → a ⊓ c ≤ b
    -- By distributivity: a ⊓ (⨆{z | a⊓z≤b}) = ⨆{a⊓z | a⊓z≤b} ≤ b
    intro hc
    -- a ⊓ c ≤ a ⊓ (⨆{z | a⊓z≤b})
    have hmono : F.le (F.meet a c) (F.meet a (F.himp a b)) :=
      F.le_meet (F.meet_le_left a c)
        (F.le_trans (F.meet_le_right a c) hc)
    -- By distributivity a ⊓ (⨆{z | a⊓z≤b}) = ⨆{a⊓z | a⊓z≤b}
    have hdist := F.meet_sSup_distrib a (fun c => F.le (F.meet a c) b)
    -- ⨆{a⊓z | a⊓z≤b} ≤ b: each generator a⊓z satisfies a⊓z ≤ b
    have hle : F.le (F.sSup (fun x => ∃ s, F.le (F.meet a s) b ∧ x = F.meet a s)) b :=
      F.sSup_le _ b (fun x ⟨s, hs, hx⟩ => hx ▸ hs)
    exact F.le_trans hmono (hdist ▸ hle)
  · -- a ⊓ c ≤ b → c ≤ ⨆{z | a⊓z≤b}  (c itself is a witness)
    intro hac
    exact F.le_sSup (fun z => F.le (F.meet a z) b) c hac

/-- Modus ponens: `a ⊓ (a → b) ≤ b`. -/
theorem himp_mp (a b : F.carrier) : F.le (F.meet a (F.himp a b)) b :=
  (F.himp_adjunction a b (F.himp a b)).mp (F.le_refl _)

/-- `a → b` is covariant in `b`. -/
theorem himp_mono_right {a b c : F.carrier} (h : F.le b c) :
    F.le (F.himp a b) (F.himp a c) :=
  (F.himp_adjunction a c _).mpr (F.le_trans (F.himp_mp a b) h)

/-- `a → b` is contravariant in `a`. -/
theorem himp_mono_left_contra {a a' b : F.carrier} (h : F.le a' a) :
    F.le (F.himp a b) (F.himp a' b) :=
  (F.himp_adjunction a' b _).mpr
    (F.le_trans (F.le_meet
      (F.le_trans (F.meet_le_left _ _) h)
      (F.meet_le_right _ _))
      (F.himp_mp a b))

/-! ### Frame as HeytingLattice

  Every Frame gives a `HeytingLattice` (S1_85 definition), bridging to the
  existing Heyting algebra development. -/

/-- Every Frame (at universe 0) gives a `HeytingLattice`. -/
noncomputable def toHeytingLattice (F : Frame.{0}) : HeytingLattice where
  carrier       := F.carrier
  le            := F.le
  le_refl       := F.le_refl
  le_trans      := @F.le_trans
  le_antisymm   := @F.le_antisymm
  meet          := F.meet
  meet_le_left  := F.meet_le_left
  meet_le_right := F.meet_le_right
  le_meet       := fun {_z _x _y} hzx hzy => F.le_meet hzx hzy
  imp           := F.himp
  imp_adj       := fun {x a b} => (F.himp_adjunction a b x).symm
  top           := F.top
  le_top        := F.le_top
  bot           := F.bot
  bot_le        := F.bot_le
  join          := F.join
  le_join_left  := F.le_join_left
  le_join_right := F.le_join_right
  join_le       := @F.join_le

end Frame

/-! ## Frame homomorphisms

  A FRAME HOMOMORPHISM f : F → G preserves:
  - finite meets: top and binary meet,
  - arbitrary joins: `sSup`.
  These are the morphisms of the category of frames / locales. -/

/-- A FRAME HOMOMORPHISM between two frames. -/
structure FrameHom (F G : Frame.{u}) where
  map : F.carrier → G.carrier
  /-- Preserves top. -/
  map_top : map F.top = G.top
  /-- Preserves binary meet. -/
  map_meet : ∀ a b, map (F.meet a b) = G.meet (map a) (map b)
  /-- Preserves arbitrary joins. -/
  map_sSup : ∀ (S : F.carrier → Prop),
    map (F.sSup S) = G.sSup (fun y => ∃ x, S x ∧ y = map x)

namespace FrameHom

variable {F G H : Frame.{u}}

/-- A frame hom is order-preserving. -/
theorem map_mono (f : FrameHom F G) {a b : F.carrier} (h : F.le a b) :
    G.le (f.map a) (f.map b) := by
  -- a ≤ b iff a = a ⊓ b (in the frame order)
  -- f(a) = f(a⊓b) = f(a)⊓f(b) ≤ f(b)
  have hab : F.meet a b = a :=
    F.le_antisymm (F.meet_le_left a b) (F.le_meet (F.le_refl _) h)
  have : G.meet (f.map a) (f.map b) = f.map a := by
    rw [← f.map_meet, hab]
  exact this ▸ G.meet_le_right (f.map a) (f.map b)

/-- Preserves bottom (= sSup of empty family). -/
theorem map_bot (f : FrameHom F G) : f.map F.bot = G.bot := by
  have h1 : F.bot = F.sSup (fun _ : F.carrier => False) :=
    (Frame.sSup_empty F).symm
  rw [h1, f.map_sSup]
  -- G.sSup (fun y => ∃ x, False ∧ y = f(x)) = G.sSup (fun _ => False) = G.bot
  have : (fun y : G.carrier => ∃ x : F.carrier, False ∧ y = f.map x) = (fun _ => False) :=
    funext (fun _ => propext ⟨fun ⟨_, h, _⟩ => h, False.elim⟩)
  rw [this, Frame.sSup_empty]

/-- Identity frame hom. -/
def id (F : Frame.{u}) : FrameHom F F where
  map := fun x => x
  map_top := rfl
  map_meet := fun _ _ => rfl
  map_sSup := fun S => by
    apply F.le_antisymm
    · exact F.sSup_le _ _ (fun x hx => F.le_sSup _ x ⟨x, hx, rfl⟩)
    · exact F.sSup_le _ _ (fun _ ⟨x, hx, hyx⟩ => hyx ▸ F.le_sSup _ x hx)

/-- Composition of frame homs. -/
def comp (g : FrameHom G H) (f : FrameHom F G) : FrameHom F H where
  map := g.map ∘ f.map
  map_top := by simp [Function.comp, f.map_top, g.map_top]
  map_meet := fun a b => by simp [Function.comp, f.map_meet, g.map_meet]
  map_sSup := fun S => by
    simp only [Function.comp]
    -- expand g(f(sSup S)) step by step
    rw [f.map_sSup]
    -- now: g.map (G.sSup (fun y => ∃ x, S x ∧ y = f.map x))
    rw [g.map_sSup]
    -- now: H.sSup (fun y => ∃ z, (∃ x, S x ∧ z = f.map x) ∧ y = g.map z)
    -- = H.sSup (fun y => ∃ x, S x ∧ y = g.map (f.map x))
    apply H.le_antisymm
    · apply H.sSup_le
      intro y ⟨z, ⟨x, hx, hzx⟩, hyz⟩
      exact H.le_sSup _ y ⟨x, hx, hyz ▸ hzx ▸ rfl⟩
    · apply H.sSup_le
      intro y ⟨x, hx, hyx⟩
      exact H.le_sSup _ y ⟨f.map x, ⟨x, hx, rfl⟩, hyx⟩

end FrameHom

/-! ## Opens X: the frame of open sets of a topological space

  We model a topology on `X` as a predicate
    `IsOpen : (X → Prop) → Prop`
  satisfying the usual axioms.  The opens form a frame O(X).

  Note: we use `(X → Prop)` as the type of subsets of X (characteristic
  functions), which is definitionally the powerset `Set X`. -/

/-- A TOPOLOGY on X: a predicate on subsets specifying which are open.
    Axioms follow Freyd's convention: unary/binary are the special cases of
    the arbitrary ones. -/
structure Topology (X : Type u) where
  /-- Predicate: which subsets of X are open. -/
  IsOpen     : (X → Prop) → Prop
  /-- Whole space is open. -/
  isOpen_top : IsOpen (fun _ => True)
  /-- Empty set is open. -/
  isOpen_bot : IsOpen (fun _ => False)
  /-- Arbitrary unions of opens are open:
      if every member of a family is open, so is their union. -/
  isOpen_sUnion : ∀ (F : (X → Prop) → Prop),
    (∀ U, F U → IsOpen U) → IsOpen (fun x => ∃ U, F U ∧ U x)
  /-- Binary intersection of opens is open. -/
  isOpen_inter : ∀ {U V : X → Prop}, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)

namespace Topology

variable {X : Type u} (τ : Topology X)

/-- An open set of `(X, τ)`: a subset `U : X → Prop` with `τ.IsOpen U`. -/
def Opens := { U : X → Prop // τ.IsOpen U }

namespace Opens

variable {τ : Topology X}

/-- Underlying set of an open. -/
def set (U : τ.Opens) : X → Prop := U.val

/-- Subset order on opens: `U ≤ V` iff `U ⊆ V`. -/
def le (U V : τ.Opens) : Prop := ∀ x, U.val x → V.val x

theorem le_refl (U : τ.Opens) : le U U := fun _ hx => hx

theorem le_trans {U V W : τ.Opens} (h1 : le U V) (h2 : le V W) : le U W :=
  fun x hx => h2 x (h1 x hx)

theorem le_antisymm {U V : τ.Opens} (h1 : le U V) (h2 : le V U) : U = V :=
  Subtype.ext (funext (fun x => propext ⟨h1 x, h2 x⟩))

/-- Top open: the whole space. -/
def top : τ.Opens := ⟨fun _ => True, τ.isOpen_top⟩

/-- Bottom open: the empty set. -/
def bot : τ.Opens := ⟨fun _ => False, τ.isOpen_bot⟩

theorem le_top (U : τ.Opens) : le U top := fun _ _ => trivial

theorem bot_le (U : τ.Opens) : le bot U := fun _ h => h.elim

/-- Binary meet: intersection of two opens. -/
def meet (U V : τ.Opens) : τ.Opens :=
  ⟨fun x => U.val x ∧ V.val x, τ.isOpen_inter U.property V.property⟩

theorem meet_le_left (U V : τ.Opens) : le (meet U V) U := fun _ ⟨hu, _⟩ => hu

theorem meet_le_right (U V : τ.Opens) : le (meet U V) V := fun _ ⟨_, hv⟩ => hv

theorem le_meet {U V W : τ.Opens} (h1 : le W U) (h2 : le W V) : le W (meet U V) :=
  fun x hx => ⟨h1 x hx, h2 x hx⟩

/-- Arbitrary join: union of a family of opens.
    The union of an arbitrary family of opens is open by `isOpen_sUnion`. -/
def sSup (S : τ.Opens → Prop) : τ.Opens :=
  ⟨fun x => ∃ U : τ.Opens, S U ∧ U.val x,
   by
     -- rewrite as a union over the set-valued family indexed by (V.val | S V)
     have : (fun x => ∃ U : τ.Opens, S U ∧ U.val x) =
            (fun x => ∃ U : X → Prop, (∃ V : τ.Opens, S V ∧ U = V.val) ∧ U x) :=
       funext (fun x => propext
         ⟨fun ⟨V, hV, hvx⟩ => ⟨V.val, ⟨V, hV, rfl⟩, hvx⟩,
          fun ⟨U, ⟨V, hV, hUV⟩, hux⟩ => ⟨V, hV, hUV ▸ hux⟩⟩)
     rw [this]
     exact τ.isOpen_sUnion _ (fun U ⟨V, _, hUV⟩ => hUV ▸ V.property)⟩

theorem le_sSup (S : τ.Opens → Prop) (U : τ.Opens) (hU : S U) :
    le U (sSup S) := fun _x hx => ⟨U, hU, hx⟩

theorem sSup_le (S : τ.Opens → Prop) (V : τ.Opens) (h : ∀ U, S U → le U V) :
    le (sSup S) V := fun x ⟨U, hU, hx⟩ => h U hU x hx

/-- Frame distributivity: `meet U (sSup S) = sSup {meet U V | V ∈ S}`.
    Proof: pointwise propositional logic (each side is `U x ∧ (∃ V ∈ S, V x)`
    vs `∃ V ∈ S, U x ∧ V x`), which are logically equivalent. -/
theorem meet_sSup_distrib (U : τ.Opens) (S : τ.Opens → Prop) :
    meet U (sSup S) = sSup (fun W => ∃ V, S V ∧ W = meet U V) := by
  apply le_antisymm
  · intro x ⟨hux, W, hW, hwx⟩
    exact ⟨meet U W, ⟨W, hW, rfl⟩, hux, hwx⟩
  · intro x ⟨W, ⟨V, hV, hWV⟩, hwx⟩
    exact ⟨hWV ▸ hwx |>.1, V, hV, hWV ▸ hwx |>.2⟩

end Opens

/-- **O(X) is a Frame** (§1.723 / book §2.227 context).
    The frame of opens of a topological space. -/
def opensFrame (τ : Topology X) : Frame.{u} where
  carrier := τ.Opens
  le      := Opens.le
  le_refl := Opens.le_refl
  le_trans := @Opens.le_trans X τ
  le_antisymm := @Opens.le_antisymm X τ
  top    := Opens.top
  le_top := Opens.le_top
  bot    := Opens.bot
  bot_le := Opens.bot_le
  meet   := Opens.meet
  meet_le_left  := Opens.meet_le_left
  meet_le_right := Opens.meet_le_right
  le_meet := fun {_z _x _y} hzx hzy => Opens.le_meet hzx hzy
  sSup   := Opens.sSup
  le_sSup := fun S a ha => Opens.le_sSup S a ha
  sSup_le := fun S b h => Opens.sSup_le S b h
  meet_sSup_distrib := fun a S => Opens.meet_sSup_distrib a S

end Topology

/-! ## Continuous maps induce frame homomorphisms O(Y) → O(X)

  A map `f : X → Y` is continuous (w.r.t. topologies τX, τY) if preimages
  of opens are open.  It induces a frame hom `f* : O(Y) → O(X)` by pullback:
  `f*(V) = f⁻¹(V) = {x | f(x) ∈ V}`.  Frame homs go in the OPPOSITE direction
  to continuous maps — this is the (contravariant) functor O : Top^op → Frame. -/

/-- Continuity: preimage of every open is open. -/
def IsContinuousMap {X Y : Type u} (τX : Topology X) (τY : Topology Y)
    (f : X → Y) : Prop :=
  ∀ V : τY.Opens, τX.IsOpen (fun x => V.val (f x))

/-- Pullback frame hom `f* : O(Y) → O(X)` induced by a continuous map `f : X → Y`. -/
def continuousMapFrameHom {X Y : Type u} {τX : Topology X} {τY : Topology Y}
    (f : X → Y) (hf : IsContinuousMap τX τY f) :
    FrameHom (τY.opensFrame) (τX.opensFrame) where
  map V := ⟨fun x => V.val (f x), hf V⟩
  map_top := by
    apply Subtype.ext; ext x; exact Iff.rfl
  map_meet := fun U V => by
    apply Subtype.ext; ext x; exact Iff.rfl
  map_sSup := fun S => by
    -- Goal: map (τY.opensFrame.sSup S) = τX.opensFrame.sSup (fun W => ∃ V, S V ∧ W = map V)
    -- Both sides are τX.Opens; compare their val predicates.
    apply Subtype.ext; ext x
    -- LHS.val x = (τY.opensFrame.sSup S).val (f x) = ∃ V ∈ S, V.val (f x)
    -- RHS.val x = ∃ W : τX.Opens, (∃ V ∈ S, W = map V) ∧ W.val x
    simp only [Topology.opensFrame, Topology.Opens.sSup]
    constructor
    · -- ∃ V ∈ S, V.val (f x)  →  ∃ W, (∃ V ∈ S, W = ⟨·(f·), _⟩) ∧ W.val x
      intro ⟨V, hVS, hVfx⟩
      exact ⟨⟨fun z => V.val (f z), hf V⟩, ⟨V, hVS, rfl⟩, hVfx⟩
    · -- ∃ W, (∃ V ∈ S, W = ⟨·(f·), _⟩) ∧ W.val x  →  ∃ V ∈ S, V.val (f x)
      intro ⟨W, ⟨V, hVS, hWV⟩, hWx⟩
      -- hWV : W = ⟨fun z => V.val (f z), hf V⟩; so W.val x = V.val (f x)
      have : W.val x = V.val (f x) := congrFun (congrArg Subtype.val hWV) x
      exact ⟨V, hVS, this ▸ hWx⟩

/-! ## Points of a locale / frame

  A POINT of a frame F is a frame homomorphism `p : F → Ω` where `Ω` is the
  two-element frame {⊥, ⊤} (= Prop / truth values).  Equivalently, a point is
  a completely-prime filter in F: a proper filter P such that
  `a ⊔ b ∈ P → a ∈ P ∨ b ∈ P`.

  In the representation theorem §2.227, the "points" of O(X) correspond exactly
  to the points of X (for sober spaces X).

  BOOK §2.227 TODO: The full representation theorem needs:
    (1) The sobriety condition on X (every completely prime filter is the
        neighbourhood filter of a unique point).
    (2) The locale of points Pt(F) for an abstract frame F.
    (3) The adjunction between Top (topological spaces) and Locale (frames^op).
  These require more set-theoretic infrastructure (filtersets, adjunction
  framework); we leave them as a precise TODO. -/

/-- A POINT of a frame `F`: a completely-prime filter.
    Concretely: a predicate `p : F.carrier → Prop` that is:
    - proper: `¬ p F.bot`,
    - upward-closed: `p a → F.le a b → p b`,
    - finite-meet-closed: `p F.top` and `p a → p b → p (F.meet a b)`,
    - completely-prime: `p (F.sSup S) → ∃ a, S a ∧ p a`. -/
structure FramePoint (F : Frame.{u}) where
  mem       : F.carrier → Prop
  mem_top   : mem F.top
  mem_up    : ∀ {a b}, mem a → F.le a b → mem b
  mem_meet  : ∀ {a b}, mem a → mem b → mem (F.meet a b)
  not_bot   : ¬ mem F.bot
  prime     : ∀ (S : F.carrier → Prop), mem (F.sSup S) → ∃ a, S a ∧ mem a

/-- The point of `O(X)` associated to `x : X` (principal ultrafilter at x):
    `U ∈ p_x ↔ x ∈ U`. -/
def Topology.principalPoint {X : Type u} (τ : Topology X) (x : X) :
    FramePoint (τ.opensFrame) where
  mem U := U.val x
  mem_top := trivial
  mem_up hUx hle := hle x hUx
  mem_meet hUx hVx := ⟨hUx, hVx⟩
  not_bot := id
  prime _S hSx := let ⟨U, hUS, hUx⟩ := hSx; ⟨U, hUS, hUx⟩

-- BOOK §2.227: Representation theorem for locales / sober spaces.
-- For a SOBER topological space X, every point of the frame O(X)
-- (= every completely-prime filter) is of the form p_x for a unique x : X.
-- This gives a bijection  Pt(O(X)) ≅ X  and an embedding Top_sober ↪ Locale^op.
-- Stating this faithfully needs:
--   (a) a definition of sobriety: every irred. closed set has a generic point,
--   (b) the bijection Pt(O(X)) → X (uses Classical.choice to pick the point),
--   (c) the topology on Pt(F) for a general frame F (= Pt-construction).
-- These are left as a precise TODO; no Sorry-bearing stubs are emitted.

/-! ## §2.16(12) F-valued sets (Ω-sets over a frame)

  Freyd §2.16(12): the allegory obtained by splitting the symmetric idempotents
  of the Z-valued-relation allegory.  An **F-valued set** is a pair `⟨I, E⟩`
  where `E : I × I → F` is:
  - symmetric:   `E i j = E j i`
  - transitive:  `E i j ∧ E j k ≤ E i k`

  These are the objects of the **allegory of F-valued sets** OSet(F).
  A **morphism** `T : ⟨I,E⟩ → ⟨J,S⟩` is an `I×J`-matrix `T : I → J → F`
  satisfying (Freyd §2.16(12)):
  - domain bound:    `T i j ≤ E i i ∧ S j j`
  - naturality:      `E i i' ∧ S j j' ∧ T i j ≤ T i' j'`

  Identity on `⟨I,E⟩` is `E` itself. Composition via the join:
    `(T ⊚ U) i k = ⨆ { T i j ∧ U j k | j : J }`. -/

/-- An **F-valued set** (Freyd §2.16(12)): a carrier `I` with an `F`-valued
    "equality" `E` that is symmetric and transitive. -/
structure OValuedSet (F : Frame.{u}) where
  /-- Carrier (index) set. -/
  carrier : Type u
  /-- F-valued equality: `E i j` = "extent to which i and j are equal". -/
  E : carrier → carrier → F.carrier
  /-- Symmetry: `E i j = E j i`. -/
  symm : ∀ i j, E i j = E j i
  /-- Transitivity: `E i j ∧ E j k ≤ E i k`. -/
  trans : ∀ i j k, F.le (F.meet (E i j) (E j k)) (E i k)

namespace OValuedSet

variable {F : Frame.{u}}

/-- The **extent** of `i`: `E i i`.  (Like Dom in an allegory.) -/
def extent (A : OValuedSet F) (i : A.carrier) : F.carrier := A.E i i

/-- Reflexivity of E: `E i i` is greatest lower bound of `E i j` and `E j i`. -/
theorem extent_le_self (A : OValuedSet F) (i j : A.carrier) :
    F.le (F.meet (A.E i j) (A.E j i)) (A.extent i) := by
  -- E i j ∧ E j i ≤ E i i via transitivity (j plays the middle role)
  have h := A.trans i j i
  -- meet(E i j, E j i) ≤ meet(E i j, E j i) — but we need to use symm too
  -- Actually: meet(E i j, E j i) ≤ E i i = extent i
  -- by transitivity with j: E i j ∧ E j i ≤ E i i
  have hsym : A.E j i = A.E i j := (A.symm j i).symm ▸ (A.symm i j)
  -- trans gives: meet(E i j, E j i) ≤ meet(E i j, E j i) ... actually use trans directly
  -- E i j ∧ E j i ≤ E i i via trans i j i
  exact h

/-- `E i j ≤ E i i` (domain bound): the extent of i bounds E i j. -/
theorem E_le_extent_left (A : OValuedSet F) (i j : A.carrier) :
    F.le (A.E i j) (A.extent i) := by
  -- E i j ≤ E i j ∧ E j i ≤ E i i (since E j i ≤ top trivially... need another route)
  -- Better: E i j = E j i (by symm), so E i j ∧ E j j ≤ E i j by meet_le_left,
  -- and then E i j ∧ E j j ≤ E i i hmm, let's just use trans directly:
  -- E i j ≤ meet(E i j, E j i) is NOT true in general since meet is GLB.
  -- We need: E i j ≤ E i i.
  -- Trick: by trans i j i: meet(E i j, E j i) ≤ E i i
  -- and E i j = E j i (symm), so meet(E i j, E i j) = E i j ≤ E i i
  have hmeet_self : F.meet (A.E i j) (A.E i j) = A.E i j :=
    F.le_antisymm (F.meet_le_left _ _)
      (F.le_meet (F.le_refl _) (F.le_refl _))
  have hsym : A.E j i = A.E i j := by rw [A.symm]
  have htrans := A.trans i j i
  rw [hsym] at htrans
  -- htrans : meet(E i j, E i j) ≤ E i i
  rw [hmeet_self] at htrans
  exact htrans

/-- `E i j ≤ E j j` (codomain bound). -/
theorem E_le_extent_right (A : OValuedSet F) (i j : A.carrier) :
    F.le (A.E i j) (A.extent j) := by
  have := A.E_le_extent_left j i
  rw [A.symm j i] at this
  exact this

end OValuedSet

/-- A **morphism of F-valued sets** `T : ⟨I,E⟩ → ⟨J,S⟩` is an `I×J`-matrix
    of F-values satisfying the source-target predicate of Freyd §2.16(12):
    (i)  `T i j ≤ E i i ∧ S j j`  (bounded by extents),
    (ii) `E i i' ∧ S j j' ∧ T i j ≤ T i' j'`  (naturality / equivariance). -/
@[ext]
structure OSetHom {F : Frame.{u}} (A B : OValuedSet F) where
  /-- The underlying F-valued relation. -/
  rel : A.carrier → B.carrier → F.carrier
  /-- Domain bound: `T i j ≤ E i i`. -/
  dom_bound : ∀ i j, F.le (rel i j) (A.E i i)
  /-- Codomain bound: `T i j ≤ S j j`. -/
  cod_bound : ∀ i j, F.le (rel i j) (B.E j j)
  /-- Naturality: `E i i' ∧ S j j' ∧ T i j ≤ T i' j'`. -/
  natural : ∀ i i' j j',
    F.le (F.meet (F.meet (A.E i i') (B.E j j')) (rel i j)) (rel i' j')

namespace OSetHom

variable {F : Frame.{u}} {A B C : OValuedSet F}

/-- Combine the two bound conditions. -/
theorem bound (f : OSetHom A B) (i : A.carrier) (j : B.carrier) :
    F.le (f.rel i j) (F.meet (A.E i i) (B.E j j)) :=
  F.le_meet (f.dom_bound i j) (f.cod_bound i j)

/-- **Identity morphism** on A: `id_A i j = E_A i j`.
    Domain bound: `E i j ≤ E i i` (by OValuedSet.E_le_extent_left).
    Codomain bound: `E i j ≤ E j j` (by E_le_extent_right).
    Naturality: `E i i' ∧ E j j' ∧ E i j ≤ E i' j'`
    — via transitivity twice (i—i'—j' and i—j—j'). -/
def id (A : OValuedSet F) : OSetHom A A where
  rel    := A.E
  dom_bound := A.E_le_extent_left
  cod_bound := A.E_le_extent_right
  natural := fun i i' j j' => by
    -- Goal: meet(meet(E i i', E j j'), E i j) ≤ E i' j'
    -- Strategy: use transitivity twice
    -- E i i' ∧ E i j → (use trans) ≤ E i' j (via symmetric: E i' i ∧ E i j ≤ E i' j)
    -- Actually easier: meet(E i i', E j j') ∧ E i j
    --   ≤ E i i' ∧ E i j ≤ ... hmm need associativity
    -- Use: meet(A, B) ∧ C ≤ A; and separately ≤ B
    -- We want: E i i' ∧ E i j ≤ E i' j  (via sym+trans: E i' i ∧ E i j ≤ E i' j)
    -- then: E i' j ∧ E j j' ≤ E i' j'   (direct from trans)
    -- So: meet(meet(E i i', E j j'), E i j)
    --   ≤ E i i' ∧ E i j  and  ≤ E j j' ∧ E i' j  ... need to chain
    -- Full chain: let's extract components
    have hEij_i : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j)) (A.E i i') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    have hEij_j : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j)) (A.E j j') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _)
    have hEij_ij : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j)) (A.E i j) :=
      F.meet_le_right _ _
    -- Step 1: E i i' ∧ E i j ≤ E i' j
    --   = E i' i (by symm) ... trans: E i' i ∧ E i j ≤ E i' j
    have step1 : F.le (F.meet (A.E i i') (A.E i j)) (A.E i' j) := by
      have hsym : A.E i i' = A.E i' i := A.symm i i'
      rw [hsym]
      exact A.trans i' i j
    -- Step 2: E i' j ∧ E j j' ≤ E i' j'
    have step2 : F.le (F.meet (A.E i' j) (A.E j j')) (A.E i' j') :=
      A.trans i' j j'
    -- Chain: our term ≤ E i' j (via step1 from components)
    have hstep1_app : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j))
        (A.E i' j) := by
      apply F.le_trans _ step1
      exact F.le_meet hEij_i hEij_ij
    -- and ≤ E j j'
    have hstep2_app : F.le (F.meet (F.meet (A.E i i') (A.E j j')) (A.E i j))
        (A.E i' j') := by
      apply F.le_trans _ step2
      exact F.le_meet hstep1_app hEij_j
    exact hstep2_app

/-- **Composition** of OSetHom: `(f ⊚ g) i k = ⨆ { f i j ∧ g j k | j : B }`. -/
def comp (f : OSetHom A B) (g : OSetHom B C) : OSetHom A C where
  rel i k := F.sSup (fun v => ∃ j : B.carrier, v = F.meet (f.rel i j) (g.rel j k))
  dom_bound i k := by
    apply F.sSup_le
    intro v ⟨j, hv⟩
    rw [hv]
    exact F.le_trans (F.meet_le_left _ _) (f.dom_bound i j)
  cod_bound i k := by
    apply F.sSup_le
    intro v ⟨j, hv⟩
    rw [hv]
    exact F.le_trans (F.meet_le_right _ _) (g.cod_bound j k)
  natural i i' k k' := by
    -- Goal: meet(meet(A.E i i', C.E k k'), sSup{f(i,j)∧g(j,k) | j}) ≤ sSup{f(i',j)∧g(j,k') | j}
    -- Use meet_sSup_distrib to push meet inside the sup, then apply naturality of f and g
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨w, ⟨j, hw⟩, hvw⟩
    rw [hw] at hvw; rw [hvw]
    -- v = meet(meet(A.E i i', C.E k k'), meet(f.rel i j, g.rel j k))
    -- Need: ≤ sSup{f(i',j')∧g(j',k') | j'}
    -- Use naturality of f at (i,i',j,j) and of g at (j,j,k,k')
    -- First: meet(A.E i i', f.rel i j) ≤ f.rel i' j
    --   from f.natural i i' j j with B.E j j ≥ f.rel i j (cod_bound)
    -- Exploit: meet(A.E i i', C.E k k') ∧ meet(f.rel i j, g.rel j k)
    --        ≤ f.rel i' j ∧ g.rel j k'  then ≤ sSup via le_sSup with witness j
    have hAii' : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (A.E i i') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    have hCkk' : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (C.E k k') :=
      F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _)
    have hfij : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (f.rel i j) :=
      F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _)
    have hgjk : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (g.rel j k) :=
      F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _)
    -- Apply f.natural i i' j j: meet(meet(A.E i i', B.E j j), f.rel i j) ≤ f.rel i' j
    -- We have B.E j j ≥ f.rel i j (cod_bound), so meet(A.E i i', f.rel i j) ≤ f.rel i' j
    have hfnat : F.le (F.meet (F.meet (A.E i i') (B.E j j)) (f.rel i j)) (f.rel i' j) :=
      f.natural i i' j j
    -- Our term → meet(A.E i i', f.rel i j): need to get B.E j j in there
    have hBjj_f : F.le (f.rel i j) (B.E j j) := f.cod_bound i j
    have hf_app : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (f.rel i' j) := by
      apply F.le_trans _ hfnat
      exact F.le_meet (F.le_meet hAii' (F.le_trans hfij hBjj_f)) hfij
    -- Apply g.natural j j k k': meet(meet(B.E j j, C.E k k'), g.rel j k) ≤ g.rel j k'
    have hgnat : F.le (F.meet (F.meet (B.E j j) (C.E k k')) (g.rel j k)) (g.rel j k') :=
      g.natural j j k k'
    -- B.E j j ≥ g.rel j k (dom_bound)
    have hBjj_g : F.le (g.rel j k) (B.E j j) := g.dom_bound j k
    have hg_app : F.le (F.meet (F.meet (A.E i i') (C.E k k'))
        (F.meet (f.rel i j) (g.rel j k))) (g.rel j k') := by
      apply F.le_trans _ hgnat
      exact F.le_meet (F.le_meet (F.le_trans hgjk hBjj_g) hCkk') hgjk
    -- Combine: term ≤ f.rel i' j ∧ g.rel j k' ≤ sSup{f(i',j')∧g(j',k')|j'}
    apply F.le_trans (F.le_meet hf_app hg_app)
    exact F.le_sSup _ _ ⟨j, rfl⟩

/-! ### §2.16(12)/§2.227  The allegory operations on OSet(F)

  Beyond identity and composition (the `Cat` structure `osetCat`), the allegory of
  `F`-valued sets carries RECIPROCATION `f° j i = f i j` and INTERSECTION `(f ∩ g) i j =
  f i j ∧ g i j`.  We define both and prove the INVOLUTION + LATTICE laws of an
  `Allegory` (`recip_recip`, `recip_comp`, `recip_inter`, `inter_idem/comm/assoc`).  These are
  the structural half of the §2.16(12) allegory; the residual `semidistrib`/`modular` laws (the
  join-composition interaction) are NOT yet built — see the note after `osetCat`. -/

/-- **Reciprocal** `f° : B ⟶ A` of `f : A ⟶ B`: `f° j i = f i j`.  Bounds/naturality follow by
    swapping `i ↔ j` and using `E`-symmetry. -/
def recip (f : OSetHom A B) : OSetHom B A where
  rel j i := f.rel i j
  dom_bound j i := f.cod_bound i j
  cod_bound j i := f.dom_bound i j
  natural j j' i i' := by
    -- meet(meet(B.E j j', A.E i i'), f.rel i j) ≤ f.rel i' j'
    -- rewrite the two E's by symmetry to (A.E i i', B.E j j') and apply f.natural i i' j j'.
    rw [B.symm j j', A.symm i i']
    refine F.le_trans ?_ (f.natural i i' j j')
    -- meet(meet(B.E j' j, A.E i' i), f.rel i j) ≤ meet(meet(A.E i i', B.E j j'), f.rel i j)
    refine F.le_meet (F.le_meet ?_ ?_) (F.le_trans (F.meet_le_right _ _) (F.le_refl _))
    · exact F.le_trans (F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _))
        (Frame.le_of_eq (A.symm i' i))
    · exact F.le_trans (F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _))
        (Frame.le_of_eq (B.symm j' j))

/-- **Intersection** `f ∩ g : A ⟶ B`: `(f ∩ g) i j = f i j ∧ g i j`.  Bounds/naturality follow
    from those of `f` (taking the left meet projection). -/
def inter (f g : OSetHom A B) : OSetHom A B where
  rel i j := F.meet (f.rel i j) (g.rel i j)
  dom_bound i j := F.le_trans (F.meet_le_left _ _) (f.dom_bound i j)
  cod_bound i j := F.le_trans (F.meet_le_left _ _) (f.cod_bound i j)
  natural i i' j j' := by
    -- meet(meet(E,E), f i j ∧ g i j) ≤ f i' j' ∧ g i' j'.
    refine F.le_meet ?_ ?_
    · -- project to f's component then apply f.natural.
      refine F.le_trans ?_ (f.natural i i' j j')
      exact F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _))
    · refine F.le_trans ?_ (g.natural i i' j j')
      exact F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _))

/-- `(f°)° = f`. -/
theorem recip_recip (f : OSetHom A B) : recip (recip f) = f := by ext i j; rfl

/-- `(f ⊚ g)° = g° ⊚ f°`:  swapping indices in the colimit and using frame-meet commutativity. -/
theorem recip_comp (f : OSetHom A B) (g : OSetHom B C) :
    recip (comp f g) = comp (recip g) (recip f) := by
  ext k i
  show F.sSup (fun v => ∃ j, v = F.meet (f.rel i j) (g.rel j k))
     = F.sSup (fun v => ∃ j, v = F.meet (g.rel j k) (f.rel i j))
  apply F.le_antisymm <;>
    refine F.sSup_le _ _ (fun v ⟨j, hv⟩ => ?_) <;> subst hv
  · exact F.le_trans (Frame.le_of_eq (F.meet_comm _ _)) (F.le_sSup _ _ ⟨j, rfl⟩)
  · exact F.le_trans (Frame.le_of_eq (F.meet_comm _ _)) (F.le_sSup _ _ ⟨j, rfl⟩)

/-- `(f ∩ g)° = f° ∩ g°`. -/
theorem recip_inter (f g : OSetHom A B) : recip (inter f g) = inter (recip f) (recip g) := by
  ext j i; rfl

/-- `f ∩ f = f`. -/
theorem inter_idem (f : OSetHom A B) : inter f f = f := by
  ext i j; exact F.meet_idem (f.rel i j)

/-- `f ∩ g = g ∩ f`. -/
theorem inter_comm (f g : OSetHom A B) : inter f g = inter g f := by
  ext i j; exact F.meet_comm (f.rel i j) (g.rel i j)

/-- `f ∩ (g ∩ h) = (f ∩ g) ∩ h`. -/
theorem inter_assoc (f g h : OSetHom A B) :
    inter f (inter g h) = inter (inter f g) h := by
  ext i j; exact (F.meet_assoc (f.rel i j) (g.rel i j) (h.rel i j)).symm

end OSetHom

/-! ### The category OSet(F)

  Objects: OValuedSet F.
  Morphisms: OSetHom A B.
  Identity and composition are defined above; associativity holds because
  ⨆ of a ⨆ over j equals ⨆ over the combined index. -/

/-- OSet(F) identity morphism. -/
def oset_id {F : Frame.{u}} (A : OValuedSet F) : OSetHom A A := OSetHom.id A

/-- OSet(F) composition. -/
def oset_comp {F : Frame.{u}} {A B C : OValuedSet F}
    (f : OSetHom A B) (g : OSetHom B C) : OSetHom A C := OSetHom.comp f g

/-- Identity is left unit: `id ⊚ f = f`.
    Proof: `(id ⊚ f) i k = ⨆ { E i j ∧ f j k | j } = f i k`. -/
theorem oset_id_comp {F : Frame.{u}} {A B : OValuedSet F} (f : OSetHom A B) :
    oset_comp (oset_id A) f = f := by
  ext i k  -- structural equality on OSetHom is via rel
  simp only [oset_comp, oset_id, OSetHom.comp, OSetHom.id]
  -- Goal: F.sSup (fun v => ∃ j, v = F.meet (A.E i j) (f.rel j k)) = f.rel i k
  apply F.le_antisymm
  · -- ⊢ sSup{E i j ∧ f j k | j} ≤ f i k
    apply F.sSup_le
    intro v ⟨j, hv⟩; rw [hv]
    -- E i j ∧ f j k ≤ f i k  by naturality of f at (j, i, k, k)
    -- f.natural j i k k: meet(meet(A.E j i, B.E k k), f.rel j k) ≤ f.rel i k
    have hnat := f.natural j i k k
    -- A.E j i = A.E i j by symm
    -- B.E k k ≥ f.rel j k by cod_bound
    have hBkk : F.le (f.rel j k) (B.E k k) := f.cod_bound j k
    have hsym : A.E j i = A.E i j := A.symm j i
    apply F.le_trans _ hnat
    rw [← hsym]
    exact F.le_meet (F.le_meet (F.meet_le_left _ _)
      (F.le_trans (F.meet_le_right _ _) hBkk))
      (F.meet_le_right _ _)
  · -- ⊢ f i k ≤ sSup{E i j ∧ f j k | j}
    -- witness j = i: E i i ∧ f i k ≥ f i k  (since f i k ≤ E i i by dom_bound)
    apply F.le_trans _ (F.le_sSup _ _ ⟨i, rfl⟩)
    -- ⊢ f.rel i k ≤ F.meet (A.E i i) (f.rel i k)
    exact F.le_meet (f.dom_bound i k) (F.le_refl _)

/-- Identity is right unit: `f ⊚ id = f`. -/
theorem oset_comp_id {F : Frame.{u}} {A B : OValuedSet F} (f : OSetHom A B) :
    oset_comp f (oset_id B) = f := by
  ext i k
  simp only [oset_comp, oset_id, OSetHom.comp, OSetHom.id]
  apply F.le_antisymm
  · apply F.sSup_le
    intro v ⟨j, hv⟩; rw [hv]
    -- f i j ∧ E j k ≤ f i k  by naturality of f at (i, i, j, k)
    -- f.natural i i j k: meet(meet(A.E i i, B.E j k), f.rel i j) ≤ f.rel i k
    have hnat := f.natural i i j k
    have hAii : F.le (f.rel i j) (A.E i i) := f.dom_bound i j
    apply F.le_trans _ hnat
    exact F.le_meet (F.le_meet (F.le_trans (F.meet_le_left _ _) hAii)
      (F.meet_le_right _ _))
      (F.meet_le_left _ _)
  · apply F.le_trans _ (F.le_sSup _ _ ⟨k, rfl⟩)
    -- goal: f.rel i k ≤ meet (f.rel i k) (B.E k k)
    exact F.le_meet (F.le_refl _) (f.cod_bound i k)

/-- Auxiliary: `sSup S ∧ a = a ∧ sSup S` (meet commutativity for sSup).
    We need this for the associativity proof because `meet_sSup_distrib` is
    `a ∧ sSup S = ...` but composition gives `sSup S ∧ h`. -/
private theorem Frame.sSup_meet_comm {F : Frame.{u}} (a : F.carrier)
    (S : F.carrier → Prop) :
    F.meet (F.sSup S) a = F.meet a (F.sSup S) :=
  F.le_antisymm
    (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))
    (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))

/-- Auxiliary: meet distributes over sSup on the right. -/
private theorem Frame.sSup_meet_distrib {F : Frame.{u}} (S : F.carrier → Prop) (b : F.carrier) :
    F.meet (F.sSup S) b = F.sSup (fun x => ∃ s, S s ∧ x = F.meet s b) := by
  rw [Frame.sSup_meet_comm, F.meet_sSup_distrib]
  -- now: sSup{b ∧ s | s ∈ S} = sSup{x | ∃ s ∈ S, x = meet s b}
  apply F.le_antisymm
  · apply F.sSup_le; intro x ⟨s, hs, hx⟩
    -- hx : x = meet b s; need: ∃ s', S s' ∧ x = meet s' b
    exact F.le_sSup _ _ ⟨s, hs, hx ▸ F.le_antisymm
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))⟩
  · apply F.sSup_le; intro x ⟨s, hs, hx⟩
    -- hx : x = meet s b; need: ∃ s', S s' ∧ x = meet b s'
    exact F.le_sSup _ _ ⟨s, hs, hx ▸ F.le_antisymm
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))
      (F.le_meet (F.meet_le_right _ _) (F.meet_le_left _ _))⟩

/-- Composition is associative: `(f ⊚ g) ⊚ h = f ⊚ (g ⊚ h)`.
    Both sides equal `⨆_{j,k} { f i j ∧ g j k ∧ h k l }`. -/
theorem oset_comp_assoc {F : Frame.{u}} {A B C D : OValuedSet F}
    (f : OSetHom A B) (g : OSetHom B C) (h : OSetHom C D) :
    oset_comp (oset_comp f g) h = oset_comp f (oset_comp g h) := by
  ext i l
  simp only [oset_comp, OSetHom.comp]
  -- LHS: sSup_k { meet(sSup_j{f i j ∧ g j k}, h k l) }
  -- RHS: sSup_j { meet(f i j, sSup_k{g j k ∧ h k l}) }
  apply F.le_antisymm
  · -- LHS ≤ RHS
    apply F.sSup_le; intro v ⟨k, hvk⟩; rw [hvk]
    -- Goal: meet(sSup_j{f i j ∧ g j k}, h k l) ≤ sSup_j{f i j ∧ sSup_k{g j k' ∧ h k' l}}
    -- Use sSup_meet_distrib to unpack the left factor
    rw [Frame.sSup_meet_distrib]
    apply F.sSup_le; intro w ⟨u, ⟨j, huj⟩, hwu⟩; rw [huj] at hwu; rw [hwu]
    -- w = meet(f i j ∧ g j k, h k l)
    apply F.le_trans _ (F.le_sSup _ _ ⟨j, rfl⟩)
    apply F.le_meet
    · exact F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    · apply F.le_trans _ (F.le_sSup _ _ ⟨k, rfl⟩)
      exact F.le_meet
        (F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _))
        (F.meet_le_right _ _)
  · -- RHS ≤ LHS
    apply F.sSup_le; intro v ⟨j, hvj⟩; rw [hvj]
    -- Goal: meet(f i j, sSup_k{g j k ∧ h k l}) ≤ sSup_k{meet(sSup_j'{f i j' ∧ g j' k}, h k l)}
    rw [F.meet_sSup_distrib]
    apply F.sSup_le; intro w ⟨u, ⟨k, huk⟩, hwu⟩; rw [huk] at hwu; rw [hwu]
    -- w = meet(f i j, g j k ∧ h k l)
    apply F.le_trans _ (F.le_sSup _ _ ⟨k, rfl⟩)
    apply F.le_meet
    · apply F.le_trans _ (F.le_sSup _ _ ⟨j, rfl⟩)
      exact F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _))
    · exact F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _)

/-! ## The category OSet(F)

  Package the id / comp / unit / assoc proofs above into a `Cat` instance
  so that `OValuedSet F` becomes a first-class category in the repo's `Cat`
  typeclass. -/

instance osetCat (F : Frame.{u}) : Cat.{u} (OValuedSet F) where
  Hom    := OSetHom
  id     := OSetHom.id
  comp   := OSetHom.comp
  id_comp := oset_id_comp
  comp_id := oset_comp_id
  assoc  := oset_comp_assoc

/-! ### §2.16(12)/§2.227  Status of the allegory structure on OSet(F)

  DONE here: `osetCat` (Cat) PLUS the involution + lattice half of the allegory —
  `OSetHom.recip`, `OSetHom.inter`, and the laws `recip_recip`, `recip_comp`, `recip_inter`,
  `inter_idem`, `inter_comm`, `inter_assoc` (the first six fields beyond `Cat` of the `Allegory`
  class in `Freyd/S2_1.lean`).

  RESIDUAL (NOT built): the two ORDER/COMPOSITION-interaction laws `semidistrib` and `modular`
  of the `Allegory` class, which couple `inter` with the `⨆`-defined `comp`.  These are the
  genuine §2.16(12) content and require frame-distributivity calculations over the colimit
  composition.  Until they are discharged, `OSet(F)` is NOT registered as a full `Allegory`
  instance (doing so is the remaining §2.227 work).  We deliberately do NOT import `S2_1`
  (`Allegory`) here to keep `Locale.lean`'s import-closure small and acyclic; the `Allegory`
  instance, when built, should live in a downstream file that imports both `Locale` and `S2_1`.

  This is exactly the piece §2.331 needs ("the allegory of `O(X)`-valued sets"): its objects,
  reciprocal and intersection now exist; only `modular`/`semidistrib` remain.  See `S2_3.lean`
  §2.331 for the conditional reduction stated over this structure. -/

/-! ### §2.16(12)/§2.227  OSet(F) is a full `Allegory`

  The remaining two `Allegory`-class fields (`semidistrib`, `modular`) couple `inter` with the
  `⨆`-defined composition.  Both reduce — via the order characterization `f ⊑ g ↔ pointwise
  `f.rel i j ≤ g.rel i j`` — to an elementary frame meet/`sSup` inequality.  We discharge them
  here and register `instOSetAllegory : Allegory (OValuedSet F)`, completing §2.227. -/

namespace OSetHom

variable {F : Frame.{u}} {A B C : OValuedSet F}

/-- Extensional order on OSetHom: `inter f g = f` iff `f.rel i j ≤ g.rel i j` pointwise.
    (This is exactly the `Allegory.le` order once the instance exists.) -/
theorem inter_eq_left_iff (f g : OSetHom A B) :
    inter f g = f ↔ ∀ i j, F.le (f.rel i j) (g.rel i j) := by
  constructor
  · intro h i j
    have : (inter f g).rel i j = f.rel i j := by rw [h]
    -- (inter f g).rel i j = meet (f i j) (g i j) = f i j  ⟹  f i j ≤ g i j
    show F.le (f.rel i j) (g.rel i j)
    have hm : F.meet (f.rel i j) (g.rel i j) = f.rel i j := this
    exact hm ▸ F.meet_le_right _ _
  · intro h; ext i j
    exact F.le_antisymm (F.meet_le_left _ _) (F.le_meet (F.le_refl _) (h i j))

/-- The `meet` of a pointwise composition value with a constant, expanded by distributivity:
    `(comp f g).rel i k ⊓ t = ⨆_j (f i j ⊓ g j k ⊓ t)`. -/
private theorem comp_rel_meet (f : OSetHom A B) (g : OSetHom B C)
    (i : A.carrier) (k : C.carrier) (t : F.carrier) :
    F.meet ((comp f g).rel i k) t
      = F.sSup (fun v => ∃ j, v = F.meet (F.meet (f.rel i j) (g.rel j k)) t) := by
  show F.meet (F.sSup (fun v => ∃ j, v = F.meet (f.rel i j) (g.rel j k))) t = _
  rw [Frame.sSup_meet_distrib]
  apply F.le_antisymm
  · -- ⨆ {meet s t | s = f i j ∧ g j k}  ≤  ⨆_j meet (meet (f i j) (g j k)) t
    apply F.sSup_le; intro x ⟨s, ⟨j, hs⟩, hx⟩
    exact F.le_sSup _ _ ⟨j, by rw [hx, hs]⟩
  · -- reverse
    apply F.sSup_le; intro x ⟨j, hx⟩
    exact F.le_sSup _ _ ⟨F.meet (f.rel i j) (g.rel j k), ⟨j, rfl⟩, hx⟩

/-- **SEMI-DISTRIBUTIVITY** (§2.11 field form): the colimit composition distributes through
    `inter` on the right as the nested intersection. -/
theorem osetAlleg_semidistrib (R : OSetHom A B) (S T : OSetHom B C) :
    comp R (inter S T) = inter (inter (comp R S) (comp R (inter S T))) (comp R T) := by
  -- Reverse direction is free (RHS ⊑ comp R (inter S T) by the inter projections); equality
  -- follows once we show comp R (inter S T) ⊑ comp R S and ⊑ comp R T pointwise.
  have hS : ∀ i k, F.le ((comp R (inter S T)).rel i k) ((comp R S).rel i k) := by
    intro i k
    show F.le (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (F.meet (S.rel j k) (T.rel j k))))
              (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (S.rel j k)))
    apply F.sSup_le; intro v ⟨j, hv⟩; rw [hv]
    refine F.le_trans ?_ (F.le_sSup _ _ ⟨j, rfl⟩)
    exact F.le_meet (F.meet_le_left _ _)
      (F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _))
  have hT : ∀ i k, F.le ((comp R (inter S T)).rel i k) ((comp R T).rel i k) := by
    intro i k
    show F.le (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (F.meet (S.rel j k) (T.rel j k))))
              (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (T.rel j k)))
    apply F.sSup_le; intro v ⟨j, hv⟩; rw [hv]
    refine F.le_trans ?_ (F.le_sSup _ _ ⟨j, rfl⟩)
    exact F.le_meet (F.meet_le_left _ _)
      (F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _))
  -- Assemble the field equality from the two ⊑'s.  Y := comp R (inter S T).
  have e1 : inter (comp R S) (comp R (inter S T)) = comp R (inter S T) := by
    rw [inter_comm]; exact (inter_eq_left_iff _ _).mpr hS
  have e2 : inter (comp R (inter S T)) (comp R T) = comp R (inter S T) :=
    (inter_eq_left_iff _ _).mpr hT
  rw [e1, e2]

/-- **MODULAR LAW** (§2.11 field form) for OSet(F). -/
theorem osetAlleg_modular (R : OSetHom A B) (S : OSetHom B C) (T : OSetHom A C) :
    inter (comp R S) T
      = inter (inter (comp R S) T) (comp (inter R (comp T (recip S))) S) := by
  -- Equivalent to  (comp R S) ∩ T  ⊑  comp (R ∩ T S°) S  pointwise.
  have key : ∀ i k,
      F.le ((inter (comp R S) T).rel i k) ((comp (inter R (comp T (recip S))) S).rel i k) := by
    intro i k
    -- LHS = meet (⨆_j R(i,j)∧S(j,k))  T(i,k) = ⨆_j (R(i,j)∧S(j,k))∧T(i,k)  by distributivity.
    show F.le (F.meet ((comp R S).rel i k) (T.rel i k)) _
    rw [comp_rel_meet R S i k (T.rel i k)]
    apply F.sSup_le; intro v ⟨j, hv⟩; rw [hv]
    -- v = meet (meet (R i j) (S j k)) (T i k);  target sup is over (R ∩ T S°) S at index j.
    refine F.le_trans ?_ (F.le_sSup _ _ ⟨j, rfl⟩)
    -- target term at j: meet ((inter R (comp T (recip S))).rel i j) (S.rel j k).
    --   (inter R (comp T (recip S))).rel i j = meet (R i j) ((comp T (recip S)).rel i j),
    --   and (comp T (recip S)).rel i j = ⨆_{k'} T(i,k') ∧ S(j,k')  ≥  T(i,k) ∧ S(j,k).
    refine F.le_meet (F.le_meet ?_ ?_) ?_
    · -- ≤ R(i,j)
      exact F.le_trans (F.meet_le_left _ _) (F.meet_le_left _ _)
    · -- ≤ (comp T (recip S)).rel i j = ⨆_{k'} T(i,k') ∧ (recip S)(k',j) = ⨆ T(i,k')∧S(j,k')
      show F.le _ (F.sSup (fun w => ∃ k', w = F.meet (T.rel i k') ((recip S).rel k' j)))
      refine F.le_trans ?_ (F.le_sSup _ _ ⟨k, rfl⟩)
      -- need meet(meet(R i j, S j k), T i k) ≤ meet (T i k) ((recip S) k j) = meet (T i k) (S j k)
      show F.le _ (F.meet (T.rel i k) (S.rel j k))
      exact F.le_meet (F.meet_le_right _ _)
        (F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _))
    · -- ≤ S(j,k)
      exact F.le_trans (F.meet_le_left _ _) (F.meet_le_right _ _)
  have e : inter (inter (comp R S) T) (comp (inter R (comp T (recip S))) S)
            = inter (comp R S) T :=
    (inter_eq_left_iff _ _).mpr key
  rw [e]

end OSetHom

/-- **OSet(F) is an Allegory** (§2.16(12)/§2.227).  Objects = `OValuedSet F`; composition is the
    `⨆`-colimit; reciprocation/intersection are pointwise; all eight `Allegory` fields hold.
    This is the abstract target of the §2.331 representation theorems (`S2_33.lean`). -/
instance instOSetAllegory (F : Frame.{u}) : Freyd.Alg.Allegory.{u} (OValuedSet F) where
  toCat       := osetCat F
  recip       := OSetHom.recip
  inter       := OSetHom.inter
  recip_recip := OSetHom.recip_recip
  recip_comp  := OSetHom.recip_comp
  recip_inter := OSetHom.recip_inter
  inter_idem  := OSetHom.inter_idem
  inter_comm  := OSetHom.inter_comm
  inter_assoc := OSetHom.inter_assoc
  semidistrib := OSetHom.osetAlleg_semidistrib
  modular     := OSetHom.osetAlleg_modular

/-! ### §2.227/§2.331  Functoriality of OSet in the frame

  A `FrameHom f : F ⟶ G` reindexes `F`-valued sets to `G`-valued sets — relabel every truth
  value by `f`.  Because `f` preserves `meet`, `top` and `sSup`, this carries the symmetric/
  transitive equalities, the morphism bounds/naturality, and (crucially for §2.331) the colimit
  composition: it is an `AllegoryFunctor (OValuedSet F) (OValuedSet G)`.  This is the abstract
  vehicle by which a SPACE enters §2.331 — Moerdijk's locale embedding `O(2^ω) ⟶ O(X)` is just
  such a `FrameHom`, inducing this functor on the OSet allegories. -/

namespace OSetFrameHom

variable {F G : Frame.{u}} (f : FrameHom F G)

/-- Object map: relabel the `F`-valued equality of `A` by `f`.  Same carrier; symmetry from
    `A.symm`, transitivity from `f.map_meet` + `f.map_mono`. -/
def obj (A : OValuedSet F) : OValuedSet G where
  carrier := A.carrier
  E i j := f.map (A.E i j)
  symm i j := by rw [A.symm]
  trans i j k := by
    rw [← f.map_meet]; exact f.map_mono (A.trans i j k)

/-- Hom map: relabel the `F`-valued relation by `f`.  Bounds from `f.map_mono`; naturality from
    `f.map_meet` (twice) + `f.map_mono`. -/
def map {A B : OValuedSet F} (R : OSetHom A B) : OSetHom (obj f A) (obj f B) where
  rel i j := f.map (R.rel i j)
  dom_bound i j := f.map_mono (R.dom_bound i j)
  cod_bound i j := f.map_mono (R.cod_bound i j)
  natural i i' j j' := by
    show G.le (G.meet (G.meet (f.map (A.E i i')) (f.map (B.E j j'))) (f.map (R.rel i j)))
              (f.map (R.rel i' j'))
    rw [← f.map_meet, ← f.map_meet]; exact f.map_mono (R.natural i i' j j')

/-- `map f` sends a `⨆`-composition to the `⨆`-composition of the images: the genuine content,
    using `f.map_sSup` and `f.map_meet`. -/
theorem map_comp {A B C : OValuedSet F} (R : OSetHom A B) (S : OSetHom B C) :
    map f (OSetHom.comp R S) = OSetHom.comp (map f R) (map f S) := by
  ext i k
  show f.map (F.sSup (fun v => ∃ j, v = F.meet (R.rel i j) (S.rel j k)))
     = G.sSup (fun w => ∃ j, w = G.meet (f.map (R.rel i j)) (f.map (S.rel j k)))
  rw [f.map_sSup]
  apply G.le_antisymm
  · apply G.sSup_le; intro y ⟨x, ⟨j, hx⟩, hy⟩
    refine G.le_sSup _ _ ⟨j, ?_⟩
    rw [hy, hx, f.map_meet]
  · apply G.sSup_le; intro w ⟨j, hw⟩
    refine G.le_sSup _ _ ⟨F.meet (R.rel i j) (S.rel j k), ⟨j, rfl⟩, ?_⟩
    rw [hw, f.map_meet]

-- The four remaining `AllegoryFunctor` laws are bundled in `Freyd/S2_33.lean`
-- (`OSetFrameHom.functor`): `AllegoryFunctor` lives in `MapCat.lean`, which transitively imports
-- `S2_3` and so cannot be imported here without a cycle.  The genuine content (`map_comp`) is the
-- theorem above; `map_id`/`map_recip`/`map_inter` are then immediate.

theorem map_id (A : OValuedSet F) : map f (OSetHom.id A) = OSetHom.id (obj f A) := by
  ext i j; show f.map (A.E i j) = f.map (A.E i j); rfl

theorem map_recip {A B : OValuedSet F} (R : OSetHom A B) :
    map f (OSetHom.recip R) = OSetHom.recip (map f R) := by ext j i; rfl

theorem map_inter {A B : OValuedSet F} (R S : OSetHom A B) :
    map f (OSetHom.inter R S) = OSetHom.inter (map f R) (map f S) := by
  ext i j; show f.map (F.meet (R.rel i j) (S.rel i j)) = _; rw [f.map_meet]; rfl

end OSetFrameHom

/-! ## Terminal F-valued set

  The terminal object of OSet(F) is the singleton carrier `PUnit` with
  equality `E () () = F.top` (everything is "equal to itself completely").
  Any morphism into it is forced: `T i () = A.E i i` (the extent of i). -/

/-- The terminal F-valued set: carrier = `PUnit`, `E () () = F.top`.
    Transitivity: `F.top ∧ F.top ≤ F.top` by `meet_le_left`. -/
def OSetTerminal (F : Frame.{u}) : OValuedSet F where
  carrier := PUnit
  E _ _   := F.top
  symm _ _ := rfl
  trans _ _ _ := F.meet_le_left F.top F.top

/-! ## F-valued predicates (§2.227 H(Y) ingredient)

  For an F-valued set `A`, an **F-valued predicate** on `A` is a function
  `p : A.carrier → F.carrier` satisfying:
    (i)  `p i ≤ A.E i i`   (domain bound),
    (ii) `A.E i j ∧ p i ≤ p j`  (naturality / equivariance).

  The collection `OPred F A` of all such predicates is ordered pointwise:
    `p ≤ q ↔ ∀ i, F.le (p.val i) (q.val i)`.

  This is a FRAME under the pointwise frame operations of F.  The Heyting
  implication is therefore also available (F is a frame ⟹ Heyting algebra).

  In the special case A = OSetTerminal F and F = O(Y), the frame OPred F A
  recovers F itself (Prop: `osetTerminal_pred_iso_frame`).  This is the
  H(Y) of §2.227. -/

/-- An F-valued predicate on an F-valued set A. -/
structure OPred {F : Frame.{u}} (A : OValuedSet F) where
  /-- The predicate. -/
  val : A.carrier → F.carrier
  /-- Domain bound: `p i ≤ A.E i i`. -/
  dom_bound : ∀ i, F.le (val i) (A.E i i)
  /-- Naturality: `A.E i j ∧ p i ≤ p j`. -/
  natural : ∀ i j, F.le (F.meet (A.E i j) (val i)) (val j)

namespace OPred

variable {F : Frame.{u}} {A : OValuedSet F}

/-- Pointwise order on predicates. -/
def le (p q : OPred A) : Prop := ∀ i, F.le (p.val i) (q.val i)

theorem le_refl (p : OPred A) : le p p := fun _i => F.le_refl _

theorem le_trans {p q r : OPred A} (hpq : le p q) (hqr : le q r) : le p r :=
  fun i => F.le_trans (hpq i) (hqr i)

theorem le_antisymm {p q : OPred A} (hpq : le p q) (hqp : le q p) : p = q := by
  cases p; cases q
  congr 1
  funext i
  exact F.le_antisymm (hpq i) (hqp i)

/-- The top predicate: `p i = A.E i i` (maximal extent). -/
def top (A : OValuedSet F) : OPred A where
  val i := A.E i i
  dom_bound _i := F.le_refl _
  -- need: F.le (F.meet (A.E i j) (A.E i i)) (A.E j j)
  -- meet (E i j) (E i i) ≤ E i j ≤ E j j
  natural i j := F.le_trans (F.meet_le_left _ _) (A.E_le_extent_right i j)

/-- Bottom predicate: `p i = F.bot`. -/
def bot (A : OValuedSet F) : OPred A where
  val _ := F.bot
  dom_bound _ := F.bot_le _
  natural _ _ := F.le_trans (F.meet_le_right _ _) (F.bot_le _)

theorem le_top (p : OPred A) : le p (top A) := fun i => p.dom_bound i

theorem bot_le (p : OPred A) : le (bot A) p := fun _i => F.bot_le _

/-- Pointwise meet of two predicates. -/
def meet (p q : OPred A) : OPred A where
  val i := F.meet (p.val i) (q.val i)
  dom_bound i := F.le_trans (F.meet_le_left _ _) (p.dom_bound i)
  natural i j := by
    -- A.E i j ∧ (p i ∧ q i) ≤ p j ∧ q j
    -- reorganise: (A.E i j ∧ p i) ≤ p j and (A.E i j ∧ q i) ≤ q j
    apply F.le_meet
    · exact F.le_trans (F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_left _ _))) (p.natural i j)
    · exact F.le_trans (F.le_meet (F.meet_le_left _ _)
        (F.le_trans (F.meet_le_right _ _) (F.meet_le_right _ _))) (q.natural i j)

theorem meet_le_left (p q : OPred A) : le (meet p q) p :=
  fun _i => F.meet_le_left _ _

theorem meet_le_right (p q : OPred A) : le (meet p q) q :=
  fun _i => F.meet_le_right _ _

theorem le_meet {p q r : OPred A} (hpr : le r p) (hqr : le r q) : le r (meet p q) :=
  fun i => F.le_meet (hpr i) (hqr i)

/-- Pointwise arbitrary join of a family of predicates.

    For `sSup S` to be equivariant we need:
    `A.E i j ∧ (⨆_{p∈S} p i) ≤ ⨆_{p∈S} p j`.
    By frame distributivity: `A.E i j ∧ (⨆ p i) = ⨆{A.E i j ∧ p i | p∈S} ≤ ⨆{p j | p∈S}`,
    using equivariance of each `p`. -/
def sSup (S : OPred A → Prop) : OPred A where
  val i := F.sSup (fun v => ∃ p, S p ∧ v = p.val i)
  dom_bound i := F.sSup_le _ _ (fun v ⟨p, _, hv⟩ => hv ▸ p.dom_bound i)
  natural i j := by
    -- LHS: A.E i j ∧ sSup{p i | p∈S}
    -- By distributivity: = sSup{A.E i j ∧ p i | p∈S}
    -- ≤ sSup{p j | p∈S}  since each A.E i j ∧ p i ≤ p j
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨w, ⟨p, hpS, hw⟩, hvw⟩
    rw [hw] at hvw; rw [hvw]
    -- v = A.E i j ∧ p i; need v ≤ sSup{p j | ...}
    apply F.le_trans (p.natural i j)
    exact F.le_sSup _ _ ⟨p, hpS, rfl⟩

theorem le_sSup (S : OPred A → Prop) (p : OPred A) (hpS : S p) : le p (sSup S) :=
  fun _i => F.le_sSup _ _ ⟨p, hpS, rfl⟩

theorem sSup_le (S : OPred A → Prop) (q : OPred A) (h : ∀ p, S p → le p q) :
    le (sSup S) q :=
  fun i => F.sSup_le _ _ (fun _v ⟨p, hpS, hv⟩ => hv ▸ h p hpS i)

/-- Frame distributivity: `meet p (sSup S) = sSup {meet p q | q ∈ S}`. -/
theorem meet_sSup_distrib (p : OPred A) (S : OPred A → Prop) :
    meet p (sSup S) = sSup (fun r => ∃ q, S q ∧ r = meet p q) := by
  apply le_antisymm
  · intro i
    -- (meet p (sSup S)).val i = F.meet (p.val i) (sSup{q.val i | q∈S})
    -- By F.meet_sSup_distrib: = sSup{p.val i ∧ q.val i | q∈S}
    -- = sSup{(meet p q).val i | q∈S}
    simp only [meet, sSup]
    rw [F.meet_sSup_distrib]
    apply F.sSup_le
    intro v ⟨w, ⟨q, hqS, hw⟩, hvw⟩
    rw [hw] at hvw; rw [hvw]
    exact F.le_sSup _ _ ⟨meet p q, ⟨q, hqS, rfl⟩, rfl⟩
  · intro i
    simp only [sSup, meet]
    apply F.sSup_le
    intro v ⟨r, ⟨q, hqS, hrpq⟩, hv⟩
    rw [hrpq] at hv; rw [hv]
    -- v = F.meet (p.val i) (q.val i); need ≤ F.meet (p.val i) (sSup{q'.val i | q'∈S})
    apply F.le_meet
    · exact F.meet_le_left _ _
    · exact F.le_trans (F.meet_le_right _ _) (F.le_sSup _ _ ⟨q, hqS, rfl⟩)

end OPred

/-- **OPred(F, A) is a Frame** (pointwise operations from F, equivariance preserved).
    This is the "H(Y)" of §2.227 when A is an O(Y)-valued set. -/
def opredFrame {F : Frame.{u}} (A : OValuedSet F) : Frame.{u} where
  carrier := OPred A
  le      := OPred.le
  le_refl := fun x => OPred.le_refl x
  le_trans := fun {_x _y _z} hxy hyz => OPred.le_trans hxy hyz
  le_antisymm := fun {_x _y} hxy hyx => OPred.le_antisymm hxy hyx
  top     := OPred.top A
  le_top  := OPred.le_top
  bot     := OPred.bot A
  bot_le  := OPred.bot_le
  meet    := OPred.meet
  meet_le_left  := OPred.meet_le_left
  meet_le_right := OPred.meet_le_right
  le_meet := fun {_z _x _y} hzx hzy => OPred.le_meet hzx hzy
  sSup    := OPred.sSup
  le_sSup := fun S a ha => OPred.le_sSup S a ha
  sSup_le := fun S b h => OPred.sSup_le S b h
  meet_sSup_distrib := fun a S => OPred.meet_sSup_distrib a S

/-! ### H(Y): OPred on the terminal F-valued set recovers F

  In §2.227, H(Y) is the frame of F-valued predicates on the terminal
  F-valued set (carrier = PUnit, equality = F.top).  A predicate here
  is just a function `PUnit → F.carrier`, which is the same as picking
  a single element of F (subject to bounds that are trivially satisfied).
  This gives an isomorphism of frames `OPred F (OSetTerminal F) ≅ F`.

  We make this explicit by two order-preserving maps and show they are
  inverse isomorphisms of frames. -/

/-- The isomorphism H(terminal) ≅ F:
    forward direction — evaluate at the unique point `PUnit.unit`. -/
def hTerminal_toFrame {F : Frame.{u}} (p : OPred (OSetTerminal F)) : F.carrier :=
  p.val PUnit.unit

/-- Backward direction: constant predicate `fun _ => a`. -/
def hTerminal_ofFrame {F : Frame.{u}} (a : F.carrier) : OPred (OSetTerminal F) where
  val _ := a
  dom_bound _ := F.le_top _   -- a ≤ F.top = E () ()
  natural _ _ := F.meet_le_right _ _  -- F.top ∧ a ≤ a

/-- `hTerminal_ofFrame` is a left inverse: `ofFrame (toFrame p) = p`. -/
theorem hTerminal_leftInv {F : Frame.{u}} (p : OPred (OSetTerminal F)) :
    hTerminal_ofFrame (hTerminal_toFrame p) = p := by
  cases p with
  | mk val db nat =>
    simp only [hTerminal_ofFrame, hTerminal_toFrame]
    -- congr 1 closes: the val fields are both `fun _ => val PUnit.unit`, equal by PUnit
    -- uniqueness; dom_bound/natural equal by proof irrelevance.
    congr 1

/-- `hTerminal_ofFrame` is a right inverse: `toFrame (ofFrame a) = a`. -/
theorem hTerminal_rightInv {F : Frame.{u}} (a : F.carrier) :
    hTerminal_toFrame (hTerminal_ofFrame a : OPred (OSetTerminal F)) = a := rfl

theorem hTerminal_mono' {F : Frame.{u}} {a b : F.carrier}
    (h : F.le a b) : OPred.le (hTerminal_ofFrame a : OPred (OSetTerminal F))
      (hTerminal_ofFrame b) :=
  fun _ => h

-- BOOK §2.227: The full equivalence  Map(O(Y)-valued sets) ≃ H(Y)  states that
-- the category OSet(O(Y)) of O(Y)-valued sets is equivalent to the category of
-- sheaves on Y (= H(Y) in Freyd's notation), where H(Y) is the topos of
-- O(Y)-valued sets whose "maps" are the local sections.
--
-- The above establishes:
--   • OSet(F) is a category  (osetCat instance),
--   • for each F-valued set A, OPred(F, A) is a Frame / Heyting algebra
--     (opredFrame instance), giving the subobject lattice,
--   • OPred(F, OSetTerminal F) ≅ F as frames
--     (hTerminal_leftInv / hTerminal_rightInv).
--
-- The full equivalence functor OSet(O(Y)) ≃ Sh(Y) requires:
--   (a) sheaf / presheaf infrastructure (compatible families, gluing),
--   (b) the "irredundant" / separated notion on O(Y)-valued sets,
--   (c) the associated-sheaf functor and unit/counit natural transformations.
-- These need the presheaf framework not yet in the repo; left as a precise TODO.

-- BOOK §2.331: O(X)-valued sets and the geometric representation theorem.
-- Any countable tabular unitary division allegory embeds in (O(X)-valued sets)^ω
-- for a suitable locale O(X). This uses §2.227 + §1.74 (focal representation).
-- Requires: tabular/division allegory infrastructure (§2.1), focal representation
-- theorem (§1.741–§1.742), and the sheaf/locale machinery above.
-- Left as a precise TODO.

-- BOOK §1.74x: Representation theorems via opens.
-- §1.741: Every logos can be embedded in a logos of the form Sh(O(X)).
-- §1.742: Countable logos embeds in Sh(O(ℝ)).
-- These require the focal representation + sheaf machinery; left as TODO.

end Freyd
