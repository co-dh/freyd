/-
  Freyd & Scedrov, *Categories and Allegories* §2.158, Target 3 — discharge of
  the σ-UNIFORM INSTANCE BOUND `InstanceBound allegoryAxioms N`.

  `InstanceBound Ax N` (S2_158c) asks, for each axiom `(A, B) ∈ Ax` and EVERY
  substitution σ, for a graph map `[σB] → [σA]` all of whose fibres are covered
  by ≤ N vertices, N independent of σ.  This file constructs the map and the
  bound for each of the 14 members of `allegoryAxioms` (S2_158b):

  * the isomorphism-shaped axioms (`∩`-comm, `∩`-assoc, `;`-assoc both ways,
    `(XY)° ⊆ Y°X°`, `X°° ⊆ X`) and the collapse-onto-a-point axioms
    (`1 ⊆ 1∩1`, `1X ⊆ X`, `X1 ⊆ X`) have a vertex-level RETRACTION, so every
    fibre is a singleton (`fibBound_of_retraction`) — bound 1;
  * the `∩`-eliminations embed `[σX₀]` into `[σX₀ ∩ σX₁]`; the embedding is
    injective except that a mark coincidence in the OTHER factor can merge the
    two marks — every collision lies in the 2-element mark set — bound 3;
  * semidistribution and the two modular laws genuinely merge vertices, but
    every collision of their canonical maps lies in the (≤ 2-element) matching
    leaf fibre or in the ≤ 8 mark classes of the source — bounds 9 / 10 / 10.

  Engine: the quotient-equality inversions `gcomp_mk_eq` / `meet_mk_eq` of
  S2_158c, specialised to per-layer COLLISION LEMMAS (`gcomp_inl_inj`,
  `meet_inl_inl`, …), and `Quot.exists_rep` (choice-free) to walk the gluing
  towers.  Everything is constructive: axioms `{propext, Quot.sound}` only.

  HEADLINE: `instanceBound_allegoryAxioms : InstanceBound allegoryAxioms 10`
  (and the packaged `∃ N` form) — the one still-open hypothesis of ingredient
  (b) BOUNDED STEP (`step_hom_tame`, `step_merge_bound`) is now discharged for
  the concrete valid axiom set `allegoryAxioms`.

  STRICTLY MATHLIB-FREE.  Only Lean 4 core + `Freyd.*`.
-/

module

public import Freyd.S2_158c_StepRigidity

namespace Freyd.S2_158

variable {L : Type}

/-! ## Generic fibre-bound helpers -/

/-- Fibres of a map with a vertex-level retraction are singletons: the cover
    of the fibre over `y` is `[g y]`.  (The retraction need only be a
    function, not a graph map.) -/
theorem fibBound_of_retraction {X Y : Type} (f : X → Y) (g : Y → X)
    (hgf : ∀ x, g (f x) = x) :
    ∀ y, ∃ l, FibCover f y l ∧ l.length ≤ 1 := by
  intro y
  refine ⟨[g y], fun x hx => ?_, Nat.le_refl 1⟩
  have hx' : x = g y := by rw [← hgf x, hx]
  rw [hx']
  exact List.mem_cons_self ..

/-- Weaken a fibre bound. -/
theorem fibBound_mono {X Y : Type} {f : X → Y} {m n : Nat} (h : m ≤ n)
    (hb : ∀ y, ∃ l, FibCover f y l ∧ l.length ≤ m) :
    ∀ y, ∃ l, FibCover f y l ∧ l.length ≤ n := fun y => by
  obtain ⟨l, hc, hl⟩ := hb y
  exact ⟨l, hc, Nat.le_trans hl h⟩

/-! ## Per-layer collision lemmas

  Specialisations of the quotient-equality inversions `gcomp_mk_eq` /
  `meet_mk_eq` (S2_158c) to the four raw-vertex constellations, phrased as
  the dichotomies the fibre analyses below consume: two raw vertices of a
  gluing land in one class only if they are equal or both are marks. -/

/-- In a `gcomp`, two left-copy vertices in one class are EQUAL (the single
    gluing pair has only one left member, the mark `t₁`). -/
theorem gcomp_inl_inj {G₁ G₂ : LGraph L} {u u' : G₁.V}
    (h : (Quot.mk (compRel G₁ G₂) (Sum.inl u) : (gcomp G₁ G₂).V)
        = Quot.mk (compRel G₁ G₂) (Sum.inl u')) : u = u' := by
  rcases gcomp_mk_eq h with heq | ⟨hp, hq⟩
  · exact Sum.inl.inj heq
  · rcases hp with hp | hp
    · rcases hq with hq | hq
      · rw [Sum.inl.inj hp, Sum.inl.inj hq]
      · nomatch hq
    · nomatch hp

/-- In a `gcomp`, two right-copy vertices in one class are equal. -/
theorem gcomp_inr_inj {G₁ G₂ : LGraph L} {w w' : G₂.V}
    (h : (Quot.mk (compRel G₁ G₂) (Sum.inr w) : (gcomp G₁ G₂).V)
        = Quot.mk (compRel G₁ G₂) (Sum.inr w')) : w = w' := by
  rcases gcomp_mk_eq h with heq | ⟨hp, hq⟩
  · exact Sum.inr.inj heq
  · rcases hp with hp | hp
    · nomatch hp
    · rcases hq with hq | hq
      · nomatch hq
      · rw [Sum.inr.inj hp, Sum.inr.inj hq]

/-- In a `gcomp`, a left- and a right-copy vertex share a class only at the
    glued pair `t₁ = s₂`. -/
theorem gcomp_inl_inr {G₁ G₂ : LGraph L} {u : G₁.V} {w : G₂.V}
    (h : (Quot.mk (compRel G₁ G₂) (Sum.inl u) : (gcomp G₁ G₂).V)
        = Quot.mk (compRel G₁ G₂) (Sum.inr w)) : u = G₁.t ∧ w = G₂.s := by
  rcases gcomp_mk_eq h with heq | ⟨hp, hq⟩
  · nomatch heq
  · rcases hp with hp | hp
    · rcases hq with hq | hq
      · nomatch hq
      · exact ⟨Sum.inl.inj hp, Sum.inr.inj hq⟩
    · nomatch hp

/-- A left-copy vertex equal (as a class) to a mark of the `gcomp` is a mark
    of the left factor. -/
theorem gcomp_inl_mark {G₁ G₂ : LGraph L} {u : G₁.V}
    (h : (Quot.mk (compRel G₁ G₂) (Sum.inl u) : (gcomp G₁ G₂).V) = (gcomp G₁ G₂).s
       ∨ (Quot.mk (compRel G₁ G₂) (Sum.inl u) : (gcomp G₁ G₂).V) = (gcomp G₁ G₂).t) :
    u = G₁.s ∨ u = G₁.t := by
  rcases h with h | h
  · exact Or.inl (gcomp_inl_inj h)
  · exact Or.inr (gcomp_inl_inr h).1

/-- A right-copy vertex equal (as a class) to a mark of the `gcomp` is a mark
    of the right factor. -/
theorem gcomp_inr_mark {G₁ G₂ : LGraph L} {w : G₂.V}
    (h : (Quot.mk (compRel G₁ G₂) (Sum.inr w) : (gcomp G₁ G₂).V) = (gcomp G₁ G₂).s
       ∨ (Quot.mk (compRel G₁ G₂) (Sum.inr w) : (gcomp G₁ G₂).V) = (gcomp G₁ G₂).t) :
    w = G₂.s ∨ w = G₂.t := by
  rcases h with h | h
  · exact Or.inl (gcomp_inl_inr h.symm).2
  · exact Or.inr (gcomp_inr_inj h)

/-- A left-copy vertex in the `s`-cluster of a `meet` is the left `s`-mark. -/
private theorem sClu_inl {G₁ G₂ : LGraph L} {u : G₁.V}
    (h : sClu G₁ G₂ (Sum.inl u)) : u = G₁.s := by
  rcases h with h | h
  · exact Sum.inl.inj h
  · nomatch h

private theorem tClu_inl {G₁ G₂ : LGraph L} {u : G₁.V}
    (h : tClu G₁ G₂ (Sum.inl u)) : u = G₁.t := by
  rcases h with h | h
  · exact Sum.inl.inj h
  · nomatch h

private theorem sClu_inr {G₁ G₂ : LGraph L} {w : G₂.V}
    (h : sClu G₁ G₂ (Sum.inr w)) : w = G₂.s := by
  rcases h with h | h
  · nomatch h
  · exact Sum.inr.inj h

private theorem tClu_inr {G₁ G₂ : LGraph L} {w : G₂.V}
    (h : tClu G₁ G₂ (Sum.inr w)) : w = G₂.t := by
  rcases h with h | h
  · nomatch h
  · exact Sum.inr.inj h

private theorem clu_mark_inl {G₁ G₂ : LGraph L} {u : G₁.V}
    (h : sClu G₁ G₂ (Sum.inl u) ∨ tClu G₁ G₂ (Sum.inl u)) :
    u = G₁.s ∨ u = G₁.t := h.imp sClu_inl tClu_inl

private theorem clu_mark_inr {G₁ G₂ : LGraph L} {w : G₂.V}
    (h : sClu G₁ G₂ (Sum.inr w) ∨ tClu G₁ G₂ (Sum.inr w)) :
    w = G₂.s ∨ w = G₂.t := h.imp sClu_inr tClu_inr

/-- In a `meet`, two left-copy vertices in one class are equal or both are
    marks of the left factor. -/
theorem meet_inl_inl {G₁ G₂ : LGraph L} {u u' : G₁.V}
    (h : (Quot.mk (meetRel G₁ G₂) (Sum.inl u) : (meet G₁ G₂).V)
        = Quot.mk (meetRel G₁ G₂) (Sum.inl u')) :
    u = u' ∨ ((u = G₁.s ∨ u = G₁.t) ∧ (u' = G₁.s ∨ u' = G₁.t)) := by
  rcases meet_mk_eq h with heq | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨_, hp, hq⟩
  · exact Or.inl (Sum.inl.inj heq)
  · exact Or.inr ⟨Or.inl (sClu_inl hp), Or.inl (sClu_inl hq)⟩
  · exact Or.inr ⟨Or.inr (tClu_inl hp), Or.inr (tClu_inl hq)⟩
  · exact Or.inr ⟨clu_mark_inl hp, clu_mark_inl hq⟩

/-- In a `meet`, two right-copy vertices in one class are equal or both are
    marks of the right factor. -/
theorem meet_inr_inr {G₁ G₂ : LGraph L} {w w' : G₂.V}
    (h : (Quot.mk (meetRel G₁ G₂) (Sum.inr w) : (meet G₁ G₂).V)
        = Quot.mk (meetRel G₁ G₂) (Sum.inr w')) :
    w = w' ∨ ((w = G₂.s ∨ w = G₂.t) ∧ (w' = G₂.s ∨ w' = G₂.t)) := by
  rcases meet_mk_eq h with heq | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨_, hp, hq⟩
  · exact Or.inl (Sum.inr.inj heq)
  · exact Or.inr ⟨Or.inl (sClu_inr hp), Or.inl (sClu_inr hq)⟩
  · exact Or.inr ⟨Or.inr (tClu_inr hp), Or.inr (tClu_inr hq)⟩
  · exact Or.inr ⟨clu_mark_inr hp, clu_mark_inr hq⟩

/-- In a `meet`, a left- and a right-copy vertex share a class only at marks
    (the two gluing pairs join marks to marks). -/
theorem meet_inl_inr {G₁ G₂ : LGraph L} {u : G₁.V} {w : G₂.V}
    (h : (Quot.mk (meetRel G₁ G₂) (Sum.inl u) : (meet G₁ G₂).V)
        = Quot.mk (meetRel G₁ G₂) (Sum.inr w)) :
    (u = G₁.s ∨ u = G₁.t) ∧ (w = G₂.s ∨ w = G₂.t) := by
  rcases meet_mk_eq h with heq | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨_, hp, hq⟩
  · nomatch heq
  · exact ⟨Or.inl (sClu_inl hp), Or.inl (sClu_inr hq)⟩
  · exact ⟨Or.inr (tClu_inl hp), Or.inr (tClu_inr hq)⟩
  · exact ⟨clu_mark_inl hp, clu_mark_inr hq⟩

/-! ## The `∩`-elimination instance maps (bound 3)

  `[σX₀] → [σX₀ ∩ σX₁]` is the left injection.  It is injective except that a
  mark coincidence in the OTHER factor can merge the two marks of THIS factor
  (`meetClose`'s fourth disjunct), so every fibre is covered by the class
  representative plus the two marks. -/

/-- The left injection into a `meet`, as a mark-preserving map. -/
def meetInl (G₁ G₂ : LGraph L) : Hom G₁ (meet G₁ G₂) where
  toEHom := gluedInl _ _ _
  map_s := rfl
  map_t := rfl

/-- The right injection into a `meet`, as a mark-preserving map. -/
def meetInr (G₁ G₂ : LGraph L) : Hom G₂ (meet G₁ G₂) where
  toEHom := gluedInr _ _ _
  map_s := meet_inr_s G₁ G₂
  map_t := meet_inr_t G₁ G₂

theorem meetInl_bound (G₁ G₂ : LGraph L) :
    ∀ y, ∃ l, FibCover (meetInl G₁ G₂).toEHom.onV y l ∧ l.length ≤ 3 := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  cases p with
  | inl a =>
    refine ⟨[a, G₁.s, G₁.t], fun x hx => ?_, Nat.le_refl 3⟩
    rcases meet_inl_inl hx with rfl | ⟨hu, -⟩
    · exact List.mem_cons_self ..
    · rcases hu with rfl | rfl <;> simp
  | inr b =>
    refine ⟨[G₁.s, G₁.t], fun x hx => ?_, Nat.le_succ 2⟩
    rcases (meet_inl_inr hx).1 with rfl | rfl <;> simp

theorem meetInr_bound (G₁ G₂ : LGraph L) :
    ∀ y, ∃ l, FibCover (meetInr G₁ G₂).toEHom.onV y l ∧ l.length ≤ 3 := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  cases p with
  | inl a =>
    refine ⟨[G₂.s, G₂.t], fun x hx => ?_, Nat.le_succ 2⟩
    rcases (meet_inl_inr hx.symm).2 with rfl | rfl <;> simp
  | inr b =>
    refine ⟨[b, G₂.s, G₂.t], fun x hx => ?_, Nat.le_refl 3⟩
    rcases meet_inr_inr hx with rfl | ⟨hw, -⟩
    · exact List.mem_cons_self ..
    · rcases hw with rfl | rfl <;> simp

/-! ## The point-collapse instance maps (bound 1)

  `[1∩1] → [1]`, `[σX] → [1 ; σX]`, `[σX] → [σX ; 1]`: each has a vertex-level
  retraction, so all fibres are singletons. -/

/-- `1 ⊆ 1∩1`: the constant map `[1∩1] → [1]` (the source has no edges). -/
def oneDiagHom : Hom (meet (one : LGraph L) one) one where
  toEHom := ⟨fun _ => (), fun h => by
    rcases glued_edge_elim h with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, he⟩ <;> exact he.elim⟩
  map_s := rfl
  map_t := rfl

/-- `[1∩1]` has a single vertex class. -/
theorem meetOneOne_unique (x : (meet (one : LGraph L) one).V) :
    x = Quot.mk (meetRel one one) (Sum.inl ()) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  cases p with
  | inl a => rfl
  | inr b =>
    exact (Quot.sound (r := meetRel one one) (a := Sum.inl ()) (b := Sum.inr b)
      (Or.inl ⟨rfl, rfl⟩)).symm

theorem oneDiag_bound :
    ∀ y, ∃ l, FibCover (oneDiagHom (L := L)).toEHom.onV y l ∧ l.length ≤ 1 :=
  fibBound_of_retraction _ (fun _ => Quot.mk (meetRel one one) (Sum.inl ()))
    (fun x => (meetOneOne_unique x).symm)

/-- `X ⊆ 1X`: the right injection `[σX] → [1 ; σX]`. -/
def oneCompHom (G : LGraph L) : Hom G (gcomp one G) where
  toEHom := gluedInr _ _ _
  map_s := (gcomp_glue one G).symm
  map_t := rfl

theorem oneComp_bound (G : LGraph L) :
    ∀ y, ∃ l, FibCover (oneCompHom G).toEHom.onV y l ∧ l.length ≤ 1 := by
  refine fibBound_of_retraction _
    (Quot.lift (Sum.elim (fun _ => G.s) (fun w => w)) ?_) (fun x => rfl)
  rintro (a | a) (b | b) h
  · nomatch h
  · obtain ⟨-, rfl⟩ := h; rfl
  · nomatch h
  · nomatch h

/-- `X ⊆ X1`: the left injection `[σX] → [σX ; 1]`. -/
def compOneHom (G : LGraph L) : Hom G (gcomp G one) where
  toEHom := gluedInl _ _ _
  map_s := rfl
  map_t := gcomp_glue G one

theorem compOne_bound (G : LGraph L) :
    ∀ y, ∃ l, FibCover (compOneHom G).toEHom.onV y l ∧ l.length ≤ 1 := by
  refine fibBound_of_retraction _
    (Quot.lift (Sum.elim (fun u => u) (fun _ => G.t)) ?_) (fun x => rfl)
  rintro (a | a) (b | b) h
  · nomatch h
  · obtain ⟨rfl, -⟩ := h; rfl
  · nomatch h
  · nomatch h

/-- `X°° ⊆ X`: the identity map `[σX] → [σX°°]` (the graphs coincide). -/
def recipRecipHom (G : LGraph L) : Hom G (recip (recip G)) where
  toEHom := ⟨fun x => x, fun h => h⟩
  map_s := rfl
  map_t := rfl

/-! ## The isomorphism-shaped instance maps (bound 1)

  `∩`-commutativity, `∩`-associativity, `;`-associativity (both directions)
  and `(XY)° ⊆ Y°X°` are graph ISOMORPHISMS: the canonical map has an explicit
  vertex-level inverse, so all fibres are singletons. -/

/-- `∩`-commutativity: the swap `[σX₁ ∩ σX₀] → [σX₀ ∩ σX₁]`. -/
def meetCommHom (X Y : LGraph L) : Hom (meet Y X) (meet X Y) where
  toEHom := gluedOut (gluedInr (meetRel X Y) _ _) (gluedInl (meetRel X Y) _ _) (by
    intro p p' h
    cases p with
    | inl a =>
      cases p' with
      | inl b => exact h.elim
      | inr b =>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact meet_inr_s X Y
        · exact meet_inr_t X Y
    | inr a =>
      cases p' with
      | inl b => exact h.elim
      | inr b => exact h.elim)
  map_s := meet_inr_s X Y
  map_t := meet_inr_t X Y

/-- The swap is its own inverse on vertices. -/
theorem meetComm_retract (X Y : LGraph L) (x : (meet Y X).V) :
    (meetCommHom Y X).toEHom.onV ((meetCommHom X Y).toEHom.onV x) = x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  cases p with
  | inl a => rfl
  | inr b => rfl

theorem meetComm_bound (X Y : LGraph L) :
    ∀ y, ∃ l, FibCover (meetCommHom X Y).toEHom.onV y l ∧ l.length ≤ 1 :=
  fibBound_of_retraction _ (meetCommHom Y X).toEHom.onV (meetComm_retract X Y)

/-- `∩`-associativity: `[(σX₀ ∩ σX₁) ∩ σX₂] → [σX₀ ∩ (σX₁ ∩ σX₂)]`. -/
def meetAssocHom (X Y Z : LGraph L) :
    Hom (meet (meet X Y) Z) (meet X (meet Y Z)) where
  toEHom := gluedOut
    (gluedOut (gluedInl (meetRel X (meet Y Z)) _ _)
      ((gluedInl (meetRel Y Z) _ _).comp (gluedInr (meetRel X (meet Y Z)) _ _)) (by
        intro p p' h
        cases p with
        | inl a =>
          cases p' with
          | inl b => exact h.elim
          | inr b =>
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (meet_inr_s X (meet Y Z)).symm
            · exact (meet_inr_t X (meet Y Z)).symm
        | inr a =>
          cases p' with
          | inl b => exact h.elim
          | inr b => exact h.elim))
    ((gluedInr (meetRel Y Z) _ _).comp (gluedInr (meetRel X (meet Y Z)) _ _)) (by
      intro p p' h
      cases p with
      | inl m =>
        cases p' with
        | inl m' => exact h.elim
        | inr c =>
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ((congrArg (fun m => Quot.mk (meetRel X (meet Y Z)) (Sum.inr m))
              (meet_inr_s Y Z)).trans (meet_inr_s X (meet Y Z))).symm
          · exact ((congrArg (fun m => Quot.mk (meetRel X (meet Y Z)) (Sum.inr m))
              (meet_inr_t Y Z)).trans (meet_inr_t X (meet Y Z))).symm
      | inr c =>
        cases p' with
        | inl m' => exact h.elim
        | inr c' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- `∩`-associativity, the inverse map `[σX₀ ∩ (σX₁ ∩ σX₂)] → [(σX₀ ∩ σX₁) ∩ σX₂]`. -/
def meetAssocInv (X Y Z : LGraph L) :
    Hom (meet X (meet Y Z)) (meet (meet X Y) Z) where
  toEHom := gluedOut
    ((gluedInl (meetRel X Y) _ _).comp (gluedInl (meetRel (meet X Y) Z) _ _))
    (gluedOut ((gluedInr (meetRel X Y) _ _).comp (gluedInl (meetRel (meet X Y) Z) _ _))
      (gluedInr (meetRel (meet X Y) Z) _ _) (by
        intro p p' h
        cases p with
        | inl b =>
          cases p' with
          | inl b' => exact h.elim
          | inr c =>
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (congrArg (fun m => Quot.mk (meetRel (meet X Y) Z) (Sum.inl m))
                (meet_inr_s X Y)).trans (meet_inr_s (meet X Y) Z).symm
            · exact (congrArg (fun m => Quot.mk (meetRel (meet X Y) Z) (Sum.inl m))
                (meet_inr_t X Y)).trans (meet_inr_t (meet X Y) Z).symm
        | inr c =>
          cases p' with
          | inl b => exact h.elim
          | inr c' => exact h.elim)) (by
      intro p p' h
      cases p with
      | inl a =>
        cases p' with
        | inl a' => exact h.elim
        | inr m =>
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact congrArg (fun m => Quot.mk (meetRel (meet X Y) Z) (Sum.inl m))
              (meet_inr_s X Y).symm
          · exact congrArg (fun m => Quot.mk (meetRel (meet X Y) Z) (Sum.inl m))
              (meet_inr_t X Y).symm
      | inr m =>
        cases p' with
        | inl a => exact h.elim
        | inr m' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- The two `∩`-associativity maps are mutually inverse on vertices. -/
theorem meetAssoc_retract (X Y Z : LGraph L) (x : (meet (meet X Y) Z).V) :
    (meetAssocInv X Y Z).toEHom.onV ((meetAssocHom X Y Z).toEHom.onV x) = x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  cases p with
  | inl m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl a => rfl
    | inr b => rfl
  | inr c => rfl

theorem meetAssoc_bound (X Y Z : LGraph L) :
    ∀ y, ∃ l, FibCover (meetAssocHom X Y Z).toEHom.onV y l ∧ l.length ≤ 1 :=
  fibBound_of_retraction _ (meetAssocInv X Y Z).toEHom.onV (meetAssoc_retract X Y Z)

/-- `;`-associativity `(X₀X₁)X₂ ⊆ X₀(X₁X₂)`: the instance map
    `[σX₀ ; (σX₁ ; σX₂)] → [(σX₀ ; σX₁) ; σX₂]`. -/
def gcompAssocL (X Y Z : LGraph L) :
    Hom (gcomp X (gcomp Y Z)) (gcomp (gcomp X Y) Z) where
  toEHom := gluedOut
    ((gluedInl (compRel X Y) _ _).comp (gluedInl (compRel (gcomp X Y) Z) _ _))
    (gluedOut ((gluedInr (compRel X Y) _ _).comp (gluedInl (compRel (gcomp X Y) Z) _ _))
      (gluedInr (compRel (gcomp X Y) Z) _ _) (by
        intro p p' h
        cases p with
        | inl b =>
          cases p' with
          | inl b' => exact h.elim
          | inr c =>
            obtain ⟨rfl, rfl⟩ := h
            exact gcomp_glue (gcomp X Y) Z
        | inr c =>
          cases p' with
          | inl b => exact h.elim
          | inr c' => exact h.elim)) (by
      intro p p' h
      cases p with
      | inl a =>
        cases p' with
        | inl a' => exact h.elim
        | inr m =>
          obtain ⟨rfl, rfl⟩ := h
          exact congrArg (fun m => Quot.mk (compRel (gcomp X Y) Z) (Sum.inl m))
            (gcomp_glue X Y)
      | inr m =>
        cases p' with
        | inl a => exact h.elim
        | inr m' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- `;`-associativity `X₀(X₁X₂) ⊆ (X₀X₁)X₂`: the instance map
    `[(σX₀ ; σX₁) ; σX₂] → [σX₀ ; (σX₁ ; σX₂)]`. -/
def gcompAssocR (X Y Z : LGraph L) :
    Hom (gcomp (gcomp X Y) Z) (gcomp X (gcomp Y Z)) where
  toEHom := gluedOut
    (gluedOut (gluedInl (compRel X (gcomp Y Z)) _ _)
      ((gluedInl (compRel Y Z) _ _).comp (gluedInr (compRel X (gcomp Y Z)) _ _)) (by
        intro p p' h
        cases p with
        | inl a =>
          cases p' with
          | inl a' => exact h.elim
          | inr b =>
            obtain ⟨rfl, rfl⟩ := h
            exact gcomp_glue X (gcomp Y Z)
        | inr b =>
          cases p' with
          | inl a => exact h.elim
          | inr b' => exact h.elim))
    ((gluedInr (compRel Y Z) _ _).comp (gluedInr (compRel X (gcomp Y Z)) _ _)) (by
      intro p p' h
      cases p with
      | inl m =>
        cases p' with
        | inl m' => exact h.elim
        | inr c =>
          obtain ⟨rfl, rfl⟩ := h
          exact congrArg (fun m => Quot.mk (compRel X (gcomp Y Z)) (Sum.inr m))
            (gcomp_glue Y Z)
      | inr c =>
        cases p' with
        | inl m => exact h.elim
        | inr c' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- The two `;`-associativity maps are mutually inverse on vertices (one way). -/
theorem gcompAssoc_retractL (X Y Z : LGraph L) (x : (gcomp X (gcomp Y Z)).V) :
    (gcompAssocR X Y Z).toEHom.onV ((gcompAssocL X Y Z).toEHom.onV x) = x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  cases p with
  | inl a => rfl
  | inr m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl b => rfl
    | inr c => rfl

/-- The two `;`-associativity maps are mutually inverse on vertices (other way). -/
theorem gcompAssoc_retractR (X Y Z : LGraph L) (x : (gcomp (gcomp X Y) Z).V) :
    (gcompAssocL X Y Z).toEHom.onV ((gcompAssocR X Y Z).toEHom.onV x) = x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  cases p with
  | inl m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl a => rfl
    | inr b => rfl
  | inr c => rfl

theorem gcompAssocL_bound (X Y Z : LGraph L) :
    ∀ y, ∃ l, FibCover (gcompAssocL X Y Z).toEHom.onV y l ∧ l.length ≤ 1 :=
  fibBound_of_retraction _ (gcompAssocR X Y Z).toEHom.onV (gcompAssoc_retractL X Y Z)

theorem gcompAssocR_bound (X Y Z : LGraph L) :
    ∀ y, ∃ l, FibCover (gcompAssocR X Y Z).toEHom.onV y l ∧ l.length ≤ 1 :=
  fibBound_of_retraction _ (gcompAssocL X Y Z).toEHom.onV (gcompAssoc_retractR X Y Z)

/-- `(X₀X₁)° ⊆ X₁°X₀°`: the instance map `[σX₁° ; σX₀°] → [(σX₀ ; σX₁)°]`
    (transpose the two copies; the reciprocal keeps vertices and edges). -/
def recipCompHom (X Y : LGraph L) :
    Hom (gcomp (recip Y) (recip X)) (recip (gcomp X Y)) where
  toEHom := gluedOut
    (⟨fun w => Quot.mk (compRel X Y) (Sum.inr w),
      fun h => ⟨Sum.inr _, Sum.inr _, rfl, rfl, h⟩⟩ : EHom (recip Y) (recip (gcomp X Y)))
    (⟨fun u => Quot.mk (compRel X Y) (Sum.inl u),
      fun h => ⟨Sum.inl _, Sum.inl _, rfl, rfl, h⟩⟩ : EHom (recip X) (recip (gcomp X Y)))
    (by
      intro p p' h
      cases p with
      | inl a =>
        cases p' with
        | inl a' => exact h.elim
        | inr b =>
          obtain ⟨rfl, rfl⟩ := h
          exact (gcomp_glue X Y).symm
      | inr b =>
        cases p' with
        | inl a => exact h.elim
        | inr b' => exact h.elim)
  map_s := rfl
  map_t := rfl

theorem recipComp_bound (X Y : LGraph L) :
    ∀ y, ∃ l, FibCover (recipCompHom X Y).toEHom.onV y l ∧ l.length ≤ 1 := by
  refine fibBound_of_retraction _
    (Quot.lift (Sum.elim
      (fun u => Quot.mk (compRel (recip Y) (recip X)) (Sum.inr u))
      (fun w => Quot.mk (compRel (recip Y) (recip X)) (Sum.inl w))) ?_) ?_
  · rintro (a | a) (b | b) h
    · exact h.elim
    · obtain ⟨rfl, rfl⟩ := h
      exact (gcomp_glue (recip Y) (recip X)).symm
    · exact h.elim
    · exact h.elim
  · intro x
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    cases p with
    | inl w => rfl
    | inr u => rfl

/-! ## Semidistribution (bound 9)

  `(X₀∩X₁)(X₂∩X₃) ⊆ X₀X₂ ∩ X₁X₃`: the canonical map
  `[σX₀σX₂ ∩ σX₁σX₃] → [(σX₀∩σX₁)(σX₂∩σX₃)]` sends each of the four leaf
  copies `A, B, C, D` identically onto its copy in the target.  The target
  glues MORE than the source (the four midpoint marks `A.t, B.t, C.s, D.s`
  become ONE class), so the map merges vertices — but every collision lies in
  the matching leaf (equal vertices) or among the 8 mark classes of the
  source.  Fibres are covered by the leaf representative plus the 8 marks. -/

private theorem sdAA {A B C D : LGraph L} {u u' : A.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inl u)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inl u')))) :
    u = u' ∨ (u = A.s ∨ u = A.t) := by
  rcases meet_inl_inl (gcomp_inl_inj h) with rfl | ⟨hu, -⟩
  · exact Or.inl rfl
  · exact Or.inr hu

private theorem sdAB {A B C D : LGraph L} {u : A.V} {w : B.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inl u)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inr w)))) :
    (u = A.s ∨ u = A.t) ∧ (w = B.s ∨ w = B.t) :=
  meet_inl_inr (gcomp_inl_inj h)

private theorem sdAC {A B C D : LGraph L} {u : A.V} {v : C.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inl u)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inl v)))) :
    (u = A.s ∨ u = A.t) ∧ (v = C.s ∨ v = C.t) := by
  obtain ⟨h1, h2⟩ := gcomp_inl_inr h
  constructor
  · rcases meet_inl_inl h1 with rfl | ⟨hu, -⟩
    · exact Or.inr rfl
    · exact hu
  · rcases meet_inl_inl h2 with rfl | ⟨hv, -⟩
    · exact Or.inl rfl
    · exact hv

private theorem sdAD {A B C D : LGraph L} {u : A.V} {z : D.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inl u)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inr z)))) :
    (u = A.s ∨ u = A.t) ∧ (z = D.s ∨ z = D.t) := by
  obtain ⟨h1, h2⟩ := gcomp_inl_inr h
  refine ⟨?_, (meet_inl_inr h2.symm).2⟩
  rcases meet_inl_inl h1 with rfl | ⟨hu, -⟩
  · exact Or.inr rfl
  · exact hu

private theorem sdBB {A B C D : LGraph L} {w w' : B.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inr w)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inr w')))) :
    w = w' ∨ (w = B.s ∨ w = B.t) := by
  rcases meet_inr_inr (gcomp_inl_inj h) with rfl | ⟨hw, -⟩
  · exact Or.inl rfl
  · exact Or.inr hw

private theorem sdBC {A B C D : LGraph L} {w : B.V} {v : C.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inr w)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inl v)))) :
    (w = B.s ∨ w = B.t) ∧ (v = C.s ∨ v = C.t) := by
  obtain ⟨h1, h2⟩ := gcomp_inl_inr h
  refine ⟨(meet_inl_inr h1.symm).2, ?_⟩
  rcases meet_inl_inl h2 with rfl | ⟨hv, -⟩
  · exact Or.inl rfl
  · exact hv

private theorem sdBD {A B C D : LGraph L} {w : B.V} {z : D.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inl (Quot.mk (meetRel A B) (Sum.inr w)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inr z)))) :
    (w = B.s ∨ w = B.t) ∧ (z = D.s ∨ z = D.t) := by
  obtain ⟨h1, h2⟩ := gcomp_inl_inr h
  exact ⟨(meet_inl_inr h1.symm).2, (meet_inl_inr h2.symm).2⟩

private theorem sdCC {A B C D : LGraph L} {v v' : C.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inl v)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inl v')))) :
    v = v' ∨ (v = C.s ∨ v = C.t) := by
  rcases meet_inl_inl (gcomp_inr_inj h) with rfl | ⟨hv, -⟩
  · exact Or.inl rfl
  · exact Or.inr hv

private theorem sdCD {A B C D : LGraph L} {v : C.V} {z : D.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inl v)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inr z)))) :
    (v = C.s ∨ v = C.t) ∧ (z = D.s ∨ z = D.t) :=
  meet_inl_inr (gcomp_inr_inj h)

private theorem sdDD {A B C D : LGraph L} {z z' : D.V}
    (h : (Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inr z)))
          : (gcomp (meet A B) (meet C D)).V)
       = Quot.mk (compRel (meet A B) (meet C D))
            (Sum.inr (Quot.mk (meetRel C D) (Sum.inr z')))) :
    z = z' ∨ (z = D.s ∨ z = D.t) := by
  rcases meet_inr_inr (gcomp_inr_inj h) with rfl | ⟨hz, -⟩
  · exact Or.inl rfl
  · exact Or.inr hz

/-- The semidistribution instance map
    `[σX₀σX₂ ∩ σX₁σX₃] → [(σX₀∩σX₁)(σX₂∩σX₃)]`. -/
def sdHom (A B C D : LGraph L) :
    Hom (meet (gcomp A C) (gcomp B D)) (gcomp (meet A B) (meet C D)) where
  toEHom := gluedOut
    (gluedOut
      ((gluedInl (meetRel A B) _ _).comp (gluedInl (compRel (meet A B) (meet C D)) _ _))
      ((gluedInl (meetRel C D) _ _).comp (gluedInr (compRel (meet A B) (meet C D)) _ _))
      (by
        intro p p' h
        cases p with
        | inl a =>
          cases p' with
          | inl a' => exact h.elim
          | inr c =>
            obtain ⟨rfl, rfl⟩ := h
            exact gcomp_glue (meet A B) (meet C D)
        | inr c =>
          cases p' with
          | inl a => exact h.elim
          | inr c' => exact h.elim))
    (gluedOut
      ((gluedInr (meetRel A B) _ _).comp (gluedInl (compRel (meet A B) (meet C D)) _ _))
      ((gluedInr (meetRel C D) _ _).comp (gluedInr (compRel (meet A B) (meet C D)) _ _))
      (by
        intro p p' h
        cases p with
        | inl b =>
          cases p' with
          | inl b' => exact h.elim
          | inr d =>
            obtain ⟨rfl, rfl⟩ := h
            exact (congrArg (fun m => Quot.mk (compRel (meet A B) (meet C D)) (Sum.inl m))
                (meet_inr_t A B)).trans
              ((gcomp_glue (meet A B) (meet C D)).trans
                (congrArg (fun m => Quot.mk (compRel (meet A B) (meet C D)) (Sum.inr m))
                  (meet_inr_s C D).symm))
        | inr d =>
          cases p' with
          | inl b => exact h.elim
          | inr d' => exact h.elim))
    (by
      intro p p' h
      cases p with
      | inl m =>
        cases p' with
        | inl m' => exact h.elim
        | inr m' =>
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact congrArg (fun m => Quot.mk (compRel (meet A B) (meet C D)) (Sum.inl m))
              (meet_inr_s A B).symm
          · exact congrArg (fun m => Quot.mk (compRel (meet A B) (meet C D)) (Sum.inr m))
              (meet_inr_t C D).symm
      | inr m =>
        cases p' with
        | inl m' => exact h.elim
        | inr m' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- The 8 mark classes of the semidistribution SOURCE `[σX₀σX₂ ∩ σX₁σX₃]`. -/
private def sdMarks (A B C D : LGraph L) : List (meet (gcomp A C) (gcomp B D)).V :=
  [Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inl (Quot.mk (compRel A C) (Sum.inl A.s))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inl (Quot.mk (compRel A C) (Sum.inl A.t))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inl (Quot.mk (compRel A C) (Sum.inr C.s))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inl (Quot.mk (compRel A C) (Sum.inr C.t))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inr (Quot.mk (compRel B D) (Sum.inl B.s))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inr (Quot.mk (compRel B D) (Sum.inl B.t))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inr (Quot.mk (compRel B D) (Sum.inr D.s))),
   Quot.mk (meetRel (gcomp A C) (gcomp B D)) (Sum.inr (Quot.mk (compRel B D) (Sum.inr D.t)))]

theorem sdHom_bound (A B C D : LGraph L) :
    ∀ y, ∃ l, FibCover (sdHom A B C D).toEHom.onV y l ∧ l.length ≤ 9 := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  cases p with
  | inl m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl a =>
      refine ⟨Quot.mk (meetRel (gcomp A C) (gcomp B D))
          (Sum.inl (Quot.mk (compRel A C) (Sum.inl a))) :: sdMarks A B C D,
        fun x hx => ?_, Nat.le_refl 9⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl u =>
          rcases sdAA hx with rfl | hu
          · exact List.mem_cons_self ..
          · rcases hu with rfl | rfl <;> simp [sdMarks]
        | inr v =>
          rcases (sdAC hx.symm).2 with rfl | rfl <;> simp [sdMarks]
      | inr mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl w =>
          rcases (sdAB hx.symm).2 with rfl | rfl <;> simp [sdMarks]
        | inr z =>
          rcases (sdAD hx.symm).2 with rfl | rfl <;> simp [sdMarks]
    | inr w₀ =>
      refine ⟨Quot.mk (meetRel (gcomp A C) (gcomp B D))
          (Sum.inr (Quot.mk (compRel B D) (Sum.inl w₀))) :: sdMarks A B C D,
        fun x hx => ?_, Nat.le_refl 9⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl u =>
          rcases (sdAB hx).1 with rfl | rfl <;> simp [sdMarks]
        | inr v =>
          rcases (sdBC hx.symm).2 with rfl | rfl <;> simp [sdMarks]
      | inr mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl w =>
          rcases sdBB hx with rfl | hw
          · exact List.mem_cons_self ..
          · rcases hw with rfl | rfl <;> simp [sdMarks]
        | inr z =>
          rcases (sdBD hx.symm).2 with rfl | rfl <;> simp [sdMarks]
  | inr m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl v₀ =>
      refine ⟨Quot.mk (meetRel (gcomp A C) (gcomp B D))
          (Sum.inl (Quot.mk (compRel A C) (Sum.inr v₀))) :: sdMarks A B C D,
        fun x hx => ?_, Nat.le_refl 9⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl u =>
          rcases (sdAC hx).1 with rfl | rfl <;> simp [sdMarks]
        | inr v =>
          rcases sdCC hx with rfl | hv
          · exact List.mem_cons_self ..
          · rcases hv with rfl | rfl <;> simp [sdMarks]
      | inr mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl w =>
          rcases (sdBC hx).1 with rfl | rfl <;> simp [sdMarks]
        | inr z =>
          rcases (sdCD hx.symm).2 with rfl | rfl <;> simp [sdMarks]
    | inr z₀ =>
      refine ⟨Quot.mk (meetRel (gcomp A C) (gcomp B D))
          (Sum.inr (Quot.mk (compRel B D) (Sum.inr z₀))) :: sdMarks A B C D,
        fun x hx => ?_, Nat.le_refl 9⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl u =>
          rcases (sdAD hx).1 with rfl | rfl <;> simp [sdMarks]
        | inr v =>
          rcases (sdCD hx).1 with rfl | rfl <;> simp [sdMarks]
      | inr mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl w =>
          rcases (sdBD hx).1 with rfl | rfl <;> simp [sdMarks]
        | inr z =>
          rcases sdDD hx with rfl | hz
          · exact List.mem_cons_self ..
          · rcases hz with rfl | rfl <;> simp [sdMarks]

/-! ## The two modular laws (bound 10)

  Both modular instances target `[(σX₀σX₁) ∩ σX₂]` = `meet (gcomp R S) T`, so
  they share one set of target collision lemmas.  Their sources carry TWO
  copies of one leaf (`S` for the modular law — one inside `TS°` — and `R`
  for its mirror), both mapped identically onto the single target copy: the
  matching leaf fibre has ≤ 2 elements, everything else collides only at the
  8 source mark classes. -/

/-- An edge-map out of `G` is an edge-map out of `recip G` (same vertices,
    same edges — only the marks move, and `EHom` ignores marks). -/
def EHom.ofRecip {G H : LGraph L} (f : EHom G H) : EHom (recip G) H :=
  ⟨f.onV, fun h => f.map_edge h⟩

private theorem mRR {R S T : LGraph L} {r r' : R.V}
    (h : (Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inl r)))
          : (meet (gcomp R S) T).V)
       = Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inl r')))) :
    r = r' ∨ (r = R.s ∨ r = R.t) := by
  rcases meet_inl_inl h with heq | ⟨hm, -⟩
  · exact Or.inl (gcomp_inl_inj heq)
  · exact Or.inr (gcomp_inl_mark hm)

private theorem mRS {R S T : LGraph L} {r : R.V} {s : S.V}
    (h : (Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inl r)))
          : (meet (gcomp R S) T).V)
       = Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inr s)))) :
    (r = R.s ∨ r = R.t) ∧ (s = S.s ∨ s = S.t) := by
  rcases meet_inl_inl h with heq | ⟨hm, hm'⟩
  · obtain ⟨rfl, rfl⟩ := gcomp_inl_inr heq
    exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exact ⟨gcomp_inl_mark hm, gcomp_inr_mark hm'⟩

private theorem mSS {R S T : LGraph L} {s s' : S.V}
    (h : (Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inr s)))
          : (meet (gcomp R S) T).V)
       = Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inr s')))) :
    s = s' ∨ (s = S.s ∨ s = S.t) := by
  rcases meet_inl_inl h with heq | ⟨hm, -⟩
  · exact Or.inl (gcomp_inr_inj heq)
  · exact Or.inr (gcomp_inr_mark hm)

private theorem mRT {R S T : LGraph L} {r : R.V} {t : T.V}
    (h : (Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inl r)))
          : (meet (gcomp R S) T).V)
       = Quot.mk (meetRel (gcomp R S) T) (Sum.inr t)) :
    (r = R.s ∨ r = R.t) ∧ (t = T.s ∨ t = T.t) := by
  obtain ⟨hm, ht⟩ := meet_inl_inr h
  exact ⟨gcomp_inl_mark hm, ht⟩

private theorem mST {R S T : LGraph L} {s : S.V} {t : T.V}
    (h : (Quot.mk (meetRel (gcomp R S) T)
            (Sum.inl (Quot.mk (compRel R S) (Sum.inr s)))
          : (meet (gcomp R S) T).V)
       = Quot.mk (meetRel (gcomp R S) T) (Sum.inr t)) :
    (s = S.s ∨ s = S.t) ∧ (t = T.s ∨ t = T.t) := by
  obtain ⟨hm, ht⟩ := meet_inl_inr h
  exact ⟨gcomp_inr_mark hm, ht⟩

private theorem mTT {R S T : LGraph L} {t t' : T.V}
    (h : (Quot.mk (meetRel (gcomp R S) T) (Sum.inr t) : (meet (gcomp R S) T).V)
       = Quot.mk (meetRel (gcomp R S) T) (Sum.inr t')) :
    t = t' ∨ (t = T.s ∨ t = T.t) := by
  rcases meet_inr_inr h with rfl | ⟨ht, -⟩
  · exact Or.inl rfl
  · exact Or.inr ht

/-- The modular-law instance map
    `[(σX₀ ∩ σX₂σX₁°) ; σX₁] → [(σX₀σX₁) ∩ σX₂]`.  The two copies of `σX₁`
    (inside `σX₂σX₁°` and the outer factor) both map onto the target's one. -/
def modHom (R S T : LGraph L) :
    Hom (gcomp (meet R (gcomp T (recip S))) S) (meet (gcomp R S) T) where
  toEHom := gluedOut
    (gluedOut
      ((gluedInl (compRel R S) _ _).comp (gluedInl (meetRel (gcomp R S) T) _ _))
      (gluedOut (gluedInr (meetRel (gcomp R S) T) _ _)
        (EHom.ofRecip
          ((gluedInr (compRel R S) _ _).comp (gluedInl (meetRel (gcomp R S) T) _ _)))
        (by
          intro p p' h
          cases p with
          | inl a =>
            cases p' with
            | inl a' => exact h.elim
            | inr b =>
              obtain ⟨rfl, rfl⟩ := h
              exact meet_inr_t (gcomp R S) T
          | inr b =>
            cases p' with
            | inl a => exact h.elim
            | inr b' => exact h.elim))
      (by
        intro p p' h
        cases p with
        | inl a =>
          cases p' with
          | inl a' => exact h.elim
          | inr b =>
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (meet_inr_s (gcomp R S) T).symm
            · exact congrArg (fun m => Quot.mk (meetRel (gcomp R S) T) (Sum.inl m))
                (gcomp_glue R S)
        | inr b =>
          cases p' with
          | inl a => exact h.elim
          | inr b' => exact h.elim))
    ((gluedInr (compRel R S) _ _).comp (gluedInl (meetRel (gcomp R S) T) _ _))
    (by
      intro p p' h
      cases p with
      | inl m =>
        cases p' with
        | inl m' => exact h.elim
        | inr b =>
          obtain ⟨rfl, rfl⟩ := h
          exact congrArg (fun m => Quot.mk (meetRel (gcomp R S) T) (Sum.inl m))
            (gcomp_glue R S)
      | inr b =>
        cases p' with
        | inl m => exact h.elim
        | inr b' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- The 8 mark classes of the modular SOURCE `[(σX₀ ∩ σX₂σX₁°) ; σX₁]`. -/
private def modMarks (R S T : LGraph L) :
    List (gcomp (meet R (gcomp T (recip S))) S).V :=
  [Quot.mk (compRel (meet R (gcomp T (recip S))) S)
     (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S))) (Sum.inl R.s))),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S)
     (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S))) (Sum.inl R.t))),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S)
     (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S)))
        (Sum.inr (Quot.mk (compRel T (recip S)) (Sum.inl T.s))))),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S)
     (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S)))
        (Sum.inr (Quot.mk (compRel T (recip S)) (Sum.inl T.t))))),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S)
     (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S)))
        (Sum.inr (Quot.mk (compRel T (recip S)) (Sum.inr S.s))))),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S)
     (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S)))
        (Sum.inr (Quot.mk (compRel T (recip S)) (Sum.inr S.t))))),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S) (Sum.inr S.s),
   Quot.mk (compRel (meet R (gcomp T (recip S))) S) (Sum.inr S.t)]

theorem modHom_bound (R S T : LGraph L) :
    ∀ y, ∃ l, FibCover (modHom R S T).toEHom.onV y l ∧ l.length ≤ 10 := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  cases p with
  | inl m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl r₀ =>
      refine ⟨Quot.mk (compRel (meet R (gcomp T (recip S))) S)
          (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S))) (Sum.inl r₀)))
          :: modMarks R S T,
        fun x hx => ?_, Nat.le_succ 9⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl u =>
          rcases mRR hx with rfl | hu
          · exact List.mem_cons_self ..
          · rcases hu with rfl | rfl <;> simp [modMarks]
        | inr my =>
          obtain ⟨qy, rfl⟩ := Quot.exists_rep my
          cases qy with
          | inl v =>
            rcases (mRT (T := T) hx.symm).2 with rfl | rfl <;> simp [modMarks]
          | inr w =>
            rcases (mRS hx.symm).2 with rfl | rfl <;> simp [modMarks]
      | inr s =>
        rcases (mRS hx.symm).2 with rfl | rfl <;> simp [modMarks]
    | inr s₀ =>
      refine ⟨Quot.mk (compRel (meet R (gcomp T (recip S))) S)
          (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S)))
            (Sum.inr (Quot.mk (compRel T (recip S)) (Sum.inr s₀)))))
          :: Quot.mk (compRel (meet R (gcomp T (recip S))) S) (Sum.inr s₀)
          :: modMarks R S T,
        fun x hx => ?_, Nat.le_refl 10⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl u =>
          rcases (mRS (T := T) hx).1 with rfl | rfl <;> simp [modMarks]
        | inr my =>
          obtain ⟨qy, rfl⟩ := Quot.exists_rep my
          cases qy with
          | inl v =>
            rcases (mST (R := R) hx.symm).2 with rfl | rfl <;> simp [modMarks]
          | inr w =>
            rcases mSS (R := R) (T := T) hx with rfl | hw
            · exact List.mem_cons_self ..
            · rcases hw with rfl | rfl <;> simp [modMarks]
      | inr s =>
        rcases mSS (R := R) (T := T) hx with rfl | hs
        · simp
        · rcases hs with rfl | rfl <;> simp [modMarks]
  | inr t₀ =>
    refine ⟨Quot.mk (compRel (meet R (gcomp T (recip S))) S)
        (Sum.inl (Quot.mk (meetRel R (gcomp T (recip S)))
          (Sum.inr (Quot.mk (compRel T (recip S)) (Sum.inl t₀)))))
        :: modMarks R S T,
      fun x hx => ?_, Nat.le_succ 9⟩
    obtain ⟨px, rfl⟩ := Quot.exists_rep x
    cases px with
    | inl mx =>
      obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
      cases qx with
      | inl u =>
        rcases (mRT (S := S) hx).1 with rfl | rfl <;> simp [modMarks]
      | inr my =>
        obtain ⟨qy, rfl⟩ := Quot.exists_rep my
        cases qy with
        | inl v =>
          rcases mTT (R := R) (S := S) hx with rfl | hv
          · exact List.mem_cons_self ..
          · rcases hv with rfl | rfl <;> simp [modMarks]
        | inr w =>
          rcases (mST (R := R) hx).1 with rfl | rfl <;> simp [modMarks]
    | inr s =>
      rcases (mST (R := R) hx).1 with rfl | rfl <;> simp [modMarks]

/-- The mirror modular-law instance map
    `[σX₀ ; (σX₁ ∩ σX₀°σX₂)] → [(σX₀σX₁) ∩ σX₂]`.  The two copies of `σX₀`
    (the outer factor and the one inside `σX₀°σX₂`) both map onto the
    target's one. -/
def mmodHom (R S T : LGraph L) :
    Hom (gcomp R (meet S (gcomp (recip R) T))) (meet (gcomp R S) T) where
  toEHom := gluedOut
    ((gluedInl (compRel R S) _ _).comp (gluedInl (meetRel (gcomp R S) T) _ _))
    (gluedOut
      ((gluedInr (compRel R S) _ _).comp (gluedInl (meetRel (gcomp R S) T) _ _))
      (gluedOut
        (EHom.ofRecip
          ((gluedInl (compRel R S) _ _).comp (gluedInl (meetRel (gcomp R S) T) _ _)))
        (gluedInr (meetRel (gcomp R S) T) _ _)
        (by
          intro p p' h
          cases p with
          | inl a =>
            cases p' with
            | inl a' => exact h.elim
            | inr b =>
              obtain ⟨rfl, rfl⟩ := h
              exact (meet_inr_s (gcomp R S) T).symm
          | inr b =>
            cases p' with
            | inl a => exact h.elim
            | inr b' => exact h.elim))
      (by
        intro p p' h
        cases p with
        | inl a =>
          cases p' with
          | inl a' => exact h.elim
          | inr b =>
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact congrArg (fun m => Quot.mk (meetRel (gcomp R S) T) (Sum.inl m))
                (gcomp_glue R S).symm
            · exact (meet_inr_t (gcomp R S) T).symm
        | inr b =>
          cases p' with
          | inl a => exact h.elim
          | inr b' => exact h.elim))
    (by
      intro p p' h
      cases p with
      | inl a =>
        cases p' with
        | inl a' => exact h.elim
        | inr m =>
          obtain ⟨rfl, rfl⟩ := h
          exact congrArg (fun m => Quot.mk (meetRel (gcomp R S) T) (Sum.inl m))
            (gcomp_glue R S)
      | inr m =>
        cases p' with
        | inl a => exact h.elim
        | inr m' => exact h.elim)
  map_s := rfl
  map_t := rfl

/-- The 8 mark classes of the mirror-modular SOURCE `[σX₀ ; (σX₁ ∩ σX₀°σX₂)]`. -/
private def mmodMarks (R S T : LGraph L) :
    List (gcomp R (meet S (gcomp (recip R) T))).V :=
  [Quot.mk (compRel R (meet S (gcomp (recip R) T))) (Sum.inl R.s),
   Quot.mk (compRel R (meet S (gcomp (recip R) T))) (Sum.inl R.t),
   Quot.mk (compRel R (meet S (gcomp (recip R) T)))
     (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T))
        (Sum.inr (Quot.mk (compRel (recip R) T) (Sum.inl R.s))))),
   Quot.mk (compRel R (meet S (gcomp (recip R) T)))
     (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T))
        (Sum.inr (Quot.mk (compRel (recip R) T) (Sum.inl R.t))))),
   Quot.mk (compRel R (meet S (gcomp (recip R) T)))
     (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T)) (Sum.inl S.s))),
   Quot.mk (compRel R (meet S (gcomp (recip R) T)))
     (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T)) (Sum.inl S.t))),
   Quot.mk (compRel R (meet S (gcomp (recip R) T)))
     (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T))
        (Sum.inr (Quot.mk (compRel (recip R) T) (Sum.inr T.s))))),
   Quot.mk (compRel R (meet S (gcomp (recip R) T)))
     (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T))
        (Sum.inr (Quot.mk (compRel (recip R) T) (Sum.inr T.t)))))]

theorem mmodHom_bound (R S T : LGraph L) :
    ∀ y, ∃ l, FibCover (mmodHom R S T).toEHom.onV y l ∧ l.length ≤ 10 := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  cases p with
  | inl m =>
    obtain ⟨q, rfl⟩ := Quot.exists_rep m
    cases q with
    | inl r₀ =>
      refine ⟨Quot.mk (compRel R (meet S (gcomp (recip R) T))) (Sum.inl r₀)
          :: Quot.mk (compRel R (meet S (gcomp (recip R) T)))
            (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T))
              (Sum.inr (Quot.mk (compRel (recip R) T) (Sum.inl r₀)))))
          :: mmodMarks R S T,
        fun x hx => ?_, Nat.le_refl 10⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl u =>
        rcases mRR (S := S) (T := T) hx with rfl | hu
        · exact List.mem_cons_self ..
        · rcases hu with rfl | rfl <;> simp [mmodMarks]
      | inr mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl s =>
          rcases (mRS hx.symm).2 with rfl | rfl <;> simp [mmodMarks]
        | inr mz =>
          obtain ⟨qz, rfl⟩ := Quot.exists_rep mz
          cases qz with
          | inl u =>
            rcases mRR (S := S) (T := T) hx with rfl | hu
            · simp
            · rcases hu with rfl | rfl <;> simp [mmodMarks]
          | inr v =>
            rcases (mRT (S := S) hx.symm).2 with rfl | rfl <;> simp [mmodMarks]
    | inr s₀ =>
      refine ⟨Quot.mk (compRel R (meet S (gcomp (recip R) T)))
          (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T)) (Sum.inl s₀)))
          :: mmodMarks R S T,
        fun x hx => ?_, Nat.le_succ 9⟩
      obtain ⟨px, rfl⟩ := Quot.exists_rep x
      cases px with
      | inl u =>
        rcases (mRS (T := T) hx).1 with rfl | rfl <;> simp [mmodMarks]
      | inr mx =>
        obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
        cases qx with
        | inl s =>
          rcases mSS (R := R) (T := T) hx with rfl | hs
          · exact List.mem_cons_self ..
          · rcases hs with rfl | rfl <;> simp [mmodMarks]
        | inr mz =>
          obtain ⟨qz, rfl⟩ := Quot.exists_rep mz
          cases qz with
          | inl u =>
            rcases (mRS (T := T) hx).1 with rfl | rfl <;> simp [mmodMarks]
          | inr v =>
            rcases (mST (R := R) hx.symm).2 with rfl | rfl <;> simp [mmodMarks]
  | inr t₀ =>
    refine ⟨Quot.mk (compRel R (meet S (gcomp (recip R) T)))
        (Sum.inr (Quot.mk (meetRel S (gcomp (recip R) T))
          (Sum.inr (Quot.mk (compRel (recip R) T) (Sum.inr t₀)))))
        :: mmodMarks R S T,
      fun x hx => ?_, Nat.le_succ 9⟩
    obtain ⟨px, rfl⟩ := Quot.exists_rep x
    cases px with
    | inl u =>
      rcases (mRT (S := S) hx).1 with rfl | rfl <;> simp [mmodMarks]
    | inr mx =>
      obtain ⟨qx, rfl⟩ := Quot.exists_rep mx
      cases qx with
      | inl s =>
        rcases (mST (R := R) hx).1 with rfl | rfl <;> simp [mmodMarks]
      | inr mz =>
        obtain ⟨qz, rfl⟩ := Quot.exists_rep mz
        cases qz with
        | inl u =>
          rcases (mRT (S := S) hx).1 with rfl | rfl <;> simp [mmodMarks]
        | inr v =>
          rcases mTT (R := R) (S := S) hx with rfl | hv
          · exact List.mem_cons_self ..
          · rcases hv with rfl | rfl <;> simp [mmodMarks]

/-! ## Assembly: the σ-uniform instance bound for `allegoryAxioms` -/

/-- **σ-UNIFORM INSTANCE BOUND, discharged.**  Every substitution instance of
    every member of the valid axiom set `allegoryAxioms` carries a graph map
    (right graph → left graph) whose fibres are covered by ≤ 10 vertices,
    UNIFORMLY in the substitution.  The three genuine mergers dominate the
    bound: semidistribution (9) and the two modular laws (10); everything
    else is 1 or 3. -/
theorem instanceBound_allegoryAxioms_ten : InstanceBound allegoryAxioms 10 := by
  intro p hp σ
  simp only [allegoryAxioms, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · -- ∩-elim-l
    exact ⟨meetInl _ _, fibBound_mono (by omega) (meetInl_bound _ _)⟩
  · -- ∩-elim-r
    exact ⟨meetInr _ _, fibBound_mono (by omega) (meetInr_bound _ _)⟩
  · -- ∩-comm
    exact ⟨meetCommHom _ _, fibBound_mono (by omega) (meetComm_bound _ _)⟩
  · -- ∩-assoc
    exact ⟨meetAssocHom _ _ _, fibBound_mono (by omega) (meetAssoc_bound _ _ _)⟩
  · -- 1 ⊆ 1∩1
    exact ⟨oneDiagHom, fibBound_mono (by omega) oneDiag_bound⟩
  · -- ;-assoc →
    exact ⟨gcompAssocL _ _ _, fibBound_mono (by omega) (gcompAssocL_bound _ _ _)⟩
  · -- ;-assoc ←
    exact ⟨gcompAssocR _ _ _, fibBound_mono (by omega) (gcompAssocR_bound _ _ _)⟩
  · -- 1X ⊆ X
    exact ⟨oneCompHom _, fibBound_mono (by omega) (oneComp_bound _)⟩
  · -- X1 ⊆ X
    exact ⟨compOneHom _, fibBound_mono (by omega) (compOne_bound _)⟩
  · -- (XY)° ⊆ Y°X°
    exact ⟨recipCompHom _ _, fibBound_mono (by omega) (recipComp_bound _ _)⟩
  · -- X°° ⊆ X
    exact ⟨recipRecipHom _,
      fibBound_mono (by omega) (fibBound_of_retraction _ (fun y => y) (fun _ => rfl))⟩
  · -- semidistribution
    exact ⟨sdHom _ _ _ _, fibBound_mono (by omega) (sdHom_bound _ _ _ _)⟩
  · -- modular law
    exact ⟨modHom _ _ _, modHom_bound _ _ _⟩
  · -- mirror modular law
    exact ⟨mmodHom _ _ _, mmodHom_bound _ _ _⟩

/-- **(b) BOUNDED STEP for `allegoryAxioms`, unconditionally`: a single
    rewrite from `allegoryAxioms` carries a canonical graph map all of whose
    fibres are covered by ≤ 21 vertices — no vertex-merge of more than 21
    pairwise-distinct vertices is possible in one step, in ANY context and
    under ANY substitution. -/
theorem allegory_step_hom_tame {E F : Term Nat} (st : Step allegoryAxioms E F) :
    ∃ c : Hom (toGraph F) (toGraph E),
      ∀ y, ∃ l, FibCover c.toEHom.onV y l ∧ l.length ≤ 2 * 10 + 1 :=
  step_hom_tame instanceBound_allegoryAxioms_ten st

theorem allegory_step_merge_bound {E F : Term Nat} (st : Step allegoryAxioms E F) :
    ∃ c : Hom (toGraph F) (toGraph E),
      ∀ vs : List (toGraph F).V, vs.Pairwise (· ≠ ·) →
        (∀ x ∈ vs, ∀ x' ∈ vs, c.toEHom.onV x = c.toEHom.onV x') →
        vs.length ≤ 2 * 10 + 1 :=
  step_merge_bound instanceBound_allegoryAxioms_ten st

end Freyd.S2_158
