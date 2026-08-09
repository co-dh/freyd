/-
  Freyd & Scedrov, *Categories and Allegories* §2.158, Target 3 — ingredients
  (b) BOUNDED STEP and (c) RIGIDITY of `RhombusHard entL entR` (see the OPEN
  note at the end of `Freyd/S2_158b_NoFiniteAxiom.lean`).

  (c) RIGIDITY (this file, Sorry-free): explicit designated vertices of the
  chain tower `[entR n]` — the top midpoints `pVert` and bottom midpoints
  `qVert`, built by recursion over `chainT` — and the rigidity theorem
  `rigidity`: EVERY mark-preserving graph map `[entR n] → [entL n]` sends all
  top midpoints to ONE vertex (`Pv`), all bottom midpoints to ONE vertex
  (`Qv`), and merges the marks.  The proof is the edge-uniqueness induction
  promised in the OPEN note: in the collapsed graph `[entL n]` every edge
  labelled `aL _` has target `Pv` (`entL_edge_aL`) and every edge labelled
  `cL _` has target `Qv` (`entL_edge_cL`) — no vertex counting.  Since
  `pVert i` carries an incoming `aL i`-edge (`pVert_edge`) and any graph map
  preserves labelled edges, its image is forced to be `Pv`; likewise `qVert`.

  Also here: pairwise DISTINCTNESS of the designated vertices in `[entR n]`
  (`pVert_inj` etc., via the position classifier `CPos`) — the input the
  final counting argument needs so that "merging all designated pairs" is a
  genuine collapse.

  (b) BOUNDED STEP (this file, Sorry-free modulo the isolated hypothesis
  `InstanceBound`): the CANONICAL graph map of a single rewrite
  `[C[σB]] → [C[σA]]` (`fillHom` — identity outside the redex) with ALL
  fibres bounded UNIFORMLY in σ and C (`step_hom_tame`), and the consumable
  counting corollary `step_merge_bound`: a single rewrite from `Ax` cannot
  merge more than `2N+1` pairwise-distinct vertices at once.  Machinery: the
  quotient-equality inversions `meet_mk_eq`/`gcomp_mk_eq`, the mark-aware
  fibre invariant `Tame`, and its preservation — with NO bound growth — by
  every gluing layer (`tame_meetL/R`, `tame_gcompL/R`, `tame_recip`,
  assembled in `fillTame`).  Fibre-boundedness (not vertex counting) is the
  context-invariant quantity, which is what makes Freyd's separatedness
  reduction for added axioms unnecessary.  The one remaining input is the
  σ-blow-up bound `InstanceBound` — see the OPEN note at the end.

  STRICTLY MATHLIB-FREE.  Only Lean 4 core + `Freyd.*`.
-/

module

public import Freyd.S2_158b_NoFiniteAxiom

namespace Freyd.S2_158

variable {L : Type}

/-! ## Edge inversion for glued graphs

  An edge of `glued G₁ G₂ r sv tv` is an embedded `G₁`-edge or an embedded
  `G₂`-edge (the raw edge relation has no cross edges).  This is the case
  analysis every layer of the towers below peels off. -/

/-- Invert an edge of a glued graph into its two component cases. -/
public theorem glued_edge_elim {G₁ G₂ : LGraph L}
    {r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop} {sv tv : G₁.V ⊕ G₂.V}
    {c d : (glued G₁ G₂ r sv tv).V} {A : L}
    (h : (glued G₁ G₂ r sv tv).edge c d A) :
    (∃ u v, Quot.mk r (Sum.inl u) = c ∧ Quot.mk r (Sum.inl v) = d ∧ G₁.edge u v A) ∨
    (∃ u v, Quot.mk r (Sum.inr u) = c ∧ Quot.mk r (Sum.inr v) = d ∧ G₂.edge u v A) := by
  obtain ⟨p, q, hp, hq, hraw⟩ := h
  cases p with
  | inl a => cases q with
    | inl b => exact Or.inl ⟨a, b, hp, hq, hraw⟩
    | inr b => exact hraw.elim
  | inr a => cases q with
    | inl b => exact hraw.elim
    | inr b => exact Or.inr ⟨a, b, hp, hq, hraw⟩

/-! ### The mark identifications of the two gluings, as reusable equations -/

/-- In a `meet`, the second factor's `s`-mark is the `s`-mark. -/
public theorem meet_inr_s (G₁ G₂ : LGraph L) :
    (Quot.mk (meetRel G₁ G₂) (Sum.inr G₂.s) : (meet G₁ G₂).V) = (meet G₁ G₂).s :=
  (Quot.sound (r := meetRel G₁ G₂) (a := Sum.inl G₁.s) (b := Sum.inr G₂.s)
    (Or.inl ⟨rfl, rfl⟩)).symm

/-- In a `meet`, the second factor's `t`-mark is the `t`-mark. -/
public theorem meet_inr_t (G₁ G₂ : LGraph L) :
    (Quot.mk (meetRel G₁ G₂) (Sum.inr G₂.t) : (meet G₁ G₂).V) = (meet G₁ G₂).t :=
  (Quot.sound (r := meetRel G₁ G₂) (a := Sum.inl G₁.t) (b := Sum.inr G₂.t)
    (Or.inr ⟨rfl, rfl⟩)).symm

/-- In a `gcomp`, the first factor's `t`-mark is glued to the second's `s`-mark. -/
public theorem gcomp_glue (G₁ G₂ : LGraph L) :
    (Quot.mk (compRel G₁ G₂) (Sum.inl G₁.t) : (gcomp G₁ G₂).V)
      = Quot.mk (compRel G₁ G₂) (Sum.inr G₂.s) :=
  Quot.sound (r := compRel G₁ G₂) (a := Sum.inl G₁.t) (b := Sum.inr G₂.s) ⟨rfl, rfl⟩

/-! ## The two lens-factor shapes

  Every leaf factor of the `entL`/`branch` towers is one of two meets of an
  arrow with a reciprocated arrow.  In each, both edges run between the two
  marks, and the label decides the direction. -/

/-- Edges of `x ∩ y°` (shape of `entL`'s first border factor and of the first
    factor of every `branch`): the `x`-edge runs `s → t`, the `y`-edge `t → s`. -/
public theorem meet_arrow_recip_edge {x y A : Nat}
    {c d : (meet (arrow x) (recip (arrow y))).V}
    (h : (meet (arrow x) (recip (arrow y))).edge c d A) :
    (A = x ∧ c = (meet (arrow x) (recip (arrow y))).s
           ∧ d = (meet (arrow x) (recip (arrow y))).t) ∨
    (A = y ∧ c = (meet (arrow x) (recip (arrow y))).t
           ∧ d = (meet (arrow x) (recip (arrow y))).s) := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact Or.inl ⟨rfl, hu.symm, hv.symm⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · rw [← hu]; exact meet_inr_t _ _
    · rw [← hv]; exact meet_inr_s _ _

/-- Edges of `y° ∩ x` (shape of `entL`'s last border factor and of the second
    factor of every `branch`): the `y`-edge runs `t → s`, the `x`-edge `s → t`. -/
public theorem meet_recip_arrow_edge {x y A : Nat}
    {c d : (meet (recip (arrow y)) (arrow x)).V}
    (h : (meet (recip (arrow y)) (arrow x)).edge c d A) :
    (A = y ∧ c = (meet (recip (arrow y)) (arrow x)).t
           ∧ d = (meet (recip (arrow y)) (arrow x)).s) ∨
    (A = x ∧ c = (meet (recip (arrow y)) (arrow x)).s
           ∧ d = (meet (recip (arrow y)) (arrow x)).t) := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact Or.inl ⟨rfl, hu.symm, hv.symm⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · rw [← hu]; exact meet_inr_s _ _
    · rw [← hv]; exact meet_inr_t _ _

/-! ## Label arithmetic

  The four label families `aL, bL, cL, dL` live in disjoint residue classes
  mod 4, so a label can belong to at most one family. -/

public theorem aL_ne_bL {i j : Nat} : aL i ≠ bL j := by simp only [aL, bL]; omega
public theorem aL_ne_cL {i j : Nat} : aL i ≠ cL j := by simp only [aL, cL]; omega
public theorem aL_ne_dL {i j : Nat} : aL i ≠ dL j := by simp only [aL, dL]; omega
public theorem cL_ne_bL {i j : Nat} : cL i ≠ bL j := by simp only [cL, bL]; omega
public theorem cL_ne_dL {i j : Nat} : cL i ≠ dL j := by simp only [cL, dL]; omega

/-! ## Edge-uniqueness in the collapsed tower `[entL n]`

  The designated collapse targets: `Pv n` is the class (in `[entL n]`) of the
  `s`-mark of the `mids`-tower — the collapsed top vertex `P` — and `Qv n` the
  class of its `t`-mark — the collapsed bottom vertex `Q`.  The lemmas
  `entL_edge_aL` / `entL_edge_cL` say: EVERY `aL`-labelled edge of `[entL n]`
  ends at `Pv n`, and EVERY `cL`-labelled edge ends at `Qv n` — the
  edge-uniqueness that drives rigidity. -/

/-- The collapsed top vertex `P` of `[entL n]`: the class of the `s`-mark of
    the `mids` tower under the two gluing layers of `entL`. -/
@[expose] public def Pv (n : Nat) : (toGraph (entL n)).V :=
  Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inl (toGraph (mids n)).s)))))

/-- The collapsed bottom vertex `Q` of `[entL n]`: the class of the `t`-mark
    of the `mids` tower. -/
@[expose] public def Qv (n : Nat) : (toGraph (entL n)).V :=
  Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inl (toGraph (mids n)).t)))))

/-- The middle vertex of branch `j` (the collapse image of corner `v_{j+1}`):
    the joint of the branch's two factors. -/
@[expose] public def branchMid (j : Nat) : (toGraph (branch j)).V :=
  Quot.mk _ (Sum.inl (toGraph (.meet (.var (bL j)) (.recip (.var (aL (j+1)))))).t)

/-- In a branch, the only `aL`-labelled edge is `aL (j+1)`, from the branch's
    middle vertex to the `s`-mark (the collapsed `P`). -/
public theorem branch_edge_aL_full {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (aL i)) :
    i = j + 1 ∧ c = branchMid j ∧ d = (toGraph (branch j)).s := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · rcases meet_arrow_recip_edge he with ⟨hlab, _, _⟩ | ⟨hlab, hut, hvs⟩
    · exact absurd hlab aL_ne_bL
    · subst hut; subst hvs
      exact ⟨(fun h => by simp only [aL] at h; omega) hlab, hu.symm, hv.symm⟩
  · rcases meet_recip_arrow_edge he with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
    · exact absurd hlab aL_ne_dL
    · exact absurd hlab aL_ne_cL

/-- In a branch, the only `cL`-labelled edge is `cL (j+1)`, from the branch's
    middle vertex to the `t`-mark (the collapsed `Q`). -/
public theorem branch_edge_cL_full {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (cL i)) :
    i = j + 1 ∧ c = branchMid j ∧ d = (toGraph (branch j)).t := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · rcases meet_arrow_recip_edge he with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
    · exact absurd hlab cL_ne_bL
    · exact absurd hlab.symm aL_ne_cL
  · rcases meet_recip_arrow_edge he with ⟨hlab, _, _⟩ | ⟨hlab, hus, hvt⟩
    · exact absurd hlab cL_ne_dL
    · subst hus; subst hvt
      refine ⟨(fun h => by simp only [cL] at h; omega) hlab, ?_, hv.symm⟩
      rw [← hu]
      exact (gcomp_glue _ _).symm
/-- In a branch, every `aL`-labelled edge ends at the `s`-mark (the collapsed
    top vertex `P`). -/
public theorem branch_edge_aL {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (aL i)) : d = (toGraph (branch j)).s := by
  exact (branch_edge_aL_full h).2.2

/-- In a branch, every `cL`-labelled edge ends at the `t`-mark (the collapsed
    bottom vertex `Q`). -/
public theorem branch_edge_cL {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (cL i)) : d = (toGraph (branch j)).t := by
  exact (branch_edge_cL_full h).2.2

/-- In the `mids` tower, every `aL`-labelled edge ends at the `s`-mark. -/
public theorem mids_edge_aL : ∀ {k i : Nat} {c d : (toGraph (mids k)).V},
    (toGraph (mids k)).edge c d (aL i) → d = (toGraph (mids k)).s := by
  intro k
  induction k with
  | zero => intro i c d h; exact branch_edge_aL h
  | succ m ih =>
    intro i c d h
    rcases glued_edge_elim h with ⟨u, v, _, hv, he⟩ | ⟨u, v, _, hv, he⟩
    · subst hv; rw [ih he]; rfl
    · subst hv; rw [branch_edge_aL he]
      exact meet_inr_s (toGraph (mids m)) (toGraph (branch (m+1)))

/-- In the `mids` tower, every `cL`-labelled edge ends at the `t`-mark. -/
public theorem mids_edge_cL : ∀ {k i : Nat} {c d : (toGraph (mids k)).V},
    (toGraph (mids k)).edge c d (cL i) → d = (toGraph (mids k)).t := by
  intro k
  induction k with
  | zero => intro i c d h; exact branch_edge_cL h
  | succ m ih =>
    intro i c d h
    rcases glued_edge_elim h with ⟨u, v, _, hv, he⟩ | ⟨u, v, _, hv, he⟩
    · subst hv; rw [ih he]; rfl
    · subst hv; rw [branch_edge_cL he]
      exact meet_inr_t (toGraph (mids m)) (toGraph (branch (m+1)))

/-- **Edge-uniqueness, top row.**  Every `aL`-labelled edge of the collapsed
    graph `[entL n]` ends at the collapsed top vertex `Pv n`. -/
public theorem entL_edge_aL {n i : Nat} {c d : (toGraph (entL n)).V}
    (h : (toGraph (entL n)).edge c d (aL i)) : d = Pv n := by
  rcases glued_edge_elim h with ⟨u, v, _, hv, he⟩ | ⟨u, v, _, hv, he⟩
  · exact he.elim
  · subst hv
    rcases glued_edge_elim he with ⟨u', v', _, hv', he'⟩ | ⟨u', v', _, hv', he'⟩
    · -- first border factor `a₀ ∩ b_{n+1}°`: the `a₀`-edge ends at its `t`,
      -- which is glued to the `s`-mark of the inner composite, i.e. to `P`.
      subst hv'
      rcases meet_arrow_recip_edge he' with ⟨_, _, hd⟩ | ⟨hlab, _, _⟩
      · rw [hd]
        exact congrArg (fun z => (Quot.mk _ (Sum.inr z) : (toGraph (entL n)).V))
          (gcomp_glue _ _)
      · exact absurd hlab aL_ne_bL
    · subst hv'
      rcases glued_edge_elim he' with ⟨u'', v'', _, hv'', he''⟩ | ⟨u'', v'', _, hv'', he''⟩
      · -- `mids` tower: `aL`-edges end at its `s`-mark, whose class is `Pv`.
        subst hv''; rw [mids_edge_aL he'']; rfl
      · -- last border factor `c₀° ∩ d_{n+1}`: has no `aL`-labelled edge.
        rcases meet_recip_arrow_edge he'' with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
        · exact absurd hlab aL_ne_cL
        · exact absurd hlab aL_ne_dL

/-- **Edge-uniqueness, bottom row.**  Every `cL`-labelled edge of the collapsed
    graph `[entL n]` ends at the collapsed bottom vertex `Qv n`. -/
public theorem entL_edge_cL {n i : Nat} {c d : (toGraph (entL n)).V}
    (h : (toGraph (entL n)).edge c d (cL i)) : d = Qv n := by
  rcases glued_edge_elim h with ⟨u, v, _, hv, he⟩ | ⟨u, v, _, hv, he⟩
  · exact he.elim
  · subst hv
    rcases glued_edge_elim he with ⟨u', v', _, hv', he'⟩ | ⟨u', v', _, hv', he'⟩
    · -- first border factor: no `cL`-labelled edge.
      rcases meet_arrow_recip_edge he' with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
      · exact absurd hlab.symm aL_ne_cL
      · exact absurd hlab cL_ne_bL
    · subst hv'
      rcases glued_edge_elim he' with ⟨u'', v'', _, hv'', he''⟩ | ⟨u'', v'', _, hv'', he''⟩
      · -- `mids` tower: `cL`-edges end at its `t`-mark, whose class is `Qv`.
        subst hv''; rw [mids_edge_cL he'']; rfl
      · -- last border factor: the `c₀`-edge ends at its `s`, glued to the
        -- `t`-mark of the `mids` tower, i.e. to `Q`.
        subst hv''
        rcases meet_recip_arrow_edge he'' with ⟨_, _, hd⟩ | ⟨hlab, _, _⟩
        · rw [hd]
          exact congrArg
            (fun z => (Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inr z))) : (toGraph (entL n)).V))
            (gcomp_glue _ _).symm
        · exact absurd hlab cL_ne_dL

/-- The `1 ∩ ·` layer of `entL` glues the two marks of `[entL n]`. -/
public theorem entL_s_eq_t (n : Nat) : (toGraph (entL n)).s = (toGraph (entL n)).t := rfl

/-! ## The designated vertices of the chain tower `[entR n]`

  `entR n = chainT (n+1)` is the chain of `n+2` lenses.  Each lens `i` has a
  top midpoint (between its `aL i`- and `bL i`-edges) and a bottom midpoint
  (between `cL i` and `dL i`).  `pVert`/`qVert` locate these midpoints inside
  the chain tower by recursion over `chainT`, and `pVert_edge`/`qVert_edge`
  exhibit the incoming `aL i`- and `cL i`-edges that rigidity consumes. -/

/-- Top midpoint of a single lens graph: the class gluing the head of the
    `aL i`-arrow to the tail of the `bL i`-arrow. -/
@[expose] public def lensP (i : Nat) : (toGraph (lens i)).V :=
  Quot.mk _ (Sum.inl (Quot.mk _ (Sum.inl true)))

/-- Bottom midpoint of a single lens graph. -/
@[expose] public def lensQ (i : Nat) : (toGraph (lens i)).V :=
  Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inl true)))

/-- The lens's `aL i`-edge enters its top midpoint from the `s`-mark. -/
public theorem lensP_edge (i : Nat) :
    (toGraph (lens i)).edge (toGraph (lens i)).s (lensP i) (aL i) :=
  ⟨Sum.inl (Quot.mk _ (Sum.inl false)), Sum.inl (Quot.mk _ (Sum.inl true)),
    rfl, rfl, ⟨Sum.inl false, Sum.inl true, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩⟩

/-- The lens's `cL i`-edge enters its bottom midpoint from the `s`-mark. -/
public theorem lensQ_edge (i : Nat) :
    (toGraph (lens i)).edge (toGraph (lens i)).s (lensQ i) (cL i) :=
  ⟨Sum.inr (Quot.mk _ (Sum.inl false)), Sum.inr (Quot.mk _ (Sum.inl true)),
    meet_inr_s _ _, rfl,
    ⟨Sum.inl false, Sum.inl true, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩⟩

/-- The designated top midpoints of the chain tower: `pVert k i` is the top
    midpoint of lens `i` inside `[chainT k]` (meaningful for `i ≤ k`). -/
@[expose] public def pVert : (k : Nat) → Nat → (toGraph (chainT k)).V
  | 0, _ => lensP 0
  | k+1, i =>
      if i ≤ k then Quot.mk _ (Sum.inl (pVert k i))
      else Quot.mk _ (Sum.inr (lensP (k+1)))

/-- The designated bottom midpoints of the chain tower. -/
@[expose] public def qVert : (k : Nat) → Nat → (toGraph (chainT k)).V
  | 0, _ => lensQ 0
  | k+1, i =>
      if i ≤ k then Quot.mk _ (Sum.inl (qVert k i))
      else Quot.mk _ (Sum.inr (lensQ (k+1)))

/-- Each designated top midpoint has an incoming `aL i`-labelled edge. -/
public theorem pVert_edge : ∀ k i, i ≤ k →
    ∃ u, (toGraph (chainT k)).edge u (pVert k i) (aL i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h0 : i = 0 := Nat.le_zero.mp hi
    subst h0
    exact ⟨_, lensP_edge 0⟩
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · -- i = m+1: the midpoint lives in the freshly composed lens
      have hnle : ¬ i ≤ m := Nat.not_le.mpr hgt
      have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      refine ⟨Quot.mk _ (Sum.inr (toGraph (lens (m+1))).s), ?_⟩
      simp only [pVert, if_neg hnle]
      exact ⟨Sum.inr (toGraph (lens (m+1))).s, Sum.inr (lensP (m+1)),
        rfl, rfl, lensP_edge (m+1)⟩
    · -- i ≤ m: embed the midpoint of the shorter chain
      obtain ⟨u, hu⟩ := ih i hle
      refine ⟨Quot.mk _ (Sum.inl u), ?_⟩
      simp only [pVert, if_pos hle]
      exact ⟨Sum.inl u, Sum.inl (pVert m i), rfl, rfl, hu⟩

/-- Each designated bottom midpoint has an incoming `cL i`-labelled edge. -/
public theorem qVert_edge : ∀ k i, i ≤ k →
    ∃ u, (toGraph (chainT k)).edge u (qVert k i) (cL i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h0 : i = 0 := Nat.le_zero.mp hi
    subst h0
    exact ⟨_, lensQ_edge 0⟩
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hnle : ¬ i ≤ m := Nat.not_le.mpr hgt
      have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      refine ⟨Quot.mk _ (Sum.inr (toGraph (lens (m+1))).s), ?_⟩
      simp only [qVert, if_neg hnle]
      exact ⟨Sum.inr (toGraph (lens (m+1))).s, Sum.inr (lensQ (m+1)),
        rfl, rfl, lensQ_edge (m+1)⟩
    · obtain ⟨u, hu⟩ := ih i hle
      refine ⟨Quot.mk _ (Sum.inl u), ?_⟩
      simp only [qVert, if_pos hle]
      exact ⟨Sum.inl u, Sum.inl (qVert m i), rfl, rfl, hu⟩

/-! ## (c) RIGIDITY -/

/-- **(c) RIGIDITY.**  Every mark-preserving graph map `[entR n] → [entL n]`
    sends ALL designated top midpoints to the single collapsed vertex `Pv n`,
    ALL designated bottom midpoints to `Qv n`, and merges the two marks —
    i.e. it merges all `2n + 3` designated pairs of the `(n+2)`-lens chain at
    once.  Proof: a graph map preserves the incoming `aL i`-edge of `pVert i`
    (`pVert_edge`), and in `[entL n]` every `aL`-labelled edge ends at `Pv n`
    (`entL_edge_aL`); likewise for `qVert`/`Qv`; the marks merge because
    `[entL n]`'s two marks coincide (`entL_s_eq_t`). -/
public theorem rigidity (n : Nat) (f : Hom (toGraph (entR n)) (toGraph (entL n))) :
    (∀ i, i ≤ n + 1 → f.toEHom.onV (pVert (n+1) i) = Pv n) ∧
    (∀ i, i ≤ n + 1 → f.toEHom.onV (qVert (n+1) i) = Qv n) ∧
    f.toEHom.onV (toGraph (entR n)).s = f.toEHom.onV (toGraph (entR n)).t := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := pVert_edge (n+1) i hi
    exact entL_edge_aL (f.toEHom.map_edge hu)
  · obtain ⟨u, hu⟩ := qVert_edge (n+1) i hi
    exact entL_edge_cL (f.toEHom.map_edge hu)
  · rw [f.map_s, f.map_t]; exact entL_s_eq_t n

/-- Rigidity, in designated-pair form: a mark-preserving map `[entR n] → [entL n]`
    merges every pair of designated top midpoints, every pair of designated
    bottom midpoints, and the mark pair. -/
theorem rigidity_pairs (n : Nat) (f : Hom (toGraph (entR n)) (toGraph (entL n))) :
    (∀ i j, i ≤ n + 1 → j ≤ n + 1 →
      f.toEHom.onV (pVert (n+1) i) = f.toEHom.onV (pVert (n+1) j)) ∧
    (∀ i j, i ≤ n + 1 → j ≤ n + 1 →
      f.toEHom.onV (qVert (n+1) i) = f.toEHom.onV (qVert (n+1) j)) ∧
    f.toEHom.onV (toGraph (entR n)).s = f.toEHom.onV (toGraph (entR n)).t := by
  obtain ⟨hp, hq, hst⟩ := rigidity n f
  exact ⟨fun i j hi hj => (hp i hi).trans (hp j hj).symm,
         fun i j hi hj => (hq i hi).trans (hq j hj).symm, hst⟩

/-! ## Distinctness of the designated vertices

  For the counting argument, "merging all designated pairs" must be a genuine
  collapse: the `n+2` top midpoints (and the bottom ones, and the two marks)
  are pairwise DISTINCT vertices of `[entR n]`.  Quotient classes are told
  apart by a position classifier `chainPos` (corner `j` / top `i` / bot `i`),
  built through the `Quot` tower by `Quot.lift`. -/

/-- Vertex positions of the chain tower: the corner vertices `v₀ … v_{k+1}`,
    the top midpoints `p_i`, the bottom midpoints `q_i`. -/
public inductive CPos where
  | corner : Nat → CPos
  | top : Nat → CPos
  | bot : Nat → CPos

/-- Position along a two-arrow path graph: `s ↦ 0`, midpoint `↦ 1`, `t ↦ 2`. -/
def path3 {x y : Nat} : (gcomp (arrow x) (arrow y)).V → Nat :=
  Quot.lift
    (fun p => match p with
      | Sum.inl false => 0
      | Sum.inl true => 1
      | Sum.inr false => 1
      | Sum.inr true => 2)
    (by
      intro p q h
      cases p with
      | inl a =>
        cases q with
        | inl b => exact h.elim
        | inr b => obtain ⟨rfl, rfl⟩ := h; rfl
      | inr a =>
        cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- Position classifier of a single lens graph: marks to corners `0`/`1`, the
    two midpoints to `top i` / `bot i`. -/
def lensPos (i : Nat) : (toGraph (lens i)).V → CPos :=
  Quot.lift
    (fun p => match p with
      | Sum.inl u =>
          if path3 u = 0 then .corner 0 else if path3 u = 2 then .corner 1 else .top i
      | Sum.inr u =>
          if path3 u = 0 then .corner 0 else if path3 u = 2 then .corner 1 else .bot i)
    (by
      intro p q h
      cases p with
      | inl a =>
        cases q with
        | inl b => exact h.elim
        | inr b => rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      | inr a =>
        cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- Relocate a lens-local corner into the chain: local `corner 0` is the
    chain's corner `k`, local `corner 1` its corner `k+1`; midpoints keep
    their (already global) indices. -/
def shiftC (k : Nat) : CPos → CPos
  | .corner 0 => .corner k
  | .corner (_+1) => .corner (k+1)
  | p => p

/-- The chain-tower position classifier, packed with its mark values (the
    packing is what lets the `Quot.lift` compatibility at the next gluing
    layer see that the previous `t`-mark and the fresh lens's `s`-mark agree). -/
def chainPosP : (k : Nat) → { f : (toGraph (chainT k)).V → CPos //
    f (toGraph (chainT k)).s = .corner 0 ∧ f (toGraph (chainT k)).t = .corner (k+1) }
  | 0 => ⟨lensPos 0, rfl, rfl⟩
  | k+1 =>
    ⟨Quot.lift
      (fun p => match p with
        | Sum.inl u => (chainPosP k).1 u
        | Sum.inr u => shiftC (k+1) (lensPos (k+1) u))
      (by
        intro p q h
        cases p with
        | inl a =>
          cases q with
          | inl b => exact h.elim
          | inr b =>
            obtain ⟨rfl, rfl⟩ := h
            show (chainPosP k).1 (toGraph (chainT k)).t
              = shiftC (k+1) (lensPos (k+1) (toGraph (lens (k+1))).s)
            rw [(chainPosP k).2.2]; rfl
        | inr a =>
          cases q with
          | inl b => exact h.elim
          | inr b => exact h.elim),
     (chainPosP k).2.1, rfl⟩

/-- The chain-tower position classifier. -/
def chainPos (k : Nat) : (toGraph (chainT k)).V → CPos := (chainPosP k).1

/-- Each designated top midpoint classifies as `top i`. -/
theorem chainPos_pVert : ∀ k i, i ≤ k → chainPos k (pVert k i) = .top i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h0 : i = 0 := Nat.le_zero.mp hi
    subst h0; rfl
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hnle : ¬ i ≤ m := Nat.not_le.mpr hgt
      have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      show chainPos (m+1) (pVert (m+1) (m+1)) = .top (m+1)
      simp only [pVert, if_neg hnle]
      rfl
    · have := ih i hle
      show chainPos (m+1) (pVert (m+1) i) = .top i
      simp only [pVert, if_pos hle]
      exact this

/-- Each designated bottom midpoint classifies as `bot i`. -/
theorem chainPos_qVert : ∀ k i, i ≤ k → chainPos k (qVert k i) = .bot i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h0 : i = 0 := Nat.le_zero.mp hi
    subst h0; rfl
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hnle : ¬ i ≤ m := Nat.not_le.mpr hgt
      have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      show chainPos (m+1) (qVert (m+1) (m+1)) = .bot (m+1)
      simp only [qVert, if_neg hnle]
      rfl
    · have := ih i hle
      show chainPos (m+1) (qVert (m+1) i) = .bot i
      simp only [qVert, if_pos hle]
      exact this

/-- **Distinctness, top row**: the designated top midpoints are pairwise
    distinct vertices of the chain tower. -/
theorem pVert_inj {k i j : Nat} (hi : i ≤ k) (hj : j ≤ k)
    (h : pVert k i = pVert k j) : i = j := by
  have := congrArg (chainPos k) h
  rw [chainPos_pVert k i hi, chainPos_pVert k j hj] at this
  injection this

/-- **Distinctness, bottom row.** -/
theorem qVert_inj {k i j : Nat} (hi : i ≤ k) (hj : j ≤ k)
    (h : qVert k i = qVert k j) : i = j := by
  have := congrArg (chainPos k) h
  rw [chainPos_qVert k i hi, chainPos_qVert k j hj] at this
  injection this

/-- Top and bottom midpoints never coincide. -/
theorem pVert_ne_qVert {k i j : Nat} (hi : i ≤ k) (hj : j ≤ k) :
    pVert k i ≠ qVert k j := by
  intro h
  have := congrArg (chainPos k) h
  rw [chainPos_pVert k i hi, chainPos_qVert k j hj] at this
  exact CPos.noConfusion this

/-- The two marks of the chain tower are distinct (so the mark pair is a
    genuine designated pair). -/
theorem chainT_s_ne_t (k : Nat) :
    (toGraph (chainT k)).s ≠ (toGraph (chainT k)).t := by
  intro h
  have := congrArg (chainPos k) h
  rw [show chainPos k (toGraph (chainT k)).s = .corner 0 from (chainPosP k).2.1,
    show chainPos k (toGraph (chainT k)).t = .corner (k+1) from (chainPosP k).2.2] at this
  injection this with h'
  exact Nat.noConfusion h'

/-- Midpoints are distinct from both marks. -/
theorem pVert_ne_s {k i : Nat} (hi : i ≤ k) :
    pVert k i ≠ (toGraph (chainT k)).s := by
  intro h
  have := congrArg (chainPos k) h
  rw [chainPos_pVert k i hi,
    show chainPos k (toGraph (chainT k)).s = .corner 0 from (chainPosP k).2.1] at this
  exact CPos.noConfusion this

theorem pVert_ne_t {k i : Nat} (hi : i ≤ k) :
    pVert k i ≠ (toGraph (chainT k)).t := by
  intro h
  have := congrArg (chainPos k) h
  rw [chainPos_pVert k i hi,
    show chainPos k (toGraph (chainT k)).t = .corner (k+1) from (chainPosP k).2.2] at this
  exact CPos.noConfusion this

theorem qVert_ne_s {k i : Nat} (hi : i ≤ k) :
    qVert k i ≠ (toGraph (chainT k)).s := by
  intro h
  have := congrArg (chainPos k) h
  rw [chainPos_qVert k i hi,
    show chainPos k (toGraph (chainT k)).s = .corner 0 from (chainPosP k).2.1] at this
  exact CPos.noConfusion this

theorem qVert_ne_t {k i : Nat} (hi : i ≤ k) :
    qVert k i ≠ (toGraph (chainT k)).t := by
  intro h
  have := congrArg (chainPos k) h
  rw [chainPos_qVert k i hi,
    show chainPos k (toGraph (chainT k)).t = .corner (k+1) from (chainPosP k).2.2] at this
  exact CPos.noConfusion this

/-! ## (b) BOUNDED STEP — I: quotient-equality inversion for the two gluings

  The fibre analysis of the canonical step map must recognise when two raw
  vertices of a gluing land in the same class.  Both gluings identify only
  marks, so their equivalence closures are tiny explicit relations
  (`compClose`, `meetClose`); the generic exactness lemma `quot_mk_eq_elim`
  (separating-invariant trick, `propext` only) inverts `Quot.mk`-equality
  into them. -/

/-- Generic `Quot`-exactness against any equivalence-closed relation
    containing the generator. -/
public theorem quot_mk_eq_elim {α : Type} {r : α → α → Prop} (R : α → α → Prop)
    (hrefl : ∀ p, R p p) (hsymm : ∀ {p q}, R p q → R q p)
    (htrans : ∀ {p q s}, R p q → R q s → R p s)
    (hgen : ∀ {p q}, r p q → R p q) {p q : α}
    (h : Quot.mk r p = Quot.mk r q) : R p q := by
  have key : Quot.lift (R p)
      (fun a b hab => propext ⟨fun hpa => htrans hpa (hgen hab),
                               fun hpb => htrans hpb (hsymm (hgen hab))⟩)
      (Quot.mk r q) := by
    rw [← h]; exact hrefl p
  exact key

/-- The equivalence closure of the single `gcomp` gluing pair: two raw
    vertices are identified iff equal or both in `{inl t₁, inr s₂}`. -/
@[expose] public def compClose (G₁ G₂ : LGraph L) (p q : G₁.V ⊕ G₂.V) : Prop :=
  p = q ∨ ((p = Sum.inl G₁.t ∨ p = Sum.inr G₂.s) ∧ (q = Sum.inl G₁.t ∨ q = Sum.inr G₂.s))

public theorem compClose_refl {G₁ G₂ : LGraph L} (p : G₁.V ⊕ G₂.V) : compClose G₁ G₂ p p :=
  Or.inl rfl

public theorem compClose_symm {G₁ G₂ : LGraph L} {p q : G₁.V ⊕ G₂.V}
    (h : compClose G₁ G₂ p q) : compClose G₁ G₂ q p := by
  rcases h with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hq, hp⟩

public theorem compClose_trans {G₁ G₂ : LGraph L} {p q s : G₁.V ⊕ G₂.V}
    (h₁ : compClose G₁ G₂ p q) (h₂ : compClose G₁ G₂ q s) : compClose G₁ G₂ p s := by
  rcases h₁ with rfl | ⟨hp, hq⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨_, hs⟩
    · exact Or.inr ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hs⟩

public theorem compRel_le_compClose {G₁ G₂ : LGraph L} {p q : G₁.V ⊕ G₂.V}
    (h : compRel G₁ G₂ p q) : compClose G₁ G₂ p q := by
  cases p with
  | inl a => cases q with
    | inl b => exact h.elim
    | inr b =>
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
  | inr a => cases q with
    | inl b => exact h.elim
    | inr b => exact h.elim

/-- `Quot.mk`-equality in a `gcomp` gluing, inverted. -/
public theorem gcomp_mk_eq {G₁ G₂ : LGraph L} {p q : G₁.V ⊕ G₂.V}
    (h : Quot.mk (compRel G₁ G₂) p = Quot.mk (compRel G₁ G₂) q) :
    compClose G₁ G₂ p q :=
  quot_mk_eq_elim _ compClose_refl compClose_symm compClose_trans
    compRel_le_compClose h

/-- The `s`-cluster of the `meet` gluing. -/
@[expose] public def sClu (G₁ G₂ : LGraph L) (p : G₁.V ⊕ G₂.V) : Prop :=
  p = Sum.inl G₁.s ∨ p = Sum.inr G₂.s

/-- The `t`-cluster of the `meet` gluing. -/
@[expose] public def tClu (G₁ G₂ : LGraph L) (p : G₁.V ⊕ G₂.V) : Prop :=
  p = Sum.inl G₁.t ∨ p = Sum.inr G₂.t

/-- The equivalence closure of the two `meet` gluing pairs: equality, the two
    clusters, and — when a factor's marks coincide, which chains the clusters
    together — the union of both clusters. -/
@[expose] public def meetClose (G₁ G₂ : LGraph L) (p q : G₁.V ⊕ G₂.V) : Prop :=
  p = q ∨ (sClu G₁ G₂ p ∧ sClu G₁ G₂ q) ∨ (tClu G₁ G₂ p ∧ tClu G₁ G₂ q) ∨
    ((G₁.s = G₁.t ∨ G₂.s = G₂.t) ∧
      (sClu G₁ G₂ p ∨ tClu G₁ G₂ p) ∧ (sClu G₁ G₂ q ∨ tClu G₁ G₂ q))

public theorem meetClose_refl {G₁ G₂ : LGraph L} (p : G₁.V ⊕ G₂.V) : meetClose G₁ G₂ p p :=
  Or.inl rfl

public theorem meetClose_symm {G₁ G₂ : LGraph L} {p q : G₁.V ⊕ G₂.V}
    (h : meetClose G₁ G₂ p q) : meetClose G₁ G₂ q p := by
  rcases h with rfl | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hco, hp, hq⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨hq, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hq, hp⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hco, hq, hp⟩))

/-- A vertex in both clusters witnesses a mark coincidence. -/
public theorem clu_cross {G₁ G₂ : LGraph L} {q : G₁.V ⊕ G₂.V}
    (hs : sClu G₁ G₂ q) (ht : tClu G₁ G₂ q) : G₁.s = G₁.t ∨ G₂.s = G₂.t := by
  rcases hs with rfl | rfl
  · rcases ht with h | h
    · exact Or.inl (Sum.inl.inj h)
    · nomatch h
  · rcases ht with h | h
    · nomatch h
    · exact Or.inr (Sum.inr.inj h)

public theorem meetClose_trans {G₁ G₂ : LGraph L} {p q s : G₁.V ⊕ G₂.V}
    (h₁ : meetClose G₁ G₂ p q) (h₂ : meetClose G₁ G₂ q s) : meetClose G₁ G₂ p s := by
  rcases h₁ with rfl | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hco, hp, hq⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨_, hs⟩ | ⟨htq, hs⟩ | ⟨hco, _, hs⟩
    · exact Or.inr (Or.inl ⟨hp, hq⟩)
    · exact Or.inr (Or.inl ⟨hp, hs⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨clu_cross hq htq, Or.inl hp, Or.inr hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hco, Or.inl hp, hs⟩))
  · rcases h₂ with rfl | ⟨hsq, hs⟩ | ⟨_, hs⟩ | ⟨hco, _, hs⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨clu_cross hsq hq, Or.inr hp, Or.inl hs⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hco, Or.inr hp, hs⟩))
  · rcases h₂ with rfl | ⟨hsq, hs⟩ | ⟨htq, hs⟩ | ⟨_, _, hs⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hco, hp, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hco, hp, Or.inl hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hco, hp, Or.inr hs⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hco, hp, hs⟩))

public theorem meetRel_le_meetClose {G₁ G₂ : LGraph L} {p q : G₁.V ⊕ G₂.V}
    (h : meetRel G₁ G₂ p q) : meetClose G₁ G₂ p q := by
  cases p with
  | inl a => cases q with
    | inl b => exact h.elim
    | inr b =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, Or.inr rfl⟩))
  | inr a => cases q with
    | inl b => exact h.elim
    | inr b => exact h.elim

/-- `Quot.mk`-equality in a `meet` gluing, inverted. -/
public theorem meet_mk_eq {G₁ G₂ : LGraph L} {p q : G₁.V ⊕ G₂.V}
    (h : Quot.mk (meetRel G₁ G₂) p = Quot.mk (meetRel G₁ G₂) q) :
    meetClose G₁ G₂ p q :=
  quot_mk_eq_elim _ meetClose_refl meetClose_symm meetClose_trans
    meetRel_le_meetClose h

/-! ## (b) BOUNDED STEP — II: the canonical layer maps

  Functoriality of the three graph operations in each argument, with the
  identity on the untouched (context) factor.  Filling these through a
  one-hole context (`fillHom`) yields THE canonical graph map of a single
  rewrite: identity outside the redex, the given map inside. -/

/-- Left injection into a gluing, as an edge-homomorphism. -/
@[expose] public def gluedInl {G₁ G₂ : LGraph L} (r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop)
    (sv tv : G₁.V ⊕ G₂.V) : EHom G₁ (glued G₁ G₂ r sv tv) where
  onV u := Quot.mk r (Sum.inl u)
  map_edge {u v _} h := ⟨Sum.inl u, Sum.inl v, rfl, rfl, h⟩

/-- Right injection into a gluing, as an edge-homomorphism. -/
@[expose] public def gluedInr {G₁ G₂ : LGraph L} (r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop)
    (sv tv : G₁.V ⊕ G₂.V) : EHom G₂ (glued G₁ G₂ r sv tv) where
  onV u := Quot.mk r (Sum.inr u)
  map_edge {u v _} h := ⟨Sum.inr u, Sum.inr v, rfl, rfl, h⟩

/-- `meet` is functorial in its left argument (identity on the right). -/
@[expose] public def meetHomL (T : LGraph L) {G G' : LGraph L} (f : Hom G G') :
    Hom (meet G T) (meet G' T) where
  toEHom := gluedOut (f.toEHom.comp (gluedInl _ _ _)) (gluedInr _ _ _) (by
    intro p p' hpp'
    cases p with
    | inl a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b =>
        rcases hpp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · show Quot.mk _ (Sum.inl (f.toEHom.onV G.s)) = Quot.mk _ (Sum.inr T.s)
          rw [f.map_s]
          exact (meet_inr_s G' T).symm
        · show Quot.mk _ (Sum.inl (f.toEHom.onV G.t)) = Quot.mk _ (Sum.inr T.t)
          rw [f.map_t]
          exact (meet_inr_t G' T).symm
    | inr a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b => exact hpp'.elim)
  map_s := by
    show Quot.mk _ (Sum.inl (f.toEHom.onV G.s)) = (meet G' T).s
    rw [f.map_s]; rfl
  map_t := by
    show Quot.mk _ (Sum.inl (f.toEHom.onV G.t)) = (meet G' T).t
    rw [f.map_t]; rfl

/-- `meet` is functorial in its right argument (identity on the left). -/
@[expose] public def meetHomR (T : LGraph L) {G G' : LGraph L} (f : Hom G G') :
    Hom (meet T G) (meet T G') where
  toEHom := gluedOut (gluedInl _ _ _) (f.toEHom.comp (gluedInr _ _ _)) (by
    intro p p' hpp'
    cases p with
    | inl a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b =>
        rcases hpp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · show Quot.mk _ (Sum.inl T.s) = Quot.mk _ (Sum.inr (f.toEHom.onV G.s))
          rw [f.map_s]
          exact (meet_inr_s T G').symm
        · show Quot.mk _ (Sum.inl T.t) = Quot.mk _ (Sum.inr (f.toEHom.onV G.t))
          rw [f.map_t]
          exact (meet_inr_t T G').symm
    | inr a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b => exact hpp'.elim)
  map_s := rfl
  map_t := rfl

/-- `gcomp` is functorial in its left argument (identity on the right). -/
@[expose] public def gcompHomL (T : LGraph L) {G G' : LGraph L} (f : Hom G G') :
    Hom (gcomp G T) (gcomp G' T) where
  toEHom := gluedOut (f.toEHom.comp (gluedInl _ _ _)) (gluedInr _ _ _) (by
    intro p p' hpp'
    cases p with
    | inl a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b =>
        obtain ⟨rfl, rfl⟩ := hpp'
        show Quot.mk _ (Sum.inl (f.toEHom.onV G.t)) = Quot.mk _ (Sum.inr T.s)
        rw [f.map_t]
        exact gcomp_glue G' T
    | inr a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b => exact hpp'.elim)
  map_s := by
    show Quot.mk _ (Sum.inl (f.toEHom.onV G.s)) = (gcomp G' T).s
    rw [f.map_s]; rfl
  map_t := rfl

/-- `gcomp` is functorial in its right argument (identity on the left). -/
@[expose] public def gcompHomR (T : LGraph L) {G G' : LGraph L} (f : Hom G G') :
    Hom (gcomp T G) (gcomp T G') where
  toEHom := gluedOut (gluedInl _ _ _) (f.toEHom.comp (gluedInr _ _ _)) (by
    intro p p' hpp'
    cases p with
    | inl a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b =>
        obtain ⟨rfl, rfl⟩ := hpp'
        show Quot.mk _ (Sum.inl T.t) = Quot.mk _ (Sum.inr (f.toEHom.onV G.s))
        rw [f.map_s]
        exact gcomp_glue T G'
    | inr a =>
      cases p' with
      | inl b => exact hpp'.elim
      | inr b => exact hpp'.elim)
  map_s := rfl
  map_t := by
    show Quot.mk _ (Sum.inr (f.toEHom.onV G.t)) = (gcomp T G').t
    rw [f.map_t]; rfl

/-- `recip` is functorial: same vertex map, marks swapped. -/
@[expose] public def recipHom {G G' : LGraph L} (f : Hom G G') : Hom (recip G) (recip G') where
  toEHom := ⟨f.toEHom.onV, f.toEHom.map_edge⟩
  map_s := f.map_t
  map_t := f.map_s

/-- **The canonical filled map** — context-functoriality of `toGraph`.  A
    graph map on the redex extends through any one-hole context: identity
    outside, the given map inside. -/
@[expose] public def fillHom : (C : Ctx Nat) → {E F : Term Nat} →
    Hom (toGraph E) (toGraph F) → Hom (toGraph (C.fill E)) (toGraph (C.fill F))
  | .hole, _, _, f => f
  | .recip C, _, _, f => recipHom (fillHom C f)
  | .meetL C T, _, _, f => meetHomL (toGraph T) (fillHom C f)
  | .meetR T C, _, _, f => meetHomR (toGraph T) (fillHom C f)
  | .compL C T, _, _, f => gcompHomL (toGraph T) (fillHom C f)
  | .compR T C, _, _, f => gcompHomR (toGraph T) (fillHom C f)

/-! ## (b) BOUNDED STEP — III: the fibre invariant `Tame`

  FIBRE-BOUNDEDNESS is the invariant that survives context-filling (vertex
  counts do not — the context is arbitrary).  `Tame f M` bounds every fibre
  of `f` by a cover list of length ≤ M, with a finer budget at the two marks:

  * `interior`: non-mark fibres are covered by ≤ M vertices;
  * `marks_ne` (marks distinct): the two mark fibres carry covers HEADED by
    the domain marks, with JOINT budget `|ls| + |lt| + 2 ≤ M + 1` — the sum
    coupling is what lets a mark-merging layer pay for the union of the two
    fibres with the head pair collapsing to one class (the `−1`);
  * `marks_eq` (marks merged): one tail `l` covers the single mark fibre with
    EITHER domain mark at the head (`|l| + 1 ≤ M`) — the double-head form is
    what `recip` (mark swap) and the `gcomp` layer (which re-separates the
    marks) consume.

  Each gluing layer preserves `Tame` with the SAME `M` — no growth — so the
  canonical filled map of a rewrite has all fibres bounded by the redex map's
  bound, independent of the context. -/

/-- `l` covers the fibre of `f` over `y`. -/
@[expose] public def FibCover {X Y : Type} (f : X → Y) (y : Y) (l : List X) : Prop :=
  ∀ x, f x = y → x ∈ l

/-- A cover stays a cover under consing. -/
public theorem FibCover.cons {X Y : Type} {f : X → Y} {y : Y} {l : List X}
    (h : FibCover f y l) (a : X) : FibCover f y (a :: l) :=
  fun x hx => List.mem_cons_of_mem a (h x hx)

/-- The mark-aware fibre-bound invariant (see the section header). -/
public structure Tame {G H : LGraph L} (f : Hom G H) (M : Nat) : Prop where
  interior : ∀ y, y ≠ H.s → y ≠ H.t →
    ∃ l, FibCover f.toEHom.onV y l ∧ l.length ≤ M
  marks_eq : H.s = H.t →
    ∃ l, FibCover f.toEHom.onV H.s (G.s :: l) ∧ FibCover f.toEHom.onV H.s (G.t :: l) ∧
      l.length + 1 ≤ M
  marks_ne : H.s ≠ H.t →
    ∃ ls lt, FibCover f.toEHom.onV H.s (G.s :: ls) ∧ FibCover f.toEHom.onV H.t (G.t :: lt) ∧
      ls.length + lt.length + 2 ≤ M + 1

/-- Any hom whose every fibre is covered by ≤ N vertices is `Tame (2N + 1)`. -/
public theorem tame_of_fibBound {G H : LGraph L} (f : Hom G H) (N : Nat)
    (hb : ∀ y, ∃ l, FibCover f.toEHom.onV y l ∧ l.length ≤ N) :
    Tame f (2 * N + 1) where
  interior y _ _ := by
    obtain ⟨l, hc, hl⟩ := hb y
    exact ⟨l, hc, by omega⟩
  marks_eq _ := by
    obtain ⟨l, hc, hl⟩ := hb H.s
    exact ⟨l, hc.cons _, hc.cons _, by omega⟩
  marks_ne _ := by
    obtain ⟨ls, hcs, hls⟩ := hb H.s
    obtain ⟨lt, hct, hlt⟩ := hb H.t
    exact ⟨ls, lt, hcs.cons _, hct.cons _, by omega⟩

/-- **Uniform fibre bound**: every fibre of a `Tame f M` map is covered by a
    list of length ≤ M. -/
public theorem Tame.fib {G H : LGraph L} {f : Hom G H} {M : Nat} (hf : Tame f M)
    (y : H.V) : ∃ l, FibCover f.toEHom.onV y l ∧ l.length ≤ M := by
  by_cases hys : y = H.s
  · by_cases hst : H.s = H.t
    · obtain ⟨l, h1, _, hlen⟩ := hf.marks_eq hst
      exact ⟨_ :: l, fun x hx => h1 x (hx.trans hys), by simpa using hlen⟩
    · obtain ⟨ls, lt, h1, _, hlen⟩ := hf.marks_ne hst
      exact ⟨_ :: ls, fun x hx => h1 x (hx.trans hys), by simp; omega⟩
  · by_cases hyt : y = H.t
    · have hst : H.s ≠ H.t := fun h => hys (hyt.trans h.symm)
      obtain ⟨ls, lt, _, h2, hlen⟩ := hf.marks_ne hst
      exact ⟨_ :: lt, fun x hx => h2 x (hx.trans hyt), by simp; omega⟩
    · exact hf.interior y hys hyt

/-- Well-typed abbreviation for the left-injection class map of a `meet`. -/
private def ml (G T : LGraph L) (u : G.V) : (meet G T).V :=
  Quot.mk (meetRel G T) (Sum.inl u)

/-- `Tame` is preserved — with the SAME bound — by the `meet`-left layer.
    This is the heart of context-invariance: the ctx factor `T` contributes
    only singleton fibres, mark coincidences merge at most the two mark
    covers whose heads collapse to one class, and nothing grows with `T`. -/
public theorem tame_meetL (T : LGraph L) {G G' : LGraph L} {f : Hom G G'} {M : Nat}
    (hM : 1 ≤ M) (hf : Tame f M) : Tame (meetHomL T f) M := by
  refine ⟨?_, ?_, ?_⟩
  · -- INTERIOR: non-mark classes have redex-only (or singleton ctx) fibres
    intro y hys hyt
    obtain ⟨p₀, hp₀⟩ := Quot.exists_rep y
    subst hp₀
    cases p₀ with
    | inl x₀ =>
      have hx₀s : x₀ ≠ G'.s := fun h => hys (by rw [h]; rfl)
      have hx₀t : x₀ ≠ G'.t := fun h => hyt (by rw [h]; rfl)
      obtain ⟨l, hcov, hlen⟩ := hf.interior x₀ hx₀s hx₀t
      refine ⟨l.map (ml G T), ?_, by rw [List.length_map]; exact hlen⟩
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl u =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl x₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · exact List.mem_map.mpr ⟨u, hcov u (Sum.inl.inj heq), rfl⟩
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hx₀s
          · nomatch h
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hx₀t
          · nomatch h
        · rcases h2 with (h | h) | (h | h)
          · exact absurd (Sum.inl.inj h) hx₀s
          · nomatch h
          · exact absurd (Sum.inl.inj h) hx₀t
          · nomatch h
      | inr w =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inr w) (q := Sum.inl x₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · nomatch heq
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hx₀s
          · nomatch h
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hx₀t
          · nomatch h
        · rcases h2 with (h | h) | (h | h)
          · exact absurd (Sum.inl.inj h) hx₀s
          · nomatch h
          · exact absurd (Sum.inl.inj h) hx₀t
          · nomatch h
    | inr w₀ =>
      have hw₀s : w₀ ≠ T.s := fun h => hys (by rw [h]; exact meet_inr_s G' T)
      have hw₀t : w₀ ≠ T.t := fun h => hyt (by rw [h]; exact meet_inr_t G' T)
      refine ⟨[Quot.mk (meetRel G T) (Sum.inr w₀)], ?_, by simpa using hM⟩
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl u =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inr w₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · nomatch heq
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀s
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀t
        · rcases h2 with (h | h) | (h | h)
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀s
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀t
      | inr w =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inr w) (q := Sum.inr w₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · rw [Sum.inr.inj heq]; exact List.mem_cons_self ..
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀s
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀t
        · rcases h2 with (h | h) | (h | h)
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀s
          · nomatch h
          · exact absurd (Sum.inr.inj h) hw₀t
  · -- MARKS_EQ: the target marks coincide as classes
    intro hst
    have hco : G'.s = G'.t ∨ T.s = T.t := by
      have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
        (p := Sum.inl G'.s) (q := Sum.inl G'.t) hst
      rcases hcl with heq | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨co, _, _⟩
      · exact Or.inl (Sum.inl.inj heq)
      · rcases h2 with h | h
        · exact Or.inl (Sum.inl.inj h).symm
        · nomatch h
      · rcases h1 with h | h
        · exact Or.inl (Sum.inl.inj h)
        · nomatch h
      · exact co
    by_cases hG' : G'.s = G'.t
    · -- the redex marks were already merged: transport f's merged cover
      obtain ⟨l, hc1, hc2, hlen⟩ := hf.marks_eq hG'
      have hGt1 : ml G T G.t ∈ (meet G T).s :: l.map (ml G T) := by
        rcases List.mem_cons.mp (hc1 G.t (f.map_t.trans hG'.symm)) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨G.t, h, rfl⟩))
      have hGs2 : ml G T G.s ∈ (meet G T).t :: l.map (ml G T) := by
        rcases List.mem_cons.mp (hc2 G.s f.map_s) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨G.s, h, rfl⟩))
      refine ⟨l.map (ml G T), ?_, ?_, by rw [List.length_map]; exact hlen⟩
      · -- cover headed by the domain `s`-mark
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · exact Sum.inl.inj heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
            · rcases h1 with h | h
              · exact (Sum.inl.inj h).trans hG'.symm
              · nomatch h
            · rcases h1 with (h | h) | (h | h)
              · exact Sum.inl.inj h
              · nomatch h
              · exact (Sum.inl.inj h).trans hG'.symm
              · nomatch h
          rcases List.mem_cons.mp (hc1 u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.s) hx
          have hw : w = T.s ∨ w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
            · rcases h1 with (h | h) | (h | h)
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
          rcases hw with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_s G T))
          · have hxt : (Quot.mk (meetRel G T) (Sum.inr w) : (meet G T).V)
                = ml G T G.t := by rw [h]; exact meet_inr_t G T
            rw [hxt]
            exact hGt1
      · -- cover headed by the domain `t`-mark
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · exact Sum.inl.inj heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
            · rcases h1 with h | h
              · exact (Sum.inl.inj h).trans hG'.symm
              · nomatch h
            · rcases h1 with (h | h) | (h | h)
              · exact Sum.inl.inj h
              · nomatch h
              · exact (Sum.inl.inj h).trans hG'.symm
              · nomatch h
          rcases List.mem_cons.mp (hc2 u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.s) hx
          have hw : w = T.s ∨ w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
            · rcases h1 with (h | h) | (h | h)
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
          rcases hw with h | h
          · have hxs : (Quot.mk (meetRel G T) (Sum.inr w) : (meet G T).V)
                = ml G T G.s := by rw [h]; exact meet_inr_s G T
            rw [hxs]
            exact hGs2
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_t G T))
    · -- the ctx marks merged the two target marks: the `−1` union of covers
      have hT : T.s = T.t := hco.resolve_left hG'
      obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
      -- KEY: the ctx coincidence also merges the two DOMAIN marks
      have hkey : ml G T G.s = ml G T G.t := by
        calc ml G T G.s = Quot.mk (meetRel G T) (Sum.inr T.s) := (meet_inr_s G T).symm
          _ = Quot.mk (meetRel G T) (Sum.inr T.t) := by rw [hT]
          _ = ml G T G.t := meet_inr_t G T
      have hcore : ∀ x, (meetHomL T f).toEHom.onV x = (meet G' T).s →
          x ∈ ml G T G.s :: (ls.map (ml G T) ++ lt.map (ml G T)) := by
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
          have hu : f.toEHom.onV u = G'.s ∨ f.toEHom.onV u = G'.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · exact Or.inl (Sum.inl.inj heq)
            · rcases h1 with h | h
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with h | h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with (h | h) | (h | h)
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
          rcases hu with h | h
          · rcases List.mem_cons.mp (hcs u h) with h2 | h2
            · exact List.mem_cons.mpr (Or.inl (by rw [ml, h2]))
            · exact List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨u, h2, rfl⟩))))
          · rcases List.mem_cons.mp (hct u h) with h2 | h2
            · exact List.mem_cons.mpr (Or.inl (by rw [ml, h2]; exact hkey.symm))
            · exact List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨u, h2, rfl⟩))))
        | inr w =>
          have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.s) hx
          have hw : w = T.s ∨ w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
            · rcases h1 with (h | h) | (h | h)
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
          rcases hw with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_s G T))
          · exact List.mem_cons.mpr (Or.inl (by rw [h, ← hT]; exact meet_inr_s G T))
      refine ⟨ls.map (ml G T) ++ lt.map (ml G T), hcore, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp (hcore x hx) with h | h
        · exact List.mem_cons.mpr (Or.inl (h.trans hkey))
        · exact List.mem_cons.mpr (Or.inr h)
      · rw [List.length_append, List.length_map, List.length_map]
        omega
  · -- MARKS_NE: no coincidence anywhere; clusters stay separated
    intro hst
    have hG' : G'.s ≠ G'.t := fun h => hst (by
      show Quot.mk (meetRel G' T) (Sum.inl G'.s) = Quot.mk (meetRel G' T) (Sum.inl G'.t)
      rw [h])
    have hT : T.s ≠ T.t := fun h => hst (by
      calc (meet G' T).s = Quot.mk (meetRel G' T) (Sum.inr T.s) := (meet_inr_s G' T).symm
        _ = Quot.mk (meetRel G' T) (Sum.inr T.t) := by rw [h]
        _ = (meet G' T).t := meet_inr_t G' T)
    obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
    refine ⟨ls.map (ml G T), lt.map (ml G T), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl u =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
        have hu : f.toEHom.onV u = G'.s := by
          rcases hcl with heq | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨co, _, _⟩
          · exact Sum.inl.inj heq
          · rcases h1 with h | h
            · exact Sum.inl.inj h
            · nomatch h
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hG'
            · nomatch h
          · exact (co.elim hG' hT).elim
        rcases List.mem_cons.mp (hcs u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      | inr w =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inr w) (q := Sum.inl G'.s) hx
        have hw : w = T.s := by
          rcases hcl with heq | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨co, _, _⟩
          · nomatch heq
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hG'
            · nomatch h
          · exact (co.elim hG' hT).elim
        exact List.mem_cons.mpr (Or.inl (by rw [hw]; exact meet_inr_s G T))
    · intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl u =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.t) hx
        have hu : f.toEHom.onV u = G'.t := by
          rcases hcl with heq | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨co, _, _⟩
          · exact Sum.inl.inj heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) (fun hh => hG' hh.symm)
            · nomatch h
          · rcases h1 with h | h
            · exact Sum.inl.inj h
            · nomatch h
          · exact (co.elim hG' hT).elim
        rcases List.mem_cons.mp (hct u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      | inr w =>
        have hcl := meet_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inr w) (q := Sum.inl G'.t) hx
        have hw : w = T.t := by
          rcases hcl with heq | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨co, _, _⟩
          · nomatch heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) (fun hh => hG' hh.symm)
            · nomatch h
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
          · exact (co.elim hG' hT).elim
        exact List.mem_cons.mpr (Or.inl (by rw [hw]; exact meet_inr_t G T))
    · rw [List.length_map, List.length_map]
      exact hlen

/-- Well-typed abbreviation for the right-injection class map of a `meet`. -/
private def mr (T G : LGraph L) (u : G.V) : (meet T G).V :=
  Quot.mk (meetRel T G) (Sum.inr u)

/-- `Tame` is preserved by the `meet`-right layer (mirror of `tame_meetL`). -/
public theorem tame_meetR (T : LGraph L) {G G' : LGraph L} {f : Hom G G'} {M : Nat}
    (hM : 1 ≤ M) (hf : Tame f M) : Tame (meetHomR T f) M := by
  refine ⟨?_, ?_, ?_⟩
  · -- INTERIOR
    intro y hys hyt
    obtain ⟨p₀, hp₀⟩ := Quot.exists_rep y
    subst hp₀
    cases p₀ with
    | inr x₀ =>
      have hx₀s : x₀ ≠ G'.s := fun h => hys (by rw [h]; exact meet_inr_s T G')
      have hx₀t : x₀ ≠ G'.t := fun h => hyt (by rw [h]; exact meet_inr_t T G')
      obtain ⟨l, hcov, hlen⟩ := hf.interior x₀ hx₀s hx₀t
      refine ⟨l.map (mr T G), ?_, by rw [List.length_map]; exact hlen⟩
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inr u =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inr x₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · exact List.mem_map.mpr ⟨u, hcov u (Sum.inr.inj heq), rfl⟩
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀s
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀t
        · rcases h2 with (h | h) | (h | h)
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀s
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀t
      | inl w =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inl w) (q := Sum.inr x₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · nomatch heq
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀s
        · rcases h2 with h | h
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀t
        · rcases h2 with (h | h) | (h | h)
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀s
          · nomatch h
          · exact absurd (Sum.inr.inj h) hx₀t
    | inl w₀ =>
      have hw₀s : w₀ ≠ T.s := fun h => hys (by rw [h]; rfl)
      have hw₀t : w₀ ≠ T.t := fun h => hyt (by rw [h]; rfl)
      refine ⟨[Quot.mk (meetRel T G) (Sum.inl w₀)], ?_, by simpa using hM⟩
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inr u =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl w₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · nomatch heq
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hw₀s
          · nomatch h
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hw₀t
          · nomatch h
        · rcases h2 with (h | h) | (h | h)
          · exact absurd (Sum.inl.inj h) hw₀s
          · nomatch h
          · exact absurd (Sum.inl.inj h) hw₀t
          · nomatch h
      | inl w =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inl w) (q := Sum.inl w₀) hx
        rcases hcl with heq | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · rw [Sum.inl.inj heq]; exact List.mem_cons_self ..
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hw₀s
          · nomatch h
        · rcases h2 with h | h
          · exact absurd (Sum.inl.inj h) hw₀t
          · nomatch h
        · rcases h2 with (h | h) | (h | h)
          · exact absurd (Sum.inl.inj h) hw₀s
          · nomatch h
          · exact absurd (Sum.inl.inj h) hw₀t
          · nomatch h
  · -- MARKS_EQ
    intro hst
    have hco : T.s = T.t ∨ G'.s = G'.t := by
      have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
        (p := Sum.inl T.s) (q := Sum.inl T.t) hst
      rcases hcl with heq | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨co, _, _⟩
      · exact Or.inl (Sum.inl.inj heq)
      · rcases h2 with h | h
        · exact Or.inl (Sum.inl.inj h).symm
        · nomatch h
      · rcases h1 with h | h
        · exact Or.inl (Sum.inl.inj h)
        · nomatch h
      · exact co
    by_cases hG' : G'.s = G'.t
    · obtain ⟨l, hc1, hc2, hlen⟩ := hf.marks_eq hG'
      have hGt1 : mr T G G.t ∈ (meet T G).s :: l.map (mr T G) := by
        rcases List.mem_cons.mp (hc1 G.t (f.map_t.trans hG'.symm)) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_s T G))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨G.t, h, rfl⟩))
      have hGs2 : mr T G G.s ∈ (meet T G).t :: l.map (mr T G) := by
        rcases List.mem_cons.mp (hc2 G.s f.map_s) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_t T G))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨G.s, h, rfl⟩))
      refine ⟨l.map (mr T G), ?_, ?_, by rw [List.length_map]; exact hlen⟩
      · -- cover headed by the domain `s`-mark
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
            · rcases h1 with h | h
              · nomatch h
              · exact (Sum.inr.inj h).trans hG'.symm
            · rcases h1 with (h | h) | (h | h)
              · nomatch h
              · exact Sum.inr.inj h
              · nomatch h
              · exact (Sum.inr.inj h).trans hG'.symm
          rcases List.mem_cons.mp (hc1 u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_s T G))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inl w =>
          have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inl T.s) hx
          have hw : w = T.s ∨ w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · exact Or.inl (Sum.inl.inj heq)
            · rcases h1 with h | h
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with h | h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with (h | h) | (h | h)
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
          rcases hw with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · have hxt : (Quot.mk (meetRel T G) (Sum.inl w) : (meet T G).V)
                = mr T G G.t := by rw [h]; exact (meet_inr_t T G).symm
            rw [hxt]
            exact hGt1
      · -- cover headed by the domain `t`-mark
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
            · rcases h1 with h | h
              · nomatch h
              · exact (Sum.inr.inj h).trans hG'.symm
            · rcases h1 with (h | h) | (h | h)
              · nomatch h
              · exact Sum.inr.inj h
              · nomatch h
              · exact (Sum.inr.inj h).trans hG'.symm
          rcases List.mem_cons.mp (hc2 u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_t T G))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inl w =>
          have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inl T.s) hx
          have hw : w = T.s ∨ w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · exact Or.inl (Sum.inl.inj heq)
            · rcases h1 with h | h
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with h | h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with (h | h) | (h | h)
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
          rcases hw with h | h
          · have hxs : (Quot.mk (meetRel T G) (Sum.inl w) : (meet T G).V)
                = mr T G G.s := by rw [h]; exact (meet_inr_s T G).symm
            rw [hxs]
            exact hGs2
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
    · -- the ctx marks merged the two target marks: the `−1` union of covers
      have hT : T.s = T.t := hco.resolve_right hG'
      obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
      have hkey : mr T G G.s = mr T G G.t := by
        have h1 : (Quot.mk (meetRel T G) (Sum.inl T.s) : (meet T G).V)
            = Quot.mk (meetRel T G) (Sum.inl T.t) := by rw [hT]
        exact (meet_inr_s T G).trans (h1.trans (meet_inr_t T G).symm)
      have hcore : ∀ x, (meetHomR T f).toEHom.onV x = (meet T G').s →
          x ∈ mr T G G.s :: (ls.map (mr T G) ++ lt.map (mr T G)) := by
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
          have hu : f.toEHom.onV u = G'.s ∨ f.toEHom.onV u = G'.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
            · rcases h1 with h | h
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
            · rcases h1 with (h | h) | (h | h)
              · nomatch h
              · exact Or.inl (Sum.inr.inj h)
              · nomatch h
              · exact Or.inr (Sum.inr.inj h)
          rcases hu with h | h
          · rcases List.mem_cons.mp (hcs u h) with h2 | h2
            · exact List.mem_cons.mpr (Or.inl (by rw [h2]; rfl))
            · exact List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨u, h2, rfl⟩))))
          · rcases List.mem_cons.mp (hct u h) with h2 | h2
            · exact List.mem_cons.mpr (Or.inl (by rw [h2]; exact hkey.symm))
            · exact List.mem_cons.mpr
                (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨u, h2, rfl⟩))))
        | inl w =>
          have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inl T.s) hx
          have hw : w = T.s ∨ w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1, _⟩
            · exact Or.inl (Sum.inl.inj heq)
            · rcases h1 with h | h
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with h | h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
            · rcases h1 with (h | h) | (h | h)
              · exact Or.inl (Sum.inl.inj h)
              · nomatch h
              · exact Or.inr (Sum.inl.inj h)
              · nomatch h
          rcases hw with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact (meet_inr_s T G).symm))
          · exact List.mem_cons.mpr (Or.inl
              (by rw [h]; exact ((meet_inr_t T G).symm.trans hkey.symm)))
      refine ⟨ls.map (mr T G) ++ lt.map (mr T G), ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp (hcore x hx) with h | h
        · exact List.mem_cons.mpr (Or.inl (h.trans (meet_inr_s T G)))
        · exact List.mem_cons.mpr (Or.inr h)
      · intro x hx
        rcases List.mem_cons.mp (hcore x hx) with h | h
        · exact List.mem_cons.mpr (Or.inl (h.trans (hkey.trans (meet_inr_t T G))))
        · exact List.mem_cons.mpr (Or.inr h)
      · rw [List.length_append, List.length_map, List.length_map]
        omega
  · -- MARKS_NE
    intro hst
    have hT : T.s ≠ T.t := fun h => hst (by
      show Quot.mk (meetRel T G') (Sum.inl T.s) = Quot.mk (meetRel T G') (Sum.inl T.t)
      rw [h])
    have hG' : G'.s ≠ G'.t := fun h => hst (by
      calc (meet T G').s = Quot.mk (meetRel T G') (Sum.inr G'.s) := (meet_inr_s T G').symm
        _ = Quot.mk (meetRel T G') (Sum.inr G'.t) := by rw [h]
        _ = (meet T G').t := meet_inr_t T G')
    obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
    refine ⟨ls.map (mr T G), lt.map (mr T G), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inr u =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
        have hu : f.toEHom.onV u = G'.s := by
          rcases hcl with heq | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨co, _, _⟩
          · nomatch heq
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hT
            · nomatch h
          · exact (co.elim hT hG').elim
        rcases List.mem_cons.mp (hcs u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_s T G))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      | inl w =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inl w) (q := Sum.inl T.s) hx
        have hw : w = T.s := by
          rcases hcl with heq | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨co, _, _⟩
          · exact Sum.inl.inj heq
          · rcases h1 with h | h
            · exact Sum.inl.inj h
            · nomatch h
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hT
            · nomatch h
          · exact (co.elim hT hG').elim
        exact List.mem_cons.mpr (Or.inl (by rw [hw]; rfl))
    · intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inr u =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.t) hx
        have hu : f.toEHom.onV u = G'.t := by
          rcases hcl with heq | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨co, _, _⟩
          · nomatch heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) (fun hh => hT hh.symm)
            · nomatch h
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
          · exact (co.elim hT hG').elim
        rcases List.mem_cons.mp (hct u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact meet_inr_t T G))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      | inl w =>
        have hcl := meet_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inl w) (q := Sum.inl T.t) hx
        have hw : w = T.t := by
          rcases hcl with heq | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨co, _, _⟩
          · exact Sum.inl.inj heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) (fun hh => hT hh.symm)
            · nomatch h
          · rcases h1 with h | h
            · exact Sum.inl.inj h
            · nomatch h
          · exact (co.elim hT hG').elim
        exact List.mem_cons.mpr (Or.inl (by rw [hw]; rfl))
    · rw [List.length_map, List.length_map]
      exact hlen

/-- Well-typed abbreviation for the left-injection class map of a `gcomp`. -/
private def gl (G T : LGraph L) (u : G.V) : (gcomp G T).V :=
  Quot.mk (compRel G T) (Sum.inl u)

/-- `Tame` is preserved by the `gcomp`-left layer.  The old `t`-mark RETIRES
    into the interior carrying its own cover; the fresh ctx `t`-mark has a
    singleton fibre — so the joint mark budget is restored, not grown. -/
public theorem tame_gcompL (T : LGraph L) {G G' : LGraph L} {f : Hom G G'} {M : Nat}
    (hM : 1 ≤ M) (hf : Tame f M) : Tame (gcompHomL T f) M := by
  refine ⟨?_, ?_, ?_⟩
  · -- INTERIOR (including the retired `t`-mark class)
    intro y hys hyt
    obtain ⟨p₀, hp₀⟩ := Quot.exists_rep y
    subst hp₀
    cases p₀ with
    | inl x₀ =>
      have hx₀s : x₀ ≠ G'.s := fun h => hys (by rw [h]; rfl)
      by_cases hx₀t : x₀ = G'.t
      · -- the RETIRED mark class
        subst hx₀t
        have hG' : G'.s ≠ G'.t := fun hh => hys (by rw [← hh]; rfl)
        obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
        refine ⟨Quot.mk (compRel G T) (Sum.inl G.t) :: lt.map (gl G T), ?_,
          by simp only [List.length_cons, List.length_map]; omega⟩
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.t) hx
          have hu : f.toEHom.onV u = G'.t := by
            rcases hcl with heq | ⟨h1, _⟩
            · exact Sum.inl.inj heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
          rcases List.mem_cons.mp (hct u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.t) hx
          have hw : w = T.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
          exact List.mem_cons.mpr (Or.inl (by rw [hw]; exact (gcomp_glue G T).symm))
      · -- a genuine interior redex class
        obtain ⟨l, hcov, hlen⟩ := hf.interior x₀ hx₀s hx₀t
        refine ⟨l.map (gl G T), ?_, by rw [List.length_map]; exact hlen⟩
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl x₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · exact List.mem_map.mpr ⟨u, hcov u (Sum.inl.inj heq), rfl⟩
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hx₀t
            · nomatch h
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl x₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hx₀t
            · nomatch h
    | inr w₀ =>
      have hw₀t : w₀ ≠ T.t := fun h => hyt (by rw [h]; rfl)
      by_cases hw₀s : w₀ = T.s
      · -- the retired class again, seen from its ctx representative
        subst hw₀s
        have hG' : G'.s ≠ G'.t := fun hh => hys
          ((gcomp_glue G' T).symm.trans (by rw [← hh]; rfl))
        obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
        refine ⟨Quot.mk (compRel G T) (Sum.inl G.t) :: lt.map (gl G T), ?_,
          by simp only [List.length_cons, List.length_map]; omega⟩
        intro x hx
        rw [← gcomp_glue G' T] at hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.t) hx
          have hu : f.toEHom.onV u = G'.t := by
            rcases hcl with heq | ⟨h1, _⟩
            · exact Sum.inl.inj heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
          rcases List.mem_cons.mp (hct u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.t) hx
          have hw : w = T.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
          exact List.mem_cons.mpr (Or.inl (by rw [hw]; exact (gcomp_glue G T).symm))
      · -- pure ctx class: singleton fibre
        refine ⟨[Quot.mk (compRel G T) (Sum.inr w₀)], ?_, by simpa using hM⟩
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inr w₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) hw₀s
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inr w₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · rw [Sum.inr.inj heq]; exact List.mem_cons_self ..
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) hw₀s
  · -- MARKS_EQ: forces BOTH coincidences
    intro hst
    have hpair := gcomp_mk_eq (G₁ := G') (G₂ := T)
      (p := Sum.inl G'.s) (q := Sum.inr T.t) hst
    have hco : G'.s = G'.t ∧ T.t = T.s := by
      rcases hpair with heq | ⟨h1, h2⟩
      · nomatch heq
      · refine ⟨?_, ?_⟩
        · rcases h1 with h | h
          · exact Sum.inl.inj h
          · nomatch h
        · rcases h2 with h | h
          · nomatch h
          · exact Sum.inr.inj h
    obtain ⟨l, hc1, hc2, hlen⟩ := hf.marks_eq hco.1
    refine ⟨l.map (gl G T), ?_, ?_, by rw [List.length_map]; exact hlen⟩
    · -- cover headed by the domain `s`-mark
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl u =>
        have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
        have hu : f.toEHom.onV u = G'.s := by
          rcases hcl with heq | ⟨h1, _⟩
          · exact Sum.inl.inj heq
          · rcases h1 with h | h
            · exact (Sum.inl.inj h).trans hco.1.symm
            · nomatch h
        rcases List.mem_cons.mp (hc1 u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      | inr w =>
        have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inr w) (q := Sum.inl G'.s) hx
        have hw : w = T.s := by
          rcases hcl with heq | ⟨h1, _⟩
          · nomatch heq
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
        rcases List.mem_cons.mp (hc1 G.t (f.map_t.trans hco.1.symm)) with h | h
        · exact List.mem_cons.mpr (Or.inl
            (by rw [hw]; exact (gcomp_glue G T).symm.trans (by rw [h]; rfl)))
        · refine List.mem_cons.mpr (Or.inr ?_)
          have hxe : (Quot.mk (compRel G T) (Sum.inr w) : (gcomp G T).V)
              = Quot.mk (compRel G T) (Sum.inl G.t) := by
            rw [hw]; exact (gcomp_glue G T).symm
          rw [hxe]
          exact List.mem_map.mpr ⟨G.t, h, rfl⟩
    · -- cover headed by the domain `t`-mark
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl u =>
        have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
        have hu : f.toEHom.onV u = G'.s := by
          rcases hcl with heq | ⟨h1, _⟩
          · exact Sum.inl.inj heq
          · rcases h1 with h | h
            · exact (Sum.inl.inj h).trans hco.1.symm
            · nomatch h
        rcases List.mem_cons.mp (hc2 u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl
            (by rw [h]; exact (gcomp_glue G T).trans (by rw [← hco.2]; rfl)))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      | inr w =>
        have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
          (p := Sum.inr w) (q := Sum.inl G'.s) hx
        have hw : w = T.s := by
          rcases hcl with heq | ⟨h1, _⟩
          · nomatch heq
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
        exact List.mem_cons.mpr (Or.inl (by rw [hw, ← hco.2]; rfl))
  · -- MARKS_NE
    intro hst
    have hnand : ¬(G'.s = G'.t ∧ T.s = T.t) := fun ⟨h1, h2⟩ => hst (by
      show Quot.mk (compRel G' T) (Sum.inl G'.s) = Quot.mk (compRel G' T) (Sum.inr T.t)
      rw [h1, ← h2]; exact gcomp_glue G' T)
    by_cases hG' : G'.s = G'.t
    · -- redex marks equal, ctx marks distinct
      have hT : T.s ≠ T.t := fun h => hnand ⟨hG', h⟩
      obtain ⟨l, hc1, hc2, hlen⟩ := hf.marks_eq hG'
      refine ⟨l.map (gl G T), [], ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · exact Sum.inl.inj heq
            · rcases h1 with h | h
              · exact (Sum.inl.inj h).trans hG'.symm
              · nomatch h
          rcases List.mem_cons.mp (hc1 u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.s) hx
          have hw : w = T.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
          rcases List.mem_cons.mp (hc1 G.t (f.map_t.trans hG'.symm)) with h | h
          · exact List.mem_cons.mpr (Or.inl
              (by rw [hw]; exact (gcomp_glue G T).symm.trans (by rw [h]; rfl)))
          · refine List.mem_cons.mpr (Or.inr ?_)
            have hxe : (Quot.mk (compRel G T) (Sum.inr w) : (gcomp G T).V)
                = Quot.mk (compRel G T) (Sum.inl G.t) := by
              rw [hw]; exact (gcomp_glue G T).symm
            rw [hxe]
            exact List.mem_map.mpr ⟨G.t, h, rfl⟩
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inr T.t) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) (fun hh => hT hh.symm)
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inr T.t) hx
          rcases hcl with heq | ⟨_, h2⟩
          · exact List.mem_cons.mpr (Or.inl (by rw [Sum.inr.inj heq]; rfl))
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) (fun hh => hT hh.symm)
      · simp only [List.length_map, List.length_nil]
        omega
    · -- redex marks distinct: transport both covers
      obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
      refine ⟨ls.map (gl G T), lt.map (gl G T), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inl G'.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨_, h2⟩
            · exact Sum.inl.inj heq
            · rcases h2 with h | h
              · exact absurd (Sum.inl.inj h) hG'
              · nomatch h
          rcases List.mem_cons.mp (hcs u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inl G'.s) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hG'
            · nomatch h
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl u =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inl (f.toEHom.onV u)) (q := Sum.inr T.t) hx
          rcases hcl with heq | ⟨h1, h2⟩
          · nomatch heq
          · have hTe : T.t = T.s := by
              rcases h2 with h | h
              · nomatch h
              · exact Sum.inr.inj h
            have hu : f.toEHom.onV u = G'.t := by
              rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
            rcases List.mem_cons.mp (hct u hu) with h | h
            · exact List.mem_cons.mpr (Or.inl
                (by rw [h]; exact (gcomp_glue G T).trans (by rw [← hTe]; rfl)))
            · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inr w =>
          have hcl := gcomp_mk_eq (G₁ := G') (G₂ := T)
            (p := Sum.inr w) (q := Sum.inr T.t) hx
          rcases hcl with heq | ⟨h1, h2⟩
          · exact List.mem_cons.mpr (Or.inl (by rw [Sum.inr.inj heq]; rfl))
          · have hTe : T.t = T.s := by
              rcases h2 with h | h
              · nomatch h
              · exact Sum.inr.inj h
            have hw : w = T.s := by
              rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
            exact List.mem_cons.mpr (Or.inl (by rw [hw, ← hTe]; rfl))
      · rw [List.length_map, List.length_map]
        exact hlen

/-- Well-typed abbreviation for the right-injection class map of a `gcomp`. -/
private def gr (T G : LGraph L) (u : G.V) : (gcomp T G).V :=
  Quot.mk (compRel T G) (Sum.inr u)

/-- `Tame` is preserved by the `gcomp`-right layer (mirror of `tame_gcompL`:
    here the redex's `s`-mark retires). -/
public theorem tame_gcompR (T : LGraph L) {G G' : LGraph L} {f : Hom G G'} {M : Nat}
    (hM : 1 ≤ M) (hf : Tame f M) : Tame (gcompHomR T f) M := by
  refine ⟨?_, ?_, ?_⟩
  · -- INTERIOR (including the retired `s`-mark class)
    intro y hys hyt
    obtain ⟨p₀, hp₀⟩ := Quot.exists_rep y
    subst hp₀
    cases p₀ with
    | inr x₀ =>
      have hx₀t : x₀ ≠ G'.t := fun h => hyt (by rw [h]; rfl)
      by_cases hx₀s : x₀ = G'.s
      · -- the RETIRED mark class
        subst hx₀s
        have hG' : G'.s ≠ G'.t := fun hh => hyt (by rw [hh]; rfl)
        obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
        refine ⟨Quot.mk (compRel T G) (Sum.inr G.s) :: ls.map (gr T G), ?_,
          by simp only [List.length_cons, List.length_map]; omega⟩
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inr G'.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · exact Sum.inr.inj heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
          rcases List.mem_cons.mp (hcs u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inr G'.s) hx
          have hw : w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
          exact List.mem_cons.mpr (Or.inl (by rw [hw]; exact gcomp_glue T G))
      · -- a genuine interior redex class
        obtain ⟨l, hcov, hlen⟩ := hf.interior x₀ hx₀s hx₀t
        refine ⟨l.map (gr T G), ?_, by rw [List.length_map]; exact hlen⟩
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inr x₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · exact List.mem_map.mpr ⟨u, hcov u (Sum.inr.inj heq), rfl⟩
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) hx₀s
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inr x₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) hx₀s
    | inl w₀ =>
      have hw₀s : w₀ ≠ T.s := fun h => hys (by rw [h]; rfl)
      by_cases hw₀t : w₀ = T.t
      · -- the retired class again, seen from its ctx representative
        subst hw₀t
        have hG' : G'.s ≠ G'.t := fun hh => hyt
          ((gcomp_glue T G').trans (by rw [hh]; rfl))
        obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
        refine ⟨Quot.mk (compRel T G) (Sum.inr G.s) :: ls.map (gr T G), ?_,
          by simp only [List.length_cons, List.length_map]; omega⟩
        intro x hx
        rw [gcomp_glue T G'] at hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inr G'.s) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · exact Sum.inr.inj heq
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
          rcases List.mem_cons.mp (hcs u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inr G'.s) hx
          have hw : w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
          exact List.mem_cons.mpr (Or.inl (by rw [hw]; exact gcomp_glue T G))
      · -- pure ctx class: singleton fibre
        refine ⟨[Quot.mk (compRel T G) (Sum.inl w₀)], ?_, by simpa using hM⟩
        intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl w₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hw₀t
            · nomatch h
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inl w₀) hx
          rcases hcl with heq | ⟨_, h2⟩
          · rw [Sum.inl.inj heq]; exact List.mem_cons_self ..
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hw₀t
            · nomatch h
  · -- MARKS_EQ: forces BOTH coincidences
    intro hst
    have hpair := gcomp_mk_eq (G₁ := T) (G₂ := G')
      (p := Sum.inl T.s) (q := Sum.inr G'.t) hst
    have hco : T.s = T.t ∧ G'.t = G'.s := by
      rcases hpair with heq | ⟨h1, h2⟩
      · nomatch heq
      · refine ⟨?_, ?_⟩
        · rcases h1 with h | h
          · exact Sum.inl.inj h
          · nomatch h
        · rcases h2 with h | h
          · nomatch h
          · exact Sum.inr.inj h
    have hds : (Quot.mk (compRel T G) (Sum.inl T.t) : (gcomp T G).V)
        = Quot.mk (compRel T G) (Sum.inl T.s) := by rw [hco.1]
    obtain ⟨l, hc1, hc2, hlen⟩ := hf.marks_eq hco.2.symm
    refine ⟨l.map (gr T G), ?_, ?_, by rw [List.length_map]; exact hlen⟩
    · -- cover headed by the domain `s`-mark (the ctx `s`)
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl w =>
        have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inl w) (q := Sum.inl T.s) hx
        have hw : w = T.s ∨ w = T.t := by
          rcases hcl with heq | ⟨h1, _⟩
          · exact Or.inl (Sum.inl.inj heq)
          · rcases h1 with h | h
            · exact Or.inr (Sum.inl.inj h)
            · nomatch h
        rcases hw with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; exact hds))
      | inr u =>
        have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
        have hu : f.toEHom.onV u = G'.s := by
          rcases hcl with heq | ⟨h1, _⟩
          · nomatch heq
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
        rcases List.mem_cons.mp (hc1 u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl
            (by rw [h]; exact (gcomp_glue T G).symm.trans hds))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
    · -- cover headed by the domain `t`-mark (the redex `t`)
      intro x hx
      obtain ⟨q, hq⟩ := Quot.exists_rep x
      subst hq
      cases q with
      | inl w =>
        have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inl w) (q := Sum.inl T.s) hx
        have hw : w = T.s ∨ w = T.t := by
          rcases hcl with heq | ⟨h1, _⟩
          · exact Or.inl (Sum.inl.inj heq)
          · rcases h1 with h | h
            · exact Or.inr (Sum.inl.inj h)
            · nomatch h
        have hTt : (Quot.mk (compRel T G) (Sum.inl T.t) : (gcomp T G).V)
            ∈ (gcomp T G).t :: l.map (gr T G) := by
          rcases List.mem_cons.mp (hc2 G.s f.map_s) with h2 | h2
          · exact List.mem_cons.mpr (Or.inl
              ((gcomp_glue T G).trans (by rw [h2]; rfl)))
          · refine List.mem_cons.mpr (Or.inr ?_)
            rw [gcomp_glue T G]
            exact List.mem_map.mpr ⟨G.s, h2, rfl⟩
        rcases hw with h | h
        · rw [show (Quot.mk (compRel T G) (Sum.inl w) : (gcomp T G).V)
              = Quot.mk (compRel T G) (Sum.inl T.t) from by rw [h]; exact hds.symm]
          exact hTt
        · rw [show (Quot.mk (compRel T G) (Sum.inl w) : (gcomp T G).V)
              = Quot.mk (compRel T G) (Sum.inl T.t) from by rw [h]]
          exact hTt
      | inr u =>
        have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
          (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
        have hu : f.toEHom.onV u = G'.s := by
          rcases hcl with heq | ⟨h1, _⟩
          · nomatch heq
          · rcases h1 with h | h
            · nomatch h
            · exact Sum.inr.inj h
        rcases List.mem_cons.mp (hc2 u hu) with h | h
        · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
        · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
  · -- MARKS_NE
    intro hst
    have hnand : ¬(T.s = T.t ∧ G'.s = G'.t) := fun ⟨h1, h2⟩ => hst (by
      show Quot.mk (compRel T G') (Sum.inl T.s) = Quot.mk (compRel T G') (Sum.inr G'.t)
      rw [h1, ← h2]; exact gcomp_glue T G')
    by_cases hG' : G'.s = G'.t
    · -- redex marks equal, ctx marks distinct
      have hT : T.s ≠ T.t := fun h => hnand ⟨h, hG'⟩
      obtain ⟨l, hc1, hc2, hlen⟩ := hf.marks_eq hG'
      refine ⟨[], l.map (gr T G), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inl T.s) hx
          rcases hcl with heq | ⟨_, h2⟩
          · exact List.mem_cons.mpr (Or.inl (by rw [Sum.inl.inj heq]; rfl))
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hT
            · nomatch h
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · exact absurd (Sum.inl.inj h) hT
            · nomatch h
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inr G'.t) hx
          have hu : f.toEHom.onV u = G'.s := by
            rcases hcl with heq | ⟨h1, _⟩
            · exact (Sum.inr.inj heq).trans hG'.symm
            · rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
          rcases List.mem_cons.mp (hc2 u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inr G'.t) hx
          have hw : w = T.t := by
            rcases hcl with heq | ⟨h1, _⟩
            · nomatch heq
            · rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
          rcases List.mem_cons.mp (hc2 G.s f.map_s) with h | h
          · exact List.mem_cons.mpr (Or.inl
              (by rw [hw]; exact (gcomp_glue T G).trans (by rw [h]; rfl)))
          · refine List.mem_cons.mpr (Or.inr ?_)
            have hxe : (Quot.mk (compRel T G) (Sum.inl w) : (gcomp T G).V)
                = Quot.mk (compRel T G) (Sum.inr G.s) := by
              rw [hw]; exact gcomp_glue T G
            rw [hxe]
            exact List.mem_map.mpr ⟨G.s, h, rfl⟩
      · simp only [List.length_map, List.length_nil]
        omega
    · -- redex marks distinct: transport both covers
      obtain ⟨ls, lt, hcs, hct, hlen⟩ := hf.marks_ne hG'
      refine ⟨ls.map (gr T G), lt.map (gr T G), ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inl T.s) hx
          rcases hcl with heq | ⟨h1, h2⟩
          · exact List.mem_cons.mpr (Or.inl (by rw [Sum.inl.inj heq]; rfl))
          · have hTe : T.s = T.t := by
              rcases h2 with h | h
              · exact Sum.inl.inj h
              · nomatch h
            have hw : w = T.t := by
              rcases h1 with h | h
              · exact Sum.inl.inj h
              · nomatch h
            exact List.mem_cons.mpr (Or.inl (by rw [hw, ← hTe]; rfl))
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inl T.s) hx
          rcases hcl with heq | ⟨h1, h2⟩
          · nomatch heq
          · have hTe : T.s = T.t := by
              rcases h2 with h | h
              · exact Sum.inl.inj h
              · nomatch h
            have hu : f.toEHom.onV u = G'.s := by
              rcases h1 with h | h
              · nomatch h
              · exact Sum.inr.inj h
            rcases List.mem_cons.mp (hcs u hu) with h | h
            · exact List.mem_cons.mpr (Or.inl
                (by rw [h]; exact (gcomp_glue T G).symm.trans (by rw [← hTe]; rfl)))
            · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
      · intro x hx
        obtain ⟨q, hq⟩ := Quot.exists_rep x
        subst hq
        cases q with
        | inr u =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inr (f.toEHom.onV u)) (q := Sum.inr G'.t) hx
          have hu : f.toEHom.onV u = G'.t := by
            rcases hcl with heq | ⟨_, h2⟩
            · exact Sum.inr.inj heq
            · rcases h2 with h | h
              · nomatch h
              · exact absurd (Sum.inr.inj h) (fun hh => hG' hh.symm)
          rcases List.mem_cons.mp (hct u hu) with h | h
          · exact List.mem_cons.mpr (Or.inl (by rw [h]; rfl))
          · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨u, h, rfl⟩))
        | inl w =>
          have hcl := gcomp_mk_eq (G₁ := T) (G₂ := G')
            (p := Sum.inl w) (q := Sum.inr G'.t) hx
          rcases hcl with heq | ⟨_, h2⟩
          · nomatch heq
          · rcases h2 with h | h
            · nomatch h
            · exact absurd (Sum.inr.inj h) (fun hh => hG' hh.symm)
      · rw [List.length_map, List.length_map]
        exact hlen

/-- `Tame` transports through `recip` (marks swap; heads swap with them). -/
public theorem tame_recip {G G' : LGraph L} {f : Hom G G'} {M : Nat} (hf : Tame f M) :
    Tame (recipHom f) M where
  interior y hys hyt := hf.interior y hyt hys
  marks_eq h := by
    obtain ⟨l, h1, h2, hlen⟩ := hf.marks_eq h.symm
    refine ⟨l, ?_, ?_, hlen⟩
    · intro x hx; exact h2 x (hx.trans h)
    · intro x hx; exact h1 x (hx.trans h)
  marks_ne h := by
    obtain ⟨ls, lt, h1, h2, hlen⟩ := hf.marks_ne (fun hh => h hh.symm)
    exact ⟨lt, ls, h2, h1, by omega⟩

/-! ## (b) BOUNDED STEP — IV: context invariance and the step theorems -/

/-- **Context invariance of the fibre bound** — the heart of (b): filling a
    `Tame` redex map through ANY one-hole context preserves the bound.  The
    canonical filled map is the identity outside the redex, so no matter how
    large the context, no fibre ever exceeds the redex map's own bound. -/
public theorem fillTame (C : Ctx Nat) {E F : Term Nat} (f : Hom (toGraph E) (toGraph F))
    {M : Nat} (hM : 1 ≤ M) (hf : Tame f M) : Tame (fillHom C f) M := by
  induction C with
  | hole => exact hf
  | recip C ih => exact tame_recip ih
  | meetL C T ih => exact tame_meetL (toGraph T) hM ih
  | meetR T C ih => exact tame_meetR (toGraph T) hM ih
  | compL C T ih => exact tame_gcompL (toGraph T) hM ih
  | compR T C ih => exact tame_gcompR (toGraph T) hM ih

/-- List pigeonhole: pairwise-distinct members of `l` number ≤ `l.length`. -/
public theorem pairwise_ne_length_le {α : Type} :
    ∀ (vs l : List α), vs.Pairwise (· ≠ ·) → (∀ x ∈ vs, x ∈ l) →
      vs.length ≤ l.length := by
  intro vs
  induction vs with
  | nil => intro l _ _; exact Nat.zero_le _
  | cons a vs ih =>
    intro l hpw hsub
    obtain ⟨s, t, rfl⟩ := List.append_of_mem (hsub a (List.mem_cons_self ..))
    have hpw' := List.pairwise_cons.mp hpw
    have hsub' : ∀ x ∈ vs, x ∈ s ++ t := by
      intro x hx
      rcases List.mem_append.mp (hsub x (List.mem_cons_of_mem a hx)) with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm (hpw'.1 x hx)
        · exact List.mem_append.mpr (Or.inr h')
    have hlen := ih (s ++ t) hpw'.2 hsub'
    simp only [List.length_cons, List.length_append] at hlen ⊢
    omega

/-- σ-UNIFORM INSTANCE BOUND for an axiom set: every substitution instance of
    every axiom carries a graph map (right graph → left graph) whose fibres
    are covered by ≤ N vertices, N depending only on `Ax`.  This is exactly
    the σ-blow-up ingredient of the OPEN note — the fibres of the blow-up of
    a fixed `[B] → [A]` are bounded by the size of `B`, independently of σ —
    isolated here as the one still-open hypothesis of (b). -/
@[expose] public def InstanceBound (Ax : List (Term Nat × Term Nat)) (N : Nat) : Prop :=
  ∀ p ∈ Ax, ∀ σ : Nat → Term Nat,
    ∃ h : Hom (toGraph (subst σ p.2)) (toGraph (subst σ p.1)),
      ∀ y, ∃ l, FibCover h.toEHom.onV y l ∧ l.length ≤ N

/-- **(b) BOUNDED STEP.**  Under a σ-uniform instance bound, every single
    rewrite `E ⊆ F` carries a CANONICAL graph map `[F] → [E]` — the filled
    instance map, identity outside the redex — ALL of whose fibres are
    covered by ≤ 2N+1 vertices, independent of the substitution and of the
    one-hole context. -/
public theorem step_hom_tame {Ax : List (Term Nat × Term Nat)} {N : Nat}
    (hb : InstanceBound Ax N) {E F : Term Nat} (st : Step Ax E F) :
    ∃ c : Hom (toGraph F) (toGraph E),
      ∀ y, ∃ l, FibCover c.toEHom.onV y l ∧ l.length ≤ 2 * N + 1 := by
  cases st with
  | mk C σ hmem =>
    rename_i A B
    obtain ⟨h0, hb0⟩ := hb (A, B) hmem σ
    exact ⟨fillHom C h0,
      (fillTame C h0 (by omega) (tame_of_fibBound h0 N hb0)).fib⟩

/-- **(b), consumable counting form**: a single rewrite from `Ax` cannot
    merge more than `2N + 1` pairwise-distinct vertices into one point — in
    particular a jump step cannot merge all `2n + 3` designated pairs of the
    entangled family once `n` exceeds the bound read off `Ax`. -/
public theorem step_merge_bound {Ax : List (Term Nat × Term Nat)} {N : Nat}
    (hb : InstanceBound Ax N) {E F : Term Nat} (st : Step Ax E F) :
    ∃ c : Hom (toGraph F) (toGraph E),
      ∀ vs : List (toGraph F).V, vs.Pairwise (· ≠ ·) →
        (∀ x ∈ vs, ∀ x' ∈ vs, c.toEHom.onV x = c.toEHom.onV x') →
        vs.length ≤ 2 * N + 1 := by
  obtain ⟨c, hc⟩ := step_hom_tame hb st
  refine ⟨c, ?_⟩
  intro vs hpw hsame
  cases vs with
  | nil => exact Nat.zero_le _
  | cons v vs' =>
    obtain ⟨l, hcov, hlen⟩ := hc (c.toEHom.onV v)
    have hsub : ∀ x ∈ v :: vs', x ∈ l := fun x hx =>
      hcov x (hsame x hx v (List.mem_cons_self ..))
    exact Nat.le_trans (pairwise_ne_length_le (v :: vs') l hpw hsub) hlen

/-! ## OPEN — status of ingredients (b) and (c) after this file

  * (c) RIGIDITY is CLOSED: `rigidity`/`rigidity_pairs` (every mark-preserving
    map `[entR n] → [entL n]` merges all `2n+3` designated pairs), with the
    designated vertices `pVert`/`qVert` explicit and pairwise DISTINCT
    (`pVert_inj`, `qVert_inj`, `pVert_ne_qVert`, `chainT_s_ne_t`).

  * (b) BOUNDED STEP is closed MODULO the σ-blow-up: `step_hom_tame` and
    `step_merge_bound` give the canonical step map `[C[σB]] → [C[σA]]`
    (`fillHom`, identity outside the redex) with ALL fibres ≤ `2N+1`,
    UNIFORMLY in σ and C — provided the axiom set satisfies `InstanceBound
    Ax N`.  The context half (the `Tame` invariant and its preservation by
    every gluing layer with NO bound growth) is fully machine-checked; what
    remains is to DISCHARGE `InstanceBound` for a valid axiom set: construct
    the blow-up hom `[σB] → [σA]` of a fixed `h : [B] → [A]` (joints follow
    `h`; the copy of `[σℓ]` over an `ℓ`-edge of `[B]` maps identically onto
    the copy over the `h`-image edge) and bound its fibres by the size of
    `B`.  Plan: a leaf-position/joint presentation of `[σE]` by induction on
    `E` (joint map `[E].V → [σE].V`, canonical leaf embeddings with an
    injective-except-ports rigidity proved layerwise from `meet_mk_eq` /
    `gcomp_mk_eq`), plus `Classical.choice` to pick target leaves.  With
    `InstanceBound` discharged, `Chain.exists_jump` + (a) SP-wall + (c)
    rigidity + `step_merge_bound` assemble into `RhombusHard entL entR`.

    UPDATE (S2_158e): `InstanceBound allegoryAxioms 10` IS DISCHARGED —
    `instanceBound_allegoryAxioms` in `Freyd/S2_158e_InstanceBound.lean`,
    constructively (`propext`, `Quot.sound` only), by per-axiom instance maps
    (no joint/leaf tower needed: the 14 axioms are concrete, and per-axiom
    collision analysis via `meet_mk_eq`/`gcomp_mk_eq` bounds every fibre).
    `step_hom_tame`/`step_merge_bound` hence hold for `allegoryAxioms`
    outright (`allegory_step_hom_tame`, `allegory_step_merge_bound`, bound
    `2·10+1 = 21`).  Still open toward `RhombusHard`: the (a) SP-wall
    dichotomy, and the assembly of (a) + (b) + (c) along a chain. -/







end Freyd.S2_158

