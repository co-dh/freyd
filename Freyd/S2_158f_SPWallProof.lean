/-
  Freyd & Scedrov §2.158 — `SPWall n` for `n ≥ 1`, the last mathematical gap.

  Proof plan: the OPEN note at the end of `Freyd/S2_158d_SPWall.lean` —
  segment configurations in an SP graph carrying an un-anchored typing
  `τ : G → [entL n]`, 5-case induction on `SP G`.  Refinement forced by the
  `n = 0` erratum (`ent0_derivable`): the two rows of a configuration may
  arrive at DIFFERENT mark vertices (descents through mark-merging `meet`s
  split the end corners), so a configuration keeps SEPARATE top-row and
  bottom-row corner functions, coupled at interior corners only, and each
  row-end is either an anchored corner (end edge present, corner a mark) or
  a bare midpoint that is itself a mark (end edge already truncated by an
  outer descent).

  This file: Part 1 — start-vertex refinements of the `aL`/`cL`
  edge-uniqueness lemmas of `[entL n]` (`entL_edge_aL_full` /
  `entL_edge_cL_full`): every `aL i`-edge runs `eCorn i → Pv`, every
  `cL i`-edge runs `eCorn i → Qv`, with `i ≤ n+1`.  (The `bL`/`dL` versions
  `entL_edge_bL`/`entL_edge_dL` are already full in S2_158d.)

  STRICTLY MATHLIB-FREE.  Only Lean 4 core + `Freyd.*`.
-/

import Freyd.S2_158d_SPWall

namespace Freyd.S2_158

/-! ## Label injectivity (completing the `bL_inj` family) -/

theorem aL_inj {i j : Nat} (h : aL i = aL j) : i = j := by
  simp only [aL] at h; omega

theorem cL_inj {i j : Nat} (h : cL i = cL j) : i = j := by
  simp only [cL] at h; omega

/-! ## Edge-uniqueness, top/bottom ENTRIES

  `entL_edge_aL` (S2_158c) only pins the END of an `aL`-edge; the segment
  typing needs the START too: `τ x_a = eCorn a` is read off the `aL a`-edge
  of a configuration.  Mirrors the `entL_edge_bL`/`entL_edge_dL` proofs. -/

/-- In a branch, the only `aL`-labelled edge is `aL (j+1)`, from the branch's
    middle vertex to the `s`-mark (the collapsed `P`). -/
theorem branch_edge_aL_full {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (aL i)) :
    i = j + 1 ∧ c = branchMid j ∧ d = (toGraph (branch j)).s := by
  have hd := branch_edge_aL h
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · rcases meet_arrow_recip_edge he with ⟨hlab, _, _⟩ | ⟨hlab, hut, _⟩
    · exact absurd hlab aL_ne_bL
    · subst hut
      exact ⟨aL_inj hlab, hu.symm, hd⟩
  · rcases meet_recip_arrow_edge he with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
    · exact absurd hlab aL_ne_dL
    · exact absurd hlab aL_ne_cL

/-- In the `mids` tower, every `aL i`-labelled edge has `i = j+1` for some
    branch index `j ≤ k`, and runs from the `j`-th middle vertex to the
    `s`-mark. -/
theorem mids_edge_aL_full : ∀ {k i : Nat} {c d : (toGraph (mids k)).V},
    (toGraph (mids k)).edge c d (aL i) →
      ∃ j, j ≤ k ∧ i = j + 1 ∧ c = midsMid k j ∧ d = (toGraph (mids k)).s := by
  intro k
  induction k with
  | zero =>
    intro i c d h
    obtain ⟨hij, hc, hd⟩ := branch_edge_aL_full h
    exact ⟨0, Nat.le_refl _, hij, hc, hd⟩
  | succ m ih =>
    intro i c d h
    rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
    · obtain ⟨j, hjk, hij, hc, hd⟩ := ih he
      subst hc; subst hd; subst hu; subst hv
      refine ⟨j, Nat.le_succ_of_le hjk, hij, ?_, rfl⟩
      simp only [midsMid, if_pos hjk]
    · obtain ⟨hij, hc, hd⟩ := branch_edge_aL_full he
      subst hc; subst hd; subst hu; subst hv
      refine ⟨m+1, Nat.le_refl _, hij, ?_, meet_inr_s _ _⟩
      simp only [midsMid, if_neg (by omega : ¬ m + 1 ≤ m)]

/-- **Edge-uniqueness, top entries.**  Every `aL i`-labelled edge of the
    collapsed graph `[entL n]` has `i ≤ n+1`, starts at the corner
    `eCorn n i`, and ends at the collapsed top vertex `Pv n`. -/
theorem entL_edge_aL_full {n i : Nat} {c d : (toGraph (entL n)).V}
    (h : (toGraph (entL n)).edge c d (aL i)) :
    i ≤ n + 1 ∧ c = eCorn n i ∧ d = Pv n := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · exact he.elim
  · subst hu; subst hv
    rcases glued_edge_elim he with ⟨u', v', hu', hv', he'⟩ | ⟨u', v', hu', hv', he'⟩
    · -- first border factor `a₀ ∩ b_{n+1}°`: the `a₀`-edge runs `s → t`.
      subst hu'; subst hv'
      rcases meet_arrow_recip_edge he' with ⟨hlab, hus, hvt⟩ | ⟨hlab, _, _⟩
      · obtain rfl : i = 0 := aL_inj hlab
        subst hus; subst hvt
        refine ⟨Nat.zero_le _, ?_, ?_⟩
        · exact meet_inr_s _ _
        · exact congrArg
            (fun z => (Quot.mk _ (Sum.inr z) : (toGraph (entL n)).V))
            (gcomp_glue _ _)
      · exact absurd hlab aL_ne_bL
    · subst hu'; subst hv'
      rcases glued_edge_elim he' with ⟨u'', v'', hu'', hv'', he''⟩ |
        ⟨u'', v'', hu'', hv'', he''⟩
      · -- `mids` tower: `aL (j+1)`-edges run `midsMid j → s`.
        subst hu''; subst hv''
        obtain ⟨j, hjk, hij, hc, hd⟩ := mids_edge_aL_full he''
        subst hc; subst hd; subst hij
        refine ⟨by omega, ?_, rfl⟩
        simp only [eCorn, if_pos hjk]
      · -- last border factor `c₀° ∩ d_{n+1}`: has no `aL`-labelled edge.
        rcases meet_recip_arrow_edge he'' with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
        · exact absurd hlab aL_ne_cL
        · exact absurd hlab aL_ne_dL

/-- In a branch, the only `cL`-labelled edge is `cL (j+1)`, from the branch's
    middle vertex to the `t`-mark (the collapsed `Q`). -/
theorem branch_edge_cL_full {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (cL i)) :
    i = j + 1 ∧ c = branchMid j ∧ d = (toGraph (branch j)).t := by
  have hd := branch_edge_cL h
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · rcases meet_arrow_recip_edge he with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
    · exact absurd hlab cL_ne_bL
    · exact absurd hlab.symm aL_ne_cL
  · rcases meet_recip_arrow_edge he with ⟨hlab, _, _⟩ | ⟨hlab, hus, _⟩
    · exact absurd hlab cL_ne_dL
    · subst hus
      refine ⟨cL_inj hlab, ?_, hd⟩
      rw [← hu]
      exact (gcomp_glue _ _).symm

/-- In the `mids` tower, every `cL i`-labelled edge has `i = j+1` for some
    branch index `j ≤ k`, and runs from the `j`-th middle vertex to the
    `t`-mark. -/
theorem mids_edge_cL_full : ∀ {k i : Nat} {c d : (toGraph (mids k)).V},
    (toGraph (mids k)).edge c d (cL i) →
      ∃ j, j ≤ k ∧ i = j + 1 ∧ c = midsMid k j ∧ d = (toGraph (mids k)).t := by
  intro k
  induction k with
  | zero =>
    intro i c d h
    obtain ⟨hij, hc, hd⟩ := branch_edge_cL_full h
    exact ⟨0, Nat.le_refl _, hij, hc, hd⟩
  | succ m ih =>
    intro i c d h
    rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
    · obtain ⟨j, hjk, hij, hc, hd⟩ := ih he
      subst hc; subst hd; subst hu; subst hv
      refine ⟨j, Nat.le_succ_of_le hjk, hij, ?_, rfl⟩
      simp only [midsMid, if_pos hjk]
    · obtain ⟨hij, hc, hd⟩ := branch_edge_cL_full he
      subst hc; subst hd; subst hu; subst hv
      refine ⟨m+1, Nat.le_refl _, hij, ?_, meet_inr_t _ _⟩
      simp only [midsMid, if_neg (by omega : ¬ m + 1 ≤ m)]

/-- **Edge-uniqueness, bottom entries.**  Every `cL i`-labelled edge of the
    collapsed graph `[entL n]` has `i ≤ n+1`, starts at the corner
    `eCorn n i`, and ends at the collapsed bottom vertex `Qv n`. -/
theorem entL_edge_cL_full {n i : Nat} {c d : (toGraph (entL n)).V}
    (h : (toGraph (entL n)).edge c d (cL i)) :
    i ≤ n + 1 ∧ c = eCorn n i ∧ d = Qv n := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · exact he.elim
  · subst hu; subst hv
    rcases glued_edge_elim he with ⟨u', v', hu', hv', he'⟩ | ⟨u', v', hu', hv', he'⟩
    · -- first border factor: no `cL`-labelled edge.
      rcases meet_arrow_recip_edge he' with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
      · exact absurd hlab.symm aL_ne_cL
      · exact absurd hlab cL_ne_bL
    · subst hu'; subst hv'
      rcases glued_edge_elim he' with ⟨u'', v'', hu'', hv'', he''⟩ |
        ⟨u'', v'', hu'', hv'', he''⟩
      · -- `mids` tower: `cL (j+1)`-edges run `midsMid j → t`.
        subst hu''; subst hv''
        obtain ⟨j, hjk, hij, hc, hd⟩ := mids_edge_cL_full he''
        subst hc; subst hd; subst hij
        refine ⟨by omega, ?_, rfl⟩
        simp only [eCorn, if_pos hjk]
      · -- last border factor `c₀° ∩ d_{n+1}`: the `c₀`-edge runs `t → s`.
        subst hu''; subst hv''
        rcases meet_recip_arrow_edge he'' with ⟨hlab, hut, hvs⟩ | ⟨hlab, _, _⟩
        · obtain rfl : i = 0 := cL_inj hlab
          subst hut; subst hvs
          refine ⟨Nat.zero_le _, ?_, ?_⟩
          · exact meet_inr_t _ _
          · exact congrArg
              (fun z => (Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inr z)))
                : (toGraph (entL n)).V))
              (gcomp_glue _ _).symm
        · exact absurd hlab cL_ne_dL

end Freyd.S2_158
