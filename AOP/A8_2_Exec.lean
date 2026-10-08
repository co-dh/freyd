/-
  Bird & de Moor §8.2, display 8.2d (book p.198) as executable Lean.

  Every relation of the 8.2d chain is instantiated at `Rel(Set)`, at the layered network's base
  bifunctor `F(A,X) = A + A×X` (`pathF`, both arguments moving), and each row gets a program
  whose graph — its output read as a set by membership — is contained in that row's relation.
  The end-to-end theorem `mcp_spec` runs the fold of `[wrap,step]` over the layers and a
  least-cost choice, and is proved by the chain itself: the code's algebra is contained in
  row 8, rows 8 → 7 → 6 are the chain's equalities, and `thinning_paths` puts the thinned fold
  inside the specification `Λ(relCata(pathAlg)) est(R)`.

  A layer is a `List V`, a set of paths a `List (ConsList V V)`; `memS` reads either as a set.
-/
module -- shake: keep-all

public import AOP.A5_7_PowerBeads
public import AOP.A5_6_ListCombinators
meta import AOP.A8_2
public import AOP.A8_2

namespace Freyd.Alg
open PowerAllegory

open RelSet RelSet.CL

/-- The initial algebra of 8.2d's fold relator `F(PV,−)`: networks are cons-lists of layers
    (book p.196).  `CL.initial`'s data verbatim; its laws carried over by `pathF_map_id`. -/
@[expose] public def pathInit (A : Type) :
    InitialAlgebra (pathF.appl (P (dE A))) where
  t := dCL (A → Prop) (A → Prop)
  α := alphaR
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f hf := by
    show _ = pathF.map (𝟙 _) _ ≫ f
    rw [pathF_map_id]
    exact (CL.initial (A → Prop) (A → Prop)).cata_comm f hf
  cata_unique f hf h hmap hcomm := by
    change _ = pathF.map (𝟙 _) _ ≫ f at hcomm
    rw [pathF_map_id] at hcomm
    exact (CL.initial (A → Prop) (A → Prop)).cata_unique f hf h hmap hcomm

/-- A fold over `pathInit` is the fold over `CL.initial`: the two differ only in how `F(𝟙,∋)`
    is spelled (8.2d, book p.198). -/
public theorem relCata_pathInit {A : Type} {B : RelSet.{0}}
    (R : (pathF.appl (P (dE A))).obj B ⟶ B) :
    relCata (I := pathInit A) R = relCata (I := CL.initial (A → Prop) (A → Prop)) R := by
  show cataFold (Λ (pathF.map (𝟙 _) (∋ B) ≫ R)) ≫ ∋ B = cataFold (Λ (Fmap _ _ (∋ B) ≫ R)) ≫ ∋ B
  rw [pathF_map_id]
  rfl

section Exec

variable {A : Type}

/-! ## The code -/

/-- A listed layer or set of paths read as a set, by membership. -/
@[expose] public def memS {α : Type} (l : List α) : α → Prop := fun a => a ∈ l

/-- 8.2d `est(R)` at `R ≜ cost≤cost°` (book p.198), executable: one cost-least member of a listed
    set, `none` on the empty one. -/
@[expose] public def minPath (wt : A → A → Nat) : List (ConsList A A) → Option (ConsList A A)
  | [] => none
  | p :: ps => some (ps.foldl (fun m q => if costOf wt q < costOf wt m then q else m) p)

/-- 8.2d `Λ(F(∋,𝟙)) = 𝟙+cpl` (book p.198), executable: take one vertex out of the layer. -/
@[expose] public def cpl : List A ⊕ (List A × List (ConsList A A))
    → List (A ⊕ (A × List (ConsList A A)))
  | .inl vs => vs.map .inl
  | .inr (vs, ps) => vs.map fun v => .inr (v, ps)

/-- 8.2d row 8 `[wrap,step]` (book p.198), executable: `wrap` the vertex, or cons it onto every
    listed tail and keep a cheapest. -/
@[expose] public def wrapStep (wt : A → A → Nat) :
    A ⊕ (A × List (ConsList A A)) → Option (ConsList A A)
  | .inl v => some (.wrap v)
  | .inr (v, ps) => minPath wt (ps.map (.cons v))

/-- 8.2d row 8 `Λ(F(∋,𝟙)) P([wrap,step])` (book p.198), executable: the fold's algebra. -/
@[expose] public def pathAlgExec (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  (cpl x).filterMap (wrapStep wt)

/-- 8.2d the fold `⦇Λ(F(∋,𝟙)) P([wrap,step])⦈` over the layers, top layer first (book p.198). -/
@[expose] public def pathsExec (wt : A → A → Nat) : ConsList (List A) (List A) → List (ConsList A A)
  | .wrap vs => pathAlgExec wt (.inl vs)
  | .cons vs n => pathAlgExec wt (.inr (vs, pathsExec wt n))

/-- 8.2d the program (book p.198): the fold over the layers, then `est(R)` — a least-cost path. -/
@[expose] public def mcp (wt : A → A → Nat) (net : ConsList (List A) (List A)) :
    Option (ConsList A A) :=
  minPath wt (pathsExec wt net)

/-- 8.2d's input read as the relation's: every layer of the network as a set. -/
@[expose] public def netSet : ConsList (List A) (List A) → ConsList (A → Prop) (A → Prop)
  | .wrap vs => .wrap (memS vs)
  | .cons vs n => .cons (memS vs) (netSet n)

/-- 8.2d's algebra input `F(PV,PLV)` read as sets. -/
@[expose] public def toS : List A ⊕ (List A × List (ConsList A A))
    → (pathF.obj (P (dE A)) (P (dCL A A))).carrier
  | .inl vs => .inl (memS vs)
  | .inr (vs, ps) => .inr (memS vs, memS ps)

/-- 8.2d's `[wrap,step]` input `F(V,PLV)` read as sets. -/
@[expose] public def toS1 : A ⊕ (A × List (ConsList A A))
    → (Fobj A A (P (dCL A A))).carrier
  | .inl v => .inl v
  | .inr (v, ps) => .inr (v, memS ps)

/-! ## `est(R)` and the algebra, code against relation -/

/-- 8.2d `est(R)` (book p.198): `minPath` returns a member of its list that costs no more than any
    member. -/
public theorem minPath_spec (wt : A → A → Nat) {l : List (ConsList A A)} {r : ConsList A A}
    (h : minPath wt l = some r) : r ∈ l ∧ ∀ q ∈ l, costOf wt r ≤ costOf wt q := by
  have key : ∀ (ps : List (ConsList A A)) (m : ConsList A A),
      ps.foldl (fun m q => if costOf wt q < costOf wt m then q else m) m ∈ m :: ps ∧
      ∀ q ∈ m :: ps,
        costOf wt (ps.foldl (fun m q => if costOf wt q < costOf wt m then q else m) m)
          ≤ costOf wt q := by
    intro ps
    induction ps with
    | nil => intro m; exact ⟨List.mem_cons.mpr (Or.inl rfl), fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Nat.le_refl _
        · exact nomatch hq⟩
    | cons q qs ih =>
      intro m
      obtain ⟨h1, h2⟩ := ih (if costOf wt q < costOf wt m then q else m)
      rw [List.foldl_cons]
      by_cases hq : costOf wt q < costOf wt m
      · rw [if_pos hq] at h1 h2 ⊢
        refine ⟨?_, fun z hz => ?_⟩
        · rcases List.mem_cons.mp h1 with e | e
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr e)))
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (h2 q (List.mem_cons.mpr (Or.inl rfl))) hq)
          · exact h2 z hz
      · rw [if_neg hq] at h1 h2 ⊢
        refine ⟨?_, fun z hz => ?_⟩
        · rcases List.mem_cons.mp h1 with e | e
          · exact List.mem_cons.mpr (Or.inl e)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr e)))
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact h2 z (List.mem_cons.mpr (Or.inl rfl))
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact Nat.le_trans (h2 m (List.mem_cons.mpr (Or.inl rfl))) (Nat.not_lt.mp hq)
            · exact h2 z (List.mem_cons.mpr (Or.inr hz))
  cases l with
  | nil => exact nomatch h
  | cons p ps =>
    cases h
    exact key ps p

/-- 8.2d `est(R)` (book p.198): on a non-empty list `minPath` returns something. -/
public theorem minPath_isSome (wt : A → A → Nat) :
    ∀ {l : List (ConsList A A)}, l ≠ [] → ∃ r, minPath wt l = some r
  | [], h => absurd rfl h
  | _ :: _, _ => ⟨_, rfl⟩

/-- **8.2d row 8, executable** (book p.198, `F(𝟙,∋) P(α) est(R) = [wrap,step]`): `wrapStep`'s
    graph is contained in `[wrap,step]`.  Proved on the row's left-hand side, `Λ(F(𝟙,∋)α) est(R)`,
    to which the row's own theorem rewrites `[wrap,step]`. -/
public theorem cpMap_comp_powerRel_alphaR_comp_est_eq_junc_exec (wt : A → A → Nat)
    (z : A ⊕ (A × List (ConsList A A))) (p : ConsList A A) (h : wrapStep wt z = some p) :
    junc (sumCop (dL A) (⟨A × (pow (dCL A A)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt)
      (toS1 z) p := by
  rw [← cpMap_comp_powerRel_alphaR_comp_est_eq_junc wt]
  have hL : cpMap (CL.F A A) (dCL A A)
      ≫ powerRel (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) = Λ (pathSplit (A := A)) := by
    have hα : Map (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) := graph_map _
    simp only [cpMap]
    rw [powerRel_map hα, Λ_absorption, ← pathSplit_eq_Fmap_comp_alphaR]
  rw [← Cat.assoc, hL, Λ_comp_est_apply]
  cases z with
  | inl v =>
    cases h
    exact ⟨(pathSplit_apply _ _).mpr rfl, fun q hq => by have hq := (pathSplit_apply _ _).mp hq; subst hq; exact (pathR_apply wt _ _).mpr (Nat.le_refl _)⟩
  | inr q =>
    obtain ⟨v, ps⟩ := q
    obtain ⟨hm, hle⟩ := minPath_spec wt h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    refine ⟨(pathSplit_apply _ _).mpr ⟨t, ht, rfl⟩, ?_⟩
    intro z hz; obtain ⟨t', ht', rfl⟩ := (pathSplit_apply _ _).mp hz
    exact (pathR_apply wt _ _).mpr (hle _ (List.mem_map.mpr ⟨t', ht', rfl⟩))

/-- 8.2d row 8 as the fold's algebra: `Λ(F(∋,𝟙)) P([wrap,step])` at `Rel(Set)`. -/
@[expose] public def pathAlgRel (wt : A → A → Nat) :
    pathF.obj (P (dE A)) (P (dCL A A))
      ⟶ P (dCL A A) :=
  Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
    ≫ powerRel (junc (sumCop (dL A) (⟨A × (pow (dCL A A)).carrier⟩ : RelSet.{0}))
      wrapR (pathStep wt))

/-- **8.2d row 8, the fold's algebra executable** (book p.198): `pathAlgExec`'s graph is contained
    in `Λ(F(∋,𝟙)) P([wrap,step])`, provided a non-leaf input carries at least one path — on an
    empty set of tails `step` has no value, so `P` relates nothing. -/
public theorem pathAlgExec_le (wt : A → A → Nat) (x : List A ⊕ (List A × List (ConsList A A)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    pathAlgRel wt (toS x) (memS (pathAlgExec wt x)) := by
  simp only [pathAlgRel]
  rw [Λ_eq_classifier]
  refine ⟨fun z => pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))) (toS x) z, rfl,
    (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro z hz
    cases x with
    | inl vs =>
      cases z with
      | inl v =>
        exact ⟨_, cpMap_comp_powerRel_alphaR_comp_est_eq_junc_exec wt (.inl v) _ rfl,
          List.mem_filterMap.mpr ⟨.inl v, List.mem_map.mpr ⟨v, hz, rfl⟩, rfl⟩⟩
      | inr q => exact hz.elim
    | inr q =>
      obtain ⟨vs, ps⟩ := q
      cases z with
      | inl v => exact hz.elim
      | inr r =>
        obtain ⟨v, P⟩ := r
        obtain ⟨hv, hP⟩ := hz
        have hP' : memS ps = P := hP
        subst hP'
        have hne : ps.map (ConsList.cons v) ≠ [] := by
          cases ps with
          | nil => exact absurd rfl (hx vs [] rfl)
          | cons t ts => exact fun h => nomatch h
        obtain ⟨y, hy⟩ := minPath_isSome wt hne
        exact ⟨y, cpMap_comp_powerRel_alphaR_comp_est_eq_junc_exec wt (.inr (v, ps)) y hy,
          List.mem_filterMap.mpr ⟨.inr (v, ps), List.mem_map.mpr ⟨v, hv, rfl⟩, hy⟩⟩
  · intro y hy
    obtain ⟨a, ha, hay⟩ := List.mem_filterMap.mp hy
    refine ⟨toS1 a, ?_, cpMap_comp_powerRel_alphaR_comp_est_eq_junc_exec wt a y hay⟩
    cases x with
    | inl vs =>
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact hv
    | inr q =>
      obtain ⟨vs, ps⟩ := q
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact ⟨hv, rfl⟩

/-- 8.2d the fold, executable (book p.198): `pathsExec` is a value of `⦇Λ(F(∋,𝟙)) P([wrap,step])⦈`
    unless it is empty — an empty layer below leaves `step` nothing to choose from. -/
public theorem pathsExec_rel (wt : A → A → Nat) :
    ∀ net : ConsList (List A) (List A),
      pathsExec wt net = [] ∨ cataR (pathAlgRel wt) (netSet net) (memS (pathsExec wt net))
  | .wrap vs => Or.inr (pathAlgExec_le wt (.inl vs) (fun _ _ h => nomatch h))
  | .cons vs n => by
    by_cases hz : pathsExec wt n = []
    · left
      show (cpl (.inr (vs, pathsExec wt n))).filterMap (wrapStep wt) = []
      rw [hz]
      simp only [cpl]
      induction vs with
      | nil => rfl
      | cons v vs ih => exact ih
    · right
      rcases pathsExec_rel wt n with h0 | hr
      · exact absurd h0 hz
      · exact ⟨_, hr, pathAlgExec_le wt (.inr (vs, pathsExec wt n))
          (fun _ _ h => by cases h; exact hz)⟩

/-- 8.2d's specification algebra `F(∋,𝟙)α` at the bifunctor IS `pathAlg` (book p.196). -/
public theorem pathF_map_comp_alphaR_eq_pathAlg :
    (pathF.map (∋ (dE A)) (𝟙 (dCL A A)) ≫ alphaR
      : pathF.obj (P (dE A)) (dCL A A) ⟶ dCL A A) = pathAlg (A := A) := by
  apply hom_ext
  intro u p
  cases u with
  | inl S =>
    constructor
    · rintro ⟨w, hw, hp⟩
      cases w with
      | inl v => exact ⟨v, hw, hp⟩
      | inr r => exact hw.elim
    · rintro ⟨v, hv, hp⟩
      exact ⟨.inl v, hv, hp⟩
  | inr q =>
    constructor
    · rintro ⟨w, hw, hp⟩
      cases w with
      | inl v => exact hw.elim
      | inr r =>
        obtain ⟨hv, ht⟩ := hw
        have ht' : q.2 = r.2 := ht
        exact ⟨r.1, hv, by rw [ht']; exact hp⟩
    · rintro ⟨v, hv, hp⟩
      exact ⟨.inr (v, q.2), ⟨hv, rfl⟩, hp⟩

/-- **The algebra chain at the layered network** (book p.198): `thinning_paths_alg` at the
    network's `α`, `R` and `Q`, whose `R∩(S°S)⊑Q` is `pathR_inter_recip_le_pathQ`. -/
public theorem thinning_paths_alg_net (wt : A → A → Nat) :
    Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ est (pathR wt))
      ⊑ Λ (pathF.map (∋ (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ thinRel (pathQ wt) :=
  thinning_paths_alg (F := pathF) (α := alphaR) (pathR_inter_recip_le_pathQ wt)

/-- **Corollary 8.1 at the layered network** (book p.198, the step the thinning theorem makes):
    the specification is above the thinned fold —
    `min R·Λ⦇α·F(∈,id)⦈ ⊒ min R·⦇thin Q·Λ(α·F(∈,∈))⦈`, mirrored.  `thinning_est` is stated at
    `Λ(F(∋)·S)·thin Q` for the fold's own relator `F(E A,−)`, whose action on `∋` is `F(𝟙,∋)`;
    `F(𝟙,∋)F(∋,𝟙)α` IS `F(∋,∋)α`, by interchange.  Its premises are the network's own laws:
    `pathQ_le_pathR`, the two preorders, and `pathAlg_monotonic`. -/
public theorem thinning_paths_step (wt : A → A → Nat) :
    relCata (I := pathInit A) (Λ (pathF.map (∋ (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ thinRel (pathQ wt))
        ≫ est (pathR wt)
      ⊑ Λ (relCata (I := pathInit A) (pathF.map (∋ (dE A)) (𝟙 (dCL A A)) ≫ alphaR))
        ≫ est (pathR wt) := by
  have e : (pathF.appl (P (dE A))).map (∋ (dCL A A)) ≫ (pathF.map (∋ (dE A)) (𝟙 (dCL A A)) ≫ alphaR)
      = pathF.map (∋ (dE A)) (∋ (dCL A A)) ≫ alphaR := by
    show pathF.map (𝟙 (P (dE A))) (∋ (dCL A A)) ≫ (pathF.map (∋ (dE A)) (𝟙 (dCL A A)) ≫ alphaR) = _
    rw [← Cat.assoc, pathF.interchange' (∋ (dE A)) (∋ (dCL A A))]
  rw [← e]
  refine thinning_est (pathInit A) (pathQ_le_pathR wt) (pathQ_preorder wt) (pathR_preorder wt) ?_
  show pathF.map (𝟙 _) (pathQ wt) ≫ _ ⊑ _
  rw [pathF_map_id, pathF_map_comp_alphaR_eq_pathAlg]
  exact pathAlg_monotonic wt

/-- **The §8.2 headline** (book p.198): a least-cost path in a layered network, as a fold over
    the layers —
    `min R·Λ⦇α·F(∈,id)⦈ ⊒ min R·⦇P(min R·Λ(α·F(id,∈)))·ΛF(∈,id)⦈`, mirrored, at the network's
    own `α = [wrap,cons]`, `R ≜ cost≤cost°` and `Q ≜ R∩(head head°)`.  `thinning_paths_alg`
    supplies the algebra, its `R∩(S°S)⊑Q` discharged by `pathR_inter_recip_le_pathQ`;
    `thinning_paths_step` supplies the fold, its monotonicity discharged by `pathAlg_monotonic`. -/
public theorem thinning_paths (wt : A → A → Nat) :
    relCata (I := pathInit A) (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ est (pathR wt)))
        ≫ est (pathR wt)
      ⊑ Λ (relCata (I := pathInit A) (pathF.map (∋ (dE A)) (𝟙 (dCL A A)) ≫ alphaR))
        ≫ est (pathR wt) :=
  -- The terms are the two laws' own sides: spelled out, `relCata`'s initial algebra is a fresh
  -- metavariable that `whnf` cannot close within the heartbeat budget.
  calc _ ⊑ _ := comp_mono_right (relCata_le_relCata (pathInit A)
          (comp_mono_left _ (thinning_paths_alg_net wt))) (est (pathR wt))
    _ ⊑ _ := thinning_paths_step wt

calc_steps thinning_paths

/-- **8.2d end to end** (book p.198): whatever `mcp` returns is related to the network by the
    specification `Λ(relCata(pathAlg)) est(R)` — a path of the network that costs no more than
    any other.  The code's algebra sits in row 8, rows 8 → 7 → 6 are the chain's equalities
    (`cpMap_comp_powerRel_alphaR_comp_est_eq_junc`, `thinning_paths_alg_map`), and
    `thinning_paths` (which runs `thinning_paths_alg`) takes the fold into the specification. -/
public theorem mcp_spec (wt : A → A → Nat) (net : ConsList (List A) (List A)) (p : ConsList A A)
    (h : mcp wt net = some p) :
    (Λ (relCata (I := CL.initial (A → Prop) (A → Prop)) (pathAlg (A := A))) ≫ est (pathR wt))
      (netSet net) p := by
  have hthin := thinning_paths wt
  have hα : Map (alphaR : pathF.obj (dE A) (dCL A A) ⟶ dCL A A) := graph_map _
  rw [← thinning_paths_alg_map (F := pathF) (A := dE A) hα (pathR wt)] at hthin
  have e8 : Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)))
      ≫ powerRel (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) ≫ est (pathR wt)
      = junc (sumCop (dL A) (⟨A × (pow (dCL A A)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt) := by
    rw [pathF_map_id]
    exact cpMap_comp_powerRel_alphaR_comp_est_eq_junc wt
  rw [e8, pathF_map_comp_alphaR_eq_pathAlg, relCata_pathInit, relCata_pathInit] at hthin
  refine le_iff.mp hthin _ _ ?_
  have hne : pathsExec wt net ≠ [] := fun h0 => by
    simp only [mcp, h0, minPath] at h
    exact nomatch h
  rcases pathsExec_rel wt net with h0 | hr
  · exact absurd h0 hne
  · obtain ⟨hm, hle⟩ := minPath_spec wt h
    refine ⟨memS (pathsExec wt net), ?_, (est_apply _ _ _).mpr ⟨hm, fun z hz => (pathR_apply wt p z).mpr (hle z hz)⟩⟩
    rw [← cataR_eq_relCata]
    exact hr

/-- `minpath` (book p.196): the program's graph — a network, read as its layers' sets, is related
    to the path `mcp` returns on it. -/
@[expose] public def minpath (wt : A → A → Nat) : dCL (A → Prop) (A → Prop) ⟶ dCL A A :=
  fun xs ys => ∃ xss, xs = netSet xss ∧ mcp wt xss = some ys

/-- `F(A,X) = A+A×X` (book p.196): the layered network's base bifunctor on objects, the
    statement 8.2a's first row prints. -/
public theorem pathF_obj (B X : RelSet.{0}) :
    pathF.obj B X = ⟨B.carrier ⊕ B.carrier × X.carrier⟩ := rfl

/-- `α = [wrap,cons]` (book p.196) at the layered network's `F`: the initial algebra
    `F(V,list⁺(V))⟶list⁺(V)`, typed at 8.2's instance of `CL`'s generic leaf and element. -/
public theorem alphaR_pathF :
    @Eq (pathF.obj (dE A) (dCL A A) ⟶ dCL A A) alphaR (RelSet.graph con) := rfl

/-- `⦇F(∋,𝟙)α⦈ = L(∋)` (book p.196): the fold that takes one vertex out of each layer is the list
    relator `L = list⁺` applied to `∋` — the type functor's action on an arrow, at `∋`. -/
public theorem relCata_pathF_eps_eq_nelist :
    relCata (I := pathInit A) (pathF.map (∋ (dE A)) (𝟙 (dCL A A)) ≫ alphaR)
      = ListRel.nelistRelator.map (∋ (dE A)) := by
  rw [relCata_pathInit, pathF_map_comp_alphaR_eq_pathAlg, ← cataR_eq_relCata]
  apply hom_ext
  intro x
  induction x with
  | wrap S =>
    intro p
    cases p with
    | wrap b => exact ⟨fun ⟨_, hv, h⟩ => (by cases h; exact hv), fun h => ⟨b, h, rfl⟩⟩
    | cons b y => exact ⟨fun ⟨_, _, h⟩ => (by cases h), False.elim⟩
  | cons S tl ih =>
    intro p
    cases p with
    | wrap b => exact ⟨fun ⟨_, _, _, _, h⟩ => (by cases h), False.elim⟩
    | cons b y =>
      exact ⟨fun ⟨_, hr, _, hv, h⟩ => (by cases h; exact ⟨hv, (ih _).mp hr⟩),
        fun ⟨hb, hy⟩ => ⟨y, (ih y).mpr hy, b, hb, rfl⟩⟩

/-- **the `⦇F(∋,𝟙)α⦈` bead is LAX** (book p.196): it is `L(∋)`, and `L` applied outside the lax
    natural `∋` keeps the square lax, `L(P(R)) ⦇F(∋,𝟙)α⦈ ⊑ ⦇F(∋,𝟙)α⦈ L(R)`. -/
public theorem relCata_pathF_eps_laxNatural :
    LaxNatural (Relator.comp (Relator.idRelator RelSet.{0}) ListRel.nelistRelator)
      (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) powerRelator)
        ListRel.nelistRelator)
      (fun a => (relCata (I := pathInit a.carrier)
          (pathF.map (∋ (dE a.carrier)) (𝟙 (dCL a.carrier a.carrier)) ≫ alphaR)
        : ListRel.dNE (a.carrier → Prop) ⟶ ListRel.dNE a.carrier)) := by
  intro a b R
  dsimp only
  rw [relCata_pathF_eps_eq_nelist, relCata_pathF_eps_eq_nelist]
  exact ListRel.nelistRelator.map_laxNatural eps_laxNatural R

/-- The problem (B&dM p.196: `minpath ⊑ min R · Λ(list⁺ ∈)`), in diagram order: whatever
    `minpath` returns is a cheapest path through the layers, `minpath ⊑ Λ(L(∋)) est(R)`. -/
public theorem minpath_spec (wt : A → A → Nat) :
    minpath wt ⊑ Λ (ListRel.nelistRelator.map (∋ (dE A))) ≫ est (pathR wt) :=
  le_iff.mpr fun _ p ⟨net, hx, h⟩ => by
    subst hx
    rw [← relCata_pathF_eps_eq_nelist, relCata_pathInit, pathF_map_comp_alphaR_eq_pathAlg]
    exact mcp_spec wt net p h

/-- 8.2d end to end, pointwise (book p.196's problem): `mcp`'s answer is a path of the network
    and no path of the network is cheaper. -/
public theorem mcp_least (wt : A → A → Nat) (net : ConsList (List A) (List A)) (p : ConsList A A)
    (h : mcp wt net = some p) :
    relCata (I := CL.initial (A → Prop) (A → Prop)) (pathAlg (A := A)) (netSet net) p
      ∧ ∀ q, relCata (I := CL.initial (A → Prop) (A → Prop)) (pathAlg (A := A)) (netSet net) q
        → costOf wt p ≤ costOf wt q :=
  have ⟨h1, h2⟩ := (Λ_comp_est_apply _ _ _ _).mp (mcp_spec wt net p h)
  ⟨h1, fun q hq => (pathR_apply wt p q).mp (h2 q hq)⟩

/-! ## Rows 1–7 of 8.2d, each with its program

  Every row is the relation of its A8_2 step theorem at `pathF`, `A := dE V`, `B := dCL V V`,
  `α := alphaR`, `Q := pathQ wt`, `R := pathR wt`; the program `rowᵢ` is the draft's `lᵢ`, and
  its lemma says `rowᵢ`'s output, read as a set, is related to the input read as sets. -/

/-- 8.2d `Λ(F(𝟙,∋)) = 𝟙+cpr` (book p.198), executable: take one path out of the listed set. -/
@[expose] public def cpr : A ⊕ (A × List (ConsList A A)) → List (A ⊕ (A × ConsList A A))
  | .inl v => [.inl v]
  | .inr (v, ps) => ps.map fun p => .inr (v, p)

/-- 8.2d `Λ(S)`, `S ≜ F(𝟙,∋)α` (book p.198), executable: every path `α` builds from one vertex
    and one listed tail. -/
@[expose] public def sExec (z : A ⊕ (A × List (ConsList A A))) : List (ConsList A A) :=
  (cpr z).map (con (L := A) (E := A))

/-- 8.2d `Q ≜ R∩(head head°)` (book p.197), decided. -/
@[expose] public def qExec [DecidableEq A] (wt : A → A → Nat) (x y : ConsList A A) : Bool :=
  decide (costOf wt x ≤ costOf wt y ∧ headOf x = headOf y)

/-- 8.2d `thin(Q)` (book (8.1)), executable: keep `x` unless a kept path `Q`-beats it, and drop
    the kept paths `x` beats. -/
@[expose] public def thinExec [DecidableEq A] (wt : A → A → Nat) (xs : List (ConsList A A)) :
    List (ConsList A A) :=
  xs.foldr (fun x ys => if ys.any (qExec wt · x) then ys else x :: ys.filter (!qExec wt x ·)) []

/-- 8.2d `thin(Q)` (book (8.1)): `thinExec` keeps a sublist that has a `Q`-lower bound for every
    member of its input. -/
public theorem thinExec_spec [DecidableEq A] (wt : A → A → Nat) (xs : List (ConsList A A)) :
    (∀ y ∈ thinExec wt xs, y ∈ xs) ∧ ∀ z ∈ xs, ∃ w ∈ thinExec wt xs, pathQ wt w z := by
  have hq : ∀ x y, qExec wt x y = true ↔ pathQ wt x y := fun _ _ => decide_eq_true_iff.trans (pathQ_apply wt _ _).symm
  induction xs with
  | nil => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | cons x xs ih =>
    obtain ⟨hs, hc⟩ := ih
    have e : thinExec wt (x :: xs) = if (thinExec wt xs).any (qExec wt · x) then thinExec wt xs
        else x :: (thinExec wt xs).filter (!qExec wt x ·) := rfl
    rw [e]
    by_cases ha : (thinExec wt xs).any (qExec wt · x) = true
    · rw [if_pos ha]
      refine ⟨fun y hy => List.mem_cons.mpr (Or.inr (hs y hy)), fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨w, hw, hwz⟩ := List.any_eq_true.mp ha
        exact ⟨w, hw, (hq w z).mp hwz⟩
      · exact hc z hz
    · rw [if_neg ha]
      refine ⟨fun y hy => ?_, fun z hz => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr (hs y (List.mem_filter.mp hy).1))
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨z, List.mem_cons.mpr (Or.inl rfl), (pathQ_apply wt z z).mpr ⟨Nat.le_refl _, rfl⟩⟩
        · obtain ⟨w, hw, hwz⟩ := hc z hz
          by_cases hx : qExec wt x w = true
          · have hxw := (pathQ_apply wt x w).mp ((hq x w).mp hx)
            have hwz := (pathQ_apply wt w z).mp hwz
            exact ⟨x, List.mem_cons.mpr (Or.inl rfl),
              (pathQ_apply wt x z).mpr ⟨Nat.le_trans hxw.1 hwz.1, hxw.2.trans hwz.2⟩⟩
          · have hf : qExec wt x w = false := Bool.eq_false_iff.mpr hx
            refine ⟨w, List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨hw, ?_⟩)), hwz⟩
            rw [hf]; rfl

/-- 8.2d `thin(Q)` at `Rel(Set)` (book (8.1)): `thinExec`'s graph is contained in `thinRel Q` on any
    set its input lists. -/
public theorem thinExec_le [DecidableEq A] (wt : A → A → Nat) (xs : List (ConsList A A))
    (P : (pow (dCL A A)).carrier) (hP : ∀ p, P p ↔ p ∈ xs) :
    thinRel (pathQ wt) P (memS (thinExec wt xs)) := by
  obtain ⟨hs, hc⟩ := thinExec_spec wt xs
  exact (thinRel_pt _ _ _).mpr ⟨fun y hy => (hP y).mpr (hs y hy),
    fun z hz => (hc z ((hP z).mp hz)).imp fun _ h => ⟨h.2, h.1⟩⟩

/-- 8.2d `Λ(F(∋,𝟙))` (book p.198): the vertices taken out of the layer are what `cpl` lists. -/
public theorem cpl_char (x : List A ⊕ (List A × List (ConsList A A)))
    (w : (pathF.obj (dE A) (P (dCL A A))).carrier) :
    pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))) (toS x) w
      ↔ ∃ z ∈ cpl x, w = toS1 z := by
  constructor
  · intro h
    cases x with
    | inl vs =>
      cases w with
      | inl v => exact ⟨.inl v, List.mem_map.mpr ⟨v, h, rfl⟩, rfl⟩
      | inr r => exact h.elim
    | inr q =>
      obtain ⟨vs, ps⟩ := q
      cases w with
      | inl v => exact h.elim
      | inr r =>
        obtain ⟨v, P⟩ := r
        obtain ⟨hv, hP⟩ := h
        have hP' : memS ps = P := hP
        subst hP'
        exact ⟨.inr (v, ps), List.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    cases x with
    | inl vs =>
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      exact hv
    | inr q =>
      obtain ⟨vs, ps⟩ := q
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      exact ⟨hv, rfl⟩

/-- 8.2d `S ≜ F(𝟙,∋)α` (book p.198): the paths `S` builds are what `sExec` lists. -/
public theorem sExec_char (z : A ⊕ (A × List (ConsList A A))) (p : ConsList A A) :
    (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) (toS1 z) p ↔ p ∈ sExec z := by
  rw [pathF_map_id, ← pathSplit_eq_Fmap_comp_alphaR, pathSplit_apply]
  cases z with
  | inl v =>
    exact ⟨fun h => List.mem_singleton.mpr h, fun h => List.mem_singleton.mp h⟩
  | inr q =>
    obtain ⟨v, ps⟩ := q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact List.mem_map.mpr ⟨.inr (v, t), List.mem_map.mpr ⟨t, ht, rfl⟩, rfl⟩
    · intro h
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      exact ⟨t, ht, rfl⟩

/-- 8.2d `Λ(S) est(R)` (book p.198): `minPath` over `sExec` is `[wrap,step]`'s program. -/
public theorem minPath_sExec (wt : A → A → Nat) (z : A ⊕ (A × List (ConsList A A))) :
    minPath wt (sExec z) = wrapStep wt z := by
  cases z with
  | inl v => rfl
  | inr q =>
    obtain ⟨v, ps⟩ := q
    simp only [sExec, cpr, wrapStep, List.map_map]
    rfl

/-- 8.2d row 3 `Λ(F(∋,𝟙)) P(Λ S) union thin(Q)` (book p.198), executable. -/
@[expose] public def row3 [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  thinExec wt ((cpl x).map sExec).flatten

/-- 8.2d row 2 `Λ(F(∋,𝟙) F(𝟙,∋) α) thin(Q)` (book p.198), executable. -/
@[expose] public def row2 [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  thinExec wt ((cpl x).flatMap fun z => (cpr z).map (con (L := A) (E := A)))

/-- 8.2d row 1 `Λ(F(∋,∋) α) thin(Q)` (book p.198), executable. -/
@[expose] public def row1 [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  thinExec wt (((cpl x).flatMap cpr).map (con (L := A) (E := A)))

/-- **8.2d row 3, executable** (book p.198): `row3`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S) union thin(Q)`. -/
public theorem thinning_paths_alg_transpose_exec [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) :
    (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR))
        ≫ union ≫ thinRel (pathQ wt)) (toS x) (memS (row3 wt x)) := by
  rw [Λ_eq_classifier, Λ_eq_classifier]
  refine ⟨_, rfl, fun T => ∃ z ∈ cpl x, T = fun p => p ∈ sExec z,
    (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩, fun p => ∃ z ∈ cpl x, p ∈ sExec z,
    (bigUnion_apply _ _).mpr fun p => ⟨?_, ?_⟩, thinExec_le wt _ _ fun p => ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := (cpl_char x w).mp hw
    exact ⟨_, funext fun p => propext (sExec_char z p).symm, z, hz, rfl⟩
  · rintro T ⟨z, hz, rfl⟩
    exact ⟨toS1 z, (cpl_char x _).mpr ⟨z, hz, rfl⟩, funext fun p => propext (sExec_char z p).symm⟩
  · rintro ⟨z, hz, hp⟩
    exact ⟨_, ⟨z, hz, rfl⟩, hp⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, hp⟩
    exact ⟨z, hz, hp⟩
  · constructor
    · rintro ⟨z, hz, hp⟩
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨z, hz, rfl⟩, hp⟩
    · intro hp
      obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hl
      exact ⟨z, hz, hp⟩

/-- **8.2d row 2, executable** (book p.198): `row2`'s graph is contained in
    `Λ(F(∋,𝟙) F(𝟙,∋) α) thin(Q)`, which `Λ(RS) = Λ(R) P(Λ(S)) union` equates
    with row 3. -/
public theorem thinning_paths_alg_bifunctors_exec [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) :
    (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A)))
        ≫ pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ thinRel (pathQ wt))
      (toS x) (memS (row2 wt x)) := by
  rw [← thinning_paths_alg.step_7]
  exact thinning_paths_alg_transpose_exec wt x

/-- **8.2d row 1, executable** (book p.198): `row1`'s graph is contained in `Λ(F(∋,∋) α) thin(Q)`,
    which bifunctoriality equates with row 2. -/
public theorem thinning_paths_alg_exec [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) :
    (Λ (pathF.map (∋ (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ thinRel (pathQ wt))
      (toS x) (memS (row1 wt x)) := by
  rw [← thinning_paths_alg.step_8]
  have e : row1 wt x = row2 wt x := by simp only [row1, row2, List.map_flatMap]
  rw [e]
  exact thinning_paths_alg_bifunctors_exec wt x

/-- 8.2d row 4 `Λ(F(∋,𝟙)) P(Λ S thin(Q)) union` (book p.198), executable. -/
@[expose] public def row4 [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  ((cpl x).map fun z => thinExec wt (sExec z)).flatten

/-- **8.2d row 4, executable** (book p.198, the `(8.4)` step): `row4`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S thin(Q)) union`. -/
public theorem thinning_paths_alg_distrib_exec [DecidableEq A] (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) :
    (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ thinRel (pathQ wt))
        ≫ union) (toS x) (memS (row4 wt x)) := by
  have hz : ∀ z, (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ thinRel (pathQ wt))
      (toS1 z) (memS (thinExec wt (sExec z))) := by
    intro z
    rw [Λ_eq_classifier]
    exact ⟨_, rfl, thinExec_le wt _ _ (sExec_char z)⟩
  rw [Λ_eq_classifier]
  refine ⟨_, rfl, fun T => ∃ z ∈ cpl x, T = memS (thinExec wt (sExec z)),
    (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩, (bigUnion_apply _ _).mpr fun p => ⟨?_, ?_⟩⟩
  · intro w hw
    obtain ⟨z, hz', rfl⟩ := (cpl_char x w).mp hw
    exact ⟨_, hz z, z, hz', rfl⟩
  · rintro T ⟨z, hz', rfl⟩
    exact ⟨toS1 z, (cpl_char x _).mpr ⟨z, hz', rfl⟩, hz z⟩
  · intro hp
    obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hl
    exact ⟨_, ⟨z, hz', rfl⟩, hp⟩
  · rintro ⟨_, ⟨z, hz', rfl⟩, hp⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨z, hz', rfl⟩, hp⟩

/-- 8.2d row 5 `Λ(F(∋,𝟙)) P(Λ S est(R) τ) union` (book p.198), executable. -/
@[expose] public def row5 (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  ((cpl x).map fun z => (minPath wt (sExec z)).toList).flatten

/-- **8.2d row 5, executable** (book p.198, the `(8.3)` step): `row5`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S est(R) τ) union`, when a non-leaf input carries a path. -/
public theorem thinning_paths_alg_elim_exec (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ est (pathR wt)
          ≫ singletonMap) ≫ union) (toS x) (memS (row5 wt x)) := by
  have hsome : ∀ z ∈ cpl x, ∃ p, minPath wt (sExec z) = some p := by
    intro z hz
    apply minPath_isSome
    cases x with
    | inl vs =>
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact fun h => nomatch h
    | inr q =>
      obtain ⟨vs, ps⟩ := q
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      cases ps with
      | nil => exact absurd rfl (hx vs [] rfl)
      | cons t ts => exact fun h => nomatch h
  have hz : ∀ z p, minPath wt (sExec z) = some p →
      (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ est (pathR wt) ≫ singletonMap)
        (toS1 z) (memS (minPath wt (sExec z)).toList) := by
    intro z p hp
    obtain ⟨hm, hle⟩ := minPath_spec wt hp
    have hest : (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ est (pathR wt)) (toS1 z) p :=
      (Λ_comp_est_apply _ _ _ _).mpr ⟨(sExec_char z p).mpr hm,
        fun q hq => (pathR_apply wt p q).mpr (hle q ((sExec_char z q).mp hq))⟩
    obtain ⟨P, hP, hPp⟩ := hest
    refine ⟨P, hP, p, hPp, ?_⟩
    show Λ (𝟙 (dCL A A)) p _
    rw [Λ_eq_classifier, hp]
    exact funext fun y => propext ⟨fun h => (List.mem_singleton.mp h).symm,
      fun h => List.mem_singleton.mpr h.symm⟩
  rw [Λ_eq_classifier]
  refine ⟨_, rfl, fun T => ∃ z ∈ cpl x, T = memS (minPath wt (sExec z)).toList,
    (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩, (bigUnion_apply _ _).mpr fun p => ⟨?_, ?_⟩⟩
  · intro w hw
    obtain ⟨z, hz', rfl⟩ := (cpl_char x w).mp hw
    obtain ⟨p, hp⟩ := hsome z hz'
    exact ⟨_, hz z p hp, z, hz', rfl⟩
  · rintro T ⟨z, hz', rfl⟩
    obtain ⟨p, hp⟩ := hsome z hz'
    exact ⟨toS1 z, (cpl_char x _).mpr ⟨z, hz', rfl⟩, hz z p hp⟩
  · intro hp
    obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hl
    exact ⟨_, ⟨z, hz', rfl⟩, hp⟩
  · rintro ⟨_, ⟨z, hz', rfl⟩, hp⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨z, hz', rfl⟩, hp⟩

/-- 8.2d row 6 `Λ(F(∋,𝟙)) P(Λ S est(R))` (book p.198), executable. -/
@[expose] public def row6 (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  (cpl x).filterMap fun z => minPath wt (sExec z)

/-- 8.2d row 7 `Λ(F(∋,𝟙)) P(Λ(F(𝟙,∋)) P(α) est(R))` (book p.198), executable. -/
@[expose] public def row7 (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A))) : List (ConsList A A) :=
  (cpl x).filterMap fun z => minPath wt ((cpr z).map (con (L := A) (E := A)))

/-- 8.2d rows 6 and 7 run `pathAlgExec` (book p.198): `P = E` on functions changes the relation,
    not the program. -/
public theorem row6_eq (wt : A → A → Nat) (x : List A ⊕ (List A × List (ConsList A A))) :
    row6 wt x = pathAlgExec wt x := by
  simp only [row6, pathAlgExec, minPath_sExec]

/-- **8.2d row 7, executable** (book p.198, `P = E` on functions): `row7`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ(F(𝟙,∋)) P(α) est(R))`, which row 8 equates with `Λ(F(∋,𝟙)) P([wrap,step])`. -/
public theorem thinning_paths_alg_map_exec (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)))
          ≫ powerRel (alphaR : pathF.obj (dE A) (dCL A A) ⟶ dCL A A) ≫ est (pathR wt)))
      (toS x) (memS (row7 wt x)) := by
  have e8 : Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)))
      ≫ powerRel (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) ≫ est (pathR wt)
      = junc (sumCop (dL A) (⟨A × (pow (dCL A A)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt) := by
    rw [pathF_map_id]
    exact cpMap_comp_powerRel_alphaR_comp_est_eq_junc wt
  rw [e8, show row7 wt x = row6 wt x from rfl, row6_eq]
  exact pathAlgExec_le wt x hx

/-- **8.2d row 6, executable** (book p.198, `union·Pτ = id`): `row6`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S est(R))`, which `P = E` on functions equates with row 7. -/
public theorem thinning_paths_alg_unit_exec (wt : A → A → Nat)
    (x : List A ⊕ (List A × List (ConsList A A)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    (Λ (pathF.map (∋ (dE A)) (𝟙 (P (dCL A A))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE A)) (∋ (dCL A A)) ≫ alphaR) ≫ est (pathR wt)))
      (toS x) (memS (row6 wt x)) := by
  have hα : Map (alphaR : pathF.obj (dE A) (dCL A A) ⟶ dCL A A) := graph_map _
  rw [← thinning_paths_alg_map (F := pathF) (A := dE A) hα (pathR wt)]
  exact thinning_paths_alg_map_exec wt x hx

/-- A network all of whose layers are non-empty (book p.196). -/
@[expose] public def LayersNonempty : ConsList (List A) (List A) → Prop
  | .wrap vs => vs ≠ []
  | .cons vs n => vs ≠ [] ∧ LayersNonempty n

/-- 8.2d (book p.196): on a network whose layers are all non-empty the fold finds a path. -/
public theorem pathsExec_ne_nil (wt : A → A → Nat) :
    ∀ net : ConsList (List A) (List A), LayersNonempty net → pathsExec wt net ≠ []
  | .wrap vs, h => by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs h
    exact List.ne_nil_of_mem
      (List.mem_filterMap.mpr ⟨.inl v, List.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩)
  | .cons vs n, ⟨h1, h2⟩ => by
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs h1
    have hps := pathsExec_ne_nil wt n h2
    have hne : (pathsExec wt n).map (ConsList.cons v) ≠ [] := by
      cases hq : pathsExec wt n with
      | nil => exact absurd hq hps
      | cons t ts => exact fun h => nomatch h
    obtain ⟨y, hy⟩ := minPath_isSome wt hne
    exact List.ne_nil_of_mem
      (List.mem_filterMap.mpr ⟨.inr (v, pathsExec wt n), List.mem_map.mpr ⟨v, hv, rfl⟩, hy⟩)

/-- 8.2d (book p.196): on a network whose layers are all non-empty `mcp` returns a path. -/
public theorem mcp_isSome (wt : A → A → Nat) (net : ConsList (List A) (List A))
    (h : LayersNonempty net) : ∃ p, mcp wt net = some p :=
  minPath_isSome wt (pathsExec_ne_nil wt net h)

end Exec

-- 8.2d sanity check (book p.196): on a three-layer network every row program, fed the top
-- layer and the fold of the two below, has the least cost `mcp` finds.
#guard
  let wt : Nat → Nat → Nat := fun a b => (a * 7 + b * 3) % 10 + 1
  let below : RelSet.CL.ConsList (List Nat) (List Nat) := .cons [3, 4, 5] (.wrap [6, 7])
  let x : List Nat ⊕ (List Nat × List (RelSet.CL.ConsList Nat Nat)) :=
    .inr ([1, 2], pathsExec wt below)
  let best (l : List (RelSet.CL.ConsList Nat Nat)) := (minPath wt l).map (costOf wt)
  let c := (mcp wt (.cons [1, 2] below)).map (costOf wt)
  c == best (row1 wt x) && c == best (row2 wt x) && c == best (row3 wt x)
    && c == best (row4 wt x) && c == best (row5 wt x) && c == best (row6 wt x)
    && c == best (row7 wt x) && c == best (pathAlgExec wt x) && c.isSome

-- printing-only: B&dM p.196 writes `minpath`; the weight `wt` is the section's one parameter.
open Lean PrettyPrinter in
@[app_unexpander minpath] public meta def unexpandMinpath : Unexpander
  | `($_ $_) => `($(mkIdent `minpath))
  | `($_ $_ $args*) => `($(mkIdent `minpath) $args*)
  | _ => `($(mkIdent `minpath))

end Freyd.Alg
