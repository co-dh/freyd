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
module

public import AOP.A5_7_PowerBeads
meta import AOP.A8_2

namespace Freyd.Alg
open PowerAllegory

open RelSet RelSet.CL

/-- The initial algebra of 8.2d's fold relator `F(PV,−)`: networks are cons-lists of layers
    (book p.196).  `CL.initial`'s data verbatim; its laws carried over by `pathF_map_id`. -/
@[expose] public def pathInit (V : Type) :
    InitialAlgebra (pathF.appl (P (dE V))) where
  t := dCL (V → Prop) (V → Prop)
  α := alphaR
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f hf := by
    show _ = pathF.map (𝟙 _) _ ≫ f
    rw [pathF_map_id]
    exact (CL.initial (V → Prop) (V → Prop)).cata_comm f hf
  cata_unique f hf h hmap hcomm := by
    change _ = pathF.map (𝟙 _) _ ≫ f at hcomm
    rw [pathF_map_id] at hcomm
    exact (CL.initial (V → Prop) (V → Prop)).cata_unique f hf h hmap hcomm

/-- A fold over `pathInit` is the fold over `CL.initial`: the two differ only in how `F(𝟙,∋)`
    is spelled (8.2d, book p.198). -/
public theorem relCata_pathInit {V : Type} {A : RelSet.{0}}
    (R : (pathF.appl (P (dE V))).obj A ⟶ A) :
    relCata (I := pathInit V) R = relCata (I := CL.initial (V → Prop) (V → Prop)) R := by
  show cataFold (Λ (pathF.map (𝟙 _) (∋ A) ≫ R)) ≫ ∋ A = cataFold (Λ (Fmap _ _ (∋ A) ≫ R)) ≫ ∋ A
  rw [pathF_map_id]
  rfl

section Exec

variable {V : Type}

/-! ## The code -/

/-- A listed layer or set of paths read as a set, by membership. -/
@[expose] public def memS {α : Type} (l : List α) : α → Prop := fun a => a ∈ l

/-- 8.2d `est(R)` at `R ≜ cost≤cost°` (book p.198), executable: one cost-least member of a listed
    set, `none` on the empty one. -/
@[expose] public def minPath (wt : V → V → Nat) : List (ConsList V V) → Option (ConsList V V)
  | [] => none
  | p :: ps => some (ps.foldl (fun m q => if costOf wt q < costOf wt m then q else m) p)

/-- 8.2d `Λ(F(∋,𝟙)) = 𝟙+cpl` (book p.198), executable: take one vertex out of the layer. -/
@[expose] public def cpl : List V ⊕ (List V × List (ConsList V V))
    → List (V ⊕ (V × List (ConsList V V)))
  | .inl vs => vs.map .inl
  | .inr (vs, ps) => vs.map fun v => .inr (v, ps)

/-- 8.2d row 8 `[wrap,step]` (book p.198), executable: `wrap` the vertex, or cons it onto every
    listed tail and keep a cheapest. -/
@[expose] public def wrapStep (wt : V → V → Nat) :
    V ⊕ (V × List (ConsList V V)) → Option (ConsList V V)
  | .inl v => some (.wrap v)
  | .inr (v, ps) => minPath wt (ps.map (.cons v))

/-- 8.2d row 8 `Λ(F(∋,𝟙)) P([wrap,step])` (book p.198), executable: the fold's algebra. -/
@[expose] public def pathAlgExec (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  (cpl x).filterMap (wrapStep wt)

/-- 8.2d the fold `⦇Λ(F(∋,𝟙)) P([wrap,step])⦈` over the layers, top layer first (book p.198). -/
@[expose] public def pathsExec (wt : V → V → Nat) : ConsList (List V) (List V) → List (ConsList V V)
  | .wrap vs => pathAlgExec wt (.inl vs)
  | .cons vs n => pathAlgExec wt (.inr (vs, pathsExec wt n))

/-- 8.2d the program (book p.198): the fold over the layers, then `est(R)` — a least-cost path. -/
@[expose] public def mcp (wt : V → V → Nat) (net : ConsList (List V) (List V)) :
    Option (ConsList V V) :=
  minPath wt (pathsExec wt net)

/-- 8.2d's input read as the relation's: every layer of the network as a set. -/
@[expose] public def netSet : ConsList (List V) (List V) → ConsList (V → Prop) (V → Prop)
  | .wrap vs => .wrap (memS vs)
  | .cons vs n => .cons (memS vs) (netSet n)

/-- 8.2d's algebra input `F(PV,PLV)` read as sets. -/
@[expose] public def toS : List V ⊕ (List V × List (ConsList V V))
    → (pathF.obj (P (dE V)) (P (dCL V V))).carrier
  | .inl vs => .inl (memS vs)
  | .inr (vs, ps) => .inr (memS vs, memS ps)

/-- 8.2d's `[wrap,step]` input `F(V,PLV)` read as sets. -/
@[expose] public def toS1 : V ⊕ (V × List (ConsList V V))
    → (Fobj V V (P (dCL V V))).carrier
  | .inl v => .inl v
  | .inr (v, ps) => .inr (v, memS ps)

/-! ## `est(R)` and the algebra, code against relation -/

/-- 8.2d `est(R)` (book p.198): `minPath` returns a member of its list that costs no more than any
    member. -/
public theorem minPath_spec (wt : V → V → Nat) {l : List (ConsList V V)} {r : ConsList V V}
    (h : minPath wt l = some r) : r ∈ l ∧ ∀ q ∈ l, costOf wt r ≤ costOf wt q := by
  have key : ∀ (ps : List (ConsList V V)) (m : ConsList V V),
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
public theorem minPath_isSome (wt : V → V → Nat) :
    ∀ {l : List (ConsList V V)}, l ≠ [] → ∃ r, minPath wt l = some r
  | [], h => absurd rfl h
  | _ :: _, _ => ⟨_, rfl⟩

/-- **8.2d row 8, executable** (book p.198, `F(𝟙,∋) P(α) est(R) = [wrap,step]`): `wrapStep`'s
    graph is contained in `[wrap,step]`.  Proved on the row's left-hand side, `Λ(F(𝟙,∋)α) est(R)`,
    to which the row's own theorem rewrites `[wrap,step]`. -/
public theorem cpMap_comp_powerRel_alphaR_comp_est_eq_junc_exec (wt : V → V → Nat)
    (z : V ⊕ (V × List (ConsList V V))) (p : ConsList V V) (h : wrapStep wt z = some p) :
    junc (sumCop (dL V) (⟨V × (pow (dCL V V)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt)
      (toS1 z) p := by
  rw [← cpMap_comp_powerRel_alphaR_comp_est_eq_junc wt]
  have hL : cpMap (CL.F V V) (dCL V V)
      ≫ powerRel (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) = Λ (pathSplit (V := V)) := by
    have hα : Map (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) := graph_map _
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
@[expose] public def pathAlgRel (wt : V → V → Nat) :
    pathF.obj (P (dE V)) (P (dCL V V))
      ⟶ P (dCL V V) :=
  Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))))
    ≫ powerRel (junc (sumCop (dL V) (⟨V × (pow (dCL V V)).carrier⟩ : RelSet.{0}))
      wrapR (pathStep wt))

/-- **8.2d row 8, the fold's algebra executable** (book p.198): `pathAlgExec`'s graph is contained
    in `Λ(F(∋,𝟙)) P([wrap,step])`, provided a non-leaf input carries at least one path — on an
    empty set of tails `step` has no value, so `P` relates nothing. -/
public theorem pathAlgExec_le (wt : V → V → Nat) (x : List V ⊕ (List V × List (ConsList V V)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    pathAlgRel wt (toS x) (memS (pathAlgExec wt x)) := by
  simp only [pathAlgRel]
  rw [Λ_eq_classifier]
  refine ⟨fun z => pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))) (toS x) z, rfl,
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
public theorem pathsExec_rel (wt : V → V → Nat) :
    ∀ net : ConsList (List V) (List V),
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
    (pathF.map (∋ (dE V)) (𝟙 (dCL V V)) ≫ alphaR
      : pathF.obj (P (dE V)) (dCL V V) ⟶ dCL V V) = pathAlg (V := V) := by
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

/-- **8.2d end to end** (book p.198): whatever `mcp` returns is related to the network by the
    specification `Λ(relCata(pathAlg)) est(R)` — a path of the network that costs no more than
    any other.  The code's algebra sits in row 8, rows 8 → 7 → 6 are the chain's equalities
    (`cpMap_comp_powerRel_alphaR_comp_est_eq_junc`, `thinning_paths_alg_map`), and
    `thinning_paths` (which runs `thinning_paths_alg`) takes the fold into the specification. -/
public theorem mcp_spec (wt : V → V → Nat) (net : ConsList (List V) (List V)) (p : ConsList V V)
    (h : mcp wt net = some p) :
    (Λ (relCata (I := CL.initial (V → Prop) (V → Prop)) (pathAlg (V := V))) ≫ est (pathR wt))
      (netSet net) p := by
  have hQR : pathQ wt ⊑ pathR wt := le_iff.mpr fun _ _ h => h.1
  have hreflQ : 𝟙 (dCL V V) ⊑ pathQ wt :=
    le_iff.mpr fun p q (h : p = q) => by subst h; exact (pathQ_apply wt p p).mpr ⟨Nat.le_refl _, rfl⟩
  have htransQ : pathQ wt ≫ pathQ wt ⊑ pathQ wt :=
    le_iff.mpr fun _ _ ⟨_, h1, h2⟩ =>
      have h1 := (pathQ_apply wt _ _).mp h1; have h2 := (pathQ_apply wt _ _).mp h2
      (pathQ_apply wt _ _).mpr ⟨Nat.le_trans h1.1 h2.1, h1.2.trans h2.2⟩
  have htransR : (pathR wt)° ≫ (pathR wt)° ⊑ (pathR wt)° :=
    le_iff.mpr fun _ _ ⟨_, h1, h2⟩ =>
      (pathR_apply wt _ _).mpr (Nat.le_trans ((pathR_apply wt _ _).mp h2) ((pathR_apply wt _ _).mp h1))
  have hmono : Freyd.Alg.MonoAlg
      ((pathF.map (∋ (dE V)) (𝟙 (dCL V V)) ≫ alphaR
        : (pathF.appl (P (dE V))).obj (dCL V V) ⟶ dCL V V)) (pathQ wt) := by
    show pathF.map (𝟙 _) (pathQ wt) ≫ _ ⊑ _
    rw [pathF_map_id, pathF_map_comp_alphaR_eq_pathAlg]
    exact pathAlg_monotonic wt
  have hQ : pathR wt ∩ ((pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR)°
      ≫ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR)) ⊑ pathQ wt := by
    rw [pathF_map_id]
    have := pathR_inter_recip_le_pathQ (V := V) wt
    rw [pathSplit_eq_Fmap_comp_alphaR] at this
    exact this
  have hthin := thinning_paths (F := pathF) (A := dE V) (B := dCL V V) (pathInit V)
    (α := alphaR) hQR hreflQ htransQ htransR hmono hQ
  have hα : Map (alphaR : pathF.obj (dE V) (dCL V V) ⟶ dCL V V) := graph_map _
  rw [← thinning_paths_alg_map (F := pathF) (A := dE V) hα (pathR wt)] at hthin
  have e8 : Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)))
      ≫ powerRel (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) ≫ est (pathR wt)
      = junc (sumCop (dL V) (⟨V × (pow (dCL V V)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt) := by
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
@[expose] public def minpath (wt : V → V → Nat) : dCL (V → Prop) (V → Prop) ⟶ dCL V V :=
  fun x p => ∃ net, x = netSet net ∧ mcp wt net = some p

/-- The problem (B&dM p.196: `minpath ⊑ min R · Λ(list⁺ ∈)`), in diagram order: whatever
    `minpath` returns is a cheapest path through the layers, `minpath ⊑ Λ(L(∋)) est(R)`. -/
public theorem minpath_spec (wt : V → V → Nat) :
    minpath wt ⊑ Λ (relCata (I := pathInit V)
      (pathF.map (∋ (dE V)) (𝟙 (dCL V V)) ≫ alphaR)) ≫ est (pathR wt) :=
  le_iff.mpr fun _ p ⟨net, hx, h⟩ => by
    subst hx
    rw [relCata_pathInit, pathF_map_comp_alphaR_eq_pathAlg]
    exact mcp_spec wt net p h

/-- 8.2d end to end, pointwise (book p.196's problem): `mcp`'s answer is a path of the network
    and no path of the network is cheaper. -/
public theorem mcp_least (wt : V → V → Nat) (net : ConsList (List V) (List V)) (p : ConsList V V)
    (h : mcp wt net = some p) :
    relCata (I := CL.initial (V → Prop) (V → Prop)) (pathAlg (V := V)) (netSet net) p
      ∧ ∀ q, relCata (I := CL.initial (V → Prop) (V → Prop)) (pathAlg (V := V)) (netSet net) q
        → costOf wt p ≤ costOf wt q :=
  have ⟨h1, h2⟩ := (Λ_comp_est_apply _ _ _ _).mp (mcp_spec wt net p h)
  ⟨h1, fun q hq => (pathR_apply wt p q).mp (h2 q hq)⟩

/-! ## Rows 1–7 of 8.2d, each with its program

  Every row is the relation of its A8_2 step theorem at `pathF`, `A := dE V`, `B := dCL V V`,
  `α := alphaR`, `Q := pathQ wt`, `R := pathR wt`; the program `rowᵢ` is the draft's `lᵢ`, and
  its lemma says `rowᵢ`'s output, read as a set, is related to the input read as sets. -/

/-- 8.2d `Λ(F(𝟙,∋)) = 𝟙+cpr` (book p.198), executable: take one path out of the listed set. -/
@[expose] public def cpr : V ⊕ (V × List (ConsList V V)) → List (V ⊕ (V × ConsList V V))
  | .inl v => [.inl v]
  | .inr (v, ps) => ps.map fun p => .inr (v, p)

/-- 8.2d `Λ(S)`, `S ≜ F(𝟙,∋)α` (book p.198), executable: every path `α` builds from one vertex
    and one listed tail. -/
@[expose] public def sExec (z : V ⊕ (V × List (ConsList V V))) : List (ConsList V V) :=
  (cpr z).map (con (L := V) (E := V))

/-- 8.2d `Q ≜ R∩(head head°)` (book p.197), decided. -/
@[expose] public def qExec [DecidableEq V] (wt : V → V → Nat) (x y : ConsList V V) : Bool :=
  decide (costOf wt x ≤ costOf wt y ∧ headOf x = headOf y)

/-- 8.2d `thin(Q)` (book (8.1)), executable: keep `x` unless a kept path `Q`-beats it, and drop
    the kept paths `x` beats. -/
@[expose] public def thinExec [DecidableEq V] (wt : V → V → Nat) (xs : List (ConsList V V)) :
    List (ConsList V V) :=
  xs.foldr (fun x ys => if ys.any (qExec wt · x) then ys else x :: ys.filter (!qExec wt x ·)) []

/-- 8.2d `thin(Q)` (book (8.1)): `thinExec` keeps a sublist that has a `Q`-lower bound for every
    member of its input. -/
public theorem thinExec_spec [DecidableEq V] (wt : V → V → Nat) (xs : List (ConsList V V)) :
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
public theorem thinExec_le [DecidableEq V] (wt : V → V → Nat) (xs : List (ConsList V V))
    (P : (pow (dCL V V)).carrier) (hP : ∀ p, P p ↔ p ∈ xs) :
    thinRel (pathQ wt) P (memS (thinExec wt xs)) := by
  obtain ⟨hs, hc⟩ := thinExec_spec wt xs
  exact (thinRel_pt _ _ _).mpr ⟨fun y hy => (hP y).mpr (hs y hy),
    fun z hz => (hc z ((hP z).mp hz)).imp fun _ h => ⟨h.2, h.1⟩⟩

/-- 8.2d `Λ(F(∋,𝟙))` (book p.198): the vertices taken out of the layer are what `cpl` lists. -/
public theorem cpl_char (x : List V ⊕ (List V × List (ConsList V V)))
    (w : (pathF.obj (dE V) (P (dCL V V))).carrier) :
    pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))) (toS x) w
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
public theorem sExec_char (z : V ⊕ (V × List (ConsList V V))) (p : ConsList V V) :
    (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) (toS1 z) p ↔ p ∈ sExec z := by
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
public theorem minPath_sExec (wt : V → V → Nat) (z : V ⊕ (V × List (ConsList V V))) :
    minPath wt (sExec z) = wrapStep wt z := by
  cases z with
  | inl v => rfl
  | inr q =>
    obtain ⟨v, ps⟩ := q
    simp only [sExec, cpr, wrapStep, List.map_map]
    rfl

/-- 8.2d row 3 `Λ(F(∋,𝟙)) P(Λ S) union thin(Q)` (book p.198), executable. -/
@[expose] public def row3 [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  thinExec wt ((cpl x).map sExec).flatten

/-- 8.2d row 2 `Λ(F(∋,𝟙) F(𝟙,∋) α) thin(Q)` (book p.198), executable. -/
@[expose] public def row2 [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  thinExec wt ((cpl x).flatMap fun z => (cpr z).map (con (L := V) (E := V)))

/-- 8.2d row 1 `Λ(F(∋,∋) α) thin(Q)` (book p.198), executable. -/
@[expose] public def row1 [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  thinExec wt (((cpl x).flatMap cpr).map (con (L := V) (E := V)))

/-- **8.2d row 3, executable** (book p.198): `row3`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S) union thin(Q)`. -/
public theorem thinning_paths_alg_transpose_exec [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) :
    (Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR))
        ≫ bigUnion ≫ thinRel (pathQ wt)) (toS x) (memS (row3 wt x)) := by
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
public theorem thinning_paths_alg_bifunctors_exec [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) :
    (Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V)))
        ≫ pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ thinRel (pathQ wt))
      (toS x) (memS (row2 wt x)) := by
  rw [← thinning_paths_alg.step_7]
  exact thinning_paths_alg_transpose_exec wt x

/-- **8.2d row 1, executable** (book p.198): `row1`'s graph is contained in `Λ(F(∋,∋) α) thin(Q)`,
    which bifunctoriality equates with row 2. -/
public theorem thinning_paths_alg_exec [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) :
    (Λ (pathF.map (∋ (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ thinRel (pathQ wt))
      (toS x) (memS (row1 wt x)) := by
  rw [← thinning_paths_alg.step_8]
  have e : row1 wt x = row2 wt x := by simp only [row1, row2, List.map_flatMap]
  rw [e]
  exact thinning_paths_alg_bifunctors_exec wt x

/-- 8.2d row 4 `Λ(F(∋,𝟙)) P(Λ S thin(Q)) union` (book p.198), executable. -/
@[expose] public def row4 [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  ((cpl x).map fun z => thinExec wt (sExec z)).flatten

/-- **8.2d row 4, executable** (book p.198, the `(8.4)` step): `row4`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S thin(Q)) union`. -/
public theorem thinning_paths_alg_distrib_exec [DecidableEq V] (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) :
    (Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ thinRel (pathQ wt))
        ≫ bigUnion) (toS x) (memS (row4 wt x)) := by
  have hz : ∀ z, (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ thinRel (pathQ wt))
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
@[expose] public def row5 (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  ((cpl x).map fun z => (minPath wt (sExec z)).toList).flatten

/-- **8.2d row 5, executable** (book p.198, the `(8.3)` step): `row5`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S est(R) τ) union`, when a non-leaf input carries a path. -/
public theorem thinning_paths_alg_elim_exec (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    (Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ est (pathR wt)
          ≫ singletonMap) ≫ bigUnion) (toS x) (memS (row5 wt x)) := by
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
      (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ est (pathR wt) ≫ singletonMap)
        (toS1 z) (memS (minPath wt (sExec z)).toList) := by
    intro z p hp
    obtain ⟨hm, hle⟩ := minPath_spec wt hp
    have hest : (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ est (pathR wt)) (toS1 z) p :=
      (Λ_comp_est_apply _ _ _ _).mpr ⟨(sExec_char z p).mpr hm,
        fun q hq => (pathR_apply wt p q).mpr (hle q ((sExec_char z q).mp hq))⟩
    obtain ⟨P, hP, hPp⟩ := hest
    refine ⟨P, hP, p, hPp, ?_⟩
    show Λ (𝟙 (dCL V V)) p _
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
@[expose] public def row6 (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  (cpl x).filterMap fun z => minPath wt (sExec z)

/-- 8.2d row 7 `Λ(F(∋,𝟙)) P(Λ(F(𝟙,∋)) P(α) est(R))` (book p.198), executable. -/
@[expose] public def row7 (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V))) : List (ConsList V V) :=
  (cpl x).filterMap fun z => minPath wt ((cpr z).map (con (L := V) (E := V)))

/-- 8.2d rows 6 and 7 run `pathAlgExec` (book p.198): `P = E` on functions changes the relation,
    not the program. -/
public theorem row6_eq (wt : V → V → Nat) (x : List V ⊕ (List V × List (ConsList V V))) :
    row6 wt x = pathAlgExec wt x := by
  simp only [row6, pathAlgExec, minPath_sExec]

/-- **8.2d row 7, executable** (book p.198, `P = E` on functions): `row7`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ(F(𝟙,∋)) P(α) est(R))`, which row 8 equates with `Λ(F(∋,𝟙)) P([wrap,step])`. -/
public theorem thinning_paths_alg_map_exec (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    (Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)))
          ≫ powerRel (alphaR : pathF.obj (dE V) (dCL V V) ⟶ dCL V V) ≫ est (pathR wt)))
      (toS x) (memS (row7 wt x)) := by
  have e8 : Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)))
      ≫ powerRel (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) ≫ est (pathR wt)
      = junc (sumCop (dL V) (⟨V × (pow (dCL V V)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt) := by
    rw [pathF_map_id]
    exact cpMap_comp_powerRel_alphaR_comp_est_eq_junc wt
  rw [e8, show row7 wt x = row6 wt x from rfl, row6_eq]
  exact pathAlgExec_le wt x hx

/-- **8.2d row 6, executable** (book p.198, `union·Pτ = id`): `row6`'s graph is contained in
    `Λ(F(∋,𝟙)) P(Λ S est(R))`, which `P = E` on functions equates with row 7. -/
public theorem thinning_paths_alg_unit_exec (wt : V → V → Nat)
    (x : List V ⊕ (List V × List (ConsList V V)))
    (hx : ∀ vs ps, x = .inr (vs, ps) → ps ≠ []) :
    (Λ (pathF.map (∋ (dE V)) (𝟙 (P (dCL V V))))
        ≫ powerRel (Λ (pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR) ≫ est (pathR wt)))
      (toS x) (memS (row6 wt x)) := by
  have hα : Map (alphaR : pathF.obj (dE V) (dCL V V) ⟶ dCL V V) := graph_map _
  rw [← thinning_paths_alg_map (F := pathF) (A := dE V) hα (pathR wt)]
  exact thinning_paths_alg_map_exec wt x hx

/-- A network all of whose layers are non-empty (book p.196). -/
@[expose] public def LayersNonempty : ConsList (List V) (List V) → Prop
  | .wrap vs => vs ≠ []
  | .cons vs n => vs ≠ [] ∧ LayersNonempty n

/-- 8.2d (book p.196): on a network whose layers are all non-empty the fold finds a path. -/
public theorem pathsExec_ne_nil (wt : V → V → Nat) :
    ∀ net : ConsList (List V) (List V), LayersNonempty net → pathsExec wt net ≠ []
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
public theorem mcp_isSome (wt : V → V → Nat) (net : ConsList (List V) (List V))
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

end Freyd.Alg
