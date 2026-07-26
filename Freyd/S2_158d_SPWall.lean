/-
  Freyd & Scedrov, *Categories and Allegories* §2.158, Target 3 — ingredient
  (a) SP-WALL of `RhombusHard entL entR` (see the OPEN note at the end of
  `Freyd/S2_158b_NoFiniteAxiom.lean`).

  M1 (subgraph lemma, Freyd's "one may show", receives-half): a connected
  marked graph with an enumerated edge/vertex set receives a mark-preserving
  SURJECTIVE (on vertices and edges) map from a term graph.  The term is the
  big meet, over all edges and vertices, of walk terms `(s⇝u)·A·(s⇝v)⁻¹·(s⇝t)`
  — every factor of the meet lands on the mark pair, so the factors glue.

  M2 (SP characterization): term graphs are exactly the graphs built by the
  five `toGraph` constructors (`one`, `arrow`, series `gcomp`, parallel
  `meet`, mark-swap `recip`); mark-MERGE (`1 ∩ X` gluing `s = t`) is the
  parallel constructor with `one` as a factor, so it needs no constructor of
  its own.

  M3/M4: the kernel dichotomy (a).  The continuation `c : [F] → [entL n]`
  types every vertex of a chain-stage graph, which pins the composite
  `[entR n] → [entL n]` to THE designated collapse (extending `rigidity` from
  the designated midpoints to the corners); hence the kernel of a stage map
  can only merge top midpoints with top midpoints, bottom midpoints with
  bottom midpoints, and the two marks.  The remaining combinatorial wall —
  a merged top (or bottom) pair forces the FULL collapse — is stated against
  the SP class of M2; see the OPEN note at the end.

  STRICTLY MATHLIB-FREE.  Only Lean 4 core + `Freyd.*`.
-/

import Freyd.S2_158c_StepRigidity

namespace Freyd.S2_158

variable {L : Type}

/-! ## M1 — walks and walk terms

  A walk may traverse edges forwards or backwards; reciprocation makes both
  directions term-expressible, so every walk `u ⇝ v` yields a term whose
  graph is the walk's path, mapping into the ambient graph with the marks on
  `u` and `v`. -/

/-- An undirected labelled walk from `u` to `v` in `H`: traverse each edge
    forwards (`fwd`) or backwards (`bwd`). -/
inductive WalkE (H : LGraph L) : H.V → H.V → Type where
  | nil (v : H.V) : WalkE H v v
  | fwd {u v w : H.V} {A : L} (e : H.edge u v A) (rest : WalkE H v w) :
      WalkE H u w
  | bwd {u v w : H.V} {A : L} (e : H.edge v u A) (rest : WalkE H v w) :
      WalkE H u w

/-- Append two walks. -/
def WalkE.append {H : LGraph L} : ∀ {u v w : H.V},
    WalkE H u v → WalkE H v w → WalkE H u w
  | _, _, _, .nil _, q => q
  | _, _, _, .fwd e p, q => .fwd e (p.append q)
  | _, _, _, .bwd e p, q => .bwd e (p.append q)

/-- Reverse a walk. -/
def WalkE.rev {H : LGraph L} : ∀ {u v : H.V}, WalkE H u v → WalkE H v u
  | _, _, .nil v => .nil v
  | _, _, .fwd e p => p.rev.append (.bwd e (.nil _))
  | _, _, .bwd e p => p.rev.append (.fwd e (.nil _))

/-- The term of a walk: one composition factor per traversed edge, a `°` on
    the backward ones. -/
def walkTerm {H : LGraph L} : ∀ {u v : H.V}, WalkE H u v → Term L
  | _, _, .nil _ => .one
  | _, _, .fwd (A := A) _ rest => .comp (.var A) (walkTerm rest)
  | _, _, .bwd (A := A) _ rest => .comp (.recip (.var A)) (walkTerm rest)

/-- **Walk realisation.**  The graph of a walk term maps into the ambient
    graph, marks going to the walk's endpoints.  (`fwd`: the fresh `arrow`
    factor maps onto the traversed edge; `bwd`: onto it with `s`/`t` swapped,
    matching the `°`; the gluing point of the composition is the shared
    intermediate vertex.) -/
theorem walk_ehom {H : LGraph L} : ∀ {u v : H.V} (p : WalkE H u v),
    ∃ f : EHom (toGraph (walkTerm p)) H,
      f.onV (toGraph (walkTerm p)).s = u ∧ f.onV (toGraph (walkTerm p)).t = v := by
  intro u v p
  induction p with
  | nil w => exact ⟨⟨fun _ => w, fun h => h.elim⟩, rfl, rfl⟩
  | fwd e rest ih =>
    rename_i x y z A
    obtain ⟨f, hfs, hft⟩ := ih
    refine ⟨gluedOut (H := H) ⟨fun b => cond b y x, ?_⟩ f ?_, rfl, hft⟩
    · intro a b B hab
      obtain ⟨rfl, rfl, rfl⟩ := hab
      exact e
    · intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => obtain ⟨rfl, rfl⟩ := h; exact hfs.symm
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim
  | bwd e rest ih =>
    rename_i x y z A
    obtain ⟨f, hfs, hft⟩ := ih
    refine ⟨gluedOut (H := H) ⟨fun b => cond b x y, ?_⟩ f ?_, rfl, hft⟩
    · intro a b B hab
      obtain ⟨rfl, rfl, rfl⟩ := hab
      exact e
    · intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => obtain ⟨rfl, rfl⟩ := h; exact hfs.symm
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim

/-- Universal property of the series gluing, with the two embedding
    equations recorded (they carry image-coverage through the assembly):
    maps out of the factors that agree at the joint glue to a map out of
    `gcomp`, restricting to the factor maps on the embedded copies. -/
theorem gcomp_ehom {G₁ G₂ H : LGraph L} {x y z : H.V}
    (f₁ : EHom G₁ H) (h₁s : f₁.onV G₁.s = x) (h₁t : f₁.onV G₁.t = y)
    (f₂ : EHom G₂ H) (h₂s : f₂.onV G₂.s = y) (h₂t : f₂.onV G₂.t = z) :
    ∃ f : EHom (gcomp G₁ G₂) H,
      f.onV (gcomp G₁ G₂).s = x ∧ f.onV (gcomp G₁ G₂).t = z ∧
      (∀ a, f.onV (Quot.mk _ (Sum.inl a)) = f₁.onV a) ∧
      (∀ b, f.onV (Quot.mk _ (Sum.inr b)) = f₂.onV b) := by
  refine ⟨gluedOut f₁ f₂ ?_, h₁s, h₂t, fun a => rfl, fun b => rfl⟩
  intro p q h
  cases p with
  | inl a => cases q with
    | inl b => exact h.elim
    | inr b => obtain ⟨rfl, rfl⟩ := h; exact h₁t.trans h₂s.symm
  | inr a => cases q with
    | inl b => exact h.elim
    | inr b => exact h.elim

/-- Universal property of the parallel gluing (marks to marks), with the two
    embedding equations recorded. -/
theorem meet_ehom {G₁ G₂ H : LGraph L} {x y : H.V}
    (f₁ : EHom G₁ H) (h₁s : f₁.onV G₁.s = x) (h₁t : f₁.onV G₁.t = y)
    (f₂ : EHom G₂ H) (h₂s : f₂.onV G₂.s = x) (h₂t : f₂.onV G₂.t = y) :
    ∃ f : EHom (meet G₁ G₂) H,
      f.onV (meet G₁ G₂).s = x ∧ f.onV (meet G₁ G₂).t = y ∧
      (∀ a, f.onV (Quot.mk _ (Sum.inl a)) = f₁.onV a) ∧
      (∀ b, f.onV (Quot.mk _ (Sum.inr b)) = f₂.onV b) := by
  refine ⟨gluedOut f₁ f₂ ?_, h₁s, h₁t, fun a => rfl, fun b => rfl⟩
  intro p q h
  cases p with
  | inl a => cases q with
    | inl b => exact h.elim
    | inr b =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h₁s.trans h₂s.symm
      · exact h₁t.trans h₂t.symm
  | inr a => cases q with
    | inl b => exact h.elim
    | inr b => exact h.elim

/-- A `G₁`-edge survives into any gluing (converse of `glued_edge_elim`). -/
theorem glued_edge_inl {G₁ G₂ : LGraph L}
    {r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop} {sv tv : G₁.V ⊕ G₂.V}
    {a b : G₁.V} {A : L} (h : G₁.edge a b A) :
    (glued G₁ G₂ r sv tv).edge (Quot.mk r (Sum.inl a)) (Quot.mk r (Sum.inl b)) A :=
  ⟨Sum.inl a, Sum.inl b, rfl, rfl, h⟩

/-- A `G₂`-edge survives into any gluing. -/
theorem glued_edge_inr {G₁ G₂ : LGraph L}
    {r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop} {sv tv : G₁.V ⊕ G₂.V}
    {a b : G₂.V} {A : L} (h : G₂.edge a b A) :
    (glued G₁ G₂ r sv tv).edge (Quot.mk r (Sum.inr a)) (Quot.mk r (Sum.inr b)) A :=
  ⟨Sum.inr a, Sum.inr b, rfl, rfl, h⟩

/-- **Edge factor.**  In a connected graph, every edge `u --A→ v` is covered
    by a term mapping in with the marks on the marks: walk out to `u`,
    traverse the edge, walk back from `v`, then out to `t` —
    `(s⇝u)·A·(v⇝s)·(s⇝t)`. -/
theorem edge_factor {H : LGraph L} (hconn : ∀ v : H.V, Nonempty (WalkE H H.s v))
    {u v : H.V} {A : L} (e : H.edge u v A) :
    ∃ (T : Term L) (f : EHom (toGraph T) H),
      f.onV (toGraph T).s = H.s ∧ f.onV (toGraph T).t = H.t ∧
      ∃ x y, (toGraph T).edge x y A ∧ f.onV x = u ∧ f.onV y = v := by
  obtain ⟨wu⟩ := hconn u
  obtain ⟨wv⟩ := hconn v
  obtain ⟨wt⟩ := hconn H.t
  obtain ⟨fu, hus, hut⟩ := walk_ehom wu
  obtain ⟨fvr, hvs, hvt⟩ := walk_ehom wv.rev
  obtain ⟨ft, hts, htt⟩ := walk_ehom wt
  obtain ⟨g₁, h1s, h1t, -, -⟩ := gcomp_ehom fvr hvs hvt ft hts htt
  obtain ⟨g₂, h2s, h2t, h2l, -⟩ :=
    gcomp_ehom (H := H) (x := u) (y := v)
      (⟨fun b => cond b v u, fun {a b B} hab => by
        obtain ⟨rfl, rfl, rfl⟩ := hab; exact e⟩ : EHom (arrow A) H)
      rfl rfl g₁ h1s h1t
  obtain ⟨g₃, h3s, h3t, -, h3r⟩ := gcomp_ehom fu hus hut g₂ h2s h2t
  refine ⟨.comp (walkTerm wu)
      (.comp (.var A) (.comp (walkTerm wv.rev) (walkTerm wt))), g₃, h3s, h3t,
    Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inl false))),
    Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inl true))),
    glued_edge_inr (glued_edge_inl (arrow_edge A)), ?_, ?_⟩
  · exact (h3r _).trans (h2l false)
  · exact (h3r _).trans (h2l true)

/-- **Vertex factor.**  In a connected graph, every vertex is covered by a
    term mapping in with the marks on the marks: `(s⇝v)·(v⇝s)·(s⇝t)`. -/
theorem vertex_factor {H : LGraph L} (hconn : ∀ v : H.V, Nonempty (WalkE H H.s v))
    (v : H.V) :
    ∃ (T : Term L) (f : EHom (toGraph T) H),
      f.onV (toGraph T).s = H.s ∧ f.onV (toGraph T).t = H.t ∧
      ∃ x, f.onV x = v := by
  obtain ⟨wv⟩ := hconn v
  obtain ⟨wt⟩ := hconn H.t
  obtain ⟨fv, hvs, hvt⟩ := walk_ehom wv
  obtain ⟨fvr, hrs, hrt⟩ := walk_ehom wv.rev
  obtain ⟨ft, hts, htt⟩ := walk_ehom wt
  obtain ⟨g₁, h1s, h1t, -, -⟩ := gcomp_ehom fvr hrs hrt ft hts htt
  obtain ⟨g₂, h2s, h2t, -, h2r⟩ := gcomp_ehom fv hvs hvt g₁ h1s h1t
  exact ⟨.comp (walkTerm wv) (.comp (walkTerm wv.rev) (walkTerm wt)), g₂,
    h2s, h2t, Quot.mk _ (Sum.inr (toGraph (.comp (walkTerm wv.rev) (walkTerm wt))).s),
    (h2r _).trans h1s⟩

/-- A coverage requirement on a map into `H`: hit a given vertex (`inl`), or
    cover a given labelled edge (`inr`). -/
def Meets {G H : LGraph L} (f : EHom G H) : H.V ⊕ H.V × H.V × L → Prop
  | .inl v => ∃ x, f.onV x = v
  | .inr (u, v, A) => ∃ x y, G.edge x y A ∧ f.onV x = u ∧ f.onV y = v

/-- Coverage transfers along the left embedding into any gluing. -/
theorem Meets.glued_inl {G₁ G₂ H : LGraph L}
    {r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop} {sv tv : G₁.V ⊕ G₂.V}
    {f₁ : EHom G₁ H} {g : EHom (glued G₁ G₂ r sv tv) H}
    (hg : ∀ a, g.onV (Quot.mk r (Sum.inl a)) = f₁.onV a)
    {req : H.V ⊕ H.V × H.V × L} (h : Meets f₁ req) : Meets g req := by
  match req, h with
  | .inl v, ⟨x, hx⟩ => exact ⟨Quot.mk r (Sum.inl x), (hg x).trans hx⟩
  | .inr (u, v, A), ⟨x, y, he, hx, hy⟩ =>
    exact ⟨Quot.mk r (Sum.inl x), Quot.mk r (Sum.inl y), glued_edge_inl he,
      (hg x).trans hx, (hg y).trans hy⟩

/-- Coverage transfers along the right embedding into any gluing. -/
theorem Meets.glued_inr {G₁ G₂ H : LGraph L}
    {r : (G₁.V ⊕ G₂.V) → (G₁.V ⊕ G₂.V) → Prop} {sv tv : G₁.V ⊕ G₂.V}
    {f₂ : EHom G₂ H} {g : EHom (glued G₁ G₂ r sv tv) H}
    (hg : ∀ b, g.onV (Quot.mk r (Sum.inr b)) = f₂.onV b)
    {req : H.V ⊕ H.V × H.V × L} (h : Meets f₂ req) : Meets g req := by
  match req, h with
  | .inl v, ⟨x, hx⟩ => exact ⟨Quot.mk r (Sum.inr x), (hg x).trans hx⟩
  | .inr (u, v, A), ⟨x, y, he, hx, hy⟩ =>
    exact ⟨Quot.mk r (Sum.inr x), Quot.mk r (Sum.inr y), glued_edge_inr he,
      (hg x).trans hx, (hg y).trans hy⟩

/-- **Meet fold.**  In a connected graph, any finite list of coverage
    requirements (whose edge requirements are genuine edges) is met by a
    single term mapping in with the marks on the marks: the meet of the
    factors, glued by `meet_ehom` since every factor lands on `(s, t)`. -/
theorem factors_fold {H : LGraph L} (hconn : ∀ v : H.V, Nonempty (WalkE H H.s v)) :
    ∀ reqs : List (H.V ⊕ H.V × H.V × L),
      (∀ u v A, .inr (u, v, A) ∈ reqs → H.edge u v A) →
      ∃ (T : Term L) (f : EHom (toGraph T) H),
        f.onV (toGraph T).s = H.s ∧ f.onV (toGraph T).t = H.t ∧
        ∀ r ∈ reqs, Meets f r := by
  intro reqs
  induction reqs with
  | nil =>
    intro _
    obtain ⟨wt⟩ := hconn H.t
    obtain ⟨ft, hts, htt⟩ := walk_ehom wt
    exact ⟨walkTerm wt, ft, hts, htt, fun r hr => nomatch hr⟩
  | cons r rest ih =>
    intro hsound
    obtain ⟨T₂, f₂, h2s, h2t, hrest⟩ :=
      ih (fun u v A h => hsound u v A (List.mem_cons_of_mem _ h))
    have hfac : ∃ (T₁ : Term L) (f₁ : EHom (toGraph T₁) H),
        f₁.onV (toGraph T₁).s = H.s ∧ f₁.onV (toGraph T₁).t = H.t ∧
        Meets f₁ r := by
      match r with
      | .inl v =>
        obtain ⟨T₁, f₁, h1s, h1t, x, hx⟩ := vertex_factor hconn v
        exact ⟨T₁, f₁, h1s, h1t, x, hx⟩
      | .inr (u, v, A) =>
        obtain ⟨T₁, f₁, h1s, h1t, x, y, he, hx, hy⟩ :=
          edge_factor hconn (hsound u v A (List.mem_cons_self ..))
        exact ⟨T₁, f₁, h1s, h1t, x, y, he, hx, hy⟩
    obtain ⟨T₁, f₁, h1s, h1t, hr⟩ := hfac
    obtain ⟨g, hgs, hgt, hgl, hgr⟩ := meet_ehom f₁ h1s h1t f₂ h2s h2t
    refine ⟨.meet T₁ T₂, g, hgs, hgt, ?_⟩
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact Meets.glued_inl hgl hr
    · exact Meets.glued_inr hgr (hrest r' hr')

/-- **M1, the subgraph lemma (Freyd's "one may show", receives-half).**
    Every connected marked graph with enumerable vertices and edges receives
    a mark-preserving map from a term graph that is SURJECTIVE on vertices
    and covers every labelled edge — `H` is a full quotient of a `Ḡ`-graph.
    In `Ĝ`-order terms the mark-preserving map says `Gle H [T]`, i.e.
    `H ≤ T` in `Ĝ` (`graph_yoneda`); surjectivity is what the kernel analysis
    of the SP wall consumes.  Instantiated to a connected marked subgraph of
    a term graph (the image of a chain stage map), this is exactly the
    "connected subgraph containing both marks is in `Ḡ`" receives-half. -/
theorem connected_receives_term (H : LGraph L)
    (hconn : ∀ v : H.V, Nonempty (WalkE H H.s v))
    (vlist : List H.V) (hvc : ∀ v : H.V, v ∈ vlist)
    (elist : List (H.V × H.V × L))
    (hes : ∀ p ∈ elist, H.edge p.1 p.2.1 p.2.2)
    (hec : ∀ {u v : H.V} {A : L}, H.edge u v A → (u, v, A) ∈ elist) :
    ∃ (T : Term L) (f : Hom (toGraph T) H),
      (∀ v : H.V, ∃ x, f.toEHom.onV x = v) ∧
      (∀ u v A, H.edge u v A →
        ∃ x y, (toGraph T).edge x y A ∧
          f.toEHom.onV x = u ∧ f.toEHom.onV y = v) := by
  obtain ⟨T, f, hs, ht, hmeets⟩ := factors_fold hconn
    (vlist.map Sum.inl ++ elist.map Sum.inr)
    (by
      intro u v A h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨a, -, heq⟩ := List.mem_map.mp h
        exact nomatch heq
      · obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
        obtain rfl : p = (u, v, A) := Sum.inr.inj heq
        exact hes _ hp)
  refine ⟨T, ⟨f, hs, ht⟩, fun v => ?_, fun u v A he => ?_⟩
  · exact hmeets (.inl v)
      (List.mem_append.mpr (Or.inl (List.mem_map_of_mem (hvc v))))
  · exact hmeets (.inr (u, v, A))
      (List.mem_append.mpr (Or.inr (List.mem_map_of_mem (hec he))))

/-! ## M2 — the SP-with-mark-merge class

  Term graphs are exactly the marked graphs generated by five constructors:
  the point (`one`), the single edge (`arrow`), series composition (`gcomp`,
  glue `t₁ = s₂`), parallel composition (`meet`, glue BOTH mark pairs), and
  the mark swap (`recip`).  This is NOT the plain series-parallel class: the
  parallel constructor with the point as one factor — the graph of `1 ∩ X` —
  IDENTIFIES the two marks (`s = t`), so no separate "mark-merge" constructor
  is needed, but the class is strictly larger than 2-terminal SP: blobs with
  merged marks can be strung along compositions. -/

/-- The SP-with-mark-merge class: the closure of the point and the single
    edge under series, parallel (mark-gluing), and mark swap — precisely the
    images of `toGraph`. -/
inductive SP : LGraph L → Prop where
  | one : SP one
  | arrow (A : L) : SP (arrow A)
  | series {G₁ G₂ : LGraph L} : SP G₁ → SP G₂ → SP (gcomp G₁ G₂)
  | parallel {G₁ G₂ : LGraph L} : SP G₁ → SP G₂ → SP (meet G₁ G₂)
  | swap {G : LGraph L} : SP G → SP (recip G)

/-- **M2.**  Every term graph is SP-with-mark-merge: `toGraph` is literally
    built from the five constructors. -/
theorem sp_toGraph : ∀ E : Term L, SP (toGraph E)
  | .var A => .arrow A
  | .one => .one
  | .recip e => .swap (sp_toGraph e)
  | .meet a b => .parallel (sp_toGraph a) (sp_toGraph b)
  | .comp a b => .series (sp_toGraph a) (sp_toGraph b)

/-- Conversely every SP graph is a term graph on the nose (`toGraph` of the
    read-back term), so `SP = range toGraph` exactly. -/
theorem sp_eq_toGraph {G : LGraph L} (h : SP G) : ∃ E : Term L, toGraph E = G := by
  induction h with
  | one => exact ⟨.one, rfl⟩
  | arrow A => exact ⟨.var A, rfl⟩
  | series _ _ ih₁ ih₂ =>
    obtain ⟨E₁, rfl⟩ := ih₁; obtain ⟨E₂, rfl⟩ := ih₂
    exact ⟨.comp E₁ E₂, rfl⟩
  | parallel _ _ ih₁ ih₂ =>
    obtain ⟨E₁, rfl⟩ := ih₁; obtain ⟨E₂, rfl⟩ := ih₂
    exact ⟨.meet E₁ E₂, rfl⟩
  | swap _ ih =>
    obtain ⟨E, rfl⟩ := ih
    exact ⟨.recip E, rfl⟩

/-! ## Towards M3/M4 — the corner vertices of the chain tower

  `chainT k` is the chain of `k+1` lenses; its `k+2` corner vertices are
  `v₀ = s, v₁, …, v_{k+1} = t`, with `vᵢ` the joint between lens `i-1` and
  lens `i`.  The kernel analysis needs them explicit (`cVert`), with the
  `bL i`-edge `pᵢ → v_{i+1}` (`chain_edge_b`) that forces a stage map's
  values on them. -/

/-- The `i`-th corner vertex of the chain tower (meaningful for `i ≤ k+1`):
    corner `i ≤ k` lives in the left part, corner `k+1` is the fresh joint
    (as the left part's `t`-mark). -/
def cVert : (k : Nat) → Nat → (toGraph (chainT k)).V
  | 0, i => if i = 0 then (toGraph (chainT 0)).s else (toGraph (chainT 0)).t
  | k+1, i =>
      if i ≤ k then Quot.mk _ (Sum.inl (cVert k i))
      else if i = k+1 then Quot.mk _ (Sum.inl (toGraph (chainT k)).t)
      else Quot.mk _ (Sum.inr (toGraph (lens (k+1))).t)

/-- Corner `0` is the `s`-mark. -/
theorem cVert_zero : ∀ k, cVert k 0 = (toGraph (chainT k)).s
  | 0 => rfl
  | k+1 => by
    show (if 0 ≤ k then _ else _) = _
    rw [if_pos (Nat.zero_le k), cVert_zero k]
    rfl

/-- Corner `k+1` is the `t`-mark. -/
theorem cVert_last : ∀ k, cVert k (k+1) = (toGraph (chainT k)).t
  | 0 => rfl
  | k+1 => by
    show (if k+2 ≤ k then _ else _) = _
    rw [if_neg (by omega), if_neg (by omega)]
    rfl

/-- The lens's `bL i`-edge exits its top midpoint into the `t`-mark. -/
theorem lens_edge_b (i : Nat) :
    (toGraph (lens i)).edge (lensP i) (toGraph (lens i)).t (bL i) :=
  ⟨Sum.inl (Quot.mk _ (Sum.inl true)), Sum.inl (Quot.mk _ (Sum.inr true)),
    rfl, rfl,
    ⟨Sum.inr false, Sum.inr true,
      (gcomp_glue (arrow (aL i)) (arrow (bL i))).symm, rfl, ⟨rfl, rfl, rfl⟩⟩⟩

/-- The lens's `dL i`-edge exits its bottom midpoint into the `t`-mark. -/
theorem lens_edge_d (i : Nat) :
    (toGraph (lens i)).edge (lensQ i) (toGraph (lens i)).t (dL i) :=
  ⟨Sum.inr (Quot.mk _ (Sum.inl true)), Sum.inr (Quot.mk _ (Sum.inr true)),
    rfl, meet_inr_t _ _,
    ⟨Sum.inr false, Sum.inr true,
      (gcomp_glue (arrow (cL i)) (arrow (dL i))).symm, rfl, ⟨rfl, rfl, rfl⟩⟩⟩

/-- Corners `i ≤ k+1` of the extended chain are the left part's corners. -/
theorem cVert_inl {k i : Nat} (hi : i ≤ k + 1) :
    cVert (k+1) i = Quot.mk _ (Sum.inl (cVert k i)) := by
  rcases Nat.lt_or_ge i (k+1) with hlt | hge
  · have h : i ≤ k := Nat.lt_succ_iff.mp hlt
    simp only [cVert, if_pos h]
  · have h : i = k + 1 := Nat.le_antisymm hi hge
    subst h
    simp only [cVert, if_neg (by omega : ¬k + 1 ≤ k), if_true, cVert_last k]

/-- The chain's `bL i`-edge runs from the `i`-th top midpoint to the
    `(i+1)`-st corner. -/
theorem chain_edge_b : ∀ k i, i ≤ k →
    (toGraph (chainT k)).edge (pVert k i) (cVert k (i+1)) (bL i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h0 : i = 0 := Nat.le_zero.mp hi
    subst h0
    simp only [cVert, if_neg (Nat.one_ne_zero)]
    exact lens_edge_b 0
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      simp only [pVert, if_neg (by omega : ¬ m + 1 ≤ m),
        cVert, if_neg (by omega : ¬ m + 2 ≤ m), if_neg (by omega : ¬ m + 2 = m + 1)]
      exact glued_edge_inr (lens_edge_b (m+1))
    · rw [cVert_inl (by omega : i + 1 ≤ m + 1)]
      simp only [pVert, if_pos hle]
      exact glued_edge_inl (ih i hle)

/-! ## The corner vertices of the collapsed tower `[entL n]`

  `[entL n]` has vertices `x` (the merged marks), `P`, `Q`, and the interior
  corners `w₁ … w_{n+1}` — `w_{j+1}` is the middle vertex of branch `j`.
  The kernel analysis needs them explicit, plus the `bL`-edge uniqueness
  (`entL_edge_bL`) that forces a stage map's corner values. -/

theorem bL_ne_dL {i j : Nat} : bL i ≠ dL j := by simp only [bL, dL]; omega
/-- The middle vertex of branch `j` inside the `mids` tower (for `j ≤ k`). -/
def midsMid : (k : Nat) → Nat → (toGraph (mids k)).V
  | 0, _ => branchMid 0
  | k+1, j =>
      if j ≤ k then Quot.mk _ (Sum.inl (midsMid k j))
      else Quot.mk _ (Sum.inr (branchMid (k+1)))

/-- The `j`-th corner vertex of the collapsed tower: `0` and everything past
    `n+1` is the merged mark `x`; `1 ≤ j ≤ n+1` is the interior corner
    `w_j`, the middle vertex of branch `j-1`. -/
def eCorn (n : Nat) : Nat → (toGraph (entL n)).V
  | 0 => (toGraph (entL n)).s
  | j+1 =>
      if j ≤ n then
        Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inl (midsMid n j))))))
      else (toGraph (entL n)).s

/-- In a branch, the only `bL`-labelled edge is `bL j`, from the `s`-mark
    (the collapsed `P`) to the branch's middle vertex. -/
theorem branch_edge_bL {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (bL i)) :
    i = j ∧ c = (toGraph (branch j)).s ∧ d = branchMid j := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · rcases meet_arrow_recip_edge he with ⟨hlab, hus, hvt⟩ | ⟨hlab, _, _⟩
    · subst hus; subst hvt
      exact ⟨strideFour_injective 1 hlab, hu.symm, hv.symm⟩
    · exact absurd hlab.symm aL_ne_bL
  · rcases meet_recip_arrow_edge he with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
    · exact absurd hlab bL_ne_dL
    · exact absurd hlab.symm cL_ne_bL

/-- In the `mids` tower, every `bL i`-labelled edge has `i ≤ k` and runs from
    the `s`-mark to the `i`-th middle vertex. -/
theorem mids_edge_bL : ∀ {k i : Nat} {c d : (toGraph (mids k)).V},
    (toGraph (mids k)).edge c d (bL i) →
      i ≤ k ∧ c = (toGraph (mids k)).s ∧ d = midsMid k i := by
  intro k
  induction k with
  | zero =>
    intro i c d h
    obtain ⟨hij, hc, hd⟩ := branch_edge_bL h
    exact ⟨Nat.le_of_eq hij, hc, hd⟩
  | succ m ih =>
    intro i c d h
    rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
    · obtain ⟨hik, hc, hd⟩ := ih he
      subst hc; subst hd; subst hu; subst hv
      refine ⟨Nat.le_succ_of_le hik, rfl, ?_⟩
      simp only [midsMid, if_pos hik]
    · obtain ⟨hij, hc, hd⟩ := branch_edge_bL he
      subst hij; subst hc; subst hd; subst hu; subst hv
      refine ⟨Nat.le_refl _, meet_inr_s _ _, ?_⟩
      simp only [midsMid, if_neg (by omega : ¬ m + 1 ≤ m)]

/-- **Edge-uniqueness, top exits.**  Every `bL i`-labelled edge of the
    collapsed graph `[entL n]` has `i ≤ n+1`, starts at the collapsed top
    vertex `Pv n`, and ends at the corner `eCorn n (i+1)` (the merged mark
    when `i = n+1`). -/
theorem entL_edge_bL {n i : Nat} {c d : (toGraph (entL n)).V}
    (h : (toGraph (entL n)).edge c d (bL i)) :
    i ≤ n + 1 ∧ c = Pv n ∧ d = eCorn n (i+1) := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · exact he.elim
  · subst hu; subst hv
    rcases glued_edge_elim he with ⟨u', v', hu', hv', he'⟩ | ⟨u', v', hu', hv', he'⟩
    · -- first border factor `a₀ ∩ b_{n+1}°`: the `b_{n+1}`-edge runs `t → s`.
      subst hu'; subst hv'
      rcases meet_arrow_recip_edge he' with ⟨hlab, _, _⟩ | ⟨hlab, hut, hvs⟩
      · exact absurd hlab.symm aL_ne_bL
      · obtain rfl := strideFour_injective 1 hlab
        subst hut; subst hvs
        refine ⟨Nat.le_refl _, ?_, ?_⟩
        · exact congrArg
            (fun z => (Quot.mk _ (Sum.inr z) : (toGraph (entL n)).V))
            (gcomp_glue _ _)
        · simp only [eCorn, if_neg (by omega : ¬ n + 1 ≤ n)]
          exact meet_inr_s _ _
    · subst hu'; subst hv'
      rcases glued_edge_elim he' with ⟨u'', v'', hu'', hv'', he''⟩ |
        ⟨u'', v'', hu'', hv'', he''⟩
      · -- `mids` tower: `bL i`-edges run from its `s`-mark to `midsMid i`.
        subst hu''; subst hv''
        obtain ⟨hik, hc, hd⟩ := mids_edge_bL he''
        subst hc; subst hd
        refine ⟨Nat.le_succ_of_le hik, rfl, ?_⟩
        simp only [eCorn, if_pos hik]
      · -- last border factor `c₀° ∩ d_{n+1}`: has no `bL`-labelled edge.
        rcases meet_recip_arrow_edge he'' with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
        · exact absurd hlab.symm cL_ne_bL
        · exact absurd hlab bL_ne_dL

/-- **The collapse is pointwise forced on corners.**  Every mark-preserving
    graph map `[entR n] → [entL n]` sends the `i`-th chain corner to the
    `i`-th collapsed corner: corner `0` by mark preservation, corner `i+1`
    because the map carries the chain's `bL i`-edge `pᵢ → v_{i+1}` to a
    `bL i`-edge of `[entL n]`, and `entL_edge_bL` says all such edges end at
    `eCorn (i+1)`.  With `rigidity` (tops to `Pv`, bottoms to `Qv`) the
    composite is THE designated collapse, vertex by vertex. -/
theorem collapse_forced_corners (n : Nat)
    (f : Hom (toGraph (entR n)) (toGraph (entL n))) :
    ∀ i, i ≤ n + 2 → f.toEHom.onV (cVert (n+1) i) = eCorn n i := by
  intro i hi
  cases i with
  | zero => rw [cVert_zero]; exact f.map_s
  | succ j =>
    have hj' : j ≤ n + 1 := by omega
    exact (entL_edge_bL (f.toEHom.map_edge (chain_edge_b (n+1) j hj'))).2.2

/-! ## The position classifier of `[entL n]`

  To tell the vertices `x`, `P`, `Q`, `w₁ … w_{n+1}` of `[entL n]` apart we
  build a `CPos`-valued classifier through the `Quot` tower, reusing `CPos`:
  `x ↦ corner 0`, `P ↦ top 0`, `Q ↦ bot 0`, `w_j ↦ corner j`.  Every leaf
  factor of the tower is a two-vertex meet of an arrow with a reciprocated
  arrow, classified generically by the marks' target positions. -/

/-- Classifier of `x ∩ y°` (two vertices): `s ↦ pS`, `t ↦ pT`. -/
def arMeetPos {x y : L} (pS pT : CPos) :
    (meet (arrow x) (recip (arrow y))).V → CPos :=
  Quot.lift (Sum.elim (fun b => cond b pT pS) (fun b => cond b pS pT))
    (by
      intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- Classifier of `y° ∩ x` (two vertices): `s ↦ pS`, `t ↦ pT`. -/
def raMeetPos {x y : L} (pS pT : CPos) :
    (meet (recip (arrow y)) (arrow x)).V → CPos :=
  Quot.lift (Sum.elim (fun b => cond b pS pT) (fun b => cond b pT pS))
    (by
      intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- Classifier of branch `j`: `s ↦ top 0` (the collapsed `P`), the middle
    vertex `↦ corner (j+1)`, `t ↦ bot 0` (the collapsed `Q`). -/
def branchPos (j : Nat) : (toGraph (branch j)).V → CPos :=
  Quot.lift
    (Sum.elim (arMeetPos (.top 0) (.corner (j+1))) (raMeetPos (.corner (j+1)) (.bot 0)))
    (by
      intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => obtain ⟨rfl, rfl⟩ := h; rfl
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- The `mids` tower classifier, packed with its mark values. -/
def midsPosP : (k : Nat) → { f : (toGraph (mids k)).V → CPos //
    f (toGraph (mids k)).s = .top 0 ∧ f (toGraph (mids k)).t = .bot 0 }
  | 0 => ⟨branchPos 0, rfl, rfl⟩
  | k+1 =>
    ⟨Quot.lift
      (fun p => match p with
        | Sum.inl u => (midsPosP k).1 u
        | Sum.inr u => branchPos (k+1) u)
      (by
        intro p q h
        cases p with
        | inl a => cases q with
          | inl b => exact h.elim
          | inr b =>
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (midsPosP k).2.1
            · exact (midsPosP k).2.2
        | inr a => cases q with
          | inl b => exact h.elim
          | inr b => exact h.elim),
     (midsPosP k).2.1, (midsPosP k).2.2⟩

/-- Each embedded branch middle classifies as its corner. -/
theorem midsPos_mid : ∀ k j, j ≤ k → (midsPosP k).1 (midsMid k j) = .corner (j+1) := by
  intro k
  induction k with
  | zero => intro j hj; obtain rfl := Nat.le_zero.mp hj; rfl
  | succ m ih =>
    intro j hj
    rcases Nat.lt_or_ge m j with hgt | hle
    · have hj1 : j = m + 1 := Nat.le_antisymm hj hgt
      subst hj1
      show (midsPosP (m+1)).1 (midsMid (m+1) (m+1)) = _
      simp only [midsMid, if_neg (by omega : ¬ m + 1 ≤ m)]
      rfl
    · show (midsPosP (m+1)).1 (midsMid (m+1) j) = _
      simp only [midsMid, if_pos hle]
      exact ih j hle

/-- Classifier of the inner composite `mids n ; (c₀° ∩ d_{n+1})`. -/
def yPos (n : Nat) :
    (toGraph (.comp (mids n) (.meet (.recip (.var (cL 0))) (.var (dL (n+1)))))).V →
      CPos :=
  Quot.lift
    (fun r => match r with
      | Sum.inl w => (midsPosP n).1 w
      | Sum.inr w => raMeetPos (.bot 0) (.corner 0) w)
    (by
      intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => obtain ⟨rfl, rfl⟩ := h; exact (midsPosP n).2.2
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- Classifier of the full composite `(a₀ ∩ b_{n+1}°) ; mids n ; (c₀° ∩ d_{n+1})`. -/
def xPos (n : Nat) :
    (toGraph (.comp (.meet (.var (aL 0)) (.recip (.var (bL (n+1)))))
      (.comp (mids n) (.meet (.recip (.var (cL 0))) (.var (dL (n+1))))))).V → CPos :=
  Quot.lift
    (fun r => match r with
      | Sum.inl w => arMeetPos (.corner 0) (.top 0) w
      | Sum.inr w => yPos n w)
    (by
      intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => obtain ⟨rfl, rfl⟩ := h; exact ((midsPosP n).2.1).symm
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

/-- The `[entL n]` position classifier: `x ↦ corner 0`, `P ↦ top 0`,
    `Q ↦ bot 0`, interior corner `w_j ↦ corner j`. -/
def entPos (n : Nat) : (toGraph (entL n)).V → CPos :=
  Quot.lift
    (fun p => match p with
      | Sum.inl _ => .corner 0
      | Sum.inr u => xPos n u)
    (by
      intro p q h
      cases p with
      | inl a => cases q with
        | inl b => exact h.elim
        | inr b => rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      | inr a => cases q with
        | inl b => exact h.elim
        | inr b => exact h.elim)

theorem entPos_s (n : Nat) : entPos n (toGraph (entL n)).s = .corner 0 := rfl

theorem entPos_eCorn (n : Nat) : ∀ i, i ≤ n + 1 →
    entPos n (eCorn n i) = .corner i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ j =>
    have hj : j ≤ n := by omega
    show entPos n (eCorn n (j+1)) = _
    simp only [eCorn, if_pos hj]
    exact midsPos_mid n j hj

/-! ## Completeness: every chain vertex is a designated vertex or a corner -/

/-- The four vertices of a lens: the two marks and the two midpoints. -/
theorem lens_complete (i : Nat) : ∀ w : (toGraph (lens i)).V,
    w = (toGraph (lens i)).s ∨ w = lensP i ∨ w = lensQ i ∨
    w = (toGraph (lens i)).t := by
  intro w
  induction w using Quot.ind with
  | _ p =>
    cases p with
    | inl u =>
      induction u using Quot.ind with
      | _ r =>
        cases r with
        | inl b =>
          cases b
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        | inr b =>
          cases b
          · exact Or.inr (Or.inl (congrArg
              (fun z => (Quot.mk _ (Sum.inl z) : (toGraph (lens i)).V))
              (gcomp_glue (arrow (aL i)) (arrow (bL i))).symm))
          · exact Or.inr (Or.inr (Or.inr rfl))
    | inr u =>
      induction u using Quot.ind with
      | _ r =>
        cases r with
        | inl b =>
          cases b
          · exact Or.inl (meet_inr_s _ _)
          · exact Or.inr (Or.inr (Or.inl rfl))
        | inr b =>
          cases b
          · exact Or.inr (Or.inr (Or.inl (congrArg
              (fun z => (Quot.mk _ (Sum.inr z) : (toGraph (lens i)).V))
              (gcomp_glue (arrow (cL i)) (arrow (dL i))).symm)))
          · exact Or.inr (Or.inr (Or.inr (meet_inr_t _ _)))

/-- **Completeness of the chain's vertex classification**: every vertex of
    the chain tower is a corner, a top midpoint, or a bottom midpoint. -/
theorem chain_complete : ∀ k (w : (toGraph (chainT k)).V),
    (∃ i, i ≤ k + 1 ∧ w = cVert k i) ∨
    (∃ i, i ≤ k ∧ w = pVert k i) ∨
    (∃ i, i ≤ k ∧ w = qVert k i) := by
  intro k
  induction k with
  | zero =>
    intro w
    rcases lens_complete 0 w with h | h | h | h
    · exact Or.inl ⟨0, Nat.zero_le _, h.trans (cVert_zero 0).symm⟩
    · exact Or.inr (Or.inl ⟨0, Nat.le_refl _, h⟩)
    · exact Or.inr (Or.inr ⟨0, Nat.le_refl _, h⟩)
    · exact Or.inl ⟨1, Nat.le_refl _, h.trans (cVert_last 0).symm⟩
  | succ m ih =>
    intro w
    induction w using Quot.ind with
    | _ p =>
      cases p with
      | inl u =>
        rcases ih u with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
        · exact Or.inl ⟨i, by omega, (cVert_inl hi).symm⟩
        · refine Or.inr (Or.inl ⟨i, by omega, ?_⟩)
          simp only [pVert, if_pos hi]
        · refine Or.inr (Or.inr ⟨i, by omega, ?_⟩)
          simp only [qVert, if_pos hi]
      | inr u =>
        rcases lens_complete (m+1) u with h | h | h | h
        · subst h
          refine Or.inl ⟨m+1, by omega, ?_⟩
          simp only [cVert, if_neg (by omega : ¬m + 1 ≤ m), if_true]
          exact (gcomp_glue _ _).symm
        · subst h
          refine Or.inr (Or.inl ⟨m+1, Nat.le_refl _, ?_⟩)
          simp only [pVert, if_neg (by omega : ¬ m + 1 ≤ m)]
        · subst h
          refine Or.inr (Or.inr ⟨m+1, Nat.le_refl _, ?_⟩)
          simp only [qVert, if_neg (by omega : ¬ m + 1 ≤ m)]
        · subst h
          refine Or.inl ⟨m+2, Nat.le_refl _, ?_⟩
          simp only [cVert, if_neg (by omega : ¬ m + 2 ≤ m),
            if_neg (by omega : ¬ m + 2 = m + 1)]

/-! ## Distinctness of the collapsed-tower vertices -/

/-- Corner `n+2` of the collapse is the merged mark (`s = t`). -/
theorem eCorn_last (n : Nat) : eCorn n (n+2) = (toGraph (entL n)).s := by
  simp only [eCorn, if_neg (by omega : ¬ n + 1 ≤ n)]

/-- Every collapsed corner classifies as some `.corner`. -/
theorem entPos_eCorn_isCorner (n : Nat) {i : Nat} (hi : i ≤ n + 2) :
    ∃ i', entPos n (eCorn n i) = .corner i' := by
  rcases Nat.lt_or_ge i (n+2) with hlt | hge
  · exact ⟨i, entPos_eCorn n i (by omega)⟩
  · obtain rfl : i = n + 2 := by omega
    exact ⟨0, by rw [eCorn_last]; rfl⟩

/-- Interior-range corners are pairwise distinct. -/
theorem eCorn_inj {n i j : Nat} (hi : i ≤ n + 1) (hj : j ≤ n + 1)
    (h : eCorn n i = eCorn n j) : i = j := by
  have := congrArg (entPos n) h
  rw [entPos_eCorn n i hi, entPos_eCorn n j hj] at this
  injection this

/-- Corners never coincide with the collapsed top vertex. -/
theorem eCorn_ne_Pv {n i : Nat} (hi : i ≤ n + 2) : eCorn n i ≠ Pv n := by
  intro h
  obtain ⟨i', hi'⟩ := entPos_eCorn_isCorner n hi
  have := hi'.symm.trans ((congrArg (entPos n) h).trans ((midsPosP n).2.1))
  exact CPos.noConfusion this

/-- Corners never coincide with the collapsed bottom vertex. -/
theorem eCorn_ne_Qv {n i : Nat} (hi : i ≤ n + 2) : eCorn n i ≠ Qv n := by
  intro h
  obtain ⟨i', hi'⟩ := entPos_eCorn_isCorner n hi
  have := hi'.symm.trans ((congrArg (entPos n) h).trans ((midsPosP n).2.2))
  exact CPos.noConfusion this

/-- The collapsed top and bottom vertices are distinct. -/
theorem Pv_ne_Qv (n : Nat) : Pv n ≠ Qv n := by
  intro h
  have := ((midsPosP n).2.1).symm.trans ((congrArg (entPos n) h).trans ((midsPosP n).2.2))
  exact CPos.noConfusion this

/-- A merge of two collapsed corners is the mark merge: the only coincidence
    among `eCorn 0 … eCorn (n+2)` is `eCorn 0 = eCorn (n+2)` (both `x`). -/
theorem eCorn_merge {n i j : Nat} (hi : i ≤ n + 2) (hj : j ≤ n + 2)
    (hne : i ≠ j) (h : eCorn n i = eCorn n j) :
    (i = 0 ∧ j = n + 2) ∨ (i = n + 2 ∧ j = 0) := by
  rcases Nat.lt_or_ge i (n+2) with hi' | hi' <;>
    rcases Nat.lt_or_ge j (n+2) with hj' | hj'
  · exact absurd (eCorn_inj (by omega) (by omega) h) hne
  · obtain rfl : j = n + 2 := by omega
    rw [eCorn_last] at h
    have := congrArg (entPos n) h
    rw [entPos_eCorn n i (by omega), entPos_s] at this
    injection this with h0
    exact Or.inl ⟨h0, rfl⟩
  · obtain rfl : i = n + 2 := by omega
    rw [eCorn_last] at h
    have := congrArg (entPos n) h.symm
    rw [entPos_eCorn n j (by omega), entPos_s] at this
    injection this with h0
    exact Or.inr ⟨rfl, h0⟩
  · omega

/-! ## Kernel typing: what a stage map can merge -/

/-- **Kernel typing.**  Let `F` be ANY chain-stage term: `g : [entR n] → [F]`
    the composite stage map and `c : [F] → [entL n]` its continuation.  If
    `g` merges two distinct vertices of the chain, they are two TOP midpoints,
    two BOTTOM midpoints, or the two marks.  (The composite `g;c` is pinned
    vertex-by-vertex to the designated collapse — `rigidity` on midpoints,
    `collapse_forced_corners` on corners — and the collapse's fibres are
    exactly: all tops, all bottoms, the mark pair, interior corners alone.)
    This kills every "weird" kernel; the SP-wall below only has to exclude
    PARTIAL top/bottom merges. -/
theorem kernel_typing (n : Nat) {F : Term Nat}
    (g : Hom (toGraph (entR n)) (toGraph F))
    (c : Hom (toGraph F) (toGraph (entL n)))
    {u v : (toGraph (entR n)).V} (hne : u ≠ v)
    (huv : g.toEHom.onV u = g.toEHom.onV v) :
    (∃ i j, i ≤ n + 1 ∧ j ≤ n + 1 ∧ i ≠ j ∧
      u = pVert (n+1) i ∧ v = pVert (n+1) j) ∨
    (∃ i j, i ≤ n + 1 ∧ j ≤ n + 1 ∧ i ≠ j ∧
      u = qVert (n+1) i ∧ v = qVert (n+1) j) ∨
    (u = (toGraph (entR n)).s ∧ v = (toGraph (entR n)).t) ∨
    (u = (toGraph (entR n)).t ∧ v = (toGraph (entR n)).s) := by
  have hs' : (EHom.comp g.toEHom c.toEHom).onV (toGraph (entR n)).s
      = (toGraph (entL n)).s := by
    show c.toEHom.onV (g.toEHom.onV _) = _
    rw [g.map_s]; exact c.map_s
  have ht' : (EHom.comp g.toEHom c.toEHom).onV (toGraph (entR n)).t
      = (toGraph (entL n)).t := by
    show c.toEHom.onV (g.toEHom.onV _) = _
    rw [g.map_t]; exact c.map_t
  obtain ⟨hp, hq, -⟩ := rigidity n ⟨EHom.comp g.toEHom c.toEHom, hs', ht'⟩
  have hcor := collapse_forced_corners n ⟨EHom.comp g.toEHom c.toEHom, hs', ht'⟩
  have huv' : c.toEHom.onV (g.toEHom.onV u) = c.toEHom.onV (g.toEHom.onV v) :=
    congrArg c.toEHom.onV huv
  rcases chain_complete (n+1) u with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    rcases chain_complete (n+1) v with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · -- corner–corner: only the mark pair survives
    have hij : i ≠ j := fun hh => hne (by rw [hh])
    have hm : eCorn n i = eCorn n j :=
      (hcor i hi).symm.trans (huv'.trans (hcor j hj))
    rcases eCorn_merge hi hj hij hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨cVert_zero (n+1), cVert_last (n+1)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨cVert_last (n+1), cVert_zero (n+1)⟩))
  · -- corner–top: impossible
    exact absurd ((hcor i hi).symm.trans (huv'.trans (hp j hj)))
      (eCorn_ne_Pv hi)
  · -- corner–bottom: impossible
    exact absurd ((hcor i hi).symm.trans (huv'.trans (hq j hj)))
      (eCorn_ne_Qv hi)
  · -- top–corner: impossible
    exact absurd ((hcor j hj).symm.trans (huv'.symm.trans (hp i hi)))
      (eCorn_ne_Pv hj)
  · -- top–top
    have hij : i ≠ j := fun hh => hne (by rw [hh])
    exact Or.inl ⟨i, j, hi, hj, hij, rfl, rfl⟩
  · -- top–bottom: impossible
    exact absurd ((hp i hi).symm.trans (huv'.trans (hq j hj))) (Pv_ne_Qv n)
  · -- bottom–corner: impossible
    exact absurd ((hcor j hj).symm.trans (huv'.symm.trans (hq i hi)))
      (eCorn_ne_Qv hj)
  · -- bottom–top: impossible
    exact absurd ((hq i hi).symm.trans (huv'.trans (hp j hj)))
      (fun hh => Pv_ne_Qv n hh.symm)
  · -- bottom–bottom
    have hij : i ≠ j := fun hh => hne (by rw [hh])
    exact Or.inr (Or.inl ⟨i, j, hi, hj, hij, rfl, rfl⟩)

/-! ### The `dL` mirrors (bottom exits) — completing the edge toolkit -/

/-- In a branch, the only `dL`-labelled edge is `dL j`, from the `t`-mark
    (the collapsed `Q`) to the branch's middle vertex. -/
theorem branch_edge_dL {j i : Nat} {c d : (toGraph (branch j)).V}
    (h : (toGraph (branch j)).edge c d (dL i)) :
    i = j ∧ c = (toGraph (branch j)).t ∧ d = branchMid j := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · rcases meet_arrow_recip_edge he with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
    · exact absurd hlab.symm bL_ne_dL
    · exact absurd hlab.symm aL_ne_dL
  · rcases meet_recip_arrow_edge he with ⟨hlab, hut, hvs⟩ | ⟨hlab, _, _⟩
    · subst hut; subst hvs
      have hij : i = j := by simp only [dL] at hlab; omega
      refine ⟨hij, hu.symm, ?_⟩
      rw [← hv]
      exact (gcomp_glue _ _).symm
    · exact absurd hlab.symm cL_ne_dL

/-- In the `mids` tower, every `dL i`-labelled edge has `i ≤ k` and runs from
    the `t`-mark to the `i`-th middle vertex. -/
theorem mids_edge_dL : ∀ {k i : Nat} {c d : (toGraph (mids k)).V},
    (toGraph (mids k)).edge c d (dL i) →
      i ≤ k ∧ c = (toGraph (mids k)).t ∧ d = midsMid k i := by
  intro k
  induction k with
  | zero =>
    intro i c d h
    obtain ⟨hij, hc, hd⟩ := branch_edge_dL h
    exact ⟨Nat.le_of_eq hij, hc, hd⟩
  | succ m ih =>
    intro i c d h
    rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
    · obtain ⟨hik, hc, hd⟩ := ih he
      subst hc; subst hd; subst hu; subst hv
      refine ⟨Nat.le_succ_of_le hik, rfl, ?_⟩
      simp only [midsMid, if_pos hik]
    · obtain ⟨hij, hc, hd⟩ := branch_edge_dL he
      subst hij; subst hc; subst hd; subst hu; subst hv
      refine ⟨Nat.le_refl _, meet_inr_t _ _, ?_⟩
      simp only [midsMid, if_neg (by omega : ¬ m + 1 ≤ m)]

/-- **Edge-uniqueness, bottom exits.**  Every `dL i`-labelled edge of the
    collapsed graph `[entL n]` has `i ≤ n+1`, starts at the collapsed bottom
    vertex `Qv n`, and ends at the corner `eCorn n (i+1)`. -/
theorem entL_edge_dL {n i : Nat} {c d : (toGraph (entL n)).V}
    (h : (toGraph (entL n)).edge c d (dL i)) :
    i ≤ n + 1 ∧ c = Qv n ∧ d = eCorn n (i+1) := by
  rcases glued_edge_elim h with ⟨u, v, hu, hv, he⟩ | ⟨u, v, hu, hv, he⟩
  · exact he.elim
  · subst hu; subst hv
    rcases glued_edge_elim he with ⟨u', v', hu', hv', he'⟩ | ⟨u', v', hu', hv', he'⟩
    · -- first border factor `a₀ ∩ b_{n+1}°`: no `dL`-labelled edge.
      rcases meet_arrow_recip_edge he' with ⟨hlab, _, _⟩ | ⟨hlab, _, _⟩
      · exact absurd hlab.symm aL_ne_dL
      · exact absurd hlab.symm bL_ne_dL
    · subst hu'; subst hv'
      rcases glued_edge_elim he' with ⟨u'', v'', hu'', hv'', he''⟩ |
        ⟨u'', v'', hu'', hv'', he''⟩
      · -- `mids` tower: `dL i`-edges run from its `t`-mark to `midsMid i`.
        subst hu''; subst hv''
        obtain ⟨hik, hc, hd⟩ := mids_edge_dL he''
        subst hc; subst hd
        refine ⟨Nat.le_succ_of_le hik, rfl, ?_⟩
        simp only [eCorn, if_pos hik]
      · -- last border factor `c₀° ∩ d_{n+1}`: the `d_{n+1}`-edge runs `s → t`.
        subst hu''; subst hv''
        rcases meet_recip_arrow_edge he'' with ⟨hlab, _, _⟩ | ⟨hlab, hus, hvt⟩
        · exact absurd hlab.symm cL_ne_dL
        · have hij : i = n + 1 := by simp only [dL] at hlab; omega
          subst hij; subst hus; subst hvt
          refine ⟨Nat.le_refl _, ?_, ?_⟩
          · exact congrArg
              (fun z => (Quot.mk _ (Sum.inr (Quot.mk _ (Sum.inr z)))
                : (toGraph (entL n)).V))
              (gcomp_glue _ _).symm
          · simp only [eCorn, if_neg (by omega : ¬ n + 1 ≤ n)]
            exact meet_inr_t _ _

/-- The chain's `aL i`-edge runs from the `i`-th corner to the `i`-th top
    midpoint (the named-source refinement of `pVert_edge`). -/
theorem chain_edge_a : ∀ k i, i ≤ k →
    (toGraph (chainT k)).edge (cVert k i) (pVert k i) (aL i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    obtain rfl := Nat.le_zero.mp hi
    rw [cVert_zero]
    exact lensP_edge 0
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      simp only [pVert, cVert, if_neg (by omega : ¬m + 1 ≤ m), if_true]
      rw [gcomp_glue]
      exact glued_edge_inr (lensP_edge (m+1))
    · rw [cVert_inl (by omega : i ≤ m + 1)]
      simp only [pVert, if_pos hle]
      exact glued_edge_inl (ih i hle)

/-- The chain's `cL i`-edge runs from the `i`-th corner to the `i`-th bottom
    midpoint. -/
theorem chain_edge_c : ∀ k i, i ≤ k →
    (toGraph (chainT k)).edge (cVert k i) (qVert k i) (cL i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    obtain rfl := Nat.le_zero.mp hi
    rw [cVert_zero]
    exact lensQ_edge 0
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      simp only [qVert, cVert, if_neg (by omega : ¬m + 1 ≤ m), if_true]
      rw [gcomp_glue]
      exact glued_edge_inr (lensQ_edge (m+1))
    · rw [cVert_inl (by omega : i ≤ m + 1)]
      simp only [qVert, if_pos hle]
      exact glued_edge_inl (ih i hle)

/-- The chain's `dL i`-edge runs from the `i`-th bottom midpoint to the
    `(i+1)`-st corner. -/
theorem chain_edge_d : ∀ k i, i ≤ k →
    (toGraph (chainT k)).edge (qVert k i) (cVert k (i+1)) (dL i) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    obtain rfl := Nat.le_zero.mp hi
    simp only [cVert, if_neg (Nat.one_ne_zero)]
    exact lens_edge_d 0
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_ge m i with hgt | hle
    · have hi1 : i = m + 1 := Nat.le_antisymm hi hgt
      subst hi1
      simp only [qVert, if_neg (by omega : ¬ m + 1 ≤ m),
        cVert, if_neg (by omega : ¬ m + 2 ≤ m), if_neg (by omega : ¬ m + 2 = m + 1)]
      exact glued_edge_inr (lens_edge_d (m+1))
    · rw [cVert_inl (by omega : i + 1 ≤ m + 1)]
      simp only [qVert, if_pos hle]
      exact glued_edge_inl (ih i hle)

/-! ## M3/M4 — the SP wall and the kernel dichotomy -/

/-- **M3, the SP wall** (Freyd's corrected claim (ii), stated for the
    `(n+2)`-rhombus chain): if a chain-stage map `g` (continuation `c` in
    hand) merges ANY two distinct top midpoints or two distinct bottom
    midpoints, it merges ALL designated pairs.  FALSE for `n = 0`
    (`ent0_derivable`); the content of §2.158 needs it for `n ≥ 1`. -/
def SPWall (n : Nat) : Prop :=
  ∀ (F : Term Nat) (g : Hom (toGraph (entR n)) (toGraph F)),
    Nonempty (Hom (toGraph F) (toGraph (entL n))) →
    (∃ i j, i ≤ n + 1 ∧ j ≤ n + 1 ∧ i ≠ j ∧
      (g.toEHom.onV (pVert (n+1) i) = g.toEHom.onV (pVert (n+1) j) ∨
       g.toEHom.onV (qVert (n+1) i) = g.toEHom.onV (qVert (n+1) j))) →
    (∀ i j, i ≤ n + 1 → j ≤ n + 1 →
      g.toEHom.onV (pVert (n+1) i) = g.toEHom.onV (pVert (n+1) j)) ∧
    (∀ i j, i ≤ n + 1 → j ≤ n + 1 →
      g.toEHom.onV (qVert (n+1) i) = g.toEHom.onV (qVert (n+1) j)) ∧
    g.toEHom.onV (toGraph (entR n)).s = g.toEHom.onV (toGraph (entR n)).t

/-- **M4, the kernel dichotomy — target (a) of the OPEN note, assembled.**
    For a chain-stage term `F` with stage map `g : [entR n] → [F]` and
    continuation `c : [F] → [entL n]`: either `ker g ≤` the `{s,t}`-pair
    (every merged pair of distinct vertices IS the mark pair), or `ker g ⊇`
    all designated pairs (all tops to one point, all bottoms to one point,
    marks merged).  Given `kernel_typing` — which needs no wall — the two
    sides are separated exactly by whether some top/bottom pair merges, and
    the SP wall upgrades one such merge to the full collapse. -/
theorem kernel_dichotomy {n : Nat} (hwall : SPWall n) (F : Term Nat)
    (g : Hom (toGraph (entR n)) (toGraph F))
    (c : Hom (toGraph F) (toGraph (entL n))) :
    (∀ u v, g.toEHom.onV u = g.toEHom.onV v → u = v ∨
      (u = (toGraph (entR n)).s ∧ v = (toGraph (entR n)).t) ∨
      (u = (toGraph (entR n)).t ∧ v = (toGraph (entR n)).s)) ∨
    ((∀ i j, i ≤ n + 1 → j ≤ n + 1 →
        g.toEHom.onV (pVert (n+1) i) = g.toEHom.onV (pVert (n+1) j)) ∧
     (∀ i j, i ≤ n + 1 → j ≤ n + 1 →
        g.toEHom.onV (qVert (n+1) i) = g.toEHom.onV (qVert (n+1) j)) ∧
     g.toEHom.onV (toGraph (entR n)).s = g.toEHom.onV (toGraph (entR n)).t) := by
  by_cases hmerge : ∃ i j, i ≤ n + 1 ∧ j ≤ n + 1 ∧ i ≠ j ∧
      (g.toEHom.onV (pVert (n+1) i) = g.toEHom.onV (pVert (n+1) j) ∨
       g.toEHom.onV (qVert (n+1) i) = g.toEHom.onV (qVert (n+1) j))
  · exact Or.inr (hwall F g ⟨c⟩ hmerge)
  · refine Or.inl fun u v huv => ?_
    by_cases hne : u = v
    · exact Or.inl hne
    · rcases kernel_typing n g c hne huv with
        ⟨i, j, hi, hj, hij, rfl, rfl⟩ | ⟨i, j, hi, hj, hij, rfl, rfl⟩ | hst | hst
      · exact absurd ⟨i, j, hi, hj, hij, Or.inl huv⟩ hmerge
      · exact absurd ⟨i, j, hi, hj, hij, Or.inr huv⟩ hmerge
      · exact Or.inr (Or.inl hst)
      · exact Or.inr (Or.inr hst)

/-! ## OPEN — the remaining content of `SPWall n` (`n ≥ 1`)

  What is CLOSED in this file (all Sorry-free):

  * **M1** — `connected_receives_term`: a connected marked graph with
    enumerable vertices/edges receives a mark-preserving, vertex- and
    edge-surjective map from a term graph (Freyd's "one may show",
    receives-half), via walk terms and the meet fold.
  * **M2** — `SP`, `sp_toGraph`, `sp_eq_toGraph`: the SP-with-mark-merge
    class IS `range toGraph` (mark merge = `parallel` with `one`).
  * **Kernel typing** — `kernel_typing`: a stage kernel merges only
    top–top, bottom–bottom, or the mark pair.  Engine: `rigidity` +
    `collapse_forced_corners` (the composite to `[entL n]` is pinned
    vertex-by-vertex) + the `entPos` classifier distinctness.
  * **M4** — `kernel_dichotomy`: the OPEN-note target (a), conditional on
    the single remaining `SPWall n`.

  What remains OPEN: `SPWall n` for `n ≥ 1` — one merged top (or bottom)
  pair forces the full collapse.  It is FALSE for `n = 0`
  (`ent0_derivable`).  ROADMAP (worked out, no treewidth/minor theory
  needed — pure SP recursion against the typing):

  Generalize to SEGMENT configurations: in a graph `G` with an EHom
  `τ : G → [entL n]` (no mark conditions), a configuration of type `[a,b]`
  (`a ≤ b ≤ n+1`) is corners `x_a … x_{b+1}`, tops `P_a … P_b`, bottoms
  `Q_a … Q_b` with the `4(b-a+1)` lens edges labelled by blocks
  `a … b`, anchored `{x_a, x_{b+1}} = {G.s, G.t}`.  τ-types are then
  DERIVED: `τ x_i = eCorn i`, `τ P_i = Pv`, `τ Q_i = Qv` (edge-uniqueness
  lemmas `entL_edge_aL/bL/cL/dL`, all in hand; the top-level configuration's
  edges are `g.toEHom.map_edge` of `chain_edge_a/b/c/d`).  CLAIM: if `G` is SP and
  some two distinct tops (or bottoms) of the configuration coincide, then
  all its tops coincide, all its bottoms coincide, and `x_a = x_{b+1}`.
  Induction on `SP G`:
  * `one`/`arrow`: a configuration with two lenses has ≥ 2 distinctly
    labelled edges — impossible.
  * `swap`: same configuration, marks exchanged — the anchor is symmetric.
  * `parallel` (`meet G₁ G₂`, glues both mark pairs): interior corners are
    non-marks (their `eCorn` types differ from the marks'), so each walk
    stays on one side; the shared interior corners force ONE side to carry
    the whole configuration (`meet_mk_eq` inverts classes; the side
    embeddings are injective).  Descend.
  * `series` (`gcomp G₁ G₂`, ONE joint class `J`): every class is
    left-only, right-only, or `J` (`gcomp_mk_eq`).  `τ J` is an `eCorn`
    type: `J` cannot be a top or bottom image (`τ P_i = Pv ≠ eCorn _`,
    `Pv ≠ Qv` — a top-walk crossing and a bottom-walk crossing are the SAME
    vertex `J`).  So either the configuration lies in one side (joint at a
    segment end; descend), or `J = x_k` with `a < k < b+1` and the
    configuration SPLITS into `[a, k-1]` (left, anchored `x_a, x_k = G₁.t`)
    and `[k, b]` (right).  A merged pair cannot straddle the split (its two
    vertices would lie in different sides, equal only if both are `J`, but
    tops are never `J`).  The sub-induction on the merged side concludes
    that side's MARKS merge: `x_a = x_k` (or `x_k = x_{b+1}`) — but
    `τ x_a = eCorn a ≠ eCorn k = τ x_k` (`eCorn_inj`), CONTRADICTION.  So
    an interior joint is impossible in the presence of any merge, and the
    series case always descends.  This is where `n ≥ 1` enters: for the
    top-level configuration `[0, n+1]`, `eCorn 0 = eCorn (n+2)` wraps
    around, and the 2-lens chain (`n = 0`) admits the split `[0,0] | [1,1]`
    at `k = 1` with both sides collapsing — exactly the erratum's
    derivation.  For `n ≥ 1` a single merge lands in a side with ≥ … the
    sub-conclusion `x_a = x_k` has `a, k ≤ n+1` genuinely distinct interior
    indices, so the contradiction fires.
  Instantiate at the top level: `G := [F]` (SP by `sp_toGraph`),
  `τ := c.toEHom`, configuration = the `g`-images (edges by
  `g.toEHom.map_edge` of `pVert_edge`/`chain_edge_b`/`qVert_edge`/the `dL`
  mirror), distinct designated images by `kernel_typing`.  Deliverable:
  `SPWall n` for `n ≥ 1`, then `kernel_dichotomy` is unconditional there.

  Downstream (from the S2_158b OPEN note): (a) = `kernel_dichotomy`,
  (b) = `step_merge_bound` (modulo `InstanceBound`), (c) = `rigidity`;
  `Chain.exists_jump` assembles them into `RhombusHard entL entR`. -/

end Freyd.S2_158
