/-
  Bird & de Moor, *Algebra of Programming* §6.6, "Quicksort" (pp.154-155) — the book's point-free
  derivation over the binary-tree datatype `tree A ::= null | fork (tree A, A, tree A)`
  (`AOP.A6_TreeBin`).  Each calculation step is one declaration, in diagram order (B&dM's `R·S` is
  `S ≫ R`).  Only the three claims the book leaves "as exercises" drop to points.

  The concrete program and its termination measure stay in `AOP.A6_6d_QSort`; this module reuses
  its list lemma `perm_cappend` where the book itself drops to points.
-/
module

public import AOP.A6_6b_SortConcrete
public import AOP.A6_6d_QSort
public import AOP.A6_TreeBin
public import AOP.A6_3

namespace Freyd.Alg.RelSet.Sort

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel
open Freyd.Alg.RelSet.TB (Tree dTree)

variable {A : Type}

/-! ## The objects and arrows of the book's quicksort -/

/-- The object `list A × A × list A`. -/
@[expose] public abbrev dLAL (A : Type) : RelSet.{0} := ⟨ConsList Unit A × A × ConsList Unit A⟩
/-- The object `tree A × A × tree A`. -/
@[expose] public abbrev dTAT (A : Type) : RelSet.{0} := ⟨Tree A × A × Tree A⟩

/-- B&dM p.154 `join(x,a,y) = x ++ [a] ++ y`. -/
@[expose] public def join : dLAL A ⟶ dList A := graph fun p => cappend p.1 (ConsList.cons p.2.1 p.2.2)
/-- The tree constructor `fork : tree A ← tree A × A × tree A`. -/
@[expose] public def fork : dTAT A ⟶ dTree A := graph fun p => Tree.node p.1 p.2.1 p.2.2
/-- The tree constructor `null : tree A ← 1`. -/
@[expose] public def null : dL Unit ⟶ dTree A := graph fun _ => Tree.nil

/-- B&dM p.154 `flatten = ⦇[nil, join]⦈`: the elements of a tree in left-to-right order. -/
@[expose] public def flatten : dTree A ⟶ dList A :=
  ⦇(junc (sumCop (dL Unit) (dLAL A)) wrapR join : (TB.F A).obj (dList A) ⟶ dList A)⦈

/-- `intree : A ← tree A`, membership in a tree. -/
@[expose] public def intreeP : Tree A → A → Prop
  | Tree.nil, _ => False
  | Tree.node l a r, b => intreeP l b ∨ b = a ∨ intreeP r b

variable (R : A → A → Prop)

/-- B&dM p.154 `check`: holds at `(x,a,y)` when `bRa` for every `b` in `x` and `aRb` for every
    `b` in `y`. -/
@[expose] public def check : dTAT A ⟶ dTAT A :=
  fun p q => p = q ∧ (∀ b, intreeP p.1 b → R b p.2.1) ∧ (∀ b, intreeP p.2.2 b → R p.2.1 b)

/-- B&dM p.155 `check'`: `check` with lists for trees. -/
@[expose] public def check' : dLAL A ⟶ dLAL A :=
  fun p q => p = q ∧ (∀ b, inlistP p.1 b → R b p.2.1) ∧ (∀ b, inlistP p.2.2 b → R p.2.1 b)

/-- B&dM p.154 `inordered = ⦇[null, fork check]⦈`: a tree is in order when `check` holds at every
    node. -/
@[expose] public def inordered : dTree A ⟶ dTree A :=
  ⦇(junc (sumCop (dL Unit) (dTAT A)) null (check R ≫ fork) : (TB.F A).obj (dTree A) ⟶ dTree A)⦈

/-! ## Points: what `flatten` and `inordered` compute -/

/-- The function `flatten` is the graph of. -/
def flat : Tree A → ConsList Unit A
  | Tree.nil => ConsList.wrap ()
  | Tree.node l a r => cappend (flat l) (ConsList.cons a (flat r))

/-- The predicate `inordered` is the coreflexive of. -/
def inorderedP : Tree A → Prop
  | Tree.nil => True
  | Tree.node l a r => inorderedP l ∧ inorderedP r
      ∧ (∀ b, intreeP l b → R b a) ∧ (∀ b, intreeP r b → R a b)

/-- `F(S)` followed by an algebra `[T, U]` is the algebra `[T, (S×𝟙×S)U]`. -/
theorem TFmap_comp_junc {C D E : RelSet.{0}} (S : C ⟶ D) (T : dL Unit ⟶ E)
    (U : (⟨D.carrier × A × D.carrier⟩ : RelSet.{0}) ⟶ E) :
    (TB.F A).map S ≫ junc (sumCop (dL Unit) ⟨D.carrier × A × D.carrier⟩) T U
      = junc (sumCop (dL Unit) ⟨C.carrier × A × C.carrier⟩) T
          (rprodMap S (rprodMap (𝟙 (dE A)) S) ≫ U) := by
  apply hom_ext; intro u y
  cases u with
  | inl d =>
    refine ⟨fun ⟨v, hv, h⟩ => ?_, fun h => ⟨Sum.inl d, trivial, ?_⟩⟩
    · cases v with
      | inl d' => exact (junc_sum_inl _ _ _ _).mpr ((junc_sum_inl _ _ _ _).mp h)
      | inr q => exact hv.elim
    · exact (junc_sum_inl _ _ _ _).mpr ((junc_sum_inl _ _ _ _).mp h)
  | inr p =>
    refine ⟨fun ⟨v, hv, h⟩ => ?_, fun h => ?_⟩
    · cases v with
      | inl d' => exact hv.elim
      | inr q => exact (junc_sum_inr _ _ _ _).mpr ⟨q, hv, (junc_sum_inr _ _ _ _).mp h⟩
    · obtain ⟨q, hq, h⟩ := (junc_sum_inr _ _ _ _).mp h
      exact ⟨Sum.inr q, hq, (junc_sum_inr _ _ _ _).mpr h⟩

theorem flatten_graph : (flatten : dTree A ⟶ dList A) = graph flat := by
  refine ((relCata_UP (TB.initial A) _ (graph flat)).mp (hom_ext fun u y => ?_)).symm
  cases u with
  | inl d =>
    refine ⟨fun ⟨t, ht, hy⟩ => ⟨Sum.inl d, trivial, (junc_sum_inl _ _ _ _).mpr ?_⟩,
      fun ⟨v, hv, h⟩ => ?_⟩
    · subst ht; exact hy
    · cases v with
      | inl d' =>
        have h' := (junc_sum_inl wrapR join d' y).mp h
        exact ⟨Tree.nil, rfl, by cases d'; exact h'⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨l, a, r⟩ := p
    refine ⟨fun ⟨t, ht, hy⟩ => ⟨Sum.inr (flat l, a, flat r), ⟨rfl, rfl, rfl⟩,
      (junc_sum_inr _ _ _ _).mpr ?_⟩, fun ⟨v, hv, h⟩ => ?_⟩
    · subst ht; exact hy
    · cases v with
      | inl d' => exact hv.elim
      | inr q =>
        obtain ⟨l', a', r'⟩ := q
        obtain ⟨h1, h2, h3⟩ := hv
        have h := (junc_sum_inr _ _ _ _).mp h
        have e1 : l' = flat l := h1
        have e2 : a = a' := h2
        have e3 : r' = flat r := h3
        subst e1 e2 e3
        exact ⟨Tree.node l a r, rfl, h⟩

theorem inordered_coref :
    (inordered R : dTree A ⟶ dTree A) = fun t u => t = u ∧ inorderedP R t := by
  refine ((relCata_UP (TB.initial A) _ _).mp (hom_ext fun u y => ?_)).symm
  cases u with
  | inl d =>
    refine ⟨fun ⟨t, ht, hy, _⟩ => ⟨Sum.inl d, trivial, (junc_sum_inl _ _ _ _).mpr ?_⟩,
      fun ⟨v, hv, h⟩ => ?_⟩
    · subst ht; subst hy; rfl
    · cases v with
      | inl d' => exact ⟨Tree.nil, rfl, ((junc_sum_inl _ _ _ _).mp h).symm, trivial⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨l, a, r⟩ := p
    refine ⟨fun ⟨t, ht, hy, ho⟩ => ?_, fun ⟨v, hv, h⟩ => ?_⟩
    · subst ht; subst hy
      obtain ⟨hl, hr, hla, har⟩ := ho
      exact ⟨Sum.inr (l, a, r), ⟨⟨rfl, hl⟩, rfl, ⟨rfl, hr⟩⟩,
        (junc_sum_inr _ _ _ _).mpr ⟨(l, a, r), ⟨rfl, hla, har⟩, rfl⟩⟩
    · cases v with
      | inl d' => exact hv.elim
      | inr q =>
        obtain ⟨l', a', r'⟩ := q
        obtain ⟨⟨h1, hl⟩, h2, ⟨h3, hr⟩⟩ := hv
        obtain ⟨q, ⟨hq, hla, har⟩, hy⟩ := (junc_sum_inr _ _ _ _).mp h
        subst hq; subst h1; subst h3; subst h2
        exact ⟨Tree.node l a r, rfl, hy.symm, hl, hr, hla, har⟩

theorem inlist_cappend_iff (b : A) : ∀ x y : ConsList Unit A,
    inlistP (cappend x y) b ↔ inlistP x b ∨ inlistP y b
  | ConsList.wrap _, y => ⟨Or.inr, fun h => h.elim False.elim id⟩
  | ConsList.cons a x, y => by
    show b = a ∨ inlistP (cappend x y) b ↔ (b = a ∨ inlistP x b) ∨ inlistP y b
    rw [inlist_cappend_iff b x y, or_assoc]

theorem inlist_flat (b : A) : ∀ t : Tree A, inlistP (flat t) b ↔ intreeP t b
  | Tree.nil => Iff.rfl
  | Tree.node l a r => by
    show inlistP (cappend (flat l) (ConsList.cons a (flat r))) b ↔ _
    rw [inlist_cappend_iff]
    show inlistP (flat l) b ∨ (b = a ∨ inlistP (flat r) b) ↔ _
    rw [inlist_flat b l, inlist_flat b r]; rfl

theorem ordered_cappend_iff : ∀ x y : ConsList Unit A,
    orderedP R (cappend x y)
      ↔ orderedP R x ∧ orderedP R y ∧ ∀ b c, inlistP x b → inlistP y c → R b c
  | ConsList.wrap _, y => ⟨fun h => ⟨trivial, h, fun _ _ hb => hb.elim⟩, fun h => h.2.1⟩
  | ConsList.cons a x, y => by
    show (∀ c, inlistP (cappend x y) c → R a c) ∧ orderedP R (cappend x y) ↔ _
    rw [ordered_cappend_iff x y]
    constructor
    · rintro ⟨ha, hx, hy, hxy⟩
      refine ⟨⟨fun c hc => ha c ((inlist_cappend_iff c x y).mpr (Or.inl hc)), hx⟩, hy, ?_⟩
      rintro b c (rfl | hb) hc
      · exact ha c ((inlist_cappend_iff c x y).mpr (Or.inr hc))
      · exact hxy b c hb hc
    · rintro ⟨⟨ha, hx⟩, hy, hxy⟩
      refine ⟨fun c hc => ?_, hx, hy, fun b c hb hc => hxy b c (Or.inr hb) hc⟩
      rcases (inlist_cappend_iff c x y).mp hc with hc | hc
      · exact ha c hc
      · exact hxy a c (Or.inl rfl) hc

theorem ordered_flat (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ t : Tree A, orderedP R (flat t) ↔ inorderedP R t
  | Tree.nil => ⟨fun _ => trivial, fun _ => trivial⟩
  | Tree.node l a r => by
    show orderedP R (cappend (flat l) (ConsList.cons a (flat r))) ↔ _
    rw [ordered_cappend_iff]
    show orderedP R (flat l) ∧ ((∀ c, inlistP (flat r) c → R a c) ∧ orderedP R (flat r))
        ∧ (∀ b c, inlistP (flat l) b → (c = a ∨ inlistP (flat r) c) → R b c) ↔ _
    rw [ordered_flat htrans l, ordered_flat htrans r]
    constructor
    · rintro ⟨hl, ⟨har, hr⟩, hx⟩
      exact ⟨hl, hr, fun b hb => hx b a ((inlist_flat b l).mpr hb) (Or.inl rfl),
        fun c hc => har c ((inlist_flat c r).mpr hc)⟩
    · rintro ⟨hl, hr, hla, har⟩
      refine ⟨hl, ⟨fun c hc => har c ((inlist_flat c r).mp hc), hr⟩, ?_⟩
      rintro b c hb (rfl | hc)
      · exact hla b ((inlist_flat b l).mp hb)
      · exact htrans b a c (hla b ((inlist_flat b l).mp hb)) (har c ((inlist_flat c r).mp hc))

/-! ## The three claims B&dM leave as exercises (p.154-155) -/

/-- **Claim, p.154**: `flatten ordered = inordered flatten`, `R` a preorder. -/
public theorem flatten_ordered (htrans : ∀ a b c, R a b → R b c → R a c) :
    (flatten : dTree A ⟶ dList A) ≫ ordered R = inordered R ≫ flatten := by
  rw [flatten_graph, inordered_coref]
  apply hom_ext; intro t y
  refine ⟨fun ⟨x, hx, hxy, ho⟩ => ⟨t, ⟨rfl, (ordered_flat R htrans t).mp (hx ▸ ho)⟩, hxy ▸ hx⟩,
    fun ⟨u, ⟨htu, ho⟩, hy⟩ => ⟨y, (htu ▸ hy), rfl, ?_⟩⟩
  subst htu; rw [hy]; exact (ordered_flat R htrans t).mpr ho

/-- **Claim, p.155**: `check F(flatten) = F(flatten) check'`. -/
public theorem check_flatten :
    check R ≫ rprodMap flatten (rprodMap (𝟙 (dE A)) flatten)
      = rprodMap flatten (rprodMap (𝟙 (dE A)) flatten) ≫ check' R := by
  rw [flatten_graph]
  apply hom_ext; intro p q
  obtain ⟨l, a, r⟩ := p
  constructor
  · rintro ⟨p', ⟨hp, hla, har⟩, h1, h2, h3⟩
    subst hp
    refine ⟨q, ⟨h1, h2, h3⟩, rfl, fun b hb => ?_, fun b hb => ?_⟩
    · rw [h1] at hb; rw [← h2]; exact hla b ((inlist_flat b l).mp hb)
    · rw [h3] at hb; rw [← h2]; exact har b ((inlist_flat b r).mp hb)
  · rintro ⟨q', ⟨h1, h2, h3⟩, hq, hla, har⟩
    subst hq
    refine ⟨(l, a, r), ⟨rfl, fun b hb => ?_, fun b hb => ?_⟩, h1, h2, h3⟩
    · have := hla b (h1 ▸ (inlist_flat b l).mpr hb); rw [← h2] at this; exact this
    · have := har b (h3 ▸ (inlist_flat b r).mpr hb); rw [← h2] at this; exact this

/-- **Claim, p.155**: `join perm = F(perm) join perm` — permuting the parts first changes nothing. -/
public theorem join_perm :
    (join : dLAL A ⟶ dList A) ≫ perm = rprodMap perm (rprodMap (𝟙 (dE A)) perm) ≫ join ≫ perm := by
  apply hom_ext; intro p z
  constructor
  · rintro ⟨y, hy, hp⟩
    exact ⟨p, ⟨Perm.refl _, rfl, Perm.refl _⟩, y, hy, hp⟩
  · rintro ⟨q, ⟨h1, h2, h3⟩, y, hy, hp⟩
    refine ⟨_, rfl, Perm.trans ?_ (hy ▸ hp)⟩
    show Perm (cappend p.1 (ConsList.cons p.2.1 p.2.2)) (cappend q.1 (ConsList.cons q.2.1 q.2.2))
    rw [← h2]; exact QSort.perm_cappend h1 (Perm.cons _ h3)

/-- **Claim, p.155**: `check' F(perm) = F(perm) check'` — permuting the parts keeps the pivot
    between them. -/
public theorem check'_perm :
    check' R ≫ rprodMap perm (rprodMap (𝟙 (dE A)) perm)
      = rprodMap perm (rprodMap (𝟙 (dE A)) perm) ≫ check' R := by
  apply hom_ext; intro p q
  constructor
  · rintro ⟨p', ⟨hp, hla, har⟩, h1, h2, h3⟩
    subst hp
    exact ⟨q, ⟨h1, h2, h3⟩, rfl, fun b hb => h2 ▸ hla b (perm_mem (Perm.symm h1) hb),
      fun b hb => h2 ▸ har b (perm_mem (Perm.symm h3) hb)⟩
  · rintro ⟨q', ⟨h1, h2, h3⟩, hq, hla, har⟩
    subst hq
    exact ⟨p, ⟨rfl, fun b hb => h2 ▸ hla b (perm_mem h1 hb),
      fun b hb => h2 ▸ har b (perm_mem h3 hb)⟩, h1, h2, h3⟩

/-! ## The fusion proviso (p.155) -/

/-- **p.155, step 1**: `check fork flatten perm = check F(flatten) join perm` — catamorphisms,
    `fork flatten = F(flatten) join` since `flatten = ⦇[nil, join]⦈`. -/
public theorem split_step1 :
    check R ≫ fork ≫ (flatten : dTree A ⟶ dList A) ≫ perm
      = check R ≫ rprodMap flatten (rprodMap (𝟙 (dE A)) flatten) ≫ join ≫ perm := by
  have h : (fork : dTAT A ⟶ dTree A) ≫ flatten
      = rprodMap flatten (rprodMap (𝟙 (dE A)) flatten) ≫ join := by
    rw [flatten_graph]
    apply hom_ext; intro p y
    obtain ⟨l, a, r⟩ := p
    exact ⟨fun ⟨t, ht, hy⟩ => ⟨(flat l, a, flat r), ⟨rfl, rfl, rfl⟩, by subst ht; exact hy⟩,
      fun ⟨⟨l', a', r'⟩, ⟨h1, h2, h3⟩, hy⟩ => ⟨_, rfl, by
        have e1 : l' = flat l := h1
        have e2 : a = a' := h2
        have e3 : r' = flat r := h3
        subst e1 e2 e3
        exact hy⟩⟩
  rw [← Cat.assoc fork, h, Cat.assoc]

/-- **p.155, step 2**: `check F(flatten) join perm = F(flatten) check' join perm` — the claim
    `check F(flatten) = F(flatten) check'`. -/
public theorem split_step2 :
    check R ≫ rprodMap flatten (rprodMap (𝟙 (dE A)) flatten) ≫ join ≫ (perm : dList A ⟶ dList A)
      = rprodMap flatten (rprodMap (𝟙 (dE A)) flatten) ≫ check' R ≫ join ≫ perm := by
  rw [← Cat.assoc, check_flatten, Cat.assoc]

/-- **p.155, step 3**: `F(flatten) check' join perm = F(flatten) F(perm) check' join perm` — the
    claims `join perm = F(perm) join perm` and `check' F(perm) = F(perm) check'`. -/
public theorem split_step3 :
    rprodMap flatten (rprodMap (𝟙 (dE A)) flatten) ≫ check' R ≫ join ≫ (perm : dList A ⟶ dList A)
      = rprodMap flatten (rprodMap (𝟙 (dE A)) flatten)
          ≫ rprodMap perm (rprodMap (𝟙 (dE A)) perm) ≫ check' R ≫ join ≫ perm := by
  conv => lhs; rw [join_perm, ← Cat.assoc (check' R), check'_perm, Cat.assoc]

/-- **p.155, step 4**: `F(flatten) F(perm) check' join perm = F(flatten perm) check' join perm` —
    functors. -/
public theorem split_step4 :
    rprodMap flatten (rprodMap (𝟙 (dE A)) flatten)
        ≫ rprodMap perm (rprodMap (𝟙 (dE A)) perm) ≫ check' R ≫ join ≫ (perm : dList A ⟶ dList A)
      = rprodMap (flatten ≫ perm) (rprodMap (𝟙 (dE A)) (flatten ≫ perm))
          ≫ check' R ≫ join ≫ perm := by
  rw [← Cat.assoc, rprodMap_comp, rprodMap_comp, Cat.id_comp]

variable {R} {split : dList A ⟶ dLAL A}

/-- **p.155, step 5**: `F(flatten perm) check' join perm ⊒ F(flatten perm) split°`, taking
    `split° ⊑ check' join perm`. -/
public theorem split_step5 (hsplit : split° ⊑ check' R ≫ join ≫ perm) :
    rprodMap (flatten ≫ perm) (rprodMap (𝟙 (dE A)) (flatten ≫ perm)) ≫ split°
      ⊑ rprodMap (flatten ≫ perm) (rprodMap (𝟙 (dE A)) (flatten ≫ perm))
          ≫ check' R ≫ join ≫ perm :=
  comp_mono_left _ hsplit

/-- **p.155**: the fusion proviso `F(flatten perm) split° ⊑ check fork flatten perm`. -/
public theorem split_proviso (hsplit : split° ⊑ check' R ≫ join ≫ perm) :
    rprodMap (flatten ≫ perm) (rprodMap (𝟙 (dE A)) (flatten ≫ perm)) ≫ split°
      ⊑ check R ≫ fork ≫ (flatten : dTree A ⟶ dList A) ≫ perm := by
  rw [split_step1, split_step2, split_step3, split_step4]; exact split_step5 hsplit

/-! ## Quicksort (p.154) -/

variable (R) in
/-- **p.154, step 1**: `perm ordered ⊒ perm flatten° flatten ordered`, `flatten` being simple. -/
public theorem qsort_step1 :
    perm ≫ (flatten : dTree A ⟶ dList A)° ≫ flatten ≫ ordered R ⊑ perm ≫ ordered R := by
  refine comp_mono_left _ ?_
  rw [← Cat.assoc]
  refine le_trans (comp_mono_right ?_ _) (le_of_eq (Cat.id_comp _))
  rw [flatten_graph]; exact graph_simple flat

variable (R) in
/-- **p.154, step 2**: `perm flatten° flatten ordered = perm flatten° inordered flatten` — the
    claim `flatten ordered = inordered flatten`. -/
public theorem qsort_step2 (htrans : ∀ a b c, R a b → R b c → R a c) :
    perm ≫ (flatten : dTree A ⟶ dList A)° ≫ flatten ≫ ordered R
      = perm ≫ flatten° ≫ inordered R ≫ flatten := by
  rw [flatten_ordered R htrans]

variable (R) in
/-- **p.154, step 3**: `perm flatten° inordered flatten = (inordered flatten perm)° flatten` —
    converses, `perm` and the coreflexive `inordered` being their own. -/
public theorem qsort_step3 :
    perm ≫ (flatten : dTree A ⟶ dList A)° ≫ inordered R ≫ flatten
      = (inordered R ≫ flatten ≫ perm)° ≫ flatten := by
  have hi : (inordered R : dTree A ⟶ dTree A)° = inordered R :=
    coref_recip (by rw [inordered_coref]; exact le_iff.mpr fun _ _ h => h.1)
  rw [Allegory.recip_comp, Allegory.recip_comp, perm_recip, hi, Cat.assoc, Cat.assoc]

/-- **p.154, step 4**: `(inordered flatten perm)° flatten ⊒ ⦇[nil, split°]⦈° flatten` — fusion
    (6.4) under the proviso. -/
public theorem qsort_step4 (hsplit : split° ⊑ check' R ≫ join ≫ perm) :
    (⦇(junc (sumCop (dL Unit) (dLAL A)) wrapR split° : (TB.F A).obj (dList A) ⟶ dList A)⦈)°
        ≫ flatten
      ⊑ (inordered R ≫ flatten ≫ perm)° ≫ flatten := by
  refine comp_mono_right (recip_mono (relCata_le_comp (TB.initial A) ?_)) _
  rw [TFmap_comp_junc, junc_comp]
  refine junc_mono _ (le_iff.mpr fun d y h => ?_)
    (by rw [Cat.assoc]; exact split_proviso hsplit)
  cases d
  refine ⟨Tree.nil, rfl, ConsList.wrap (), ?_, h ▸ Perm.refl _⟩
  rw [flatten_graph]; rfl

/-- **Quicksort (B&dM p.154)**: `perm ordered ⊒ ⦇[nil, split°]⦈° flatten`. -/
public theorem quicksort (htrans : ∀ a b c, R a b → R b c → R a c)
    (hsplit : split° ⊑ check' R ≫ join ≫ perm) :
    (⦇(junc (sumCop (dL Unit) (dLAL A)) wrapR split° : (TB.F A).obj (dList A) ⟶ dList A)⦈)°
        ≫ flatten
      ⊑ (perm : dList A ⟶ dList A) ≫ ordered R := by
  refine le_trans ?_ (qsort_step1 R)
  rw [qsort_step2 R htrans, qsort_step3 R]; exact qsort_step4 hsplit

end Freyd.Alg.RelSet.Sort
