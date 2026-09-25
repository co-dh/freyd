/-
  Bird & de Moor, *Algebra of Programming* §9.3  Optimal bracketing (book pp. 230-238).

  A bracketing of `a₁⊕⋯⊕aₙ` is a leaf-labelled binary tree flattening to the given non-empty
  list, and the problem is to find one of least cost.  The specification is `flatten° est(R)`
  with `R ≜ cost ≤ cost°`, and `flatten ≜ ⦇[wrap,cat]⦈ : tree A ⟶ list⁺ A` over
  `AOP.A6_TreeTip`'s `F X = A + X²`.

  What is certified here is the note's `mct-defn` and the second row of `mct-laws`, Theorem 9.1
  IN CONTEXT (`AOP.A9_1.dynamic_programming_context`): there is no thinning step, because no
  decomposition of a list is preferable to another, and the ONLY condition is monotonicity in
  context, `F(R∩(flatten flatten°))h⊑hR` — only trees with the same flattening are ever
  compared.  That is Proposition 9.3 (`AOP.A9_1.monotonicAlg_in_context`) at `H° = flatten`, a
  map, with the note's two displayed equations:

  * (9.5) `[tip,bin] cost=(𝟙+⟨cost,flatten⟩²)g` — `mct_cost_alg`: the cost of a node reads only
    the cost and the flattening of its two subtrees;
  * (9.6) `(𝟙+(≤×𝟙)²)g⊑g≤` — `mct_g_mono`: `g` is monotonic on `≤` in its two cost arguments.

  (9.5) is where `sb` associative is used, through `size=flatten sz` (`size_eq_sz_flatten`):
  the size of a tree depends only on its flattening, so a node's cost can be recovered from the
  two flattenings, which is what makes the context `flatten flatten°` enough.

  NOT DONE, and why:
  * `mct-laws` row 3 (`single→wrap° tip`) is **Proposition 9.1**, dropped for the whole repo by
    the setting-mismatch note at the end of `AOP.A9_1`.
  * rows 5-7 (the array tabulation (9.7)-(9.10)) relate arrays of trees, which the note itself
    marks as outside the relational picture.  Row 4 is NOT one of them and is proved below
    (`mct_prog`): `splits` and `minlist R` are arrows of the same allegory the body is written in.

  B&dM's `Real` is `Int`, as everywhere in this repo's chapter 8-10 case studies.  `list⁺ A` is
  `AOP.A6_ConsList`'s `ConsList A A` — a leaf carries the last element, so the datatype IS the
  non-empty lists, with no side condition to carry.
-/
module

public import AOP.A9_1
public import AOP.A6_TreeTip
public import AOP.A5_6_ListCombinators
-- The fourth row is the PROGRAM: `minlist R` (8.7's list minimum, `AOP.A8_3`) standing in for
-- `est(R)`, and `setify`'s lax naturality (`AOP.A5_7_ListBeads`) shunting `list(f)` to `P(f)`.
public import AOP.A8_3
public import AOP.A5_7_ListBeads

namespace Freyd.Alg.RelSet.Bracket

open Freyd Freyd.Alg Freyd.Alg.RelSet.TT Freyd.Alg.RelSet.ListRel

variable {A S : Type} (st : A → S) (sb : S × S → S) (cb : S × S → Int)

/-! ## `mct-defn` -/

-- **mct-defn**: `list⁺ A` and the object carrying it are `AOP.A5_6_ListCombinators`'s, the one
-- non-empty-list object the `list⁺` relator's action is taken over.

/-- **mct-defn**: `cat`, the append of two non-empty lists. -/
@[expose] public def cat : NEList A → NEList A → NEList A
  | CL.ConsList.wrap a, y => CL.ConsList.cons a y
  | CL.ConsList.cons a x, y => CL.ConsList.cons a (cat x y)

/-- **mct-defn**: the algebra `[wrap,cat] : F(list⁺ A)⟶list⁺ A` whose catamorphism is
    `flatten`. -/
@[expose] public def wrapCatFn : (TFobj A (dNE A)).carrier → NEList A
  | Sum.inl a => CL.ConsList.wrap a
  | Sum.inr (x, y) => cat x y

/-- **mct-defn**: `flatten≜⦇[wrap,cat]⦈ : tree A⟶list⁺ A`, read as the function it is. -/
@[expose] public def flattenFn : Tree A → NEList A
  | Tree.tip a => CL.ConsList.wrap a
  | Tree.bin l r => cat (flattenFn l) (flattenFn r)

/-- **mct-defn**: the catamorphism of `[wrap,cat]` IS `flattenFn`. -/
public theorem flatten_cata : cataR (graph (wrapCatFn (A := A))) = graph flattenFn := by
  apply hom_ext; intro t
  induction t with
  | tip a => exact fun x => Iff.rfl
  | bin l r ihl ihr =>
    intro x
    constructor
    · rintro ⟨xl, xr, hl, hr, hstep⟩
      obtain rfl : xl = flattenFn l := (ihl xl).mp hl
      obtain rfl : xr = flattenFn r := (ihr xr).mp hr
      exact hstep
    · intro (h : x = cat (flattenFn l) (flattenFn r))
      exact ⟨flattenFn l, flattenFn r, (ihl _).mpr rfl, (ihr _).mpr rfl, h⟩

/-- **mct-defn**: `sz`, the size of a non-empty list read directly off it. -/
@[expose] public def szFn (st : A → S) (sb : S × S → S) : NEList A → S
  | CL.ConsList.wrap a => st a
  | CL.ConsList.cons a x => sb (st a, szFn st sb x)

/-- **mct-defn**: `⟨cost,size⟩≜⦇[opt,opb]⦈` with `opt≜⟨zero,st⟩` and
    `opb ((cx,sx),(cy,sy))=(cb (sx,sy)+cx+cy,sb (sx,sy))` — cost alone is not a fold, so it is
    tupled with size. -/
@[expose] public def costSizeFn (st : A → S) (sb : S × S → S) (cb : S × S → Int) :
    Tree A → Int × S
  | Tree.tip a => (0, st a)
  | Tree.bin l r =>
      (cb ((costSizeFn st sb cb l).2, (costSizeFn st sb cb r).2)
          + (costSizeFn st sb cb l).1 + (costSizeFn st sb cb r).1,
        sb ((costSizeFn st sb cb l).2, (costSizeFn st sb cb r).2))

/-- **mct-defn**: `cost`, the first component of the tupled fold. -/
@[expose] public def costFn (st : A → S) (sb : S × S → S) (cb : S × S → Int) (t : Tree A) : Int :=
  (costSizeFn st sb cb t).1

/-- **mct-defn**: `sb` associative — the hypothesis behind `size=flatten sz`. -/
@[expose] public def Assoc (sb : S × S → S) : Prop :=
  ∀ p q r : S, sb (sb (p, q), r) = sb (p, sb (q, r))

public theorem sz_cat (hassoc : Assoc sb) :
    ∀ (x y : NEList A), szFn st sb (cat x y) = sb (szFn st sb x, szFn st sb y)
  | CL.ConsList.wrap a, y => rfl
  | CL.ConsList.cons a x, y => by
    show sb (st a, szFn st sb (cat x y)) = sb (sb (st a, szFn st sb x), szFn st sb y)
    rw [sz_cat hassoc x y, hassoc]

/-- **mct-defn**: `sb` associative, so `size=flatten sz` — the size of a tree depends only on
    its flattening, which is what makes the context `flatten flatten°` enough for (9.5). -/
public theorem size_eq_sz_flatten (hassoc : Assoc sb) :
    ∀ t : Tree A, (costSizeFn st sb cb t).2 = szFn st sb (flattenFn t)
  | Tree.tip a => rfl
  | Tree.bin l r => by
    show sb ((costSizeFn st sb cb l).2, (costSizeFn st sb cb r).2)
      = szFn st sb (cat (flattenFn l) (flattenFn r))
    rw [sz_cat st sb hassoc, size_eq_sz_flatten hassoc l, size_eq_sz_flatten hassoc r]

/-- **mct-defn**: `R≜cost≤cost°`. -/
@[expose] public def R (st : A → S) (sb : S × S → S) (cb : S × S → Int) :
    dTree A ⟶ dTree A := fun t t' => costFn st sb cb t ≤ costFn st sb cb t'

public theorem R_eq :
    R st sb cb = (graph (costFn st sb cb) : dTree A ⟶ (⟨Int⟩ : RelSet.{0})) ≫ leq
      ≫ (graph (costFn st sb cb) : dTree A ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro t t'
  constructor
  · intro h; exact ⟨costFn st sb cb t, rfl, costFn st sb cb t', h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    obtain rfl : m = costFn st sb cb t := hm
    obtain rfl : n = costFn st sb cb t' := hn
    exact hmn

public theorem R_recip_eq :
    (R st sb cb)° = (graph (costFn st sb cb) : dTree A ⟶ (⟨Int⟩ : RelSet.{0})) ≫ geq
      ≫ (graph (costFn st sb cb) : dTree A ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro t t'
  constructor
  · intro h; exact ⟨costFn st sb cb t, rfl, costFn st sb cb t', h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    obtain rfl : m = costFn st sb cb t := hm
    obtain rfl : n = costFn st sb cb t' := hn
    exact hmn

public theorem R_recip_trans : (R st sb cb)° ≫ (R st sb cb)° ⊑ (R st sb cb)° :=
  le_iff.mpr fun t t'' h => by
    obtain ⟨t', h1, h2⟩ := h
    exact Int.le_trans (h2 : costFn st sb cb t'' ≤ costFn st sb cb t')
      (h1 : costFn st sb cb t' ≤ costFn st sb cb t)

public theorem R_recip_refl : 𝟙 (dTree A) ⊑ (R st sb cb)° :=
  le_iff.mpr fun t t' h => by
    obtain rfl : t = t' := h
    exact Int.le_refl _

/-- **mct-defn**: `g≜[zero,(𝟙×sz)² opb π₁]` — the cost of a node computed from the cost and the
    FLATTENING of each subtree. -/
@[expose] public def gFn (st : A → S) (sb : S × S → S) (cb : S × S → Int) :
    (TFobj A (⟨Int × NEList A⟩ : RelSet.{0})).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr (p, q) => cb (szFn st sb p.2, szFn st sb q.2) + p.1 + q.1

/-- The product `Int × list⁺ A` the context bundle `⟨cost,flatten⟩` lands in. -/
@[expose] public abbrev P (A : Type) : RelProd (⟨Int⟩ : RelSet.{0}) (dNE A) :=
  relProd (⟨Int⟩ : RelSet.{0}) (dNE A)

/-- **mct-defn**: `size`, the second component of the tupled fold. -/
@[expose] public def sizeFn (st : A → S) (sb : S × S → S) (cb : S × S → Int) (t : Tree A) : S :=
  (costSizeFn st sb cb t).2

/-- **mct-defn**: `zero`, the cost of a leaf. -/
@[expose] public def zeroFn (_ : A) : Int := 0

/-- **mct-defn**: `opb ((cx,sx),(cy,sy))=(cb (sx,sy)+cx+cy,sb (sx,sy))`, the node half of the
    tupled fold's algebra. -/
@[expose] public def opbFn (sb : S × S → S) (cb : S × S → Int) (p : (Int × S) × (Int × S)) :
    Int × S :=
  (cb (p.1.2, p.2.2) + p.1.1 + p.2.1, sb (p.1.2, p.2.2))

/-- `⟨R,S⟩(U×V)=⟨RU,SV⟩` — a pair followed by a product action acts on each component. -/
public theorem rpair_comp_rprodMap {C A B a' b' : RelSet.{0}} (R : C ⟶ A) (S : C ⟶ B)
    (U : A ⟶ a') (V : B ⟶ b') : rpair R S ≫ rprodMap U V = rpair (R ≫ U) (S ≫ V) :=
  hom_ext fun _ _ => ⟨fun ⟨m, ⟨hR, hS⟩, hU, hV⟩ => ⟨⟨m.1, hR, hU⟩, ⟨m.2, hS, hV⟩⟩,
    fun ⟨⟨y, hR, hU⟩, ⟨z, hS, hV⟩⟩ => ⟨(y, z), ⟨hR, hS⟩, hU, hV⟩⟩

/-- A pair of graphs is the graph of the paired function. -/
public theorem rpair_graph {C A B : RelSet.{0}} (f : C.carrier → A.carrier)
    (g : C.carrier → B.carrier) :
    rpair (graph f) (graph g)
      = (graph (fun x => (f x, g x)) : C ⟶ (⟨A.carrier × B.carrier⟩ : RelSet.{0})) :=
  hom_ext fun _ _ => ⟨fun h => Prod.ext h.1 h.2,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

set_option hygiene false in
local notation "costG" => (graph (costFn st sb cb) : dTree A ⟶ (⟨Int⟩ : RelSet.{0}))
set_option hygiene false in
local notation "sizeG" => (graph (sizeFn st sb cb) : dTree A ⟶ (⟨S⟩ : RelSet.{0}))
set_option hygiene false in
local notation "szG" => (graph (szFn st sb) : dNE A ⟶ (⟨S⟩ : RelSet.{0}))
set_option hygiene false in
local notation "flattenG" => (graph flattenFn : dTree A ⟶ dNE A)
set_option hygiene false in
local notation "zeroG" => (graph (zeroFn (A := A)) : dA A ⟶ (⟨Int⟩ : RelSet.{0}))
set_option hygiene false in
local notation "opbG" => (graph (opbFn sb cb)
  : (⟨(Int × S) × (Int × S)⟩ : RelSet.{0}) ⟶ (⟨Int × S⟩ : RelSet.{0}))
set_option hygiene false in
local notation "outlG" => (graph (Prod.fst : Int × S → Int)
  : (⟨Int × S⟩ : RelSet.{0}) ⟶ (⟨Int⟩ : RelSet.{0}))
set_option hygiene false in
local notation "binG" => (graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2)
  : (⟨Tree A × Tree A⟩ : RelSet.{0}) ⟶ dTree A)
set_option hygiene false in
local notation "tipG" => (graph (Tree.tip (A := A)) : dA A ⟶ dTree A)
set_option hygiene false in
local notation "gG" => (graph (gFn st sb cb)
  : TFobj A (⟨Int × NEList A⟩ : RelSet.{0}) ⟶ (⟨Int⟩ : RelSet.{0}))

/-- **mct-defn**: `g≜[zero,(𝟙×sz)² opb π₁]` — the note's definition of `g` is `gFn`. -/
public theorem g_eq :
    gG = junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
      (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
        ≫ opbG ≫ outlG) := by
  apply hom_ext; intro u n
  cases u with
  | inl a => rw [ListRel.junc_sum_inl]; exact Iff.rfl
  | inr p =>
    rw [ListRel.junc_sum_inr]
    constructor
    · intro h
      exact ⟨((p.1.1, szFn st sb p.1.2), (p.2.1, szFn st sb p.2.2)), ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
        _, rfl, h⟩
    · rintro ⟨m, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, m', hm', hn⟩
      obtain ⟨⟨c1, s1⟩, ⟨c2, s2⟩⟩ := m
      obtain rfl : p.1.1 = c1 := h1
      obtain rfl : s1 = szFn st sb p.1.2 := h2
      obtain rfl : p.2.1 = c2 := h3
      obtain rfl : s2 = szFn st sb p.2.2 := h4
      obtain rfl := hm'
      exact hn

/-! ## `mct-laws` — Proposition 9.3's two equations -/

/-- (9.5), first step: definition of `g`, then coproducts and products —
    `F(⟨cost,flatten⟩)g = [zero,⟨cost,flatten sz⟩² opb π₁]`. -/
public theorem mct_cost_alg_step1 :
    (TT.F A).map ((P A).pair costG flattenG) ≫ gG
      = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
          (rprodMap (rpair costG (flattenG ≫ szG)) (rpair costG (flattenG ≫ szG))
            ≫ opbG ≫ outlG) := by
  rw [g_eq]
  refine (Fmap_comp_junc _ _ _).trans ?_
  rw [pair_eq_rpair, ← Cat.assoc (rprodMap _ _) (rprodMap _ _), rprodMap_comp,
    rpair_comp_rprodMap, Cat.comp_id]

/-- (9.5), second step: `size=flatten sz` (`size_eq_sz_flatten`, where `sb` associative enters). -/
public theorem mct_cost_alg_step2 (hassoc : Assoc sb) :
    junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
        (rprodMap (rpair costG (flattenG ≫ szG)) (rpair costG (flattenG ≫ szG)) ≫ opbG ≫ outlG)
      = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
          (rprodMap (rpair costG sizeG) (rpair costG sizeG) ≫ opbG ≫ outlG) := by
  have h : flattenG ≫ szG = sizeG := by
    rw [graph_comp]
    exact congrArg graph (funext fun t => (size_eq_sz_flatten st sb cb hassoc t).symm)
  rw [h]

/-- (9.5), third step: `⟨cost,size⟩≜⦇[opt,opb]⦈`, at its node: `bin⟨cost,size⟩=⟨cost,size⟩² opb`. -/
public theorem mct_cost_alg_step3 :
    junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
        (rprodMap (rpair costG sizeG) (rpair costG sizeG) ≫ opbG ≫ outlG)
      = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
          (binG ≫ rpair costG sizeG ≫ outlG) := by
  simp only [rpair_graph, graph_comp]
  refine congrArg (junc _ _) (hom_ext fun p n => ⟨?_, fun h => ⟨((costFn st sb cb p.1,
    sizeFn st sb cb p.1), (costFn st sb cb p.2, sizeFn st sb cb p.2)), ⟨rfl, rfl⟩, h⟩⟩)
  rintro ⟨⟨m1, m2⟩, ⟨h1, h2⟩, h⟩
  subst h1 h2
  exact h

/-- (9.5), fourth step: `tip cost=zero`, and `⟨cost,size⟩π₁=cost`. -/
public theorem mct_cost_alg_step4 :
    junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG (binG ≫ rpair costG sizeG ≫ outlG)
      = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) (tipG ≫ costG) (binG ≫ costG) := by
  simp only [rpair_graph, graph_comp]
  rfl

/-- (9.5), fifth step: coproducts, `[tip cost,bin cost]=[tip,bin] cost`. -/
public theorem mct_cost_alg_step5 :
    junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) (tipG ≫ costG) (binG ≫ costG)
      = graph con ≫ costG := by
  rw [con_eq_junc, junc_comp]

/-- **mct-laws** (9.5): `(𝟙+⟨cost,flatten⟩²)g=[tip,bin] cost` — the cost of a node reads only
    the cost and the flattening of its two subtrees.  `sb` associative enters at step 2, through
    `size=flatten sz`. -/
public theorem mct_cost_alg (hassoc : Assoc sb) :
    (TT.F A).map ((P A).pair costG flattenG) ≫ gG = graph con ≫ costG :=
  calc (TT.F A).map ((P A).pair costG flattenG) ≫ gG
      _ = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
          (rprodMap (rpair costG (flattenG ≫ szG)) (rpair costG (flattenG ≫ szG))
            ≫ opbG ≫ outlG) := mct_cost_alg_step1 st sb cb
      _ = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
          (rprodMap (rpair costG sizeG) (rpair costG sizeG) ≫ opbG ≫ outlG) :=
        mct_cost_alg_step2 st sb cb hassoc
      _ = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) zeroG
          (binG ≫ rpair costG sizeG ≫ outlG) := mct_cost_alg_step3 st sb cb
      _ = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) (tipG ≫ costG) (binG ≫ costG) :=
        mct_cost_alg_step4 st sb cb
      _ = graph con ≫ costG := mct_cost_alg_step5 st sb cb

/-- (9.6), first step: definition of `g` — `F(≤×𝟙)g=[zero,(≤×sz)² opb π₁]`. -/
public theorem mct_g_mono_step1 :
    (TT.F A).map (prodMap (P A) (P A) leq (𝟙 (dNE A))) ≫ gG
      = junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
          (rprodMap (rprodMap leq szG) (rprodMap leq szG) ≫ opbG ≫ outlG) := by
  rw [g_eq]
  refine (Fmap_comp_junc _ _ _).trans ?_
  rw [prodMap_eq_rprodMap, ← Cat.assoc (rprodMap _ _) (rprodMap _ _), rprodMap_comp,
    rprodMap_comp, Cat.comp_id, Cat.id_comp]
  rfl

/-- (9.6), second step: definition of `opb`, and `+` monotonic — `(≤×sz)² opb π₁⊑(𝟙×sz)² opb π₁≤`. -/
public theorem mct_g_mono_step2 :
    junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
        (rprodMap (rprodMap leq szG) (rprodMap leq szG) ≫ opbG ≫ outlG)
      ⊑ junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
          (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
            ≫ opbG ≫ outlG ≫ leq) := by
  refine junc_mono _ (le_refl _) (le_iff.mpr fun p n h => ?_)
  obtain ⟨m, ⟨⟨hc1, hs1⟩, ⟨hc2, hs2⟩⟩, m', hm', hn⟩ := h
  obtain ⟨⟨c1, s1⟩, ⟨c2, s2⟩⟩ := m
  obtain rfl : s1 = szFn st sb p.1.2 := hs1
  obtain rfl : s2 = szFn st sb p.2.2 := hs2
  obtain rfl := hm'
  obtain rfl := hn
  exact ⟨((p.1.1, szFn st sb p.1.2), (p.2.1, szFn st sb p.2.2)), ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
    _, rfl, _, rfl,
    Int.add_le_add (Int.add_le_add (Int.le_refl _) (hc1 : p.1.1 ≤ c1)) (hc2 : p.2.1 ≤ c2)⟩

/-- (9.6), third step: `≤` reflexive (`zero⊑zero ≤`), then coproducts. -/
public theorem mct_g_mono_step3 :
    junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
        (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
          ≫ opbG ≫ outlG ≫ leq)
      ⊑ junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
          (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
            ≫ opbG ≫ outlG) ≫ leq := by
  rw [junc_comp, Cat.assoc, Cat.assoc]
  exact junc_mono _ (le_iff.mpr fun _ n h => ⟨n, h, Int.le_refl n⟩) (le_refl _)

/-- (9.6), fourth step: definition of `g`. -/
public theorem mct_g_mono_step4 :
    junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
        (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
          ≫ opbG ≫ outlG) ≫ leq
      = gG ≫ leq := by
  rw [g_eq]

/-- **mct-laws** (9.6): `(𝟙+(≤×𝟙)²)g⊑g≤` — `g` is monotonic on `≤` in its two cost arguments,
    the flattenings being held fixed. -/
public theorem mct_g_mono :
    (TT.F A).map (prodMap (P A) (P A) leq (𝟙 (dNE A))) ≫ gG ⊑ gG ≫ leq :=
  calc (TT.F A).map (prodMap (P A) (P A) leq (𝟙 (dNE A))) ≫ gG
      _ = junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
          (rprodMap (rprodMap leq szG) (rprodMap leq szG) ≫ opbG ≫ outlG) :=
        mct_g_mono_step1 st sb cb
      _ ⊑ junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
          (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
            ≫ opbG ≫ outlG ≫ leq) := mct_g_mono_step2 st sb cb
      _ ⊑ junc (sumCop (dA A) (⟨(Int × NEList A) × (Int × NEList A)⟩ : RelSet.{0})) zeroG
          (rprodMap (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG) (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) szG)
            ≫ opbG ≫ outlG) ≫ leq := mct_g_mono_step3 st sb cb
      _ = gG ≫ leq := mct_g_mono_step4 st sb cb

/-- (9.6) at the mirrored order, which is the one Theorem 9.1 consumes. -/
public theorem mct_g_mono_geq :
    (TT.F A).map (prodMap (P A) (P A) geq (𝟙 (dNE A))) ≫ graph (gFn st sb cb)
      ⊑ graph (gFn st sb cb) ≫ geq := by
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun u n h => ?_
  obtain ⟨w, hw, hn⟩ := h
  cases u with
  | inl a =>
    cases w with
    | inl a' => exact ⟨0, rfl, Int.le_of_eq (hn : n = 0)⟩
    | inr _ => exact hw.elim
  | inr p =>
    cases w with
    | inl _ => exact hw.elim
    | inr q =>
      obtain ⟨⟨plc, plf⟩, ⟨prc, prf⟩⟩ := p
      obtain ⟨⟨qlc, qlf⟩, ⟨qrc, qrf⟩⟩ := q
      obtain ⟨⟨hc1, hf1⟩, ⟨hc2, hf2⟩⟩ := hw
      obtain rfl : plf = qlf := hf1
      obtain rfl : prf = qrf := hf2
      refine ⟨cb (szFn st sb plf, szFn st sb prf) + plc + prc, rfl, ?_⟩
      show n ≤ cb (szFn st sb plf, szFn st sb prf) + plc + prc
      rw [(hn : n = cb (szFn st sb plf, szFn st sb prf) + qlc + qrc)]
      exact Int.add_le_add (Int.add_le_add (Int.le_refl _) (hc1 : qlc ≤ plc)) (hc2 : qrc ≤ prc)

/-- **mct-laws**, second row: monotonicity IN CONTEXT `F(R∩(flatten flatten°))h⊑hR` —
    Proposition 9.3 at `H°=flatten`, a map, with (9.5) and (9.6).  Only trees with the same
    flattening are ever compared. -/
public theorem mct_mono (hassoc : Assoc sb) :
    (TT.F A).map (R st sb cb ∩ (graph flattenFn ≫ (graph (flattenFn (A := A)))°)) ≫ graph con
      ⊑ graph con ≫ R st sb cb :=
  monotonicAlg_in_context (graph_map (costFn st sb cb)) (graph_map flattenFn).2 (R_eq st sb cb)
    (mct_cost_alg st sb cb hassoc).symm (mct_g_mono st sb cb)

/-- The same at the mirrored order, which is what `dynamic_programming_context` consumes. -/
public theorem mct_mono_recip (hassoc : Assoc sb) :
    (TT.F A).map ((R st sb cb)° ∩ (graph flattenFn ≫ (graph (flattenFn (A := A)))°)) ≫ graph con
      ⊑ graph con ≫ (R st sb cb)° :=
  monotonicAlg_in_context (graph_map (costFn st sb cb)) (graph_map flattenFn).2
    (R_recip_eq st sb cb) (mct_cost_alg st sb cb hassoc).symm (mct_g_mono_geq st sb cb)

/-- **mct-laws**, second row (B&dM p.231): a least-cost bracketing is the least fixed point of
    `(μX : [wrap,cat]° P([tip,(X×X)bin]) est(R))` — split the list in every way, bracket both
    halves, join.  Theorem 9.1 IN CONTEXT: the one condition is `mct_mono_recip`, and there is
    no thinning step because no decomposition of a list is preferable to another.
    `H = ⦇[tip,bin]⦈·⦇[wrap,cat]⦈°` collapses to `flatten°` by reflection
    (`AOP.A6_TreeTip.cataR_con`). -/
public theorem mct_laws (hassoc : Assoc sb) :
    mu (fun X : dNE A ⟶ dTree A =>
        Λ (Allegory.recip (graph wrapCatFn : (TT.F A).obj (dNE A) ⟶ dNE A))
          ≫ powerRel ((TT.F A).map X ≫ graph (con (A := A))) ≫ est (R st sb cb))
      ⊑ Λ (Allegory.recip (graph flattenFn : dTree A ⟶ dNE A)) ≫ est (R st sb cb) := by
  have hH : (relCata (F := TT.F A) (graph (wrapCatFn (A := A))))°
        ≫ relCata (F := TT.F A) (I := initial A) (graph (con (A := A)))
      = Allegory.recip (graph flattenFn : dTree A ⟶ dNE A) := by
    rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, flatten_cata]
    exact Cat.comp_id _
  have key := dynamic_programming_context (F := TT.F A) (F_preservesRecip A) (initial A)
    (h := graph (con (A := A))) (T := graph (wrapCatFn (A := A))) (R := R st sb cb)
    (graph_map con)
    (by simp only [H]; rw [hH, Allegory.recip_recip]; exact mct_mono_recip st sb cb hassoc)
    (R_recip_trans st sb cb) (R_recip_refl st sb cb)
  simp only [H] at key; rwa [hH] at key

/-- `cat` ALWAYS RETURNS A `cons`: joining two non-empty lists never gives a one-element list.
    That is the disjointness the summand law asks for — at a list `cat` reaches, `[wrap,cat]`
    reaches it through the `cat` summand and no other. -/
public theorem cat_ne_wrap (x y : NEList A) (a : A) : cat x y ≠ CL.ConsList.wrap a := by
  cases x with
  | wrap b => exact fun h => nomatch (show CL.ConsList.cons b y = CL.ConsList.wrap a from h)
  | cons b x =>
    exact fun h => nomatch (show CL.ConsList.cons b (cat x y) = CL.ConsList.wrap a from h)

/-- **mct-laws**, third row: the `cat` ARM of the body, `(cat°)%∋ P((X×X)bin)est(R)` refining
    `([wrap,cat]°)%∋ P([tip,(X×X)bin])est(R)`.  Proposition 9.1 at one summand
    (`RelSet.pow_summand_le`) along `ι ≜ inr`, its disjointness discharged by `cat_ne_wrap`; the
    summand relator is the SQUARE `X ↦ X×X`, which is what makes the arm's algebra `(X×X)bin`. -/
public theorem mct_branch (X : dNE A ⟶ dTree A) :
    Λ ((graph (fun p : NEList A × NEList A => cat p.1 p.2)
          : (⟨NEList A × NEList A⟩ : RelSet.{0}) ⟶ dNE A)°)
        ≫ powerRel (rprodMap X X
            ≫ graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2)) ≫ est (R st sb cb)
      ⊑ Λ (Allegory.recip (graph wrapCatFn : (TT.F A).obj (dNE A) ⟶ dNE A))
          ≫ powerRel ((TT.F A).map X ≫ graph (con (A := A))) ≫ est (R st sb cb) := by
  -- The square relator's action IS the pointwise `X×X` (`prodMap_eq_rprodMap`), so the arm the
  -- note draws and the summand the law quantifies over are the same arrow.
  have hmap : (Relator.prod (Relator.idRelator RelSet.{0})
      (Relator.idRelator RelSet.{0})).map X = rprodMap X X := prodMap_eq_rprodMap X X
  rw [← hmap]
  refine RelSet.pow_summand_le (A := dNE A) (B := dTree A) (F := TT.F A)
    (Fᵢ := Relator.prod (Relator.idRelator RelSet.{0}) (Relator.idRelator RelSet.{0}))
    Sum.inr (graph_map _) ?_ ?_ ?_
  · exact fun _ _ => Iff.rfl
  · intro p z
    rw [hmap, Fmap_comp_con X]
    exact (junc_sum_inr _ _ p z).symm
  · rintro (a | q) p y hp hw
    · exact absurd (hp.symm.trans hw) (cat_ne_wrap p.1 p.2 a)
    · exact ⟨q, rfl⟩

/-! ## `mct-laws`, fourth row: the recursive program -/

/-- `cons a` on the LEFT half of every split — what `splits` does to the splits of the tail when
    one more element arrives at the front. -/
@[expose] public def consSplits (a : A) :
    CL.ConsList Unit (NEList A × NEList A) → CL.ConsList Unit (NEList A × NEList A)
  | CL.ConsList.wrap u => CL.ConsList.wrap u
  | CL.ConsList.cons p ps => CL.ConsList.cons (CL.ConsList.cons a p.1, p.2) (consSplits a ps)

/-- **mct-laws**, fourth row: `splits≜⟨inits⁺,tails⁺⟩ zip`, every way of cutting a non-empty list
    into two non-empty pieces.  The zip is performed as the list is built — `inits⁺` and `tails⁺`
    are only ever paired — so `splits` is one structural recursion with no side condition. -/
@[expose] public def splitsFn : NEList A → CL.ConsList Unit (NEList A × NEList A)
  | CL.ConsList.wrap _ => CL.ConsList.wrap ()
  | CL.ConsList.cons a x => CL.ConsList.cons (CL.ConsList.wrap a, x) (consSplits a (splitsFn x))

/-- `splits : list⁺ A⟶[list⁺ A×list⁺ A]`, the map the note's panel draws. -/
@[expose] public def splits : dNE A ⟶ dList (NEList A × NEList A) := graph splitsFn

public theorem inlistP_consSplits (a : A) (p : NEList A × NEList A) :
    ∀ ps : CL.ConsList Unit (NEList A × NEList A),
      inlistP (consSplits a ps) p ↔ ∃ q, p = (CL.ConsList.cons a q.1, q.2) ∧ inlistP ps q := by
  intro ps
  induction ps with
  | wrap _ => exact ⟨fun (h : False) => h.elim, fun ⟨_, _, hq⟩ => (hq : False).elim⟩
  | cons q qs ih =>
      show (p = (CL.ConsList.cons a q.1, q.2) ∨ inlistP (consSplits a qs) p) ↔ _
      rw [ih]
      constructor
      · rintro (h | ⟨r, hr, hm⟩)
        · exact ⟨q, h, Or.inl rfl⟩
        · exact ⟨r, hr, Or.inr hm⟩
      · rintro ⟨r, hr, (rfl | hm)⟩
        · exact Or.inl hr
        · exact Or.inr ⟨r, hr, hm⟩

/-- `splits` LISTS the splits: `(u,v)` occurs in `splits x` exactly when `cat u v = x`.  This is
    the row's content — `splits` implements `cat°` — and the induction is the one `cat` itself
    runs on, with `cat_ne_wrap` (Proposition 9.1) closing the singleton. -/
public theorem mem_splits : ∀ (x : NEList A) (p : NEList A × NEList A),
    inlistP (splitsFn x) p ↔ x = cat p.1 p.2 := by
  intro x
  induction x with
  | wrap b =>
      exact fun p => ⟨fun (h : False) => h.elim, fun h => (cat_ne_wrap p.1 p.2 b h.symm).elim⟩
  | cons a x ih =>
      intro p
      show (p = (CL.ConsList.wrap a, x) ∨ inlistP (consSplits a (splitsFn x)) p) ↔ _
      rw [inlistP_consSplits]
      constructor
      · rintro (rfl | ⟨q, rfl, hm⟩)
        · rfl
        · exact congrArg (CL.ConsList.cons a) ((ih q).mp hm)
      · intro h
        obtain ⟨u, v⟩ := p
        cases u with
        | wrap b =>
            left
            injection h with hab hxv
            subst hab; subst hxv; rfl
        | cons b u =>
            right
            refine ⟨(u, v), ?_, ?_⟩
            · injection h with hab _
              subst hab; rfl
            · injection h with _ hxv
              exact (ih (u, v)).mpr hxv

/-- **mct-laws**, fourth row (B&dM p.232): `splits list((mct×mct)bin)minlist R` refines the body
    `(cat°)%∋ P((X×X)bin)est(R)` of the fixed point — `splits` implements `cat°` (`mem_splits`)
    and `minlist R` implements `est(R)`, the list standing in for the set it `setify`s to.  The
    one inequality is `CL.list_comp_minlist_le`, `setify`'s lax naturality: a list of `f`-images of
    the splits has, as a SET, an `P(f)`-image of the set of splits.  Exponential,
    since the segments of one list overlap — the tabulation (9.7)-(9.10) is what fixes that, and
    it relates arrays of trees, outside the relational picture. -/
public theorem mct_prog (mct : dNE A ⟶ dTree A) :
    splits ≫ list (rprodMap mct mct ≫ graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2))
        ≫ CL.minlist (R st sb cb)
      ⊑ Λ ((graph (fun p : NEList A × NEList A => cat p.1 p.2)
              : (⟨NEList A × NEList A⟩ : RelSet.{0}) ⟶ dNE A)°)
          ≫ powerRel (rprodMap mct mct ≫ graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2))
          ≫ est (R st sb cb) := by
  have hmem : ∀ x : NEList A, (fun p => inlistP (splitsFn x) p)
      = fun p : NEList A × NEList A => x = cat p.1 p.2 :=
    fun x => funext fun p => propext (mem_splits x p)
  have hsplit : splits ≫ setify
      = Λ ((graph (fun p : NEList A × NEList A => cat p.1 p.2)
              : (⟨NEList A × NEList A⟩ : RelSet.{0}) ⟶ dNE A)°) := by
    rw [Λ_eq_classifier]
    funext x S
    refine propext ⟨?_, ?_⟩
    · rintro ⟨_, rfl, hS⟩
      exact (hS : S = fun p => inlistP (splitsFn x) p).trans (hmem x)
    · intro hS
      exact ⟨splitsFn x, rfl,
        (hS : S = fun p => x = cat p.1 p.2).trans (hmem x).symm⟩
  rw [← hsplit, Cat.assoc]
  exact comp_mono_left splits (CL.list_comp_minlist_le _ _)

/-! ## What the panels' beads claim: the naturality of `splits`, `bin` and `flatten°` -/

/-- `list⁺(R)` respects `cat`: a related list splits exactly where the original does. -/
public theorem nelistP_cat {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x u : NEList A) (y : NEList B),
      nelistP R (cat x u) y ↔ ∃ v w, y = cat v w ∧ nelistP R x v ∧ nelistP R u w := by
  intro x
  induction x with
  | wrap a =>
      intro u y
      constructor
      · intro h
        cases y with
        | wrap _ => exact h.elim
        | cons b z => exact ⟨CL.ConsList.wrap b, z, rfl, h.1, h.2⟩
      · rintro ⟨v, w, rfl, hv, hw⟩
        cases v with
        | wrap _ => exact ⟨hv, hw⟩
        | cons _ _ => exact hv.elim
  | cons a x ih =>
      intro u y
      constructor
      · intro h
        cases y with
        | wrap _ => exact h.elim
        | cons b z =>
            obtain ⟨v, w, rfl, hv, hw⟩ := (ih u z).mp h.2
            exact ⟨CL.ConsList.cons b v, w, rfl, ⟨h.1, hv⟩, hw⟩
      · rintro ⟨v, w, rfl, hv, hw⟩
        cases v with
        | wrap _ => exact hv.elim
        | cons b v => exact ⟨hv.1, (ih u (cat v w)).mpr ⟨v, w, rfl, hv.2, hw⟩⟩

/-- **`[wrap,cat]` IS STRICTLY NATURAL** — the initial algebra read lane by lane: the source is the
    coproduct `A + [A]⁺×[A]⁺`, whose leaf arm is the object itself and whose pair arm is
    `list⁺(R)×list⁺(R)`.  The leaf arm is `wrap`, the pair arm is `nelistP_cat`. -/
public theorem wrapCat_strictNatural :
    StrictNatural nelistRelator
      (Relator.sum (Relator.idRelator RelSet.{0})
        (Relator.prod nelistRelator nelistRelator))
      (fun a => graph (wrapCatFn (A := a.carrier))) := by
  intro a b R
  rw [show (Relator.sum (Relator.idRelator RelSet.{0})
        (Relator.prod nelistRelator nelistRelator)).map R
      = sumMap (sumCop a ⟨(dNE a.carrier).carrier × (dNE a.carrier).carrier⟩)
          (sumCop b ⟨(dNE b.carrier).carrier × (dNE b.carrier).carrier⟩)
          R (rprodMap (nelist R) (nelist R)) from prodMap_eq_rprodMap _ _ ▸ rfl]
  apply hom_ext
  intro u y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨wrapCatFn u, rfl, ?_⟩
    cases hw with
    | inl h => obtain ⟨e, rfl, e', he, rfl⟩ := h; exact he
    | inr h =>
      obtain ⟨p, rfl, q, hq, rfl⟩ := h
      obtain ⟨p₁, p₂⟩ := p; obtain ⟨q₁, q₂⟩ := q
      exact (nelistP_cat R p₁ p₂ (cat q₁ q₂)).mpr ⟨q₁, q₂, rfl, hq.1, hq.2⟩
  · rintro ⟨x, rfl, hx⟩
    cases u with
    | inl e =>
      cases y with
      | wrap e' => exact ⟨Sum.inl e', Or.inl ⟨e, rfl, e', hx, rfl⟩, rfl⟩
      | cons _ _ => exact hx.elim
    | inr p =>
      obtain ⟨p₁, p₂⟩ := p
      obtain ⟨v, w, rfl, hv, hw⟩ := (nelistP_cat R p₁ p₂ y).mp hx
      exact ⟨Sum.inr (v, w), Or.inr ⟨(p₁, p₂), rfl, (v, w), ⟨hv, hw⟩, rfl⟩, rfl⟩

/-- `[wrap,cat]°`, the bead the §9.3 picture carries: both lanes preserve `°` on a tabular
    allegory, so the square turns round. -/
public theorem wrapCat_recip_strictNatural :
    StrictNatural
      (Relator.sum (Relator.idRelator RelSet.{0})
        (Relator.prod nelistRelator nelistRelator))
      nelistRelator
      (fun a => (graph (wrapCatFn (A := a.carrier)))°) :=
  strictNatural_recip (Relator.preservesRecip_of_tabular _)
    (Relator.preservesRecip_of_tabular _) wrapCat_strictNatural

/-- **mct-defn**: `flatten` commutes with relabelling — `tree(R) flatten = flatten list⁺(R)`,
    pointwise: a tree's flattening is related exactly to the flattenings of the related trees. -/
public theorem flattenP_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (t : Tree A) (y : NEList B),
      nelistP R (flattenFn t) y ↔ ∃ u, treeP R t u ∧ y = flattenFn u := by
  intro t
  induction t with
  | tip a =>
      intro y
      constructor
      · intro h
        cases y with
        | wrap b => exact ⟨Tree.tip b, h, rfl⟩
        | cons _ _ => exact h.elim
      · rintro ⟨u, hu, rfl⟩
        cases u with
        | tip _ => exact hu
        | bin _ _ => exact hu.elim
  | bin l r ihl ihr =>
      intro y
      constructor
      · intro h
        obtain ⟨v, w, rfl, hv, hw⟩ := (nelistP_cat R (flattenFn l) (flattenFn r) y).mp h
        obtain ⟨ul, hul, rfl⟩ := (ihl v).mp hv
        obtain ⟨ur, hur, rfl⟩ := (ihr w).mp hw
        exact ⟨Tree.bin ul ur, ⟨hul, hur⟩, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        cases u with
        | tip _ => exact hu.elim
        | bin ul ur =>
            exact (nelistP_cat R (flattenFn l) (flattenFn r) _).mpr
              ⟨flattenFn ul, flattenFn ur, rfl, (ihl _).mpr ⟨ul, hu.1, rfl⟩,
                (ihr _).mpr ⟨ur, hu.2, rfl⟩⟩

/-- **mct-laws**, second row: the `flatten°` bead is STRICTLY natural,
    `list⁺(R) flatten° = flatten° tree(R)` — the converse of `flatten`'s own square, read at `R°`
    through `list⁺` and `tree` preserving converse. -/
public theorem flatten_recip_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ (graph (flattenFn (A := B)))° = (graph (flattenFn (A := A)))° ≫ tree R := by
  apply hom_ext
  intro x t
  constructor
  · rintro ⟨y, hxy, rfl⟩
    obtain ⟨u, hu, hx⟩ := (flattenP_natural R° t x).mp ((nelistP_recip R (flattenFn t) x).mpr hxy)
    exact ⟨u, hx, (treeP_recip R t u).mp hu⟩
  · rintro ⟨s, rfl, hst⟩
    exact ⟨flattenFn t, (flattenP_natural R s (flattenFn t)).mpr ⟨t, hst, rfl⟩, rfl⟩

/-- **mct-laws**, fourth row: the `bin` bead is the initial algebra's constructor, so its square
    is an EQUALITY — relating the two subtrees is relating the node they build. -/
public theorem bin_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    rprodMap (tree R) (tree R) ≫ graph (fun p : Tree B × Tree B => Tree.bin p.1 p.2)
      = graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2) ≫ tree R := by
  apply hom_ext
  intro p t
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Tree.bin p.1 p.2, rfl, hq.1, hq.2⟩
  · rintro ⟨u, rfl, h⟩
    cases t with
    | tip _ => exact h.elim
    | bin t₁ t₂ => exact ⟨(t₁, t₂), ⟨h.1, h.2⟩, rfl⟩

/-- `consSplits` transports along `list⁺(R)`: one more element at the front of both lists leaves
    the two split lists position for position related. -/
public theorem listP_consSplits {B : Type} {R : CL.dE A ⟶ CL.dE B} {a : A} {b : B} (hab : R a b) :
    ∀ (ps : CL.ConsList Unit (NEList A × NEList A)) (qs : CL.ConsList Unit (NEList B × NEList B)),
      listP (rprodMap (nelist R) (nelist R)) ps qs →
        listP (rprodMap (nelist R) (nelist R)) (consSplits a ps) (consSplits b qs)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, h => h
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ ps, CL.ConsList.cons _ qs, h =>
      ⟨⟨⟨hab, h.1.1⟩, h.1.2⟩, listP_consSplits hab ps qs h.2⟩

/-- **mct-laws**, fourth row: the `splits` bead is LAX natural — relating the elements relates the
    two split lists position by position, so every split of the related list is the related split.
    Only `⊑`: the other inclusion would have to rebuild a list from an arbitrary list of pairs. -/
public theorem splits_lax_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ splits (A := B) ⊑ splits (A := A) ≫ list (rprodMap (nelist R) (nelist R)) := by
  have key : ∀ (x : NEList A) (y : NEList B), nelistP R x y →
      listP (rprodMap (nelist R) (nelist R)) (splitsFn x) (splitsFn y) := by
    intro x
    induction x with
    | wrap a =>
        intro y hxy
        cases y with
        | wrap _ => trivial
        | cons _ _ => exact hxy.elim
    | cons a x ih =>
        intro y hxy
        cases y with
        | wrap _ => exact hxy.elim
        | cons b y =>
            exact ⟨⟨hxy.1, hxy.2⟩, listP_consSplits hxy.1 _ _ (ih y hxy.2)⟩
  rw [le_iff]
  rintro x zs ⟨y, hxy, rfl⟩
  exact ⟨splitsFn x, rfl, key x y hxy⟩

-- printing-only: the note's bead is `R`, the order the bracketing is optimised under.  The leaf
-- map, the split cost and the combine cost are the section's context, not part of the name.
open Lean PrettyPrinter in
@[app_unexpander R] public meta def unexpandBracketR : Unexpander
  | _ => `($(mkIdent `R))

end Freyd.Alg.RelSet.Bracket
