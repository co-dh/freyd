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
-- `bmin`, B&dM's binary minimum, from which `minlist(R)` is folded.
public import AOP.A9_2_Edit

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

/-- **mct-defn**: `g`, the relation drawn as one bead — the graph of `gFn`, whose two summands a
    picture would otherwise open. -/
@[expose] public def gR (st : A → S) (sb : S × S → S) (cb : S × S → Int) :
    (TT.F A).obj (⟨Int × NEList A⟩ : RelSet.{0}) ⟶ (⟨Int⟩ : RelSet.{0}) :=
  graph (gFn st sb cb)

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
local notation "gG" => (gR st sb cb
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
      = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) tipG binG ≫ costG := by
  exact (junc_comp _ _ _ _).symm

/-- **mct-laws** (9.5): `(𝟙+⟨cost,flatten⟩²)g=[tip,bin] cost` — the cost of a node reads only
    the cost and the flattening of its two subtrees.  `sb` associative enters at step 2, through
    `size=flatten sz`. -/
public theorem mct_cost_alg (hassoc : Assoc sb) :
    (TT.F A).map ((P A).pair costG flattenG) ≫ gG = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) tipG binG ≫ costG :=
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
      _ = junc (sumCop (dA A) (⟨Tree A × Tree A⟩ : RelSet.{0})) tipG binG ≫ costG := mct_cost_alg_step5 st sb cb

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
    ((mct_cost_alg st sb cb hassoc).trans (congrArg (· ≫ _) con_eq_junc.symm)).symm (mct_g_mono st sb cb)

/-- The same at the mirrored order, which is what `dynamic_programming_context` consumes. -/
public theorem mct_mono_recip (hassoc : Assoc sb) :
    (TT.F A).map ((R st sb cb)° ∩ (graph flattenFn ≫ (graph (flattenFn (A := A)))°)) ≫ graph con
      ⊑ graph con ≫ (R st sb cb)° :=
  monotonicAlg_in_context (graph_map (costFn st sb cb)) (graph_map flattenFn).2
    (R_recip_eq st sb cb) ((mct_cost_alg st sb cb hassoc).trans (congrArg (· ≫ _) con_eq_junc.symm)).symm (mct_g_mono_geq st sb cb)

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

/-- **`[tip,bin]` IS STRICTLY NATURAL** — the constructors of `tree`, read lane by lane: the leaf
    arm relates two tips exactly when `R` relates their labels, the node arm is `bin_natural`. -/
public theorem tipBin_strictNatural :
    StrictNatural treeRelator
      (Relator.sum (Relator.idRelator RelSet.{0}) (Relator.prod treeRelator treeRelator))
      (fun a => junc (sumCop a (⟨Tree a.carrier × Tree a.carrier⟩ : RelSet.{0}))
        (graph (Tree.tip (A := a.carrier)) : a ⟶ dTree a.carrier)
        (graph (fun p : Tree a.carrier × Tree a.carrier => Tree.bin p.1 p.2)
          : (⟨Tree a.carrier × Tree a.carrier⟩ : RelSet.{0}) ⟶ dTree a.carrier)) := by
  intro a b R
  rw [show (Relator.sum (Relator.idRelator RelSet.{0})
        (Relator.prod treeRelator treeRelator)).map R
      = sumMap (sumCop a ⟨Tree a.carrier × Tree a.carrier⟩)
          (sumCop b ⟨Tree b.carrier × Tree b.carrier⟩)
          R (rprodMap (tree R) (tree R)) from prodMap_eq_rprodMap _ _ ▸ rfl,
    sumMap_junc, junc_comp]
  congr 1
  · apply hom_ext; intro x t
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨Tree.tip x, rfl, hy⟩
    · rintro ⟨u, rfl, h⟩
      cases t with
      | tip y => exact ⟨y, h, rfl⟩
      | bin _ _ => exact h.elim
  · exact bin_natural R

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

/-! ## The tabulation (9.7)-(9.10) and `addcol` (B&dM pp. 233-236)

  Every arrow here is a MAP except `minlist(R)` inside `mix`; `mct` is a map satisfying its
  recursive case, the program being tabulated.  `inits`, `tails` land in `list`, not `list⁺`, so
  the one relator `list` serves the rows and the proper prefixes alike (those can be empty).
  `init`, `tail` are total, a singleton being its own `init` and `tail`: every equation that uses
  them is taken on non-singletons, behind the coreflexive `nonsingle`. -/

/-- `nonsingle`, the coreflexive on lists of two or more elements — the book's "on non-singletons". -/
@[expose] public def nonsingle : dNE A ⟶ dNE A :=
  fun x y => x = y ∧ ∃ a z, x = CL.ConsList.cons a z

/-- The `nonsingle` bead is STRICTLY natural: `list⁺(R)` keeps the length, so relating the
    elements and then testing for two or more is testing first. -/
public theorem nonsingle_strictNatural :
    StrictNatural nelistRelator nelistRelator
      (fun a => (nonsingle : dNE a.carrier ⟶ dNE a.carrier)) := by
  intro a b R
  apply hom_ext; intro x y
  constructor
  · rintro ⟨m, h, rfl, c, z, rfl⟩
    cases x with
    | wrap _ => exact h.elim
    | cons a' z' => exact ⟨_, ⟨rfl, a', z', rfl⟩, h⟩
  · rintro ⟨m, ⟨rfl, a', z', rfl⟩, h⟩
    cases y with
    | wrap _ => exact h.elim
    | cons c w => exact ⟨_, h, rfl, c, w, rfl⟩

/-- `init`, all but the last element. -/
@[expose] public def initFn : NEList A → NEList A
  | CL.ConsList.wrap a => CL.ConsList.wrap a
  | CL.ConsList.cons a (CL.ConsList.wrap _) => CL.ConsList.wrap a
  | CL.ConsList.cons a (CL.ConsList.cons b x) => CL.ConsList.cons a (initFn (CL.ConsList.cons b x))

/-- `tail`, all but the first element.  Irreducible, as is `tailsPFn`: a non-recursive match is
    unfolded by the exporter into the matcher, which names no arrow the note writes. -/
@[expose, irreducible] public def tailFn : NEList A → NEList A
  | CL.ConsList.wrap a => CL.ConsList.wrap a
  | CL.ConsList.cons _ x => x

/-- `inits`, the non-empty prefixes by increasing length. -/
@[expose] public def neInitsFn : NEList A → CL.ConsList Unit (NEList A)
  | CL.ConsList.wrap a => CL.ConsList.cons (CL.ConsList.wrap a) (CL.ConsList.wrap ())
  | CL.ConsList.cons a x =>
      CL.ConsList.cons (CL.ConsList.wrap a) (cmap (CL.ConsList.cons a) (neInitsFn x))

/-- `tails`, the non-empty suffixes by decreasing length. -/
@[expose] public def neTailsFn : NEList A → CL.ConsList Unit (NEList A)
  | CL.ConsList.wrap a => CL.ConsList.cons (CL.ConsList.wrap a) (CL.ConsList.wrap ())
  | CL.ConsList.cons a x => CL.ConsList.cons (CL.ConsList.cons a x) (neTailsFn x)

/-- `inits⁺`, the PROPER non-empty prefixes. -/
@[expose] public def initsPFn : NEList A → CL.ConsList Unit (NEList A)
  | CL.ConsList.wrap _ => CL.ConsList.wrap ()
  | CL.ConsList.cons a x =>
      CL.ConsList.cons (CL.ConsList.wrap a) (cmap (CL.ConsList.cons a) (initsPFn x))

/-- `tails⁺`, the PROPER non-empty suffixes. -/
@[expose, irreducible] public def tailsPFn : NEList A → CL.ConsList Unit (NEList A)
  | CL.ConsList.wrap _ => CL.ConsList.wrap ()
  | CL.ConsList.cons _ x => neTailsFn x

public theorem tailFn_cons (a : A) (z : NEList A) : tailFn (CL.ConsList.cons a z) = z := by
  unfold tailFn; rfl

public theorem tailsPFn_cons (a : A) (z : NEList A) :
    tailsPFn (CL.ConsList.cons a z) = neTailsFn z := by
  unfold tailsPFn; rfl

/-- `zip`, pairing two lists position by position, cut to the shorter. -/
@[expose] public def zipFn {X Y : Type} : CL.ConsList Unit X × CL.ConsList Unit Y → CL.ConsList Unit (X × Y)
  | (CL.ConsList.cons x xs, CL.ConsList.cons y ys) => CL.ConsList.cons (x, y) (zipFn (xs, ys))
  | (CL.ConsList.wrap _, _) => CL.ConsList.wrap ()
  | (CL.ConsList.cons _ _, CL.ConsList.wrap _) => CL.ConsList.wrap ()

/-- `snoc`, one element onto the END of a list. -/
@[expose] public def snocFn {X : Type} (p : CL.ConsList Unit X × X) : CL.ConsList Unit X :=
  cappend p.1 (CL.ConsList.cons p.2 (CL.ConsList.wrap ()))

/-- `minlist(R) : list A⟶A` as B&dM implement it (p. 267), `foldr1 bmin(R)`: the leftmost of the
    `R`-least elements, so a FUNCTION.  `default` answers `[]`, which no non-singleton's `splits` is. -/
@[expose] public def minlistFn {X : Type} [Inhabited X] (Q : CL.dE X ⟶ CL.dE X)
    [∀ a b, Decidable (Q a b)] : CL.ConsList Unit X → X
  | CL.ConsList.wrap _ => default
  | CL.ConsList.cons a (CL.ConsList.wrap _) => a
  | CL.ConsList.cons a (CL.ConsList.cons b x) => Edit.bmin Q (a, minlistFn Q (CL.ConsList.cons b x))

public instance instDecR (t t' : Tree A) : Decidable (R st sb cb t t') :=
  inferInstanceAs (Decidable (costFn st sb cb t ≤ costFn st sb cb t'))

/-- The length of a non-empty list — the bound `mct`'s recursion runs to. -/
@[expose] public def neLen : NEList A → Nat
  | CL.ConsList.wrap _ => 1
  | CL.ConsList.cons _ x => neLen x + 1

/-- `mct` unfolded `n` times: the recursion `(single→tip head,minlist(R) list(bin(X×X)) splits)`
    by structural recursion on the depth, since a split's halves are shorter but not sub-terms. -/
@[expose] public def mctN [Inhabited A] : Nat → NEList A → Tree A
  | _, CL.ConsList.wrap a => Tree.tip a
  | 0, CL.ConsList.cons a _ => Tree.tip a
  | n + 1, x@(CL.ConsList.cons _ _) =>
      minlistFn (R st sb cb) (cmap (fun p => Tree.bin (mctN n p.1) (mctN n p.2)) (splitsFn x))

/-- **mct-defn** (B&dM p. 233): `mct≜(single→tip head,minlist(R) list(bin(mct×mct)) splits)`,
    unfolded as deep as the list is long. -/
@[expose] public def mct [Inhabited A] (x : NEList A) : Tree A := mctN st sb cb (neLen x) x

public theorem neLen_pos : ∀ x : NEList A, 1 ≤ neLen x
  | CL.ConsList.wrap _ => Nat.le_refl 1
  | CL.ConsList.cons _ x => Nat.le_add_left 1 (neLen x)

public theorem neLen_cat : ∀ u v : NEList A, neLen (cat u v) = neLen u + neLen v
  | CL.ConsList.wrap _, v => by simp only [cat, neLen]; omega
  | CL.ConsList.cons _ u, v => by simp only [cat, neLen]; rw [neLen_cat u v]; omega

/-- `list(f)=list(g)` on a list whose every element `f` and `g` agree on. -/
public theorem cmap_congr {X Y : Type} {f g : X → Y} :
    ∀ xs : CL.ConsList Unit X, (∀ p, inlistP xs p → f p = g p) → cmap f xs = cmap g xs
  | CL.ConsList.wrap _, _ => rfl
  | CL.ConsList.cons b xs, h => by
      show CL.ConsList.cons (f b) (cmap f xs) = CL.ConsList.cons (g b) (cmap g xs)
      rw [h b (Or.inl rfl), cmap_congr xs fun p hp => h p (Or.inr hp)]

/-- Each half of a split of `x` is at least one shorter than `x`. -/
public theorem neLen_splits {x : NEList A} {p : NEList A × NEList A} (hp : inlistP (splitsFn x) p) :
    neLen p.1 + 1 ≤ neLen x ∧ neLen p.2 + 1 ≤ neLen x := by
  have hl := congrArg neLen ((mem_splits x p).mp hp)
  rw [neLen_cat] at hl
  have h1 := neLen_pos p.1; have h2 := neLen_pos p.2
  omega

/-- Any depth past the length gives the same tree. -/
public theorem mctN_stable [Inhabited A] : ∀ (n m : Nat) (x : NEList A),
    neLen x ≤ n + 1 → neLen x ≤ m + 1 → mctN st sb cb n x = mctN st sb cb m x
  | n, m, CL.ConsList.wrap _, _, _ => by cases n <;> cases m <;> rfl
  | 0, _, CL.ConsList.cons _ z, h, _ => by have := neLen_pos z; simp only [neLen] at h; omega
  | _ + 1, 0, CL.ConsList.cons _ z, _, h => by have := neLen_pos z; simp only [neLen] at h; omega
  | n + 1, m + 1, CL.ConsList.cons a z, hn, hm => by
      show minlistFn _ (cmap _ _) = minlistFn _ (cmap _ _)
      refine congrArg _ (cmap_congr _ fun p hp => ?_)
      have hs := neLen_splits hp
      rw [mctN_stable n m p.1 (by omega) (by omega), mctN_stable n m p.2 (by omega) (by omega)]

/-- `mct`'s recursive case, pointwise. -/
public theorem mct_cons [Inhabited A] (a : A) (z : NEList A) :
    mct st sb cb (CL.ConsList.cons a z) = minlistFn (R st sb cb)
      (cmap (fun p => Tree.bin (mct st sb cb p.1) (mct st sb cb p.2))
        (splitsFn (CL.ConsList.cons a z))) := by
  show minlistFn _ (cmap _ _) = minlistFn _ (cmap _ _)
  refine congrArg _ (cmap_congr _ fun p hp => ?_)
  have hs := neLen_splits hp
  simp only [neLen] at hs
  show Tree.bin _ _ = Tree.bin (mctN st sb cb _ p.1) (mctN st sb cb _ p.2)
  rw [mctN_stable st sb cb (neLen z) (neLen p.1) p.1 (by omega) (by omega),
    mctN_stable st sb cb (neLen z) (neLen p.2) p.2 (by omega) (by omega)]

/-- `f×g` of two maps is the map of the pair. -/
public theorem rprodMap_graph_pair {X Y X' Y' : RelSet.{0}} (f : X.carrier → X'.carrier)
    (g : Y.carrier → Y'.carrier) :
    rprodMap (graph f : X ⟶ X') (graph g : Y ⟶ Y')
      = graph (fun p : X.carrier × Y.carrier => (f p.1, g p.2)) :=
  hom_ext fun _ _ => ⟨fun h => Prod.ext h.1 h.2,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- `row≜tails list(mct)`. -/
@[expose] public def row [Inhabited A] : dNE A ⟶ dList (Tree A) :=
  (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))

/-- `col≜inits list(mct)`. -/
@[expose] public def col [Inhabited A] : dNE A ⟶ dList (Tree A) :=
  (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))

/-- `mix≜zip list(bin) minlist(R)`. -/
@[expose] public def mix [Inhabited A] (st : A → S) (sb : S × S → S) (cb : S × S → Int) :
    (⟨CL.ConsList Unit (Tree A) × CL.ConsList Unit (Tree A)⟩ : RelSet.{0}) ⟶ dTree A :=
  (graph zipFn : _ ⟶ dList (Tree A × Tree A)) ≫ list binG ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A)

/-- `next≜⟨π₁,mix⟩ snoc`. -/
@[expose] public def next [Inhabited A] (st : A → S) (sb : S × S → S) (cb : S × S → Int) :
    (⟨CL.ConsList Unit (Tree A) × CL.ConsList Unit (Tree A)⟩ : RelSet.{0}) ⟶ dList (Tree A) :=
  rpair (graph Prod.fst : _ ⟶ dList (Tree A)) (mix st sb cb)
    ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0}) ⟶ dList (Tree A))

/-- A graph followed by a graph and then anything is one graph followed by it. -/
public theorem graph_comp_comp {X Y Z W : RelSet.{0}} (f : X.carrier → Y.carrier)
    (g : Y.carrier → Z.carrier) (M : Z ⟶ W) :
    graph f ≫ graph g ≫ M = graph (fun x => g (f x)) ≫ M := by
  rw [← Cat.assoc, graph_comp]

/-- `𝟙=graph(id)` on `list⁺ A` — `RelSet.graph_id` is not public, and exposing it would rebuild
    every importer. -/
public theorem id_eq_graph : 𝟙 (dNE A) = (graph (fun x : NEList A => x) : dNE A ⟶ dNE A) :=
  hom_ext fun _ _ => ⟨Eq.symm, Eq.symm⟩

/-- Behind `nonsingle`, two maps that agree on every `cons` are the same arrow. -/
public theorem nonsingle_graph {Y : RelSet.{0}} {f g : NEList A → Y.carrier}
    (h : ∀ a z, f (CL.ConsList.cons a z) = g (CL.ConsList.cons a z)) :
    nonsingle ≫ (graph f : dNE A ⟶ Y) = nonsingle ≫ graph g := by
  apply hom_ext; intro x w
  constructor
  · rintro ⟨y, ⟨rfl, a, z, rfl⟩, hw⟩
    exact ⟨_, ⟨rfl, a, z, rfl⟩, hw.trans (h a z)⟩
  · rintro ⟨y, ⟨rfl, a, z, rfl⟩, hw⟩
    exact ⟨_, ⟨rfl, a, z, rfl⟩, hw.trans (h a z).symm⟩

/-- The same with a common tail `M`. -/
public theorem nonsingle_graph_comp {Y W : RelSet.{0}} {f g : NEList A → Y.carrier} (M : Y ⟶ W)
    (h : ∀ a z, f (CL.ConsList.cons a z) = g (CL.ConsList.cons a z)) :
    nonsingle ≫ (graph f : dNE A ⟶ Y) ≫ M = nonsingle ≫ graph g ≫ M := by
  rw [← Cat.assoc, ← Cat.assoc, nonsingle_graph h]

/-- Behind a coreflexive, the second component of a pair may be put behind it too. -/
public theorem nonsingle_rpair {X Y : RelSet.{0}} (U : dNE A ⟶ X) (V : dNE A ⟶ Y) :
    nonsingle ≫ rpair U V = nonsingle ≫ rpair U (nonsingle ≫ V) := by
  apply hom_ext; intro x w
  constructor
  · rintro ⟨y, ⟨rfl, a, z, rfl⟩, hU, hV⟩
    exact ⟨_, ⟨rfl, a, z, rfl⟩, hU, _, ⟨rfl, a, z, rfl⟩, hV⟩
  · rintro ⟨y, ⟨rfl, a, z, rfl⟩, hU, _, ⟨rfl, _⟩, hV⟩
    exact ⟨_, ⟨rfl, a, z, rfl⟩, hU, hV⟩

public theorem cmap_snoc {X Y : Type} (f : X → Y) (a : X) :
    ∀ xs : CL.ConsList Unit X,
      cmap f (snocFn (xs, a)) = snocFn (cmap f xs, f a)
  | CL.ConsList.wrap _ => rfl
  | CL.ConsList.cons b xs => congrArg (CL.ConsList.cons (f b)) (cmap_snoc f a xs)

/-- `list(f) list(g)=list(f g)`, pointwise. -/
public theorem cmap_cmap {X Y Z : Type} (f : X → Y) (g : Y → Z) :
    ∀ xs : CL.ConsList Unit X, cmap g (cmap f xs) = cmap (fun x => g (f x)) xs
  | CL.ConsList.wrap _ => rfl
  | CL.ConsList.cons b xs => congrArg (CL.ConsList.cons (g (f b))) (cmap_cmap f g xs)

/-- `list(f×g) zip = zip (list f×list g)`, pointwise. -/
public theorem cmap_zip {X Y X' Y' : Type} (f : X → X') (g : Y → Y') :
    ∀ (xs : CL.ConsList Unit X) (ys : CL.ConsList Unit Y),
      cmap (fun p => (f p.1, g p.2)) (zipFn (xs, ys)) = zipFn (cmap f xs, cmap g ys)
  | CL.ConsList.wrap _, _ => by simp only [zipFn, cmap]
  | CL.ConsList.cons _ _, CL.ConsList.wrap _ => by simp only [zipFn, cmap]
  | CL.ConsList.cons x xs, CL.ConsList.cons y ys => by
      simp only [zipFn, cmap]; rw [cmap_zip f g xs ys]

public theorem consSplits_zip (a : A) :
    ∀ (xs ys : CL.ConsList Unit (NEList A)),
      consSplits a (zipFn (xs, ys)) = zipFn (cmap (CL.ConsList.cons a) xs, ys)
  | CL.ConsList.wrap _, _ => by simp only [zipFn, cmap, consSplits]
  | CL.ConsList.cons _ _, CL.ConsList.wrap _ => by simp only [zipFn, cmap, consSplits]
  | CL.ConsList.cons x xs, CL.ConsList.cons y ys => by
      simp only [zipFn, cmap, consSplits]; rw [consSplits_zip a xs ys]

public theorem neTails_eq : ∀ x : NEList A, neTailsFn x = CL.ConsList.cons x (tailsPFn x)
  | CL.ConsList.wrap _ => by unfold tailsPFn; rfl
  | CL.ConsList.cons _ _ => by rw [tailsPFn_cons]; rfl

/-- `splits≜⟨inits⁺,tails⁺⟩ zip`: the definition the note states, of `splitsFn`. -/
public theorem splitsFn_eq : ∀ x : NEList A, splitsFn x = zipFn (initsPFn x, tailsPFn x)
  | CL.ConsList.wrap _ => by simp only [splitsFn, initsPFn, tailsPFn, zipFn]
  | CL.ConsList.cons a x => by
      simp only [splitsFn, initsPFn, tailsPFn]
      rw [neTails_eq x, zipFn, splitsFn_eq x, consSplits_zip]

/-- `inits⁺=init inits` on non-singletons. -/
public theorem initsP_eq (a : A) :
    ∀ z : NEList A, initsPFn (CL.ConsList.cons a z) = neInitsFn (initFn (CL.ConsList.cons a z))
  | CL.ConsList.wrap _ => rfl
  | CL.ConsList.cons b z => by
      show CL.ConsList.cons _ (cmap _ (initsPFn (CL.ConsList.cons b z))) = _
      rw [initsP_eq b z]; rfl

/-- `inits=⟨init inits,𝟙⟩ snoc` on non-singletons. -/
public theorem inits_snoc (a : A) :
    ∀ z : NEList A, neInitsFn (CL.ConsList.cons a z)
      = snocFn (neInitsFn (initFn (CL.ConsList.cons a z)), CL.ConsList.cons a z)
  | CL.ConsList.wrap _ => rfl
  | CL.ConsList.cons b z => by
      show CL.ConsList.cons _ (cmap _ (neInitsFn (CL.ConsList.cons b z))) = _
      rw [inits_snoc b z, cmap_snoc]; rfl

/-! ### What the tabulation's beads claim: each list function is lax natural -/

/-- A square of two maps closes pointwise: related inputs give related outputs. -/
public theorem graph_lax {X Y X' Y' : RelSet.{0}} (F : X ⟶ X') (G : Y ⟶ Y') (f : X.carrier → Y.carrier)
    (f' : X'.carrier → Y'.carrier) (h : ∀ x x', F x x' → G (f x) (f' x')) :
    F ≫ graph f' ⊑ graph f ≫ G :=
  le_iff.mpr fun x z ⟨x', hx, hz⟩ => ⟨f x, rfl, by rw [hz]; exact h x x' hx⟩

public theorem listP_cmap_cons {B : Type} {R : CL.dE A ⟶ CL.dE B} {a : A} {b : B} (hab : R a b) :
    ∀ (I : CL.ConsList Unit (NEList A)) (J : CL.ConsList Unit (NEList B)),
      listP (nelist R) I J → listP (nelist R) (cmap (CL.ConsList.cons a) I) (cmap (CL.ConsList.cons b) J)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, h => h
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ I, CL.ConsList.cons _ J, h => ⟨⟨hab, h.1⟩, listP_cmap_cons hab I J h.2⟩

public theorem listP_inits {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x : NEList A) (y : NEList B), nelistP R x y → listP (nelist R) (neInitsFn x) (neInitsFn y)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, h => ⟨h, trivial⟩
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ x, CL.ConsList.cons _ y, h =>
      ⟨h.1, listP_cmap_cons h.1 _ _ (listP_inits R x y h.2)⟩

public theorem listP_tails {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x : NEList A) (y : NEList B), nelistP R x y → listP (nelist R) (neTailsFn x) (neTailsFn y)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, h => ⟨h, trivial⟩
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ x, CL.ConsList.cons _ y, h => ⟨h, listP_tails R x y h.2⟩

public theorem listP_initsP {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x : NEList A) (y : NEList B), nelistP R x y → listP (nelist R) (initsPFn x) (initsPFn y)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, _ => trivial
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ x, CL.ConsList.cons _ y, h =>
      ⟨h.1, listP_cmap_cons h.1 _ _ (listP_initsP R x y h.2)⟩

public theorem listP_tailsP {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x : NEList A) (y : NEList B), nelistP R x y → listP (nelist R) (tailsPFn x) (tailsPFn y)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, _ => by unfold tailsPFn; trivial
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ x, CL.ConsList.cons _ y, h => by
      rw [tailsPFn_cons, tailsPFn_cons]; exact listP_tails R x y h.2

public theorem nelistP_init {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x : NEList A) (y : NEList B), nelistP R x y → nelistP R (initFn x) (initFn y)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, h => h
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ (CL.ConsList.wrap _), CL.ConsList.cons _ (CL.ConsList.wrap _), h => h.1
  | CL.ConsList.cons _ (CL.ConsList.wrap _), CL.ConsList.cons _ (CL.ConsList.cons _ _), h => h.2.elim
  | CL.ConsList.cons _ (CL.ConsList.cons _ _), CL.ConsList.cons _ (CL.ConsList.wrap _), h => h.2.elim
  | CL.ConsList.cons _ (CL.ConsList.cons a' x), CL.ConsList.cons _ (CL.ConsList.cons b' y), h =>
      ⟨h.1, nelistP_init R (CL.ConsList.cons a' x) (CL.ConsList.cons b' y) h.2⟩

public theorem nelistP_tail {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    ∀ (x : NEList A) (y : NEList B), nelistP R x y → nelistP R (tailFn x) (tailFn y)
  | CL.ConsList.wrap _, CL.ConsList.wrap _, h => by unfold tailFn; exact h
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.cons _ _, h => by rw [tailFn_cons, tailFn_cons]; exact h.2

public theorem listP_zip {X X' Y Y' : Type} (R : CL.dE X ⟶ CL.dE X') (S : CL.dE Y ⟶ CL.dE Y') :
    ∀ (xs : CL.ConsList Unit X) (xs' : CL.ConsList Unit X') (ys : CL.ConsList Unit Y)
      (ys' : CL.ConsList Unit Y'), listP R xs xs' → listP S ys ys' →
        listP (rprodMap R S) (zipFn (xs, ys)) (zipFn (xs', ys'))
  | CL.ConsList.wrap _, CL.ConsList.wrap _, _, _, _, _ => by simp only [zipFn]; trivial
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, _, _, h, _ => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, _, _, h, _ => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.cons _ _, CL.ConsList.wrap _, CL.ConsList.wrap _, _, _ => by
      simp only [zipFn]; trivial
  | CL.ConsList.cons _ _, CL.ConsList.cons _ _, CL.ConsList.wrap _, CL.ConsList.cons _ _, _, k =>
      k.elim
  | CL.ConsList.cons _ _, CL.ConsList.cons _ _, CL.ConsList.cons _ _, CL.ConsList.wrap _, _, k =>
      k.elim
  | CL.ConsList.cons _ xs, CL.ConsList.cons _ xs', CL.ConsList.cons _ ys, CL.ConsList.cons _ ys',
      h, k => by
      simp only [zipFn]; exact ⟨⟨h.1, k.1⟩, listP_zip R S xs xs' ys ys' h.2 k.2⟩

public theorem listP_snoc {X X' : Type} (R : CL.dE X ⟶ CL.dE X') {a : X} {a' : X'} (ha : R a a') :
    ∀ (xs : CL.ConsList Unit X) (xs' : CL.ConsList Unit X'), listP R xs xs' →
      listP R (snocFn (xs, a)) (snocFn (xs', a'))
  | CL.ConsList.wrap _, CL.ConsList.wrap _, _ => ⟨ha, trivial⟩
  | CL.ConsList.wrap _, CL.ConsList.cons _ _, h => h.elim
  | CL.ConsList.cons _ _, CL.ConsList.wrap _, h => h.elim
  | CL.ConsList.cons _ xs, CL.ConsList.cons _ xs', h => ⟨h.1, listP_snoc R ha xs xs' h.2⟩

/-- The `inits` bead is lax natural. -/
public theorem inits_lax_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ (graph neInitsFn : dNE B ⟶ dList (NEList B))
      ⊑ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (nelist R) :=
  graph_lax _ _ _ _ (listP_inits R)

/-- The `tails` bead is lax natural. -/
public theorem tails_lax_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ (graph neTailsFn : dNE B ⟶ dList (NEList B))
      ⊑ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (nelist R) :=
  graph_lax _ _ _ _ (listP_tails R)

/-- The `⟨inits⁺,tails⁺⟩` bead is lax natural. -/
public theorem initsP_tailsP_lax_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ rpair (graph initsPFn : dNE B ⟶ dList (NEList B))
        (graph tailsPFn : dNE B ⟶ dList (NEList B))
      ⊑ rpair (graph initsPFn : dNE A ⟶ dList (NEList A))
          (graph tailsPFn : dNE A ⟶ dList (NEList A))
        ≫ rprodMap (list (nelist R)) (list (nelist R)) := by
  simp only [rpair_graph]
  exact graph_lax _ _ _ _ fun x y h => ⟨listP_initsP R x y h, listP_tailsP R x y h⟩

/-- The `⟨init inits,𝟙⟩` bead is lax natural. -/
public theorem initInits_id_lax_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ rpair ((graph initFn : dNE B ⟶ dNE B) ≫ (graph neInitsFn : dNE B ⟶ dList (NEList B)))
        (𝟙 (dNE B))
      ⊑ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)))
          (𝟙 (dNE A))
        ≫ rprodMap (list (nelist R)) (nelist R) := by
  simp only [id_eq_graph, graph_comp, rpair_graph]
  exact graph_lax _ _ _ _ fun x y h => ⟨listP_inits R _ _ (nelistP_init R x y h), h⟩

/-- The `⟨𝟙,tail tails⟩` bead is lax natural. -/
public theorem id_tailTails_lax_natural {B : Type} (R : CL.dE A ⟶ CL.dE B) :
    nelist R ≫ rpair (𝟙 (dNE B))
        ((graph tailFn : dNE B ⟶ dNE B) ≫ (graph neTailsFn : dNE B ⟶ dList (NEList B)))
      ⊑ rpair (𝟙 (dNE A))
          ((graph tailFn : dNE A ⟶ dNE A) ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)))
        ≫ rprodMap (nelist R) (list (nelist R)) := by
  simp only [id_eq_graph, graph_comp, rpair_graph]
  exact graph_lax _ _ _ _ fun x y h => ⟨h, listP_tails R _ _ (nelistP_tail R x y h)⟩

/-- The `zip` bead is lax natural. -/
public theorem zip_lax_natural {X X' Y Y' : Type} (R : CL.dE X ⟶ CL.dE X') (S : CL.dE Y ⟶ CL.dE Y') :
    rprodMap (list R) (list S)
        ≫ (graph zipFn : (⟨CL.ConsList Unit X' × CL.ConsList Unit Y'⟩ : RelSet.{0}) ⟶ dList (X' × Y'))
      ⊑ (graph zipFn : (⟨CL.ConsList Unit X × CL.ConsList Unit Y⟩ : RelSet.{0}) ⟶ dList (X × Y))
        ≫ list (rprodMap R S) :=
  graph_lax _ _ _ _ fun p q h => listP_zip R S p.1 q.1 p.2 q.2 h.1 h.2

/-- The `snoc` bead is lax natural. -/
public theorem snoc_lax_natural {X X' : Type} (R : CL.dE X ⟶ CL.dE X') :
    rprodMap (list R) R
        ≫ (graph snocFn : (⟨CL.ConsList Unit X' × X'⟩ : RelSet.{0}) ⟶ dList X')
      ⊑ (graph snocFn : (⟨CL.ConsList Unit X × X⟩ : RelSet.{0}) ⟶ dList X) ≫ list R :=
  graph_lax _ _ _ _ fun p q h => listP_snoc R h.2 p.1 q.1 h.1

/-- The `cons` bead is lax natural. -/
public theorem consAtUnit_lax_natural {X X' : Type} (R : CL.dE X ⟶ CL.dE X') :
    rprodMap R (list R) ≫ (consAtUnit : _ ⟶ dList X') ⊑ (consAtUnit : _ ⟶ dList X) ≫ list R := by
  simp only [consAtUnit, CL.consR]
  exact graph_lax _ _ _ _ fun p q h => ⟨h.1, h.2⟩

/-! ### (9.7): `mct` in terms of `row` and `col` -/

variable [Inhabited A]

/-- **mct-defn**: `mct`'s recursive equation, proved once — on non-singletons
    `mct=splits list(bin(mct×mct)) minlist(R)`. -/
public theorem mct_eq :
    nonsingle ≫ (graph (mct st sb cb) : dNE A ⟶ dTree A)
      = nonsingle ≫ splits ≫ list (rprodMap (graph (mct st sb cb)) (graph (mct st sb cb)) ≫ binG)
          ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A) := by
  simp only [splits, rprodMap_graph_pair, list_graph, graph_comp, graph_comp_comp]
  exact nonsingle_graph fun a z => mct_cons st sb cb a z

/-- (9.7), first step: recursive case of `mct` and definition of `splits`. -/
public theorem mct_rec_step1 :
    nonsingle ≫ (graph (mct st sb cb) : dNE A ⟶ dTree A)
      = nonsingle ≫ rpair (graph initsPFn : dNE A ⟶ dList (NEList A))
            (graph tailsPFn : dNE A ⟶ dList (NEList A))
          ≫ (graph zipFn : _ ⟶ dList (NEList A × NEList A))
          ≫ list (rprodMap (graph (mct st sb cb)) (graph (mct st sb cb)) ≫ binG) ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A) := by
  rw [mct_eq, rpair_graph, graph_comp_comp]
  exact congrArg (fun f => nonsingle ≫ (graph f : dNE A ⟶ dList (NEList A × NEList A)) ≫ _)
    (funext splitsFn_eq)

/-- (9.7), second step: `list(f×g) zip = zip (list f×list g)`. -/
public theorem mct_rec_step2 :
    nonsingle ≫ rpair (graph initsPFn : dNE A ⟶ dList (NEList A))
          (graph tailsPFn : dNE A ⟶ dList (NEList A))
        ≫ (graph zipFn : _ ⟶ dList (NEList A × NEList A))
        ≫ list (rprodMap (graph (mct st sb cb)) (graph (mct st sb cb)) ≫ binG) ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A)
      = nonsingle ≫ rpair ((graph initsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
            ((graph tailsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ≫ (graph zipFn : _ ⟶ dList (Tree A × Tree A)) ≫ list binG ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A) := by
  simp only [rprodMap_graph_pair, list_graph, graph_comp, rpair_graph, graph_comp_comp]
  refine nonsingle_graph_comp _ fun a z => ?_
  rw [← cmap_zip, cmap_cmap]

/-- (9.7), third step: introducing `mix≜zip list(bin) minlist(R)`. -/
public theorem mct_rec_step3 :
    nonsingle ≫ rpair ((graph initsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ((graph tailsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
        ≫ (graph zipFn : _ ⟶ dList (Tree A × Tree A)) ≫ list binG ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A)
      = nonsingle ≫ rpair ((graph initsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ((graph tailsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))) ≫ mix st sb cb := rfl

/-- (9.7), fourth step: `inits⁺=init inits` and `tails⁺=tail tails`, on non-singletons. -/
public theorem mct_rec_step4 :
    nonsingle ≫ rpair ((graph initsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ((graph tailsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))) ≫ mix st sb cb
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A)
              ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
            ((graph tailFn : dNE A ⟶ dNE A)
              ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ≫ mix st sb cb := by
  simp only [list_graph, graph_comp, rpair_graph]
  refine nonsingle_graph_comp _ fun a z => ?_
  rw [initsP_eq, tailsPFn_cons, tailFn_cons]

/-- (9.7), fifth step: definition of `row` and `col`. -/
public theorem mct_rec_step5 :
    nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A)
            ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ((graph tailFn : dNE A ⟶ dNE A)
            ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
        ≫ mix st sb cb
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ mix st sb cb := rfl

/-- **(9.7)**: `mct=(single→head tip,⟨init col,tail row⟩ mix)`, its recursive case — on a list of
    two or more, `mct` is `mix` of the column above and the row beside. -/
public theorem mct_rec :
    nonsingle ≫ (graph (mct st sb cb) : dNE A ⟶ dTree A)
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ mix st sb cb :=
  calc nonsingle ≫ (graph (mct st sb cb) : dNE A ⟶ dTree A)
      _ = nonsingle ≫ rpair (graph initsPFn : dNE A ⟶ dList (NEList A))
            (graph tailsPFn : dNE A ⟶ dList (NEList A))
          ≫ (graph zipFn : _ ⟶ dList (NEList A × NEList A))
          ≫ list (rprodMap (graph (mct st sb cb)) (graph (mct st sb cb)) ≫ binG) ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A) :=
        mct_rec_step1 st sb cb
      _ = nonsingle ≫ rpair ((graph initsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
            ((graph tailsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ≫ (graph zipFn : _ ⟶ dList (Tree A × Tree A)) ≫ list binG
          ≫ (graph (minlistFn (R st sb cb)) : dList (Tree A) ⟶ dTree A) := mct_rec_step2 st sb cb
      _ = nonsingle ≫ rpair ((graph initsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ((graph tailsPFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))) ≫ mix st sb cb :=
        mct_rec_step3 st sb cb
      _ = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A)
              ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
            ((graph tailFn : dNE A ⟶ dNE A)
              ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)))
          ≫ mix st sb cb := mct_rec_step4 st sb cb
      _ = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ mix st sb cb := mct_rec_step5 st sb cb

/-- A pair whose first component is a map, followed by `⟨π₁,M⟩`, keeps that component. -/
public theorem rpair_graph_fst {C P Q W : RelSet.{0}} (f : C.carrier → P.carrier) (V : C ⟶ Q)
    (M : (⟨P.carrier × Q.carrier⟩ : RelSet.{0}) ⟶ W) :
    rpair (graph f) V ≫ rpair (graph Prod.fst : (⟨P.carrier × Q.carrier⟩ : RelSet.{0}) ⟶ P) M
      = rpair (graph f) (rpair (graph f) V ≫ M) := by
  apply hom_ext; intro x w
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, hw1, hw2⟩
    exact ⟨hw1.trans hm1, m, ⟨hm1, hm2⟩, hw2⟩
  · rintro ⟨hw1, m, ⟨hm1, hm2⟩, hw2⟩
    exact ⟨m, ⟨hm1, hm2⟩, hw1.trans hm1.symm, hw2⟩

/-! ### (9.8): `col` in terms of `row` and `col` -/

/-- (9.8), first step: definition of `col`. -/
public theorem col_rec_step1 :
    nonsingle ≫ col st sb cb
      = nonsingle ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)) := rfl

/-- (9.8), second step: `inits=⟨init inits,𝟙⟩ snoc` on non-singletons. -/
public theorem col_rec_step2 :
    nonsingle ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A)
            ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A))) (𝟙 (dNE A))
          ≫ (graph snocFn : (⟨CL.ConsList Unit (NEList A) × NEList A⟩ : RelSet.{0})
              ⟶ dList (NEList A))
          ≫ list (graph (mct st sb cb)) := by
  simp only [id_eq_graph, list_graph, graph_comp, rpair_graph]
  exact nonsingle_graph fun a z => by rw [inits_snoc]

/-- (9.8), third step: `list(f) snoc=snoc (list f×f)`, and definition of `col`. -/
public theorem col_rec_step3 :
    nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A)
          ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A))) (𝟙 (dNE A))
        ≫ (graph snocFn : (⟨CL.ConsList Unit (NEList A) × NEList A⟩ : RelSet.{0})
            ⟶ dList (NEList A))
        ≫ list (graph (mct st sb cb))
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb) (graph (mct st sb cb) : dNE A ⟶ dTree A)
          ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0})
              ⟶ dList (Tree A)) := by
  simp only [col, id_eq_graph, list_graph, graph_comp, rpair_graph]
  exact nonsingle_graph fun a z => cmap_snoc _ _ _

/-- (9.8), fourth step: (9.7) on non-singletons. -/
public theorem col_rec_step4 :
    nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb) (graph (mct st sb cb) : dNE A ⟶ dTree A)
        ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0}) ⟶ dList (Tree A))
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
            (rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
              ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ mix st sb cb)
          ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0})
              ⟶ dList (Tree A)) := by
  rw [← Cat.assoc, nonsingle_rpair, mct_rec st sb cb, ← nonsingle_rpair, Cat.assoc]

/-- (9.8), fifth step: introducing `next≜⟨π₁,mix⟩ snoc`. -/
public theorem col_rec_step5 :
    nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          (rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
            ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ mix st sb cb)
        ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0}) ⟶ dList (Tree A))
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ next st sb cb := by
  have hX : (graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb
      = graph (fun x => cmap (mct st sb cb) (neInitsFn (initFn x))) := by
    simp only [col, list_graph, graph_comp]; rfl
  rw [hX, next, ← Cat.assoc (rpair _ _) (rpair _ _), rpair_graph_fst]

/-- **(9.8)**: `col=(single→head tip wrap,⟨init col,tail row⟩ next)`, its recursive case — on a
    list of two or more, the column is the column above extended by `next`. -/
public theorem col_rec :
    nonsingle ≫ col st sb cb
      = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ next st sb cb :=
  calc nonsingle ≫ col st sb cb
      _ = nonsingle ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)) :=
        col_rec_step1 st sb cb
      _ = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A)
            ≫ (graph neInitsFn : dNE A ⟶ dList (NEList A))) (𝟙 (dNE A))
          ≫ (graph snocFn : (⟨CL.ConsList Unit (NEList A) × NEList A⟩ : RelSet.{0})
              ⟶ dList (NEList A))
          ≫ list (graph (mct st sb cb)) := col_rec_step2 st sb cb
      _ = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
            (graph (mct st sb cb) : dNE A ⟶ dTree A)
          ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0})
              ⟶ dList (Tree A)) := col_rec_step3 st sb cb
      _ = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
            (rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
              ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ mix st sb cb)
          ≫ (graph snocFn : (⟨CL.ConsList Unit (Tree A) × Tree A⟩ : RelSet.{0})
              ⟶ dList (Tree A)) := col_rec_step4 st sb cb
      _ = nonsingle ≫ rpair ((graph initFn : dNE A ⟶ dNE A) ≫ col st sb cb)
          ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ next st sb cb :=
        col_rec_step5 st sb cb

/-! ### (9.10): `row` in terms of `mct` and `row` -/

/-- (9.10), first step: definition of `row`. -/
public theorem row_rec_step1 :
    nonsingle ≫ row st sb cb
      = nonsingle ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)) := rfl

/-- (9.10), second step: `tails=⟨𝟙,tail tails⟩ cons` on non-singletons. -/
public theorem row_rec_step2 :
    nonsingle ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb))
      = nonsingle ≫ rpair (𝟙 (dNE A)) ((graph tailFn : dNE A ⟶ dNE A)
            ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)))
          ≫ consAtUnit ≫ list (graph (mct st sb cb)) := by
  simp only [consAtUnit, CL.consR, id_eq_graph, list_graph, graph_comp, rpair_graph]
  exact nonsingle_graph fun a z => by rw [tailFn_cons]; rfl

/-- (9.10), third step: `list(f) cons=cons (f×list f)`, and definition of `row`. -/
public theorem row_rec_step3 :
    nonsingle ≫ rpair (𝟙 (dNE A)) ((graph tailFn : dNE A ⟶ dNE A)
          ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)))
        ≫ consAtUnit ≫ list (graph (mct st sb cb))
      = nonsingle ≫ rpair (graph (mct st sb cb) : dNE A ⟶ dTree A) ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb)
          ≫ consAtUnit := by
  simp only [row, consAtUnit, CL.consR, id_eq_graph, list_graph, graph_comp, rpair_graph]
  exact nonsingle_graph fun a z => by rw [tailFn_cons]; rfl

/-- **(9.10)**: `row=(single→wrap tip head,⟨mct,tail row⟩ cons)`, its recursive case — on a list
    of two or more, the row is `mct` of the whole list in front of the row of its tail. -/
public theorem row_rec :
    nonsingle ≫ row st sb cb
      = nonsingle ≫ rpair (graph (mct st sb cb) : dNE A ⟶ dTree A) ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb)
          ≫ consAtUnit :=
  calc nonsingle ≫ row st sb cb
      _ = nonsingle ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)) ≫ list (graph (mct st sb cb)) :=
        row_rec_step1 st sb cb
      _ = nonsingle ≫ rpair (𝟙 (dNE A)) ((graph tailFn : dNE A ⟶ dNE A)
            ≫ (graph neTailsFn : dNE A ⟶ dList (NEList A)))
          ≫ consAtUnit ≫ list (graph (mct st sb cb)) := row_rec_step2 st sb cb
      _ = nonsingle ≫ rpair (graph (mct st sb cb) : dNE A ⟶ dTree A)
            ((graph tailFn : dNE A ⟶ dNE A) ≫ row st sb cb) ≫ consAtUnit := row_rec_step3 st sb cb

-- printing-only: the note's bead is `R`, the order the bracketing is optimised under.  The leaf
-- map, the split cost and the combine cost are the section's context, not part of the name.
open Lean PrettyPrinter in
@[app_unexpander R] public meta def unexpandBracketR : Unexpander
  | _ => `($(mkIdent `R))

end Freyd.Alg.RelSet.Bracket
