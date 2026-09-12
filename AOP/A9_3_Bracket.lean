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
  * rows 4-7 (`splits`, and the array tabulation (9.7)-(9.10)) relate arrays of trees, which the
    note itself marks as outside the relational picture.

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

/-- **mct-defn**: `list⁺ A`, the non-empty lists — `wrap a` is `[a]`, `cons a x` is `[a]⧺x`. -/
@[expose] public abbrev NEList (A : Type) : Type := CL.ConsList A A

/-- The object carrying `list⁺ A`. -/
@[expose] public abbrev dNE (A : Type) : RelSet.{0} := ⟨NEList A⟩

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

/-! ## `mct-laws` — Proposition 9.3's two equations -/

/-- **mct-laws** (9.5): `[tip,bin] cost=(𝟙+⟨cost,flatten⟩²)g` — the cost of a node reads only
    the cost and the flattening of its two subtrees.  `sb` associative enters here, through
    `size=flatten sz`. -/
public theorem mct_cost_alg (hassoc : Assoc sb) :
    graph con ≫ (graph (costFn st sb cb) : dTree A ⟶ (⟨Int⟩ : RelSet.{0}))
      = (TT.F A).map ((P A).pair (graph (costFn st sb cb)) (graph flattenFn))
        ≫ graph (gFn st sb cb) := by
  apply hom_ext; intro u n
  rw [pair_eq_rpair]
  constructor
  · rintro ⟨t, ht, hn⟩
    obtain rfl : t = con u := ht
    cases u with
    | inl a => exact ⟨Sum.inl a, rfl, hn⟩
    | inr p =>
      obtain ⟨l, r⟩ := p
      refine ⟨Sum.inr ((costFn st sb cb l, flattenFn l), (costFn st sb cb r, flattenFn r)),
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ?_⟩
      show n = cb (szFn st sb (flattenFn l), szFn st sb (flattenFn r))
        + costFn st sb cb l + costFn st sb cb r
      rw [← size_eq_sz_flatten st sb cb hassoc l, ← size_eq_sz_flatten st sb cb hassoc r]
      exact hn
  · rintro ⟨w, hw, hn⟩
    cases u with
    | inl a =>
      cases w with
      | inl a' => obtain rfl : a = a' := hw; exact ⟨Tree.tip a, rfl, hn⟩
      | inr _ => exact hw.elim
    | inr p =>
      cases w with
      | inl _ => exact hw.elim
      | inr q =>
        obtain ⟨l, r⟩ := p
        obtain ⟨pl, pr⟩ := q
        obtain ⟨plc, plf⟩ := pl
        obtain ⟨prc, prf⟩ := pr
        obtain ⟨⟨hc1, hf1⟩, ⟨hc2, hf2⟩⟩ := hw
        obtain rfl : plc = costFn st sb cb l := hc1
        obtain rfl : plf = flattenFn l := hf1
        obtain rfl : prc = costFn st sb cb r := hc2
        obtain rfl : prf = flattenFn r := hf2
        refine ⟨Tree.bin l r, rfl, ?_⟩
        show n = cb ((costSizeFn st sb cb l).2, (costSizeFn st sb cb r).2)
          + costFn st sb cb l + costFn st sb cb r
        rw [size_eq_sz_flatten st sb cb hassoc l, size_eq_sz_flatten st sb cb hassoc r]
        exact hn

/-- **mct-laws** (9.6): `(𝟙+(≤×𝟙)²)g⊑g≤` — `g` is monotonic on `≤` in its two cost arguments,
    the flattenings being held fixed. -/
public theorem mct_g_mono :
    (TT.F A).map (prodMap (P A) (P A) leq (𝟙 (dNE A))) ≫ graph (gFn st sb cb)
      ⊑ graph (gFn st sb cb) ≫ leq := by
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun u n h => ?_
  obtain ⟨w, hw, hn⟩ := h
  cases u with
  | inl a =>
    cases w with
    | inl a' => exact ⟨0, rfl, Int.le_of_eq (hn : n = 0).symm⟩
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
      show cb (szFn st sb plf, szFn st sb prf) + plc + prc ≤ n
      rw [(hn : n = cb (szFn st sb plf, szFn st sb prf) + qlc + qrc)]
      exact Int.add_le_add (Int.add_le_add (Int.le_refl _) (hc1 : plc ≤ qlc)) (hc2 : prc ≤ qrc)

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
    (mct_cost_alg st sb cb hassoc) (mct_g_mono st sb cb)

/-- The same at the mirrored order, which is what `dynamic_programming_context` consumes. -/
public theorem mct_mono_recip (hassoc : Assoc sb) :
    (TT.F A).map ((R st sb cb)° ∩ (graph flattenFn ≫ (graph (flattenFn (A := A)))°)) ≫ graph con
      ⊑ graph con ≫ (R st sb cb)° :=
  monotonicAlg_in_context (graph_map (costFn st sb cb)) (graph_map flattenFn).2
    (R_recip_eq st sb cb) (mct_cost_alg st sb cb hassoc) (mct_g_mono_geq st sb cb)

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

/-- `AOP.A8_3`'s `setifyCL` and `AOP.A5_6_ListCombinators`' `setify` are the SAME arrow — one is
    written with `clMem`, the other with `inlistP`, and the two memberships are the same
    predicate read in the two argument orders. -/
public theorem clMem_iff_inlistP {B : Type} (w : B) :
    ∀ xs : CL.ConsList Unit B, CL.clMem w xs ↔ inlistP xs w
  | CL.ConsList.wrap _ => Iff.rfl
  | CL.ConsList.cons _ xs => or_congr Iff.rfl (clMem_iff_inlistP w xs)

public theorem setifyCL_eq_setify {B : Type} : (CL.setifyCL : dList B ⟶ _) = setify := by
  show graph (fun xs => fun w => CL.clMem w xs) = graph (inlistP (A := B))
  exact congrArg graph (funext fun xs => funext fun w => propext (clMem_iff_inlistP w xs))

/-- `minlist Q ≜ setify est(Q)`, in the note's own `setify`. -/
public theorem minlist_eq_setify_comp_est {B : Type} (Q : CL.dE B ⟶ CL.dE B) :
    CL.minlist Q = setify ≫ est Q := by
  show CL.setifyCL ≫ est Q = setify ≫ est Q
  rw [setifyCL_eq_setify]

/-- **mct-laws**, fourth row (B&dM p.232): `splits list((mct×mct)bin)minlist R` refines the body
    `(cat°)%∋ P((X×X)bin)est(R)` of the fixed point — `splits` implements `cat°` (`mem_splits`)
    and `minlist R` implements `est(R)`, the list standing in for the set it `setify`s to.  The
    one inequality is `setify`'s lax naturality (`AOP.A5_7_ListBeads.setify_lax_natural`): a list
    of `f`-images of the splits has, as a SET, an `P(f)`-image of the set of splits.  Exponential,
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
  have hnat : list (rprodMap mct mct ≫ graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2))
        ≫ setify ≫ est (R st sb cb)
      ⊑ setify ≫ powerRel (rprodMap mct mct
          ≫ graph (fun p : Tree A × Tree A => Tree.bin p.1 p.2)) ≫ est (R st sb cb) := by
    rw [← Cat.assoc, ← Cat.assoc]
    exact comp_mono_right (setify_lax_natural _) _
  rw [minlist_eq_setify_comp_est, ← hsplit, Cat.assoc]
  exact comp_mono_left splits hnat

-- printing-only: the note's bead is `R`, the order the bracketing is optimised under.  The leaf
-- map, the split cost and the combine cost are the section's context, not part of the name.
open Lean PrettyPrinter in
@[app_unexpander R] public meta def unexpandBracketR : Unexpander
  | _ => `($(mkIdent `R))

end Freyd.Alg.RelSet.Bracket
