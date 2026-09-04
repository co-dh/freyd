/-
  Are the three PARTY beads of §7.3 natural transformations?  B&dM 5.13's LAX naturality asks
  `G(R) φ ⊑ φ F(R)` for EVERY relation `R` between the ELEMENT types — not for the single cost
  preorder that `AOP.A7_3_Party`'s greedy premises (`include_monotonic`, `exclude_monotonic`,
  `chooseR_monotonic`, `party_mono`) fix.  Those squares are the same shape at one `R`; these
  are the free theorems.

  VERDICT: all three are LAX ONLY.  `include` is a function, but it DISCARDS the first component
  of every subtree pair (`include = (𝟙×(list(π₂) concat)) cons`), so the reverse inclusion would
  need `list(R)` to be entire where the data was dropped; `Rtt` (on `Bool`: `true ↦ true`,
  `false ↦ nothing`) refutes it.  `S = ⟨include, exclude⟩` inherits that failure through
  `include` — and `exclude` is not even a map, it runs `choose` on every subtree.  `party = ⦇S⦈
  choose` inherits it through `⦇S⦈`, on the same counterexample lifted to a two-node tree.
-/
module

public import AOP.A7_3_Party

namespace Freyd.Alg.RelSet.Party

open Freyd CL ListRel
open RT (Rose dRose cataFold cataFoldList cataFoldList_eq_listP)

variable {A B : Type}

/-! ## The source object `x×[[x]×[x]]` and its relator -/

/-- The note's source object `x×[[x]×[x]]`: `F(A, [x]×[x])`, one branch of the rose tree with
    both parties already computed for every subtree. -/
public abbrev dBranch (A : Type) : RelSet.{0} :=
  (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})

/-- The relator of `x×[[x]×[x]]`: `R × list(list(R) × list(R))`. -/
@[expose] public def branch (R : dE A ⟶ dE B) : dBranch A ⟶ dBranch B :=
  rprodMap R (list (rprodMap (list R) (list R)))

/-! ## `include` -/

/-- Elementwise: a `R×S`-related pair of lists has `S`-related second components. -/
public theorem listP_cmap_snd {A₁ A₂ B₁ B₂ : Type} (R : dE A₁ ⟶ dE B₁) (S : dE A₂ ⟶ dE B₂) :
    ∀ (us : ConsList Unit (A₁ × A₂)) (vs : ConsList Unit (B₁ × B₂)),
      listP (rprodMap R S) us vs → listP S (cmap Prod.snd us) (cmap Prod.snd vs)
  | ConsList.wrap _, ConsList.wrap _, _ => trivial
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons _ us, ConsList.cons _ vs, h => ⟨h.1.2, listP_cmap_snd R S us vs h.2⟩

/-- **`include` is lax natural**: `(R×list(list R×list R)) include ⊑ include list(R)` — the
    root is passed through by `R`, and the concatenated second components are `list(R)`-related
    because `list(R)` cannot move an element across a segment boundary (`listP_cconcat`). -/
public theorem include_lax_natural (R : dE A ⟶ dE B) :
    branch R ≫ (graph includeFn : dBranch B ⟶ dList B)
      ⊑ (graph includeFn : dBranch A ⟶ dList A) ≫ list R := by
  refine le_iff.mpr fun u w h => ?_
  obtain ⟨v, ⟨h1, h2⟩, rfl⟩ := h
  exact ⟨includeFn u, rfl, h1,
    listP_cconcat R _ _ (listP_cmap_snd (list R) (list R) u.2 v.2 h2)⟩

/-! ## `choose` and `exclude` -/

/-- **`choose` is lax natural** — `choose_monotonic` says this for an endo-relation on one
    object; `choose` also relates two DIFFERENT element types, which is what naturality needs. -/
public theorem chooseR_lax_natural (R : dE A ⟶ dE B) :
    rprodMap (list R) (list R) ≫ chooseR ⊑ chooseR ≫ list R := by
  refine le_iff.mpr fun p y h => ?_
  obtain ⟨q, hq, hy⟩ := h
  rcases (show y = q.1 ∨ y = q.2 from hy) with rfl | rfl
  · exact ⟨p.1, Or.inl rfl, hq.1⟩
  · exact ⟨p.2, Or.inr rfl, hq.2⟩

/-- Elementwise `choose`, transferred back along the relator: whatever `choose` picks from the
    `B`-side subtree pairs, the matching component of the `A`-side pairs is `list(R)`-related
    to it.  The per-element choice is `chooseR_lax_natural`; no axiom of choice — the
    disjunction `choose = π₁∪π₂` is eliminated constructively at each element. -/
public theorem listP_choose_transfer (R : dE A ⟶ dE B) :
    ∀ (us : ConsList Unit (ConsList Unit A × ConsList Unit A))
      (vs : ConsList Unit (ConsList Unit B × ConsList Unit B))
      (qs : ConsList Unit (ConsList Unit B)),
      listP (rprodMap (list R) (list R)) us vs → listP chooseR vs qs →
      ∃ ps, listP chooseR us ps ∧ listP (list R) ps qs
  | ConsList.wrap _, ConsList.wrap _, ConsList.wrap _, _, _ => ⟨ConsList.wrap (), trivial, trivial⟩
  | ConsList.wrap _, ConsList.wrap _, ConsList.cons _ _, _, hq => hq.elim
  | ConsList.wrap _, ConsList.cons _ _, _, hp, _ => hp.elim
  | ConsList.cons _ _, ConsList.wrap _, _, hp, _ => hp.elim
  | ConsList.cons _ _, ConsList.cons _ _, ConsList.wrap _, _, hq => hq.elim
  | ConsList.cons u us, ConsList.cons v vs, ConsList.cons q qs, hp, hq => by
      obtain ⟨ps, hps, hpq⟩ := listP_choose_transfer R us vs qs hp.2 hq.2
      obtain ⟨x, hx, hxq⟩ := le_iff.mp (chooseR_lax_natural R) u q ⟨v, hp.1, hq.1⟩
      exact ⟨ConsList.cons x ps, ⟨hx, hps⟩, hxq, hpq⟩

/-- **`exclude` is lax natural**: `(R×list(list R×list R)) exclude ⊑ exclude list(R)`. -/
public theorem exclude_lax_natural (R : dE A ⟶ dE B) :
    branch R ≫ (excludeR : dBranch B ⟶ dList B)
      ⊑ (excludeR : dBranch A ⟶ dList A) ≫ list R := by
  refine le_iff.mpr fun u y h => ?_
  obtain ⟨v, ⟨-, h2⟩, qs, hqs, rfl⟩ := h
  obtain ⟨ps, hps, hpq⟩ := listP_choose_transfer R u.2 v.2 qs h2 hqs
  exact ⟨cconcat ps, ⟨ps, hps, rfl⟩, listP_cconcat R ps qs hpq⟩

/-! ## `S = ⟨include, exclude⟩` -/

/-- **`S` is lax natural**: `(R×list(list R×list R)) S ⊑ S (list R×list R)`.  `S` is NOT a map
    (`exclude` runs `choose` on every subtree), so an equality was never on the table; the two
    components are `include_lax_natural` and `exclude_lax_natural`, paired as in `party_mono`. -/
public theorem S_lax_natural (R : dE A ⟶ dE B) :
    branch R ≫ S ⊑ S ≫ rprodMap (list R) (list R) := by
  refine le_iff.mpr fun u p h => ?_
  obtain ⟨v, hv, hi, he⟩ := h
  obtain ⟨z1, hz1, hR1⟩ := le_iff.mp (include_lax_natural R) u p.1 ⟨v, hv, hi⟩
  obtain ⟨z2, hz2, hR2⟩ := le_iff.mp (exclude_lax_natural R) u p.2 ⟨v, hv, he⟩
  exact ⟨(z1, z2), ⟨hz1, hz2⟩, hR1, hR2⟩

/-! ## The tree relator `tree(R)` -/

mutual
  /-- `tree(R)`: same shape, roots related by `R`, subtrees elementwise.  Defined with its own
      list-of-subtrees copy so the nested recursion stays structural (as `cataFold` is). -/
  @[expose] public def roseP (R : dE A ⟶ dE B) : Rose A → Rose B → Prop
    | Rose.node a ts => fun t => ∃ b us, t = Rose.node b us ∧ R a b ∧ roseListP R ts us
  /-- `list(tree(R))`, unrolled. -/
  @[expose] public def roseListP (R : dE A ⟶ dE B) :
      ConsList Unit (Rose A) → ConsList Unit (Rose B) → Prop
    | ConsList.wrap _ => fun us => us = ConsList.wrap ()
    | ConsList.cons t ts => fun us =>
        ∃ u us', roseP R t u ∧ roseListP R ts us' ∧ us = ConsList.cons u us'
end

/-- The unrolled copy IS `list(tree(R))`. -/
public theorem roseListP_eq_listP (R : dE A ⟶ dE B) :
    ∀ (ts : ConsList Unit (Rose A)) (us : ConsList Unit (Rose B)),
      roseListP R ts us ↔ listP (roseP R) ts us
  | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨(fun h => nomatch h), False.elim⟩
  | ConsList.cons _ _, ConsList.wrap _ => ⟨(fun ⟨_, _, _, _, h⟩ => nomatch h), False.elim⟩
  | ConsList.cons t ts, ConsList.cons u us => by
      constructor
      · rintro ⟨u', us', h1, h2, heq⟩
        obtain ⟨rfl, rfl⟩ : u = u' ∧ us = us' :=
          ⟨(ConsList.cons.inj heq).1, (ConsList.cons.inj heq).2⟩
        exact ⟨h1, (roseListP_eq_listP R ts us).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨u, us, h1, (roseListP_eq_listP R ts us).mpr h2, rfl⟩

/-- `tree(R)` is the relator of the base functor `F(A,X) = A × [X]`, one layer at a time:
    `node(a,ts) tree(R) node(b,us)` iff `R a b` and `list(tree(R)) ts us`. -/
public theorem roseP_node (R : dE A ⟶ dE B) (a : A) (b : B)
    (ts : ConsList Unit (Rose A)) (us : ConsList Unit (Rose B)) :
    roseP R (Rose.node a ts) (Rose.node b us) ↔ R a b ∧ listP (roseP R) ts us := by
  constructor
  · rintro ⟨b', us', heq, hab, hus⟩
    obtain ⟨rfl, rfl⟩ : b = b' ∧ us = us' :=
      ⟨(Rose.node.inj heq).1, (Rose.node.inj heq).2⟩
    exact ⟨hab, (roseListP_eq_listP R ts us).mp hus⟩
  · rintro ⟨hab, hus⟩
    exact ⟨b, us, rfl, hab, (roseListP_eq_listP R ts us).mpr hus⟩

/-- `tree(R) : tree A ⟶ tree B`. -/
@[expose] public def rose (R : dE A ⟶ dE B) : dRose A ⟶ dRose B := roseP R

mutual
  /-- `tree(𝟙) = 𝟙`, pointwise — the relator law that pins `rose` down (and shows the lax
      square below is not vacuous: `rose(𝟙)` relates every tree to itself). -/
  public theorem roseP_id : ∀ t t' : Rose A, roseP (𝟙 (dE A)) t t' ↔ t = t'
    | Rose.node a ts, Rose.node b us => by
        constructor
        · rintro ⟨b', us', heq, hab, hus⟩
          obtain ⟨rfl, rfl⟩ : b = b' ∧ us = us' :=
            ⟨(Rose.node.inj heq).1, (Rose.node.inj heq).2⟩
          rw [(show a = b from hab), (roseListP_id ts us).mp hus]
        · rintro heq
          obtain ⟨rfl, rfl⟩ : a = b ∧ ts = us :=
            ⟨(Rose.node.inj heq).1, (Rose.node.inj heq).2⟩
          exact ⟨a, ts, rfl, rfl, (roseListP_id ts ts).mpr rfl⟩
  /-- `list(tree(𝟙)) = 𝟙`, pointwise. -/
  public theorem roseListP_id : ∀ ts us : ConsList Unit (Rose A),
      roseListP (𝟙 (dE A)) ts us ↔ ts = us
    | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => rfl, fun _ => rfl⟩
    | ConsList.wrap _, ConsList.cons _ _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | ConsList.cons _ _, ConsList.wrap _ =>
        ⟨(fun ⟨_, _, _, _, h⟩ => nomatch h), (fun h => nomatch h)⟩
    | ConsList.cons t ts, ConsList.cons u us => by
        constructor
        · rintro ⟨u', us', htu, hts, heq⟩
          obtain ⟨rfl, rfl⟩ : u = u' ∧ us = us' :=
            ⟨(ConsList.cons.inj heq).1, (ConsList.cons.inj heq).2⟩
          rw [(roseP_id t u).mp htu, (roseListP_id ts us).mp hts]
        · rintro heq
          obtain ⟨rfl, rfl⟩ : t = u ∧ ts = us :=
            ⟨(ConsList.cons.inj heq).1, (ConsList.cons.inj heq).2⟩
          exact ⟨t, ts, (roseP_id t t).mpr rfl, (roseListP_id ts ts).mpr rfl, rfl⟩
end

/-- `tree(𝟙) = 𝟙`. -/
public theorem rose_id : rose (𝟙 (dE A)) = 𝟙 (dRose A) := hom_ext roseP_id

/-! ## `party = ⦇S⦈ choose` -/

mutual
  /-- The catamorphism half: `tree(R) ⦇S⦈ ⊑ ⦇S⦈ (list R×list R)`, by tree induction from
      `S_lax_natural` (fold fusion, done structurally on `cataFold`). -/
  public theorem cataS_lax_natural (R : dE A ⟶ dE B) :
      ∀ (t : Rose A) (t' : Rose B) (w : ConsList Unit B × ConsList Unit B),
        roseP R t t' → cataFold S t' w →
        ∃ w₀, cataFold S t w₀ ∧ rprodMap (list R) (list R) w₀ w
    | Rose.node a ts, _, w, ht, hw => by
        obtain ⟨b, us, rfl, hab, hus⟩ := ht
        obtain ⟨rs, hrs, hS⟩ := hw
        obtain ⟨rs₀, hrs₀, hrel⟩ :=
          cataSList_lax_natural R ts us rs hus ((cataFoldList_eq_listP S us rs).mp hrs)
        obtain ⟨w₀, hw₀, hw₀rel⟩ :=
          le_iff.mp (S_lax_natural R) (a, rs₀) w ⟨(b, rs), ⟨hab, hrel⟩, hS⟩
        exact ⟨w₀, ⟨rs₀, (cataFoldList_eq_listP S ts rs₀).mpr hrs₀, hw₀⟩, hw₀rel⟩
  /-- The same, one list of subtrees at a time. -/
  public theorem cataSList_lax_natural (R : dE A ⟶ dE B) :
      ∀ (ts : ConsList Unit (Rose A)) (us : ConsList Unit (Rose B))
        (rs : ConsList Unit (ConsList Unit B × ConsList Unit B)),
        roseListP R ts us → listP (cataFold S) us rs →
        ∃ rs₀, listP (cataFold S) ts rs₀ ∧ listP (rprodMap (list R) (list R)) rs₀ rs
    | ConsList.wrap _, _, rs, ht, hr => by
        subst ht
        cases rs with
        | wrap _ => exact ⟨ConsList.wrap (), trivial, trivial⟩
        | cons _ _ => exact hr.elim
    | ConsList.cons t ts, _, rs, ht, hr => by
        obtain ⟨u, us', htu, hts, rfl⟩ := ht
        cases rs with
        | wrap _ => exact hr.elim
        | cons r rs' =>
            obtain ⟨w₀, hw₀, hrel⟩ := cataS_lax_natural R t u r htu hr.1
            obtain ⟨rs₀, hrs₀, hrel'⟩ := cataSList_lax_natural R ts us' rs' hts hr.2
            exact ⟨ConsList.cons w₀ rs₀, ⟨hw₀, hrs₀⟩, hrel, hrel'⟩
end

/-- **`party` is lax natural**: `tree(R) party ⊑ party list(R)` for every `R` — the fold half is
    `cataS_lax_natural`, the tail is `chooseR_lax_natural`. -/
public theorem party_lax_natural (R : dE A ⟶ dE B) :
    rose R ≫ party ⊑ party ≫ list R := by
  refine le_iff.mpr fun t y h => ?_
  obtain ⟨t', ht, w, hw, hy⟩ := h
  obtain ⟨w₀, hw₀, hrel⟩ := cataS_lax_natural R t t' w ht hw
  rcases (show y = w.1 ∨ y = w.2 from hy) with rfl | rfl
  · exact ⟨w₀.1, ⟨w₀, hw₀, Or.inl rfl⟩, hrel.1⟩
  · exact ⟨w₀.2, ⟨w₀, hw₀, Or.inr rfl⟩, hrel.2⟩

/-! ## None of the three is strict

  The witness is one non-entire relation.  `include` throws away the first component of every
  subtree pair, so the reverse inclusion has to invent a `list(R)`-image of data the right-hand
  side never looked at. -/

/-- On `Bool`: `true` relates to `true`, `false` to nothing — `Rtt` is not entire. -/
@[expose] public def Rtt : dE Bool ⟶ dE Bool := fun x y => x = true ∧ y = true

/-- `Rtt` relates `[false]` to no list at all. -/
public theorem Rtt_no_image : ∀ y, ¬ listP Rtt (ConsList.cons false (ConsList.wrap ())) y
  | ConsList.wrap _, h => h.elim
  | ConsList.cons _ _, h => Bool.noConfusion h.1.1

/-- The counterexample branch: root `true`, one subtree whose include-party is `[false]` (which
    `Rtt` relates to nothing) and whose exclude-party is `[]`. -/
@[expose] public def uEx : (dBranch Bool).carrier :=
  (true, ConsList.cons (ConsList.cons false (ConsList.wrap ()), ConsList.wrap ())
    (ConsList.wrap ()))

/-- `branch Rtt` relates `uEx` to nothing. -/
public theorem branch_Rtt_empty : ∀ v, ¬ branch Rtt uEx v
  | (_, ConsList.wrap _), h => h.2.elim
  | (_, ConsList.cons p _), h => Rtt_no_image p.1 h.2.1.1

/-- **`include` is not strict**: `include list(R) ⊑ (R×list(list R×list R)) include` fails at
    `Rtt` — the right-hand side must relate the discarded `[false]`, the left-hand side never
    sees it. -/
public theorem include_not_strict :
    ¬ ((graph includeFn : dBranch Bool ⟶ dList Bool) ≫ list Rtt
        ⊑ branch Rtt ≫ (graph includeFn : dBranch Bool ⟶ dList Bool)) := by
  intro hle
  have hrhs : ((graph includeFn : dBranch Bool ⟶ dList Bool) ≫ list Rtt) uEx
      (ConsList.cons true (ConsList.wrap ())) :=
    ⟨includeFn uEx, rfl, ⟨rfl, rfl⟩, trivial⟩
  obtain ⟨v, hv, -⟩ := le_iff.mp hle _ _ hrhs
  exact branch_Rtt_empty v hv

/-- **`S` is not strict**: it inherits `include_not_strict` in its first component. -/
public theorem S_not_strict :
    ¬ ((S : dBranch Bool ⟶ ⟨ConsList Unit Bool × ConsList Unit Bool⟩)
        ≫ rprodMap (list Rtt) (list Rtt) ⊑ branch Rtt ≫ S) := by
  intro hle
  have hrhs : ((S : dBranch Bool ⟶ ⟨ConsList Unit Bool × ConsList Unit Bool⟩)
      ≫ rprodMap (list Rtt) (list Rtt)) uEx
      (ConsList.cons true (ConsList.wrap ()), ConsList.wrap ()) :=
    ⟨(includeFn uEx, ConsList.wrap ()),
     ⟨rfl, ConsList.cons (ConsList.wrap ()) (ConsList.wrap ()), ⟨Or.inr rfl, trivial⟩, rfl⟩,
     ⟨⟨rfl, rfl⟩, trivial⟩, trivial⟩
  obtain ⟨v, hv, -⟩ := le_iff.mp hle _ _ hrhs
  exact branch_Rtt_empty v hv

/-- The counterexample tree: the president `true` with one subordinate `false`. -/
@[expose] public def tEx : Rose Bool :=
  Rose.node true (ConsList.cons (Rose.node false (ConsList.wrap ())) (ConsList.wrap ()))

/-- `tree(Rtt)` relates `tEx` to nothing. -/
public theorem rose_Rtt_empty : ∀ t', ¬ roseP Rtt tEx t' := by
  rintro _ ⟨_, _, rfl, -, hus⟩
  obtain ⟨_, _, hu, -, rfl⟩ := hus
  obtain ⟨_, _, rfl, hb, -⟩ := hu
  exact Bool.noConfusion hb.1

/-- **`party` is not strict**: `party list(R) ⊑ tree(R) party` fails at `Rtt`.  `party tEx`
    still returns `[true]` — the subordinate is simply not invited — but no tree is
    `tree(Rtt)`-related to `tEx`, because `Rtt` relates `false` to nothing. -/
public theorem party_not_strict :
    ¬ ((party : dRose Bool ⟶ dList Bool) ≫ list Rtt ⊑ rose Rtt ≫ party) := by
  intro hle
  have hleaf : cataFold S (Rose.node false (ConsList.wrap ()))
      (ConsList.cons false (ConsList.wrap ()), ConsList.wrap ()) :=
    ⟨ConsList.wrap (), rfl, rfl, ConsList.wrap (), trivial, rfl⟩
  have hroot : cataFold S tEx (ConsList.cons true (ConsList.wrap ()), ConsList.wrap ()) :=
    ⟨ConsList.cons (ConsList.cons false (ConsList.wrap ()), ConsList.wrap ()) (ConsList.wrap ()),
     ⟨_, ConsList.wrap (), hleaf, rfl, rfl⟩,
     rfl, ConsList.cons (ConsList.wrap ()) (ConsList.wrap ()), ⟨Or.inr rfl, trivial⟩, rfl⟩
  have hrhs : ((party : dRose Bool ⟶ dList Bool) ≫ list Rtt) tEx
      (ConsList.cons true (ConsList.wrap ())) :=
    ⟨ConsList.cons true (ConsList.wrap ()),
     ⟨_, hroot, Or.inl rfl⟩, ⟨rfl, rfl⟩, trivial⟩
  obtain ⟨t', ht, -⟩ := le_iff.mp hle _ _ hrhs
  exact rose_Rtt_empty t' ht

end Freyd.Alg.RelSet.Party
