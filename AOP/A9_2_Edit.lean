/-
  Bird & de Moor, *Algebra of Programming* §9.2  The string edit problem (book pp. 224-230).

  `edit ≜ ⦇[base,step]⦈ : [Op] ⟶ [Char]×[Char]` reconstitutes two strings from an edit
  sequence — `cpy a` appends `a` to both, `del a` to the left only, `ins a` to the right only.
  The specification is `edit° est(R)` with `R ≜ length ≤ length°`: a SHORTEST edit sequence
  from which both strings can be reconstituted.

  What is certified here is the note's `edit-defn` and the second row of `edit-laws`, Theorem
  9.2 at `Q ≜ 𝟙+(U×V)`, `U ≜ ⊤`, `V ≜ suffix°×suffix°`.  The two `#src` claims that carry it:

  * monotonicity `F(R)α ⊑ αR` is Proposition 9.2 (`AOP.A9_1.monotonicAlg_of_cost`) at
    `length ≜ ⦇[zero,π₂ succ]⦈` — `edit_mono`;
  * the thinning condition is Proposition 9.4 at `U ≜ ⊤` and `V ≜ suffix°×suffix°`, whose
    substance is `edit V° ⊑ R° edit` — `edit_Vrecip`, the note's two rows
    `edit (suffix×𝟙) ⊑ R° edit` and `edit (𝟙×suffix) ⊑ R° edit` composed.

  NO IN-CONTEXT TRAP HERE.  Unlike `AOP.A8_6_Tour`'s `tour-mono`, whose positive rows are
  false as printed because the book argues them only for tours of the SAME input, `V`'s two
  rows are unconditional: `shrink_left`/`shrink_right` prove them for EVERY edit sequence, by
  the `cpy`/`del`/`ins` induction the book sketches on p.226 ("if `e = ins b`, remove it; if
  `e = cpy b`, replace it by `del b`").  Both constructions leave the other output alone and
  never lengthen the sequence, which is exactly `R°`.

  Proposition 9.4 is used through its concrete instance rather than
  `AOP.A9_1.birelator_thin_condition`: the `Birelator` `G(Y,X) = L + Y×X` that instance needs
  is `rel.AutoDeriveGreedyDP.sumBirel`, which lives DOWNSTREAM of this file (it imports
  `AOP.A10_1`), and copying it here would be the duplication the abstract route exists to
  avoid.  `Q ≜ 𝟙+(⊤×V)` is written out and `edit_thin_condition` derives Theorem 9.2's `hQ`
  from `edit_V` — the same calculation, at one relator.

  NOT DONE, and why:
  * `edit-laws` row 3 (the `empty→nil` split) is **Proposition 9.1**, dropped for the whole
    repo by the setting-mismatch note at the end of `AOP.A9_1` (coreflexive negation lives in
    `DistributiveAllegory`, thinning in `UnguardedPowerLCDA`, and no `𝒜` instantiates both).
  * `edit-laws` rows 5-7 (the tabulation, `column`/`nextcol`) are curried functions on lists,
    which the note itself marks as outside the relational picture.
  * `unstep` is defined and proved SOUND (everything it returns is a decomposition,
    `unstep_sound`); "unstep implements `frac(step°,∋) thin(U×V)`" as a relational inequality
    is not proved.
-/
module

public import AOP.A9_1
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Edit

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {Char : Type}

/-! ## `edit-defn` -/

/-- **edit-defn**: `Op::=cpy Char∣del Char∣ins Char`. -/
public inductive Op (Char : Type) where
  | cpy : Char → Op Char
  | del : Char → Op Char
  | ins : Char → Op Char

/-- The object carrying edit sequences `[Op]`. -/
@[expose] public abbrev dEdit (Char : Type) : RelSet.{0} := dCL Unit (Op Char)

/-- The object carrying the two strings `[Char]×[Char]`. -/
@[expose] public abbrev dPair (Char : Type) : RelSet.{0} :=
  ⟨ConsList Unit Char × ConsList Unit Char⟩

/-- **edit-defn**: `base` returning `([],[])`, and `step (cpy a,(xs,ys))=([a]⧺xs,[a]⧺ys)`,
    `step (del a,(xs,ys))=([a]⧺xs,ys)`, `step (ins a,(xs,ys))=(xs,[a]⧺ys)`. -/
@[expose] public def baseStepFn :
    (Fobj Unit (Op Char) (dPair Char)).carrier → ConsList Unit Char × ConsList Unit Char
  | Sum.inl _ => (ConsList.wrap (), ConsList.wrap ())
  | Sum.inr (Op.cpy a, p) => (ConsList.cons a p.1, ConsList.cons a p.2)
  | Sum.inr (Op.del a, p) => (ConsList.cons a p.1, p.2)
  | Sum.inr (Op.ins a, p) => (p.1, ConsList.cons a p.2)

/-- **edit-defn**: the algebra `[base,step] : F(Op,[Char]×[Char])⟶[Char]×[Char]`. -/
@[expose] public def editAlg : (F Unit (Op Char)).obj (dPair Char) ⟶ dPair Char :=
  graph baseStepFn

/-- **edit-defn**: `edit≜⦇[base,step]⦈`, read as the function it is. -/
@[expose] public def editFn : ConsList Unit (Op Char) → ConsList Unit Char × ConsList Unit Char
  | ConsList.wrap _ => (ConsList.wrap (), ConsList.wrap ())
  | ConsList.cons op es => baseStepFn (Sum.inr (op, editFn es))

@[simp] public theorem editFn_nil (u : Unit) :
    editFn (ConsList.wrap u : ConsList Unit (Op Char))
      = (ConsList.wrap (), ConsList.wrap ()) := rfl
@[simp] public theorem editFn_cpy (a : Char) (es : ConsList Unit (Op Char)) :
    editFn (ConsList.cons (Op.cpy a) es)
      = (ConsList.cons a (editFn es).1, ConsList.cons a (editFn es).2) := rfl
@[simp] public theorem editFn_del (a : Char) (es : ConsList Unit (Op Char)) :
    editFn (ConsList.cons (Op.del a) es)
      = (ConsList.cons a (editFn es).1, (editFn es).2) := rfl
@[simp] public theorem editFn_ins (a : Char) (es : ConsList Unit (Op Char)) :
    editFn (ConsList.cons (Op.ins a) es)
      = ((editFn es).1, ConsList.cons a (editFn es).2) := rfl

/-- **edit-defn**: the catamorphism of `[base,step]` IS `editFn`. -/
public theorem edit_cata : cataR (editAlg (Char := Char)) = graph editFn := by
  apply hom_ext; intro es
  induction es with
  | wrap _ => exact fun p => Iff.rfl
  | cons op es ih =>
    intro p
    constructor
    · rintro ⟨p', hp', hstep⟩
      obtain rfl : p' = editFn es := (ih p').mp hp'
      exact hstep
    · intro (h : p = baseStepFn (Sum.inr (op, editFn es)))
      exact ⟨editFn es, (ih _).mpr rfl, h⟩

/-- `≤` on `Nat`: the lengths of edit sequences are counts, so `R` is pulled back along a
    `Nat`-valued cost, not along `AOP.A5_6_ListCombinators`'s `Int`-valued `leq`. -/
@[expose] public def leqN : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Nat⟩ := fun m n => m ≤ n

/-- **edit-defn**: the algebra `[zero,π₂ succ]` of `length`. -/
@[expose] public def lenAlgFn : (Fobj Unit (Op Char) (⟨Nat⟩ : RelSet.{0})).carrier → Nat
  | Sum.inl _ => 0
  | Sum.inr p => p.2 + 1

/-- **edit-defn**: `length≜⦇[zero,π₂ succ]⦈` is the list length `clen`. -/
public theorem length_cata :
    cataR (graph (lenAlgFn (Char := Char)))
      = (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0})) := by
  apply hom_ext; intro es
  induction es with
  | wrap _ => exact fun n => Iff.rfl
  | cons op es ih =>
    intro n
    constructor
    · rintro ⟨m, hm, hstep⟩
      obtain rfl : m = clen es := (ih m).mp hm
      exact hstep
    · intro (h : n = clen es + 1)
      exact ⟨clen es, (ih _).mpr rfl, h⟩

/-- **edit-defn**: `R≜length≤length°`. -/
@[expose] public def R (Char : Type) : dEdit Char ⟶ dEdit Char := fun es fs => clen es ≤ clen fs

public theorem R_eq :
    R Char = (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0})) ≫ leqN
      ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  apply hom_ext; intro es fs
  constructor
  · intro h; exact ⟨clen es, rfl, clen fs, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    obtain rfl : m = clen es := hm
    obtain rfl : n = clen fs := hn
    exact hmn

public theorem R_recip_trans : (R Char)° ≫ (R Char)° ⊑ (R Char)° :=
  le_iff.mpr fun es gs h => by
    obtain ⟨fs, h1, h2⟩ := h
    exact Nat.le_trans (h2 : clen gs ≤ clen fs) (h1 : clen fs ≤ clen es)

/-- **edit-defn**: `V≜suffix°×suffix°` — `V (xs,ys) (xs',ys')` iff `xs` is a suffix of `xs'`
    and `ys` a suffix of `ys'`. -/
@[expose] public def V (Char : Type) : dPair Char ⟶ dPair Char :=
  rprodMap (suffixR (A := Char))° (suffixR (A := Char))°

/-- **edit-defn**: `U≜⊤`, `Q≜𝟙+(U×V)` — the identity on the `base` summand; on the `step`
    summand `U≜⊤` leaves any two operations comparable and `V` orders the two strings. -/
@[expose] public def Q (Char : Type) :
    (F Unit (Op Char)).obj (dPair Char) ⟶ (F Unit (Op Char)).obj (dPair Char) :=
  fun u v => match u, v with
    | Sum.inl _, Sum.inl _ => True
    | Sum.inr p, Sum.inr q => V Char p.2 q.2
    | _, _ => False

/-- **edit-defn**: `unstep ([a]⧺xs,[])=[(del a,(xs,[]))]`,
    `unstep ([],[b]⧺ys)=[(ins b,([],ys))]`, and
    `unstep ([a]⧺xs,[b]⧺ys)=(a=b→[(cpy a,(xs,ys))],[(del a,(xs,[b]⧺ys)),(ins b,([a]⧺xs,ys))])`
    — the thinned decompositions, a copy beating a delete and an insert where available. -/
@[expose] public def unstep [DecidableEq Char] :
    ConsList Unit Char × ConsList Unit Char →
      List (Op Char × (ConsList Unit Char × ConsList Unit Char))
  | (ConsList.wrap _, ConsList.wrap _) => []
  | (ConsList.cons a xs, ConsList.wrap _) => [(Op.del a, (xs, ConsList.wrap ()))]
  | (ConsList.wrap _, ConsList.cons b ys) => [(Op.ins b, (ConsList.wrap (), ys))]
  | (ConsList.cons a xs, ConsList.cons b ys) =>
      if a = b then [(Op.cpy a, (xs, ys))]
      else [(Op.del a, (xs, ConsList.cons b ys)), (Op.ins b, (ConsList.cons a xs, ys))]

/-- **edit-laws**, the sound half of `unstep` implementing `frac(step°,∋) thin(U×V)`:
    everything `unstep` returns really is a decomposition, `step (unstep p) = p`. -/
public theorem unstep_sound [DecidableEq Char]
    (p : ConsList Unit Char × ConsList Unit Char)
    (q : Op Char × (ConsList Unit Char × ConsList Unit Char)) (h : q ∈ unstep p) :
    baseStepFn (Sum.inr q) = p := by
  obtain ⟨xs, ys⟩ := p
  cases xs with
  | wrap _ =>
    cases ys with
    | wrap _ => simp [unstep] at h
    | cons b ys => simp only [unstep, List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl
  | cons a xs =>
    cases ys with
    | wrap _ =>
      simp only [unstep, List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl
    | cons b ys =>
      by_cases hab : a = b
      · subst hab
        simp only [unstep, if_pos, List.mem_cons, List.not_mem_nil, or_false] at h
        subst h; rfl
      · simp only [unstep, if_neg hab, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> rfl

/-! ## `edit-laws` — monotonicity, Proposition 9.2 at `length` -/

public theorem lenAlg_comm :
    graph con ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
      = (F Unit (Op Char)).map (graph clen) ≫ graph lenAlgFn := by
  apply hom_ext; intro u n
  constructor
  · rintro ⟨dec, hdec, hn⟩
    obtain rfl : dec = con u := hdec
    cases u with
    | inl _ => exact ⟨Sum.inl (), rfl, hn⟩
    | inr p => exact ⟨Sum.inr (p.1, clen p.2), ⟨rfl, rfl⟩, hn⟩
  · rintro ⟨w, hw, hn⟩
    cases u with
    | inl _ =>
      cases w with
      | inl _ => exact ⟨ConsList.wrap (), rfl, hn⟩
      | inr _ => exact hw.elim
    | inr p =>
      cases w with
      | inl _ => exact hw.elim
      | inr q =>
        obtain ⟨op, m⟩ := q
        obtain ⟨op', es⟩ := p
        refine ⟨ConsList.cons op' es, rfl, ?_⟩
        obtain rfl : m = clen es := hw.2
        exact hn

public theorem lenAlg_mono :
    (F Unit (Op Char)).map leqN ≫ graph lenAlgFn ⊑ graph lenAlgFn ≫ leqN :=
  le_iff.mpr fun u n h => by
    obtain ⟨w, hw, hn⟩ := h
    cases u with
    | inl _ =>
      cases w with
      | inl _ => exact ⟨0, rfl, Nat.zero_le n⟩
      | inr _ => exact hw.elim
    | inr p =>
      cases w with
      | inl _ => exact hw.elim
      | inr q =>
        refine ⟨p.2 + 1, rfl, ?_⟩
        show p.2 + 1 ≤ n
        rw [(hn : n = q.2 + 1)]
        exact Nat.succ_le_succ (hw.2 : p.2 ≤ q.2)

/-- **edit-laws**, second row's monotonicity `F(R)α⊑αR`: Proposition 9.2 at
    `length≜⦇[zero,π₂ succ]⦈`, `succ` monotonic on `≤`, so `cons` is monotonic on `R`. -/
public theorem edit_mono : MonotonicAlg (F := F Unit (Op Char)) (graph con) (R Char) :=
  monotonicAlg_of_cost (graph_map clen) R_eq lenAlg_comm lenAlg_mono

/-- Theorem 9.2 asks for monotonicity at the mirrored `R°`, which `cons` also has. -/
public theorem edit_mono_recip : MonotonicAlg (F := F Unit (Op Char)) (graph con) (R Char)° :=
  (monotonicAlg_recip_iff (graph_map con) (F_preservesRecip Unit (Op Char))).mp edit_mono

/-! ## `edit-laws` — the `V` condition, B&dM p.226

  The book's argument, on points: to shorten one output by a head, find the element of the
  edit sequence that produced that head and either delete it (an `ins`) or weaken it to a
  `del` (a `cpy`).  The other output is untouched and the sequence never grows. -/

/-- Dropping heads off the RIGHT output: every suffix `y` of `(edit es).2` is reached by an
    edit sequence `fs` no longer than `es`, with the left output unchanged. -/
public theorem shrink_right : ∀ (es : ConsList Unit (Op Char)) {y : ConsList Unit Char},
    suffixP y (editFn es).2 → ∃ fs, editFn fs = ((editFn es).1, y) ∧ clen fs ≤ clen es := by
  intro es
  induction es with
  | wrap _ =>
    intro y hy
    obtain rfl : y = ConsList.wrap () := hy
    exact ⟨ConsList.wrap (), rfl, Nat.le_refl _⟩
  | cons op es ih =>
    intro y hy
    cases op with
    | cpy a =>
      rcases (hy : y = ConsList.cons a (editFn es).2 ∨ suffixP y (editFn es).2) with rfl | h
      · exact ⟨ConsList.cons (Op.cpy a) es, rfl, Nat.le_refl _⟩
      · obtain ⟨fs, hfs, hlen⟩ := ih h
        exact ⟨ConsList.cons (Op.del a) fs, by simp only [editFn_del, editFn_cpy, hfs],
          Nat.succ_le_succ hlen⟩
    | del a =>
      obtain ⟨fs, hfs, hlen⟩ := ih (hy : suffixP y (editFn es).2)
      exact ⟨ConsList.cons (Op.del a) fs, by simp only [editFn_del, hfs],
        Nat.succ_le_succ hlen⟩
    | ins a =>
      rcases (hy : y = ConsList.cons a (editFn es).2 ∨ suffixP y (editFn es).2) with rfl | h
      · exact ⟨ConsList.cons (Op.ins a) es, rfl, Nat.le_refl _⟩
      · obtain ⟨fs, hfs, hlen⟩ := ih h
        exact ⟨fs, by simp only [editFn_ins, hfs], Nat.le_trans hlen (Nat.le_succ _)⟩

/-- Dropping heads off the LEFT output — the mirror of `shrink_right`, `ins` for `del`. -/
public theorem shrink_left : ∀ (es : ConsList Unit (Op Char)) {x : ConsList Unit Char},
    suffixP x (editFn es).1 → ∃ fs, editFn fs = (x, (editFn es).2) ∧ clen fs ≤ clen es := by
  intro es
  induction es with
  | wrap _ =>
    intro x hx
    obtain rfl : x = ConsList.wrap () := hx
    exact ⟨ConsList.wrap (), rfl, Nat.le_refl _⟩
  | cons op es ih =>
    intro x hx
    cases op with
    | cpy a =>
      rcases (hx : x = ConsList.cons a (editFn es).1 ∨ suffixP x (editFn es).1) with rfl | h
      · exact ⟨ConsList.cons (Op.cpy a) es, rfl, Nat.le_refl _⟩
      · obtain ⟨fs, hfs, hlen⟩ := ih h
        exact ⟨ConsList.cons (Op.ins a) fs, by simp only [editFn_ins, editFn_cpy, hfs],
          Nat.succ_le_succ hlen⟩
    | del a =>
      rcases (hx : x = ConsList.cons a (editFn es).1 ∨ suffixP x (editFn es).1) with rfl | h
      · exact ⟨ConsList.cons (Op.del a) es, rfl, Nat.le_refl _⟩
      · obtain ⟨fs, hfs, hlen⟩ := ih h
        exact ⟨fs, by simp only [editFn_del, hfs], Nat.le_trans hlen (Nat.le_succ _)⟩
    | ins a =>
      obtain ⟨fs, hfs, hlen⟩ := ih (hx : suffixP x (editFn es).1)
      exact ⟨ConsList.cons (Op.ins a) fs, by simp only [editFn_ins, hfs],
        Nat.succ_le_succ hlen⟩

/-- **edit-laws**, second row: `edit (𝟙×suffix)⊑R° edit`. -/
public theorem edit_suffix_right :
    graph (editFn (Char := Char)) ≫ rprodMap (𝟙 (dList Char)) suffixR
      ⊑ (R Char)° ≫ graph editFn :=
  le_iff.mpr fun es q h => by
    obtain ⟨p, hp, hx, hy⟩ := h
    obtain rfl : p = editFn es := hp
    obtain ⟨fs, hfs, hlen⟩ := shrink_right es (hy : suffixP q.2 (editFn es).2)
    refine ⟨fs, hlen, ?_⟩
    show q = editFn fs
    rw [hfs, (hx : (editFn es).1 = q.1)]

/-- **edit-laws**, second row: `edit (suffix×𝟙)⊑R° edit`. -/
public theorem edit_suffix_left :
    graph (editFn (Char := Char)) ≫ rprodMap suffixR (𝟙 (dList Char))
      ⊑ (R Char)° ≫ graph editFn :=
  le_iff.mpr fun es q h => by
    obtain ⟨p, hp, hx, hy⟩ := h
    obtain rfl : p = editFn es := hp
    obtain ⟨fs, hfs, hlen⟩ := shrink_left es (hx : suffixP q.1 (editFn es).1)
    refine ⟨fs, hlen, ?_⟩
    show q = editFn fs
    rw [hfs, (hy : (editFn es).2 = q.2)]

/-- **edit-laws**, second row: the two rows composed, `edit V°⊑R° edit` at
    `V≜suffix°×suffix°` — shorten one output, then the other, never lengthening. -/
public theorem edit_Vrecip :
    graph (editFn (Char := Char)) ≫ (V Char)° ⊑ (R Char)° ≫ graph editFn := by
  have hsplit : (V Char)° = rprodMap (suffixR (A := Char)) (𝟙 (dList Char))
      ≫ rprodMap (𝟙 (dList Char)) (suffixR (A := Char)) := by
    rw [rprodMap_comp, Cat.comp_id, Cat.id_comp, V, rprodMap_recip]
    simp only [Allegory.recip_recip]
  rw [hsplit, ← Cat.assoc]
  refine le_trans (comp_mono_right edit_suffix_left _) ?_
  rw [Cat.assoc]
  refine le_trans (comp_mono_left _ edit_suffix_right) ?_
  rw [← Cat.assoc]
  exact comp_mono_right R_recip_trans _

/-- **edit-laws**, second row: Proposition 9.4's `hV`, `V edit°⊑edit° R`. -/
public theorem edit_V :
    V Char ≫ (graph (editFn (Char := Char)))° ⊑ (graph editFn)° ≫ R Char := by
  have h := recip_mono (edit_Vrecip (Char := Char))
  rw [Allegory.recip_comp, Allegory.recip_comp] at h
  exact h

/-- **edit-laws**, second row: Theorem 9.2's thinning condition, Proposition 9.4 at `U≜⊤` and
    `V≜suffix°×suffix°`.  The `base` summand needs only reflexivity of `R`; on the `step`
    summand `U≜⊤` leaves the operation free and `edit_V` supplies the shorter sequence for the
    `V`-smaller pair of strings, which `cons` then lengthens by one on both sides. -/
public theorem edit_thin_condition :
    Q Char ≫ (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°) ≫ graph con
      ⊑ (F Unit (Op Char)).map ((graph editFn)°) ≫ graph con ≫ R Char :=
  le_iff.mpr fun u es h => by
    obtain ⟨v, hQ, w, hFw, hcon⟩ := h
    cases u with
    | inl _ =>
      cases v with
      | inr _ => exact hQ.elim
      | inl _ =>
        cases w with
        | inr _ => exact hFw.elim
        | inl _ =>
          obtain rfl : es = ConsList.wrap () := hcon
          exact ⟨Sum.inl (), rfl, ConsList.wrap (), rfl, Nat.le_refl _⟩
    | inr p =>
      cases v with
      | inl _ => exact hQ.elim
      | inr q =>
        cases w with
        | inl _ => exact hFw.elim
        | inr r =>
          obtain rfl : es = ConsList.cons r.1 r.2 := hcon
          obtain ⟨t₀, ht₀, hlen⟩ := le_iff.mp edit_V p.2 r.2
            ⟨q.2, hQ, (hFw.2 : q.2 = editFn r.2)⟩
          exact ⟨Sum.inr (p.1, t₀), ⟨rfl, ht₀⟩, ConsList.cons p.1 t₀, rfl,
            Nat.succ_le_succ hlen⟩

/-- **edit-laws**, second row (B&dM p.226): a shortest edit sequence is the least fixed point
    of `(μX : [base,step]° thin Q P([nil,(𝟙×X)cons]) est(R))` — Theorem 9.2 at `Q≜𝟙+(U×V)`,
    `U≜⊤`, `V≜suffix°×suffix°`.  `H = ⦇α⦈·⦇[base,step]⦈°` collapses to `edit°` by reflection
    (`AOP.A6_ConsList.cataR_con`). -/
public theorem edit_laws :
    mu (fun X : dPair Char ⟶ dEdit Char =>
        Λ ((editAlg (Char := Char))°) ≫ thinRel (Q Char)
          ≫ powerRel ((F Unit (Op Char)).map X ≫ graph con) ≫ est (R Char))
      ⊑ Λ ((graph (editFn (Char := Char)))°) ≫ est (R Char) := by
  have hH : (relCata (editAlg (Char := Char)))° ≫ relCata (graph con)
      = (graph (editFn (Char := Char)))° := by
    rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, edit_cata]
    exact Cat.comp_id _
  have key := dynamic_programming_thin (F := F Unit (Op Char)) (F_preservesRecip Unit (Op Char))
    (initial Unit (Op Char)) (h := graph con) (T := editAlg (Char := Char)) (R := R Char)
    (Q := Q Char) (graph_map con) edit_mono_recip R_recip_trans
    (by rw [hH]; exact edit_thin_condition)
  rwa [hH] at key

end Freyd.Alg.RelSet.Edit
