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
  * `edit-tabulation` (`column`/`nextcol`) is curried functions on lists, outside the relational
    picture, so it is proved as function equations at the end of the file, `mle` taken as the
    recursive characterisation B&dM derive from the program on p.228.
  * `edit-laws` row 4 IS proved (`edit_prog`), but `unstep_complete` is completeness up to the
    thinning order, not on the nose: where the two heads agree `unstep` keeps the `cpy` alone, and
    the `del`/`ins` it drops are the ones that `cpy` beats under `V`.  That is what a thinning is,
    and it is all `thinRel` asks for — it is NOT `mem_reduce`'s iff.
-/
module

public import AOP.A9_1
public import AOP.A5_6_ListCombinators
public import AOP.A8_3
public import AOP.A6_GenFold
-- `listP_clen` — `list(P)` relates lists of one length — is the whole content of `est(R)`'s
-- naturality here, and it is stated once, for the schedules.
public import AOP.A7_5_VanBeads

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

/-! ### `Op` is a relator

  `Op` is an operation on the ALPHABET, so every end of this section — `[Op]`, `F(Op,[Char]×[Char])`,
  `Op×([Char]×[Char])` — is a functor of `Char` and states a naturality.  It is that functor only
  once `Op` is bundled as a lane; until then the pictures had `Op Char` varying with the index and
  no relator to read it as. -/

/-- `Op(R)` pointwise: the SAME operation, its character related by `R`. -/
@[expose] public def opP {A B : Type} (R : dE A ⟶ dE B) : Op A → Op B → Prop
  | Op.cpy a, Op.cpy b => R a b
  | Op.del a, Op.del b => R a b
  | Op.ins a, Op.ins b => R a b
  | _, _ => False

/-- `Op(R) : Op A ⟶ Op B`, the relator's action. -/
@[expose] public def opRel {A B : Type} (R : dE A ⟶ dE B) : dE (Op A) ⟶ dE (Op B) := opP R

public theorem opP_id {A : Type} : ∀ x y : Op A, opP (𝟙 (dE A)) x y ↔ x = y
  | Op.cpy a, Op.cpy b => ⟨fun h => by rw [show a = b from h], fun h => by cases h; exact rfl⟩
  | Op.del a, Op.del b => ⟨fun h => by rw [show a = b from h], fun h => by cases h; exact rfl⟩
  | Op.ins a, Op.ins b => ⟨fun h => by rw [show a = b from h], fun h => by cases h; exact rfl⟩
  | Op.cpy _, Op.del _ | Op.cpy _, Op.ins _ | Op.del _, Op.cpy _
  | Op.del _, Op.ins _ | Op.ins _, Op.cpy _ | Op.ins _, Op.del _ =>
      ⟨False.elim, fun h => nomatch h⟩

/-- `Op(𝟙) = 𝟙`. -/
public theorem op_id {A : Type} : opRel (𝟙 (dE A)) = 𝟙 (dE (Op A)) := hom_ext opP_id

public theorem opP_comp {A B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    ∀ (x : Op A) (z : Op C), opP (R ≫ S) x z ↔ ∃ y, opP R x y ∧ opP S y z
  | Op.cpy a, Op.cpy c => ⟨fun ⟨b, hR, hS⟩ => ⟨Op.cpy b, hR, hS⟩,
      fun ⟨y, h1, h2⟩ => by cases y <;> first | exact ⟨_, h1, h2⟩ | exact h1.elim | exact h2.elim⟩
  | Op.del a, Op.del c => ⟨fun ⟨b, hR, hS⟩ => ⟨Op.del b, hR, hS⟩,
      fun ⟨y, h1, h2⟩ => by cases y <;> first | exact ⟨_, h1, h2⟩ | exact h1.elim | exact h2.elim⟩
  | Op.ins a, Op.ins c => ⟨fun ⟨b, hR, hS⟩ => ⟨Op.ins b, hR, hS⟩,
      fun ⟨y, h1, h2⟩ => by cases y <;> first | exact ⟨_, h1, h2⟩ | exact h1.elim | exact h2.elim⟩
  | Op.cpy _, Op.del _ | Op.cpy _, Op.ins _ | Op.del _, Op.cpy _
  | Op.del _, Op.ins _ | Op.ins _, Op.cpy _ | Op.ins _, Op.del _ =>
      ⟨False.elim, fun ⟨y, h1, h2⟩ => by cases y <;> first | exact h1.elim | exact h2.elim⟩

/-- `Op(RS) = Op(R) Op(S)`. -/
public theorem op_comp {A B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    opRel (R ≫ S) = opRel R ≫ opRel S := hom_ext (opP_comp R S)

public theorem opP_mono {A B : Type} {R S : dE A ⟶ dE B} (h : ∀ a b, R a b → S a b) :
    ∀ x y, opP R x y → opP S x y
  | Op.cpy a, Op.cpy b, hxy => h a b hxy
  | Op.del a, Op.del b, hxy => h a b hxy
  | Op.ins a, Op.ins b, hxy => h a b hxy
  | Op.cpy _, Op.del _, hxy | Op.cpy _, Op.ins _, hxy | Op.del _, Op.cpy _, hxy
  | Op.del _, Op.ins _, hxy | Op.ins _, Op.cpy _, hxy | Op.ins _, Op.del _, hxy => hxy.elim

/-- `R ⊑ S ⟹ Op(R) ⊑ Op(S)`. -/
public theorem op_mono {A B : Type} {R S : dE A ⟶ dE B} (h : R ⊑ S) : opRel R ⊑ opRel S :=
  le_iff.mpr (opP_mono (le_iff.mp h))

/-- `Op` BUNDLED as a relator: the lane the edit pictures run the alphabet along. -/
@[expose] public def opRelator : Relator RelSet.{0} RelSet.{0} where
  obj a := dE (Op a.carrier)
  map R := opRel R
  map_id _ := op_id
  map_comp R S := op_comp R S
  map_mono h := op_mono h

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
@[expose] public def unstepFn [DecidableEq Char] :
    ConsList Unit Char × ConsList Unit Char →
      ConsList Unit (Op Char × (ConsList Unit Char × ConsList Unit Char))
  | (ConsList.wrap _, ConsList.wrap _) => ConsList.wrap ()
  | (ConsList.cons a xs, ConsList.wrap _) =>
      ConsList.cons (Op.del a, (xs, ConsList.wrap ())) (ConsList.wrap ())
  | (ConsList.wrap _, ConsList.cons b ys) =>
      ConsList.cons (Op.ins b, (ConsList.wrap (), ys)) (ConsList.wrap ())
  | (ConsList.cons a xs, ConsList.cons b ys) =>
      if a = b then ConsList.cons (Op.cpy a, (xs, ys)) (ConsList.wrap ())
      else ConsList.cons (Op.del a, (xs, ConsList.cons b ys))
            (ConsList.cons (Op.ins b, (ConsList.cons a xs, ys)) (ConsList.wrap ()))

-- The note's `[·]` is `ConsList Unit`, so the program returns one of THOSE: the panel's
-- `list((𝟙×mle)cons)` is the list relator at the same list type its `minlist(R)` reads, and a
-- Lean `List` here would put a second list type on the one wire.
/-- **edit-laws**, fourth row: `unstep : [Char]×[Char]⟶[Op×([Char]×[Char])]`, the arrow the
    panel draws. -/
@[expose] public def unstep [DecidableEq Char] :
    dPair Char ⟶ dList (Op Char × (dPair Char).carrier) := graph unstepFn

/-- **edit-laws**, the sound half of `unstep` implementing `frac(step°,∋) thin(U×V)`:
    everything `unstep` returns really is a decomposition, `step (unstep p) = p`. -/
public theorem unstep_sound [DecidableEq Char]
    (p : ConsList Unit Char × ConsList Unit Char)
    (q : Op Char × (ConsList Unit Char × ConsList Unit Char)) (h : inlistP (unstepFn p) q) :
    baseStepFn (Sum.inr q) = p := by
  obtain ⟨xs, ys⟩ := p
  cases xs with
  | wrap _ =>
    cases ys with
    | wrap _ => exact (h : False).elim
    | cons b ys =>
      obtain rfl | hf := (h : q = (Op.ins b, (ConsList.wrap (), ys)) ∨ False)
      · rfl
      · exact hf.elim
  | cons a xs =>
    cases ys with
    | wrap _ =>
      obtain rfl | hf := (h : q = (Op.del a, (xs, ConsList.wrap ())) ∨ False)
      · rfl
      · exact hf.elim
    | cons b ys =>
      by_cases hab : a = b
      · subst hab
        simp only [unstepFn, if_pos, inlistP, or_false] at h
        subst h; rfl
      · simp only [unstepFn, if_neg hab, inlistP, or_false] at h
        rcases h with rfl | rfl <;> rfl

/-- **edit-laws**, the COMPLETE half of the same implementation: what `unstep` drops, a returned
    decomposition beats.  For every `q` with `step q = p` there is a returned `q'` whose pair of
    strings is `V`-below `q`'s — where the two heads agree the copy is returned alone, and the
    `del` and `ins` it hides leave behind a LONGER pair, one operation more to spend; where they
    differ both survivors are returned, so nothing is dropped at all. -/
public theorem unstep_complete [DecidableEq Char]
    (p : ConsList Unit Char × ConsList Unit Char)
    (q : Op Char × (ConsList Unit Char × ConsList Unit Char))
    (h : baseStepFn (Sum.inr q) = p) :
    ∃ q', inlistP (unstepFn p) q' ∧ V Char q'.2 q.2 := by
  obtain ⟨op, x, y⟩ := q
  cases op with
  | cpy a =>
    subst h
    refine ⟨(Op.cpy a, (x, y)), ?_, ⟨suffixP.refl x, suffixP.refl y⟩⟩
    simp [baseStepFn, unstepFn, inlistP]
  | del a =>
    cases y with
    | wrap u =>
      subst h
      exact ⟨(Op.del a, (x, ConsList.wrap ())), Or.inl rfl, ⟨suffixP.refl x, rfl⟩⟩
    | cons b ys =>
      by_cases hab : a = b
      · subst hab
        subst h
        refine ⟨(Op.cpy a, (x, ys)), ?_, ⟨suffixP.refl x, Or.inr (suffixP.refl ys)⟩⟩
        simp [baseStepFn, unstepFn, inlistP]
      · subst h
        refine ⟨(Op.del a, (x, ConsList.cons b ys)), ?_,
          ⟨suffixP.refl x, suffixP.refl (ConsList.cons b ys)⟩⟩
        simp [baseStepFn, unstepFn, inlistP, if_neg hab]
  | ins b =>
    cases x with
    | wrap u =>
      subst h
      exact ⟨(Op.ins b, (ConsList.wrap (), y)), Or.inl rfl, ⟨rfl, suffixP.refl y⟩⟩
    | cons a xs =>
      by_cases hab : a = b
      · subst hab
        subst h
        refine ⟨(Op.cpy a, (xs, y)), ?_, ⟨Or.inr (suffixP.refl xs), suffixP.refl y⟩⟩
        simp [baseStepFn, unstepFn, inlistP]
      · subst h
        refine ⟨(Op.ins b, (ConsList.cons a xs, y)), ?_,
          ⟨suffixP.refl (ConsList.cons a xs), suffixP.refl y⟩⟩
        simp [baseStepFn, unstepFn, inlistP, if_neg hab]

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

/-! ### `edit-mono` — Proposition 9.2 at `length`, one step per fact (B&dM p.226) -/

/-- `edit-mono`, first step: `R≜length≤length°`, and `F` preserves composition. -/
public theorem edit_mono_step1 :
    (F Unit (Op Char)).map (R Char) ≫ graph con
      = (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ (F Unit (Op Char)).map leqN
          ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
          ≫ graph con := by
  rw [R_eq, (F Unit (Op Char)).map_comp, (F Unit (Op Char)).map_comp]; simp only [Cat.assoc]

/-- `edit-mono`, second step: `length` is entire, `𝟙⊑length length°`. -/
public theorem edit_mono_step2 :
    (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
        ≫ graph con
      ⊑ (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
        ≫ graph con ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  have h := comp_mono_left (graph con : (F Unit (Op Char)).obj (dEdit Char) ⟶ dEdit Char)
    (map_entire_le (graph_map (A := dEdit Char) (B := (⟨Nat⟩ : RelSet.{0})) clen))
  rw [Cat.comp_id] at h
  exact comp_mono_left _ (comp_mono_left _ (comp_mono_left _ h))

/-- `edit-mono`, third step: `α length=F(length)[zero,π₂ succ]` (`lenAlg_comm`). -/
public theorem edit_mono_step3 :
    (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
        ≫ graph con ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°
      = (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
        ≫ (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ graph lenAlgFn ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  have h := congrArg (fun Z => (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
    ≫ (F Unit (Op Char)).map leqN
    ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
    ≫ Z ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°) (lenAlg_comm (Char := Char))
  simpa only [Cat.assoc] using h

/-- `edit-mono`, fourth step: `F(length)` is simple, `F(length°)F(length)⊑F(𝟙)=𝟙`. -/
public theorem edit_mono_step4 :
    (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
        ≫ (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ graph lenAlgFn ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°
      ⊑ (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ graph lenAlgFn ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  have hs : (F Unit (Op Char)).map ((graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
      ≫ (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
      ⊑ 𝟙 _ := by
    rw [← (F Unit (Op Char)).map_comp, ← (F Unit (Op Char)).map_id]
    exact (F Unit (Op Char)).map_mono (graph_map clen).2
  have h := comp_mono_right hs
    (graph lenAlgFn ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
  rw [Cat.id_comp, Cat.assoc] at h
  exact comp_mono_left _ (comp_mono_left _ h)

/-- `edit-mono`, fifth step: `succ` is monotonic on `≤`, `F(≤)[zero,π₂ succ]⊑[zero,π₂ succ]≤`
    (`lenAlg_mono`). -/
public theorem edit_mono_step5 :
    (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ (F Unit (Op Char)).map leqN
        ≫ graph lenAlgFn ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°
      ⊑ (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ graph lenAlgFn ≫ leqN ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  have h := comp_mono_right (lenAlg_mono (Char := Char))
    (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°
  simp only [Cat.assoc] at h
  exact comp_mono_left _ h

/-- `edit-mono`, sixth step: `lenAlg_comm` read backwards. -/
public theorem edit_mono_step6 :
    (F Unit (Op Char)).map (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))
        ≫ graph lenAlgFn ≫ leqN ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°
      = graph con ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0})) ≫ leqN
        ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  have h := congrArg (fun Z => Z ≫ leqN ≫ (graph clen : dEdit Char ⟶ (⟨Nat⟩ : RelSet.{0}))°)
    (lenAlg_comm (Char := Char))
  simpa only [Cat.assoc] using h.symm

/-- **edit-laws**, second row's monotonicity `F(R)α⊑αR`: Proposition 9.2 at
    `length≜⦇[zero,π₂ succ]⦈`, `succ` monotonic on `≤`, so `cons` is monotonic on `R`. -/
public theorem edit_mono :
    (F Unit (Op Char)).map (R Char) ≫ graph con ⊑ graph con ≫ R Char :=
  calc (F Unit (Op Char)).map (R Char) ≫ graph con
      _ = _ := edit_mono_step1
      _ ⊑ _ := edit_mono_step2
      _ = _ := edit_mono_step3
      _ ⊑ _ := edit_mono_step4
      _ ⊑ _ := edit_mono_step5
      _ = _ := edit_mono_step6
      _ = graph con ≫ R Char := by rw [R_eq]

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

/-- `edit-V`, first step: `V°=suffix×suffix` splits into `(suffix×𝟙)(𝟙×suffix)`. -/
public theorem edit_Vrecip_step1 :
    graph (editFn (Char := Char)) ≫ (V Char)°
      = graph editFn ≫ rprodMap (suffixR (A := Char)) (𝟙 (dList Char))
          ≫ rprodMap (𝟙 (dList Char)) (suffixR (A := Char)) := by
  rw [rprodMap_comp, Cat.comp_id, Cat.id_comp, V, rprodMap_recip]
  simp only [Allegory.recip_recip]

/-- `edit-V`, second step: `edit (suffix×𝟙)⊑R° edit` (`edit_suffix_left`). -/
public theorem edit_Vrecip_step2 :
    graph (editFn (Char := Char)) ≫ rprodMap (suffixR (A := Char)) (𝟙 (dList Char))
        ≫ rprodMap (𝟙 (dList Char)) (suffixR (A := Char))
      ⊑ (R Char)° ≫ graph editFn ≫ rprodMap (𝟙 (dList Char)) (suffixR (A := Char)) := by
  have h := comp_mono_right (edit_suffix_left (Char := Char))
    (rprodMap (𝟙 (dList Char)) (suffixR (A := Char)))
  simpa only [Cat.assoc] using h

/-- `edit-V`, third step: `edit (𝟙×suffix)⊑R° edit` (`edit_suffix_right`). -/
public theorem edit_Vrecip_step3 :
    (R Char)° ≫ graph editFn ≫ rprodMap (𝟙 (dList Char)) (suffixR (A := Char))
      ⊑ (R Char)° ≫ (R Char)° ≫ graph editFn :=
  comp_mono_left _ edit_suffix_right

/-- `edit-V`, fourth step: `R°` is transitive (`R_recip_trans`). -/
public theorem edit_Vrecip_step4 :
    (R Char)° ≫ (R Char)° ≫ graph (editFn (Char := Char)) ⊑ (R Char)° ≫ graph editFn := by
  have h := comp_mono_right (R_recip_trans (Char := Char)) (graph (editFn (Char := Char)))
  simpa only [Cat.assoc] using h

/-- **edit-V**: `edit V°⊑R° edit` at `V≜suffix°×suffix°` — shorten one output, then the other,
    never lengthening. -/
public theorem edit_Vrecip :
    graph (editFn (Char := Char)) ≫ (V Char)° ⊑ (R Char)° ≫ graph editFn :=
  calc graph (editFn (Char := Char)) ≫ (V Char)°
      _ = _ := edit_Vrecip_step1
      _ ⊑ _ := edit_Vrecip_step2
      _ ⊑ _ := edit_Vrecip_step3
      _ ⊑ _ := edit_Vrecip_step4

/-- **edit-laws**, second row: Proposition 9.4's `hV`, `V edit°⊑edit° R`. -/
public theorem edit_V :
    V Char ≫ (graph (editFn (Char := Char)))° ⊑ (graph editFn)° ≫ R Char := by
  have h := recip_mono (edit_Vrecip (Char := Char))
  rw [Allegory.recip_comp, Allegory.recip_comp] at h
  exact h

/-! ### `edit-thin` — Proposition 9.4 at `Q≜F(⊤,V)`, one step per fact (B&dM p.226) -/

/-- The bifunctor `F(A,B)=1+(A×B)` preserves composition in both arguments at once. -/
public theorem Fbimap_comp {L E E' E'' : Type} {C C' C'' : RelSet.{0}} (U : dE E ⟶ dE E')
    (V : C ⟶ C') (U' : dE E' ⟶ dE E'') (V' : C' ⟶ C'') :
    Fbimap L U V ≫ Fbimap L U' V' = Fbimap L (U ≫ U') (V ≫ V') :=
  hom_ext fun u w => by
    cases u with
    | inl d => cases w with
      | inl d' => exact ⟨fun ⟨v, h1, h2⟩ => by
          cases v with
          | inl _ => exact h1.trans h2
          | inr _ => exact h1.elim, fun h => ⟨Sum.inl d, rfl, h⟩⟩
      | inr _ => exact ⟨fun ⟨v, h1, h2⟩ => by
          cases v with
          | inl _ => exact h2.elim
          | inr _ => exact h1.elim, fun h => h.elim⟩
    | inr p => cases w with
      | inl _ => exact ⟨fun ⟨v, h1, h2⟩ => by
          cases v with
          | inl _ => exact h1.elim
          | inr _ => exact h2.elim, fun h => h.elim⟩
      | inr q => exact ⟨fun ⟨v, h1, h2⟩ => by
          cases v with
          | inl _ => exact h1.elim
          | inr r => exact ⟨⟨r.1, h1.1, h2.1⟩, ⟨r.2, h1.2, h2.2⟩⟩,
        fun ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩ => ⟨Sum.inr (a, b), ⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩⟩

/-- `edit-thin`, first step: `Q≜𝟙+(U×V)` IS `F(U,V)` at `U≜⊤`. -/
public theorem edit_thin_step1 :
    Q Char ≫ (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°) ≫ graph con
      = Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) (V Char)
          ≫ (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°) ≫ graph con := by
  congr 1
  exact hom_ext fun u w => by
    cases u with
    | inl _ => cases w with
      | inl _ => exact ⟨fun _ => rfl, fun _ => trivial⟩
      | inr _ => exact Iff.rfl
    | inr p => cases w with
      | inl _ => exact Iff.rfl
      | inr q => exact ⟨fun h => ⟨topMor_apply _ _, h⟩, fun h => h.2⟩

/-- `edit-thin`, second step: `F(U,V)F(𝟙,edit°)=F(U,V edit°)`. -/
public theorem edit_thin_step2 :
    Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) (V Char)
        ≫ (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°) ≫ graph con
      = Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) (V Char ≫ (graph editFn)°)
          ≫ graph con := by
  rw [← Cat.assoc]
  congr 1
  exact (Fbimap_comp _ _ _ _).trans (by rw [Cat.comp_id])

/-- `edit-thin`, third step: Proposition 9.4's `V edit°⊑edit° R` (`edit_V`) under `F(U,−)`. -/
public theorem edit_thin_step3 :
    Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) (V Char ≫ (graph (editFn (Char := Char)))°)
        ≫ graph con
      ⊑ Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) ((graph editFn)° ≫ R Char)
          ≫ graph con :=
  comp_mono_right (le_iff.mpr fun u w h => by
    cases u with
    | inl _ => cases w with
      | inl _ => exact h
      | inr _ => exact h.elim
    | inr p => cases w with
      | inl _ => exact h.elim
      | inr q => exact ⟨h.1, le_iff.mp edit_V _ _ h.2⟩) _

/-- `edit-thin`, fourth step: `F(U,edit° R)=F(𝟙,edit°)F(U,R)`. -/
public theorem edit_thin_step4 :
    Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) ((graph (editFn (Char := Char)))° ≫ R Char)
        ≫ graph con
      = (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°)
          ≫ Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) (R Char) ≫ graph con := by
  rw [← Cat.assoc]
  congr 1
  exact ((Fbimap_comp _ _ _ _).trans (by rw [Cat.id_comp])).symm

/-- `edit-thin`, fifth step: Proposition 9.4's `F(U,R)α⊑αR` at `U≜⊤` — `cons` adds one to both
    lengths whatever the two operations are. -/
public theorem edit_thin_step5 :
    (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°)
        ≫ Fbimap Unit (topMor (dE (Op Char)) (dE (Op Char))) (R Char) ≫ graph con
      ⊑ (F Unit (Op Char)).map ((graph editFn)°) ≫ graph con ≫ R Char :=
  comp_mono_left _ (le_iff.mpr fun u es h => by
    obtain ⟨v, hv, hcon⟩ := h
    obtain rfl : es = con v := hcon
    refine ⟨con u, rfl, ?_⟩
    cases u with
    | inl _ => cases v with
      | inl _ => exact Nat.le_refl _
      | inr _ => exact hv.elim
    | inr p => cases v with
      | inl _ => exact hv.elim
      | inr q => exact Nat.succ_le_succ hv.2)

/-- **edit-laws**, second row: Theorem 9.2's thinning condition, Proposition 9.4 at `U≜⊤` and
    `V≜suffix°×suffix°`.  The `base` summand needs only reflexivity of `R`; on the `step`
    summand `U≜⊤` leaves the operation free and `edit_V` supplies the shorter sequence for the
    `V`-smaller pair of strings, which `cons` then lengthens by one on both sides. -/
public theorem edit_thin_condition :
    Q Char ≫ (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°) ≫ graph con
      ⊑ (F Unit (Op Char)).map ((graph editFn)°) ≫ graph con ≫ R Char :=
  calc Q Char ≫ (F Unit (Op Char)).map ((graph (editFn (Char := Char)))°) ≫ graph con
      _ = _ := edit_thin_step1
      _ = _ := edit_thin_step2
      _ ⊑ _ := edit_thin_step3
      _ = _ := edit_thin_step4
      _ ⊑ _ := edit_thin_step5

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
    (by simp only [H]; rw [hH]; exact edit_thin_condition)
  simp only [H] at key; rwa [hH] at key

/-! ## `edit-laws`, third row: Proposition 9.1 at the `step` summand

  `base` returns `([],[])` and no `step` returns it, so the body's thinning splits and the third
  row is the `step` arm alone.  That is `AOP.A9_1`'s `thin_summand_le` at `ι ≜ Sum.inr`, the one
  summand lemma the snoc-direction rows also use: its arm relator `Fᵢ` is whichever side of the
  product the recursion sits on — `−×E` there, the element-first `E×−` here. -/

/-- **edit-defn**: `step`, the second arm of `[base,step]`.  The note writes the third row at
    this arm alone, so the arm has the name the note gives it. -/
@[expose] public def step : (⟨Op Char × (dPair Char).carrier⟩ : RelSet.{0}) ⟶ dPair Char :=
  graph (fun q => baseStepFn (Sum.inr q))

/-- `step` never returns the empty pair — `cpy` and `del` put a character on the left string,
    `ins` one on the right — and `base` returns nothing else.  This is Proposition 9.1's
    disjointness hypothesis at `[base,step]`. -/
public theorem step_ne_base (q : Op Char × (dPair Char).carrier) :
    baseStepFn (Sum.inr q) ≠ ((ConsList.wrap () : ConsList Unit Char), ConsList.wrap ()) := by
  obtain ⟨op, p⟩ := q
  cases op with
  | cpy a => intro h; injection h with h1 _; cases h1
  | del a => intro h; injection h with h1 _; cases h1
  | ins a => intro h; injection h with _ h2; cases h2

/-- **edit-defn**: `base`, the first arm of `[base,step]`, returning `([],[])`. -/
@[expose] public def base : dL Unit ⟶ dPair Char := graph (fun d => baseStepFn (Sum.inl d))

/-- **edit-defn**: `empty`, the coreflexive on `(xs,ys)` with both lists empty. -/
@[expose] public def empty : dPair Char ⟶ dPair Char :=
  fun p q => p = q ∧ p = ((ConsList.wrap () : ConsList Unit Char), ConsList.wrap ())

/-- `edit-disj`, first step: `base` returns only `([],[])`, so `base°=empty base°`. -/
public theorem edit_disj_step1 :
    step (Char := Char) ≫ (base (Char := Char))° = step ≫ empty ≫ (base (Char := Char))° := by
  congr 1
  exact hom_ext fun p d => ⟨fun h => ⟨p, ⟨rfl, h⟩, h⟩, fun ⟨_, ⟨h1, _⟩, h2⟩ => h1 ▸ h2⟩

/-- `edit-disj`, second step: `step empty=𝟘`, no `step` returns `([],[])` (`step_ne_base`). -/
public theorem edit_disj_step2 :
    step (Char := Char) ≫ empty ≫ (base (Char := Char))° = 𝟘 ≫ (base (Char := Char))° := by
  rw [← Cat.assoc]
  congr 1
  exact hom_ext fun q p => ⟨fun ⟨_, h1, _, h2⟩ => absurd (h1.symm.trans h2) (step_ne_base q),
    fun h => h.elim⟩

/-- **edit-disj** (B&dM p.227): `base` and `step` have disjoint ranges, `step base°=𝟘` —
    Proposition 9.1's hypothesis. -/
public theorem edit_disj : step (Char := Char) ≫ (base (Char := Char))° = 𝟘 :=
  calc step (Char := Char) ≫ (base (Char := Char))°
      _ = _ := edit_disj_step1
      _ = _ := edit_disj_step2
      _ = 𝟘 := hom_ext fun _ _ => ⟨fun ⟨_, h, _⟩ => h.elim, fun h => h.elim⟩

/-- The `step` arm of `F(X)[nil,cons]` is the note's `(𝟙×X)cons`: `F(X)` keeps the operation and
    recurses in the second component. -/
public theorem arm_Fmap_con (X : dPair Char ⟶ dEdit Char)
    (p : Op Char × (dPair Char).carrier) (z : (dEdit Char).carrier) :
    (rprodMap (𝟙 (dE (Op Char))) X ≫ consR) p z
      ↔ ((F Unit (Op Char)).map X ≫ graph con) (Sum.inr p) z := by
  constructor
  · rintro ⟨q, hq, hz⟩
    exact ⟨Sum.inr q, ⟨hq.1, hq.2⟩, hz⟩
  · rintro ⟨w, hw, hz⟩
    cases w with
    | inl d => exact hw.elim
    | inr q => exact ⟨q, ⟨hw.1, hw.2⟩, hz⟩

/-- **edit-laws**, third row (Proposition 9.1): the branch
    `(step°)%∋ thin(U×V)P((𝟙×X)cons)est(R)` refines `edit_laws`' body
    `([base,step]°)%∋ thin(Q)P([nil,(𝟙×X)cons])est(R)` — `AOP.A9_1.thin_summand_le` at
    `ι ≜ Sum.inr`, whose `Qᵢ` at `Q ≜ 𝟙+(U×V)` is `U×V` with `U ≜ ⊤`. -/
public theorem edit_branch (X : dPair Char ⟶ dEdit Char) :
    Λ ((step (Char := Char))°)
        ≫ thinRel (rprodMap (topMor (dE (Op Char)) (dE (Op Char))) (V Char))
        ≫ powerRel (rprodMap (𝟙 (dE (Op Char))) X ≫ consR) ≫ est (R Char)
      ⊑ Λ ((editAlg (Char := Char))°) ≫ thinRel (Q Char)
          ≫ powerRel ((F Unit (Op Char)).map X ≫ graph con) ≫ est (R Char) := by
  have hmap : (Relator.prod (Relator.const (dE (Op Char)))
      (Relator.idRelator RelSet.{0})).map X = rprodMap (𝟙 (dE (Op Char))) X :=
    prodMap_eq_rprodMap _ _
  have key := RelSet.thin_summand_le
    (Fᵢ := Relator.prod (Relator.const (dE (Op Char))) (Relator.idRelator RelSet.{0}))
    (F := F Unit (Op Char)) (T := editAlg (Char := Char)) (Q := Q Char) (X := X)
    (h := graph con) (R := R Char) (Vᵢ := step) (Uᵢ := consR)
    (Qᵢ := rprodMap (topMor (dE (Op Char)) (dE (Op Char))) (V Char))
    Sum.inr (graph_map _) (fun _ _ => Iff.rfl) (fun _ _ h => h.2)
    (fun p z => by rw [hmap]; exact arm_Fmap_con X p z)
    (fun w p y hstep hT => by
      cases w with
      | inl d =>
        have hy : baseStepFn (Sum.inr p)
            = ((ConsList.wrap () : ConsList Unit Char), ConsList.wrap ()) :=
          Eq.trans (Eq.symm hstep) hT
        exact absurd hy (step_ne_base p)
      | inr q => exact ⟨q, rfl⟩)
  rwa [hmap] at key

/-! ## edit-laws, fourth row: `unstep` IS the thinned decomposition -/

/-- **edit-laws**, fourth row: `unstep` implements `frac(step°,∋) thin(U×V)` — the note's own
    claim for that row, and the two halves of `thinRel` are exactly `unstep`'s two.  Read as a
    set: `setify(unstep p)` is a subset of `p`'s decompositions (`unstep_sound`) that still
    dominates all of them (`unstep_complete`), which is what a thinning is.  `U≜⊤` on the
    operation leaves the three comparable and `V` orders the two strings. -/
public theorem unstep_thins [DecidableEq Char] :
    unstep ≫ setify
      ⊑ Λ ((step (Char := Char))°)
          ≫ thinRel (rprodMap (topMor (dE (Op Char)) (dE (Op Char))) (V Char)) := by
  rw [le_iff]
  rintro p Y ⟨L, rfl, rfl⟩
  refine ⟨fun q => step q p, by rw [Λ_eq_classifier]; rfl, ?_, ?_⟩
  · intro q hq
    exact (unstep_sound p q hq).symm
  · intro q hq
    obtain ⟨q', hq', hV⟩ := unstep_complete p q (hq : p = baseStepFn (Sum.inr q)).symm
    exact ⟨q', ⟨topMor_apply q'.1 q.1, hV⟩, hq'⟩

/-- **edit-laws**, fourth row (B&dM p.228): `unstep list((𝟙×mle)cons)minlist(R)` refines the branch
    `(step°)%∋ thin(U×V)P((𝟙×X)cons)est(R)` — `unstep` implements `(step°)%∋ thin(U×V)`
    (`unstep_thins`) and `minlist(R)` implements `est(R)`, the list standing in for the set it
    `setify`s to (`CL.list_comp_minlist_le`, `setify`'s lax naturality). -/
public theorem edit_prog [DecidableEq Char] (mle : dPair Char ⟶ dEdit Char) :
    unstep ≫ ListRel.list (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ minlist(R Char)
      ⊑ Λ ((step (Char := Char))°)
          ≫ thinRel (rprodMap (topMor (dE (Op Char)) (dE (Op Char))) (V Char))
          ≫ powerRel (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ est (R Char) :=
  calc unstep ≫ ListRel.list (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ minlist(R Char)
      ⊑ unstep ≫ ListRel.setify
          ≫ powerRel (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ est (R Char) :=
        comp_mono_left unstep (CL.list_comp_minlist_le _ _)
    _ = (unstep ≫ ListRel.setify)
          ≫ powerRel (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ est (R Char) := by
        rw [← Cat.assoc]
    _ ⊑ (Λ ((step (Char := Char))°)
            ≫ thinRel (rprodMap (topMor (dE (Op Char)) (dE (Op Char))) (V Char)))
          ≫ powerRel (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ est (R Char) :=
        comp_mono_right unstep_thins _
    _ = Λ ((step (Char := Char))°)
          ≫ thinRel (rprodMap (topMor (dE (Op Char)) (dE (Op Char))) (V Char))
          ≫ powerRel (rprodMap (𝟙 (dE (Op Char))) mle ≫ consR) ≫ est (R Char) := by
        rw [Cat.assoc]

/-! ## The beads of the `edit` panels, and what the environment says about them -/

/-- **`est(R)` is LAX natural** in the alphabet: `E(list(Op(S)))est(R) ⊑ est(R)list(Op(S))`.
    `R` compares LENGTHS and `Op(S)` relates an operation only to one of the same shape, so
    `list(Op(S))` relates sequences of equal length: a shortest sequence of the image comes from a
    member of the set, and that member is shortest there.  Not STRICT — the right side asks every
    member of the set for an image, which a relation that is not entire need not give. -/
public theorem est_R_laxNatural :
    LaxNatural (opRelator.comp listRelator) ((opRelator.comp listRelator).comp powerRelator)
      (fun a => est (R a.carrier)) := by
  intro x y S
  refine le_iff.mpr fun es r => ?_
  rintro ⟨fs, hxy, hest⟩
  obtain ⟨hfs, hmin⟩ := (est_apply _ _ _).mp hest
  obtain ⟨hfwd, hbwd⟩ := (powerRel_apply _ _ _).mp hxy
  obtain ⟨w, hw, hwr⟩ := hbwd r hfs
  refine ⟨w, (est_apply _ _ _).mpr ⟨hw, fun z hz => ?_⟩, hwr⟩
  obtain ⟨v, hzv, hv⟩ := hfwd z hz
  show clen w ≤ clen z
  rw [Van.listP_clen (P := opRel S) hwr, Van.listP_clen (P := opRel S) hzv]
  exact hmin v hv

/-- The `F` lane of the edit panels, spelled as the sum and product of the lanes its two summands
    are — `𝟏 + Op×[Op]` — which is what `[nil,cons]`'s two ends read as.  `F Unit (Op Char)` holds
    the alphabet FIXED, so its own `map` moves the tail alone and states no naturality in `Char`. -/
@[expose] public def opF : Relator RelSet.{0} RelSet.{0} :=
  Relator.sum (Relator.const (dL Unit)) (Relator.prod opRelator (opRelator.comp listRelator))

/-- `F(Op(S),list(Op(S)))` is the lane stack's own action: the leaf arm untouched, the pair arm
    moving the operation and the tail together.  `Fbimap` is the action `alphaR_natural` is
    written in, and the two agree pointwise. -/
public theorem opF_map {x y : RelSet.{0}} (S : x ⟶ y) :
    opF.map S = Fbimap Unit (opRel S) (list (opRel S)) := by
  apply hom_ext; intro u v
  cases u <;> cases v <;>
    simp [opF, Relator.sum, Relator.prod, Relator.const, Relator.comp, sumMap,
      junc, RelProd.pair, prodMap, graph, Fbimap, instPositiveAllegory, instHasRelProd, sumCop,
      opRelator, listRelator] <;> first | grind | exact Subsingleton.elim _ _

/-- **`[nil,cons]` is STRICTLY natural** in the alphabet: `F(Op(S),list(Op(S)))[nil,cons] =
    [nil,cons]list(Op(S))`.  `ListRel.alphaR_natural` at the alphabet `Op(Char)`, with the lane
    stack's action put in place of `Fbimap`'s — the canonical home is `A5_6_ListCombinators`, and
    this specialisation belongs beside it once that file is free. -/
public theorem con_strictNatural :
    StrictNatural (opRelator.comp listRelator) opF
      (fun a => (graph con : (F Unit (Op a.carrier)).obj (dEdit a.carrier) ⟶ dEdit a.carrier)) := by
  intro x y S
  rw [opF_map]
  exact (ListRel.alphaR_natural (opRel S)).symm

/-- The `F` lane at the PAIR carrier: `𝟏 + Op×([Char]×[Char])`, the source of `[base,step]`. -/
@[expose] public def pairF : Relator RelSet.{0} RelSet.{0} :=
  Relator.sum (Relator.const (dL Unit))
    (Relator.prod opRelator (Relator.prod listRelator listRelator))

public theorem pairF_map {x y : RelSet.{0}} (S : x ⟶ y) :
    pairF.map S = Fbimap Unit (opRel S) (rprodMap (list S) (list S)) := by
  apply hom_ext; intro u v
  cases u <;> cases v <;>
    simp [pairF, Relator.sum, Relator.prod, Relator.const, Relator.comp, sumMap, junc,
      RelProd.pair, prodMap, rprodMap, graph, Fbimap, instPositiveAllegory, instHasRelProd, sumCop,
      opRelator, listRelator] <;> first | grind | exact Subsingleton.elim _ _

/-- **`[base,step]` is LAX natural** in the alphabet: `F(Op(S),S×S)[base,step] ⊑
    [base,step](list(S)×list(S))`.  Not STRICT — `cpy a` writes ONE character into BOTH outputs, so
    the right side may send the two copies to two different characters of the new alphabet where
    the left side, which chooses the operation first, can only send them to one. -/
public theorem editAlg_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) pairF
      (fun a => editAlg (Char := a.carrier)) := by
  intro x y S
  rw [pairF_map]
  refine le_iff.mpr fun u q => ?_
  rintro ⟨v, hv, rfl⟩
  rcases u with d | ⟨op, xs, ys⟩ <;> rcases v with d' | ⟨op', xs', ys'⟩
  · simp_all [Fbimap, editAlg, graph, baseStepFn, Relator.prod, prodMap, RelProd.pair,
      instHasRelProd, rprodMap, listRelator, list, listP]
  · exact (hv : False).elim
  · exact (hv : False).elim
  · rcases op with a | a | a <;> rcases op' with b | b | b <;>
      simp_all [Fbimap, editAlg, graph, baseStepFn, Relator.prod, prodMap, RelProd.pair,
        instHasRelProd, rprodMap, opRel, opP, listRelator, list, listP]

/-- **`step` is LAX natural** — the `inr` arm of `editAlg_laxNatural`, at the arm's own lane
    `Op×([Char]×[Char])`, which is the relator `edit-laws`' third row draws. -/
public theorem step_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator)
      (Relator.prod opRelator (Relator.prod listRelator listRelator))
      (fun a => step (Char := a.carrier)) := by
  intro x y S
  refine le_iff.mpr fun u q => ?_
  rintro ⟨v, hv, rfl⟩
  obtain ⟨op, xs, ys⟩ := u
  obtain ⟨op', xs', ys'⟩ := v
  rcases op with a | a | a <;> rcases op' with b | b | b <;>
    simp_all [step, graph, baseStepFn, Relator.prod, prodMap, RelProd.pair, instHasRelProd,
      rprodMap, opRelator, opRel, opP, listRelator, list, listP]

/-- An edit sequence and one it is `Op(S)`-related to reconstitute `S`-related strings: every
    operation puts its own character where the related operation puts the related one. -/
public theorem editFn_rel {x y : RelSet.{0}} (S : x ⟶ y) :
    ∀ (es : ConsList Unit (Op x.carrier)) (fs : ConsList Unit (Op y.carrier)),
      listP (opRel S) es fs →
      listP S (editFn es).1 (editFn fs).1 ∧ listP S (editFn es).2 (editFn fs).2 := by
  intro es
  induction es with
  | wrap u => rintro (fs | ⟨op', fs⟩) h <;> simp_all [opRel, opP, listP]
  | cons op es ih =>
    rintro (fs | ⟨op', fs⟩) h
    · simp_all [opRel, opP, listP]
    · obtain ⟨h1, h2⟩ := ih fs h.2
      rcases op with a | a | a <;> rcases op' with b | b | b <;>
        simp_all [opRel, opP, listP]

/-- **`edit` is LAX natural**: `list(Op(S))edit ⊑ edit(list(S)×list(S))`.  Not STRICT — a `cpy`
    writes ONE character into BOTH strings, so a pair whose two copies of it are sent to different
    characters of the new alphabet is reached by no edit sequence. -/
public theorem edit_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (opRelator.comp listRelator)
      (fun a => graph (editFn (Char := a.carrier))) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _]
  refine le_iff.mpr fun es p => ?_
  rintro ⟨fs, hfs, rfl⟩
  obtain ⟨h1, h2⟩ := editFn_rel S es fs hfs
  exact ⟨editFn es, rfl, h1, h2⟩

/-- **`minlist(R)` is LAX natural**: `list(list(Op(S)))minlist(R) ⊑ minlist(R)list(Op(S))`.  The
    argument of `est_R_laxNatural` with the LIST standing in for the set it `setify`s to: a shortest
    member of the image list comes from a member of the original, of the same length, and every
    other member of the original has an image of its own length. -/
public theorem minlist_R_laxNatural :
    LaxNatural (opRelator.comp listRelator) ((opRelator.comp listRelator).comp listRelator)
      (fun a => CL.minlist (R a.carrier)) := by
  intro x y S
  refine le_iff.mpr fun ess r => ?_
  rintro ⟨fss, hff, hmin⟩
  obtain ⟨hr, hleast⟩ := (minlist_apply _ _ _).mp hmin
  obtain ⟨hfwd, hbwd⟩ := listP_inlistP_split (list (opRel S)) ess fss hff
  obtain ⟨w, hw, hwr⟩ := hbwd r ((clMem_iff_inlistP _ _).mp hr)
  refine ⟨w, (minlist_apply _ _ _).mpr ⟨(clMem_iff_inlistP _ _).mpr hw, fun z hz => ?_⟩, hwr⟩
  obtain ⟨v, hzv, hv⟩ := hfwd z ((clMem_iff_inlistP _ _).mp hz)
  show clen w ≤ clen z
  rw [Van.listP_clen (P := opRel S) hwr, Van.listP_clen (P := opRel S) hzv]
  exact hleast v ((clMem_iff_inlistP _ _).mpr hv)

/-! ## The two thinning beads are not even lax natural

  `V` orders the two strings by SUFFIX, and a suffix is a claim about the CHARACTERS that an
  alphabet map need not reflect.  Over `Bool` `[false]` is no suffix of `[true,true]`, so the two
  candidates are incomparable and a thinning must keep both; over `Unit` their images `[()]` and
  `[(),()]` ARE comparable and a thinning drops the longer.  So the left side of the square thins
  the IMAGE and reaches a one-element set, while the right side thins first, keeps both, and its
  image has two members. -/

/-- The alphabet map that identifies every character. -/
@[expose] public def toU : dE Bool ⟶ dE Unit := graph (fun _ : Bool => ())

/-- `[false]`, and `[true,true]`, of which it is no suffix. -/
@[expose] public def shortB : ConsList Unit Bool := ConsList.cons false (ConsList.wrap ())

@[expose] public def longB : ConsList Unit Bool :=
  ConsList.cons true (ConsList.cons true (ConsList.wrap ()))

/-- Their `toU`-images: `[()]` IS a suffix of `[(),()]`. -/
@[expose] public def shortU : ConsList Unit Unit := ConsList.cons () (ConsList.wrap ())

@[expose] public def longU : ConsList Unit Unit :=
  ConsList.cons () (ConsList.cons () (ConsList.wrap ()))

/-- A candidate decomposition: one `del`, the given first string, the second string empty. -/
@[expose] public def cand (a : Char) (xs : ConsList Unit Char) : Op Char × (dPair Char).carrier :=
  (Op.del a, (xs, ConsList.wrap ()))

/-- `V` pointwise: each string of `p` is a suffix of the corresponding string of `q`. -/
public theorem V_apply (p q : (dPair Char).carrier) :
    V Char p q ↔ suffixP p.1 q.1 ∧ suffixP p.2 q.2 := Iff.rfl

/-- `Op×([Char]×[Char])`'s action pointwise, the lane `edit-branch`'s thinning bead runs on. -/
public theorem stepF_apply {x y : RelSet.{0}} (S : x ⟶ y)
    (p : Op x.carrier × (dPair x.carrier).carrier)
    (q : Op y.carrier × (dPair y.carrier).carrier) :
    (Relator.prod opRelator (Relator.prod listRelator listRelator)).map S p q
      ↔ opP S p.1 q.1 ∧ listP S p.2.1 q.2.1 ∧ listP S p.2.2 q.2.2 := by
  simp [Relator.prod, prodMap, RelProd.pair, instHasRelProd, opRelator, listRelator,
    opRel, list, graph]

/-- `F(Op(S),S×S)`'s action on the `step` summand, the lane `edit-laws`' thinning bead runs on. -/
public theorem pairF_apply_inr {x y : RelSet.{0}} (S : x ⟶ y)
    (p : Op x.carrier × (dPair x.carrier).carrier)
    (q : Op y.carrier × (dPair y.carrier).carrier) :
    pairF.map S (Sum.inr p) (Sum.inr q)
      ↔ opP S p.1 q.1 ∧ listP S p.2.1 q.2.1 ∧ listP S p.2.2 q.2.2 := by
  rw [pairF_map]
  simp [Fbimap, rprodMap, opRel, list]

public theorem toU_short : listP toU shortB shortU := ⟨rfl, trivial⟩

public theorem toU_long : listP toU longB longU := ⟨rfl, rfl, trivial⟩

/-- `[true,true]` has no `list(toU)`-image of length one. -/
public theorem toU_long_not_short : ¬ listP toU longB shortU := fun h => h.2.elim

/-- `[false]` is no suffix of `[true,true]`: it is neither the whole list nor a suffix of `[true]`. -/
public theorem short_not_suffix_long : ¬ suffixP shortB longB := by
  simp [suffixP, shortB, longB]

/-- `[()]` IS a suffix of `[(),()]` — the thinning the alphabet map opens up. -/
public theorem shortU_suffix_longU : suffixP shortU longU := Or.inr (Or.inl rfl)

/-- **`thin(Q)` is not even lax natural**: `E(F(Op(S),S×S))thin(Q) ⊑ thin(Q)E(F(Op(S),S×S))`
    fails at `S := toU` on the set of the two `del` candidates.  Over `Bool` neither `V`-dominates
    the other, so the right side keeps both and its image has two members; over `Unit` the shorter
    dominates, so the left side reaches the one-element set. -/
public theorem thin_Q_not_lax_natural :
    ¬ LaxNatural (pairF.comp powerRelator) (pairF.comp powerRelator)
      (fun a : RelSet.{0} => thinRel (Q a.carrier)) := by
  intro hlax
  obtain ⟨W, hthin, hpow⟩ :=
    le_iff.mp (hlax toU)
      (fun z => z = Sum.inr (cand true shortB) ∨ z = Sum.inr (cand true longB))
      (fun z => z = Sum.inr (cand () shortU))
      ⟨fun z => z = Sum.inr (cand () shortU) ∨ z = Sum.inr (cand () longU),
        (powerRel_apply _ _ _).mpr
          ⟨fun p hp => by
              rcases hp with rfl | rfl
              · exact ⟨Sum.inr (cand () shortU), (pairF_apply_inr _ _ _).mpr ⟨rfl, toU_short, trivial⟩, Or.inl rfl⟩
              · exact ⟨Sum.inr (cand () longU), (pairF_apply_inr _ _ _).mpr ⟨rfl, toU_long, trivial⟩, Or.inr rfl⟩,
           fun q hq => by
              rcases hq with rfl | rfl
              · exact ⟨Sum.inr (cand true shortB), Or.inl rfl, (pairF_apply_inr _ _ _).mpr ⟨rfl, toU_short, trivial⟩⟩
              · exact ⟨Sum.inr (cand true longB), Or.inr rfl, (pairF_apply_inr _ _ _).mpr ⟨rfl, toU_long, trivial⟩⟩⟩,
        (thinRel_pt _ _ _).mpr
          ⟨fun y hy => Or.inl hy,
           fun z hz => by
             rcases hz with rfl | rfl
             · exact ⟨Sum.inr (cand () shortU), ⟨suffixP.refl _, rfl⟩, rfl⟩
             · exact ⟨Sum.inr (cand () shortU), ⟨shortU_suffix_longU, rfl⟩, rfl⟩⟩⟩
  obtain ⟨hsub, hdom⟩ := (thinRel_pt _ _ _).mp hthin
  obtain ⟨w, hwQ, hwW⟩ := hdom (Sum.inr (cand true longB)) (Or.inr rfl)
  obtain ⟨hfwd, -⟩ := (powerRel_apply _ _ _).mp hpow
  rcases hsub w hwW with rfl | rfl
  · exact short_not_suffix_long (hwQ : V Bool _ _).1
  · obtain ⟨q, hq, rfl⟩ := hfwd _ hwW
    exact toU_long_not_short ((pairF_apply_inr _ _ _).mp hq).2.1

/-- **`thin(⊤×V)` is not even lax natural** — `edit-branch`'s thinning bead, at the same witness:
    the operations are `⊤`-comparable either way, so the whole verdict rests on `V`, which is the
    one of `thin(Q)` with the sum injection dropped. -/
public theorem thin_UV_not_lax_natural :
    ¬ LaxNatural ((Relator.prod opRelator (Relator.prod listRelator listRelator)).comp powerRelator)
      ((Relator.prod opRelator (Relator.prod listRelator listRelator)).comp powerRelator)
      (fun a : RelSet.{0} =>
        thinRel (rprodMap (topMor (dE (Op a.carrier)) (dE (Op a.carrier))) (V a.carrier))) := by
  intro hlax
  obtain ⟨W, hthin, hpow⟩ :=
    le_iff.mp (hlax toU)
      (fun z => z = cand true shortB ∨ z = cand true longB)
      (fun z => z = cand () shortU)
      ⟨fun z => z = cand () shortU ∨ z = cand () longU,
        (powerRel_apply _ _ _).mpr
          ⟨fun p hp => by
              rcases hp with rfl | rfl
              · exact ⟨cand () shortU, (stepF_apply _ _ _).mpr ⟨rfl, toU_short, trivial⟩, Or.inl rfl⟩
              · exact ⟨cand () longU, (stepF_apply _ _ _).mpr ⟨rfl, toU_long, trivial⟩, Or.inr rfl⟩,
           fun q hq => by
              rcases hq with rfl | rfl
              · exact ⟨cand true shortB, Or.inl rfl, (stepF_apply _ _ _).mpr ⟨rfl, toU_short, trivial⟩⟩
              · exact ⟨cand true longB, Or.inr rfl, (stepF_apply _ _ _).mpr ⟨rfl, toU_long, trivial⟩⟩⟩,
        (thinRel_pt _ _ _).mpr
          ⟨fun y hy => Or.inl hy,
           fun z hz => by
             rcases hz with rfl | rfl
             · exact ⟨cand () shortU, ⟨topMor_apply _ _, suffixP.refl _, rfl⟩, rfl⟩
             · exact ⟨cand () shortU, ⟨topMor_apply _ _, shortU_suffix_longU, rfl⟩, rfl⟩⟩⟩
  obtain ⟨hsub, hdom⟩ := (thinRel_pt _ _ _).mp hthin
  obtain ⟨w, hwQ, hwW⟩ := hdom (cand true longB) (Or.inr rfl)
  obtain ⟨hfwd, -⟩ := (powerRel_apply _ _ _).mp hpow
  rcases hsub w hwW with rfl | rfl
  · exact short_not_suffix_long hwQ.2.1
  · obtain ⟨q, hq, rfl⟩ := hfwd _ hwW
    exact toU_long_not_short ((stepF_apply _ _ _).mp hq).2.1

/-! ## `edit-tabulation` (B&dM pp.227-229): `mle` computed column by column -/

section Tabulation

variable {A : Type}

public instance instInhabitedCL : Inhabited (ConsList Unit A) := ⟨ConsList.wrap ()⟩

/-- `head : [A] → A`; the tabulation only takes it of a non-empty column. -/
@[expose] public def head [Inhabited A] : ConsList Unit A → A
  | ConsList.wrap _ => default
  | ConsList.cons a _ => a

/-- `tail : [A] → [A]`. -/
@[expose] public def tail : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons _ x => x

/-- `init : [A] → [A]`, the list without its last element. -/
@[expose] public def init : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons _ (ConsList.wrap _) => ConsList.wrap ()
  | ConsList.cons a (ConsList.cons b x) => ConsList.cons a (init (ConsList.cons b x))

/-- `last : [A] → A`; the tabulation only takes it of a non-empty column. -/
@[expose] public def last [Inhabited A] : ConsList Unit A → A
  | ConsList.wrap _ => default
  | ConsList.cons a (ConsList.wrap _) => a
  | ConsList.cons _ (ConsList.cons b x) => last (ConsList.cons b x)

/-- `zip : [A]×[B] → [A×B]`, cut to the shorter list. -/
@[expose] public def zip {B : Type} : ConsList Unit A → ConsList Unit B → ConsList Unit (A × B)
  | ConsList.wrap _, ConsList.wrap _ => ConsList.wrap ()
  | ConsList.wrap _, ConsList.cons _ _ => ConsList.wrap ()
  | ConsList.cons _ _, ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons a x, ConsList.cons b y => ConsList.cons (a, b) (zip x y)

/-- `bmin(Q) : A×A → A`, B&dM's `bmin R = (R → outl, outr)`: the left one when it is `Q`-below the
    right one, the right one otherwise. -/
@[expose] public def bmin {X : RelSet.{0}} (Q : X ⟶ X) [∀ a b, Decidable (Q a b)]
    (p : X.carrier × X.carrier) : X.carrier :=
  if Q p.1 p.2 then p.1 else p.2

public instance instDecR (es fs : (dEdit Char).carrier) : Decidable (R Char es fs) :=
  inferInstanceAs (Decidable (clen es ≤ clen fs))

end Tabulation

variable [DecidableEq Char]

/-- **edit-tabulation**: `mle`, the recursive characterisation of the program `edit-laws` states
    (B&dM p.228): a copy where the heads agree, otherwise the `R`-better of a delete and an
    insert. -/
@[expose] public def mle : ConsList Unit Char × ConsList Unit Char → ConsList Unit (Op Char)
  | (ConsList.wrap _, ConsList.wrap _) => ConsList.wrap ()
  | (ConsList.cons a xs, ConsList.wrap _) => ConsList.cons (Op.del a) (mle (xs, ConsList.wrap ()))
  | (ConsList.wrap _, ConsList.cons b ys) => ConsList.cons (Op.ins b) (mle (ConsList.wrap (), ys))
  | (ConsList.cons a xs, ConsList.cons b ys) =>
      if a = b then ConsList.cons (Op.cpy a) (mle (xs, ys))
      else bmin (R Char) (ConsList.cons (Op.del a) (mle (xs, ConsList.cons b ys)),
                          ConsList.cons (Op.ins b) (mle (ConsList.cons a xs, ys)))
termination_by p => clen p.1 + clen p.2
decreasing_by all_goals (simp only [clen]; omega)

/-- **edit-tabulation**: `column(xs)(ys)=[mle(u,ys)∣u←tails(xs)]`. -/
@[expose] public def column (xs ys : ConsList Unit Char) : ConsList Unit (ConsList Unit (Op Char)) :=
  cmap (fun u => mle (u, ys)) (tailsFn xs)

/-- **edit-tabulation**: `fstcol=list(del) tails`, the rightmost column. -/
@[expose] public def fstcol (xs : ConsList Unit Char) : ConsList Unit (ConsList Unit (Op Char)) :=
  tailsFn (cmap Op.del xs)

namespace Tab

/-- **edit-tabulation**: `base(b,u)=[[ins(b)]⧺u]`, the bottom entry of the next column. -/
@[expose] public def base (p : Char × ConsList Unit (Op Char)) :
    ConsList Unit (ConsList Unit (Op Char)) :=
  ConsList.cons (ConsList.cons (Op.ins p.1) p.2) (ConsList.wrap ())

/-- **edit-tabulation**: `step(b)((a,(u,v)),ws)=(a=b→[[cpy(a)]⧺v]⧺ws,[bmin(R)([del(a)]⧺w,[ins(b)]⧺u)]⧺ws)`
    with `w=head(ws)`: the entry above `ws` in the next column. -/
@[expose] public def step (b : Char)
    (q : Char × (ConsList Unit (Op Char) × ConsList Unit (Op Char)))
    (ws : ConsList Unit (ConsList Unit (Op Char))) : ConsList Unit (ConsList Unit (Op Char)) :=
  if q.1 = b then ConsList.cons (ConsList.cons (Op.cpy q.1) q.2.2) ws
  else ConsList.cons (bmin (R Char) (ConsList.cons (Op.del q.1) (head ws),
                                     ConsList.cons (Op.ins b) q.2.1)) ws

end Tab

/-- **edit-tabulation**: `nextcol(xs)(b,us)=⦇[base(b,last(us)),step(b)]⦈(xus)`,
    `xus=zip(xs,zip(init(us),tail(us)))`. -/
@[expose] public def nextcol (xs : ConsList Unit Char)
    (p : Char × ConsList Unit (ConsList Unit (Op Char))) :
    ConsList Unit (ConsList Unit (Op Char)) :=
  cfold (fun _ => Tab.base (p.1, last p.2)) (Tab.step p.1) (zip xs (zip (init p.2) (tail p.2)))

theorem nextcol_cons (a b : Char) (x : ConsList Unit Char) (u v : ConsList Unit (Op Char))
    (t : ConsList Unit (ConsList Unit (Op Char))) :
    nextcol (ConsList.cons a x) (b, ConsList.cons u (ConsList.cons v t))
      = Tab.step b (a, (u, v)) (nextcol x (b, ConsList.cons v t)) := by
  cases t <;> rfl

/-- The top entry of `column(xs)(ys)` is `mle(xs,ys)`. -/
theorem column_top (xs ys : ConsList Unit Char) :
    ∃ t, column xs ys = ConsList.cons (mle (xs, ys)) t := by
  cases xs with
  | wrap u => cases u; exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- **edit-tabulation**: `mle(xs,ys)=head(column(xs,ys))`. -/
public theorem mle_head_column (xs ys : ConsList Unit Char) :
    mle (xs, ys) = head (column xs ys) := by
  obtain ⟨t, ht⟩ := column_top xs ys
  rw [ht]; rfl

theorem mle_nil_right (u : Unit) : ∀ xs : ConsList Unit Char,
    mle (xs, ConsList.wrap u) = cmap Op.del xs
  | ConsList.wrap _ => by rw [mle]; rfl
  | ConsList.cons a xs => by rw [mle, mle_nil_right () xs]; rfl

theorem tails_cmap {A B : Type} (f : A → B) : ∀ xs : ConsList Unit A,
    tailsFn (cmap f xs) = cmap (cmap f) (tailsFn xs)
  | ConsList.wrap _ => rfl
  | ConsList.cons a xs => by
      show ConsList.cons _ (tailsFn (cmap f xs)) = _
      rw [tails_cmap f xs]; rfl

/-- **edit-tabulation**: the rightmost column is `fstcol(xs)`. -/
public theorem column_nil (xs : ConsList Unit Char) (u : Unit) :
    column xs (ConsList.wrap u) = fstcol xs := by
  show cmap _ (tailsFn xs) = tailsFn (cmap Op.del xs)
  rw [tails_cmap, show (fun v => mle (v, ConsList.wrap u)) = cmap Op.del from
    funext (mle_nil_right u)]

/-- **edit-tabulation**: `column(xs)([b]⧺ys)=nextcol(xs)(b,column(xs)(ys))` — each column is
    built from the one to its right. -/
public theorem column_cons (b : Char) (ys : ConsList Unit Char) : ∀ xs : ConsList Unit Char,
    column xs (ConsList.cons b ys) = nextcol xs (b, column xs ys)
  | ConsList.wrap u => by
      cases u
      show ConsList.cons (mle (ConsList.wrap (), ConsList.cons b ys)) (ConsList.wrap ()) = _
      rw [mle]; rfl
  | ConsList.cons a x => by
      obtain ⟨t, ht⟩ := column_top x ys
      obtain ⟨t', ht'⟩ := column_top x (ConsList.cons b ys)
      have ih := column_cons b ys x
      show ConsList.cons (mle (ConsList.cons a x, ConsList.cons b ys)) (column x (ConsList.cons b ys))
        = nextcol (ConsList.cons a x) (b, ConsList.cons (mle (ConsList.cons a x, ys)) (column x ys))
      rw [ht] at ih ⊢
      rw [nextcol_cons, ← ih, ht', mle]
      by_cases h : a = b
      · subst h; simp only [Tab.step, if_true]
      · simp only [Tab.step, h, if_false]; rfl

/-- **edit-tabulation**: `column(xs)=⦇[fstcol(xs),nextcol(xs)]⦈` — the columns are built right to
    left. -/
public theorem column_cata (xs : ConsList Unit Char) :
    (graph (column xs) : dList Char ⟶ ⟨ConsList Unit (ConsList Unit (Op Char))⟩)
      = cataR (consScalarAlg (fun _ => fstcol xs) (fun b us => nextcol xs (b, us))) :=
  consFold_unique _ _ _ (column_nil xs) (fun b ys => column_cons b ys xs)

end Freyd.Alg.RelSet.Edit
