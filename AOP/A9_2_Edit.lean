/-
  Bird & de Moor, *Algebra of Programming* §9.2  The string edit problem (book pp. 224-230).

  `edit ≜ ⦇[base,step]⦈ : [Op] ⟶ [A]×[A]` reconstitutes two strings from an edit
  sequence — `cpy a` appends `a` to both, `del a` to the left only, `ins a` to the right only.
  The specification is `edit° est(R)` with `R ≜ length ≤ length°`: a SHORTEST edit sequence
  from which both strings can be reconstituted.

  What is certified here is the note's `edit-defn` and the second row of `edit-laws`, Theorem
  9.2 at `Q ≜ F(⊤,V)`, `U ≜ ⊤`, `V ≜ suffix°×suffix°`.  The two `#src` claims that carry it:

  * monotonicity `F(R)α ⊑ αR` is Proposition 9.2 (`AOP.A9_1.monotonicAlg_of_cost`) at
    `length ≜ ⦇[zero,π₂ succ]⦈` — `edit_mono`;
  * the thinning condition is Proposition 9.4 at `U ≜ ⊤` and `V ≜ suffix°×suffix°`, whose
    substance is `edit V° ⊑ R° edit` — `edit_Vrecip`, the note's two rows
    `edit (suffix×𝟙) ⊑ R° edit` and `edit (𝟙×suffix) ⊑ R° edit` composed.

  NO IN-CONTEXT TRAP HERE.  Unlike `AOP.A8_6_Tour`'s `tour-mono`, whose positive rows are
  false as printed because the book argues them only for tours of the SAME input, `V`'s two
  rows are unconditional, by the book's route on p.226: the `tail` rows `edit_tail_snd`/
  `edit_tail_fst` for EVERY edit sequence ("if `e = ins b`, remove it; if `e = cpy b`, replace it
  by `del b`" — `dropTgt`/`dropSrc`), then the `suffix` rows from them by `suffix = tail*` and
  `B A ⊑ C B ⟹ B A* ⊑ C* B`.

  Proposition 9.4 is used through its concrete instance rather than
  `AOP.A9_1.birelator_thin_condition`: the `Birelator` `G(Y,X) = L + Y×X` that instance needs
  is `rel.AutoDeriveGreedyDP.sumBirel`, which lives DOWNSTREAM of this file (it imports
  `AOP.A10_1`), and copying it here would be the duplication the abstract route exists to
  avoid.  `Q ≜ 𝟙+(⊤×V)` is written out and `edit_thin_condition` derives Theorem 9.2's `hQ`
  from `edit_V` — the same calculation, at one relator.

  `edit-laws` row 3 (the `empty→nil` split, B&dM p.227) is Proposition 9.1 in `Rel(Set)`
  (`RelSet.dp_disjoint_ranges`): `edit_body_split`, and `edit_X` its least fixed point.  The book's
  conditional `(empty→nil,…)` is stated as the union of its two guarded branches, because `cond`
  (`AOP.A5_3`) needs a Boolean allegory, which `Rel(Set)` is only classically.

  NOT DONE, and why:
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
public import AOP.A8_3
public import AOP.A7_2_RelSet
import AOP.A5_7_PowerBeads
public import AOP.A6_7
import AOP.A7_5_VanBeads
import AOP.A6_FinRel
-- `listP_clen` — `list(P)` relates lists of one length — is the whole content of `est(R)`'s
-- naturality here, and it is stated once, for the schedules.

namespace Freyd.Alg.RelSet.Edit

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-! ## `edit-defn` -/

/-- **edit-defn**: `Op::=cpy A∣del A∣ins A`. -/
public inductive Op (A : Type) where
  | cpy : A → Op A
  | del : A → Op A
  | ins : A → Op A
  deriving DecidableEq

-- The book writes the bare `del a`; the alias makes `del` resolve here before any other `del`.
export Op (cpy del ins)

/-- The object carrying edit sequences `[Op]`. -/
@[expose] public abbrev dEdit (A : Type) : RelSet.{0} := dCL Unit (Op A)

/-- The object carrying the two strings `[A]×[A]`. -/
@[expose] public abbrev dPair (A : Type) : RelSet.{0} :=
  ⟨Str A × Str A⟩

/-! ### `Op` is a relator

  `Op` is an operation on the ALPHABET, so every end of this section — `[Op]`, `F(Op,[A]×[A])`,
  `Op×([A]×[A])` — is a functor of `A` and states a naturality.  It is that functor only
  once `Op` is bundled as a lane; until then the pictures had `Op A` varying with the index and
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
@[expose] public def op : Relator RelSet.{0} RelSet.{0} where
  obj a := dE (Op a.carrier)
  map R := opRel R
  map_id _ := op_id
  map_comp R S := op_comp R S
  map_mono h := op_mono h

/-- **edit-defn**: `base` returning `([],[])`. -/
@[expose] public def baseFn (_ : Unit) : Str A × Str A :=
  (ConsList.wrap (), ConsList.wrap ())

/-- **edit-defn**: `step (cpy a,(xs,ys))=([a]⧺xs,[a]⧺ys)`, `step (del a,(xs,ys))=([a]⧺xs,ys)`,
    `step (ins a,(xs,ys))=(xs,[a]⧺ys)`. -/
@[expose] public def stepFn :
    Op A × (Str A × Str A) → Str A × Str A
  | (Op.cpy a, (xs, ys)) => (ConsList.cons a xs, ConsList.cons a ys)
  | (Op.del a, (xs, ys)) => (ConsList.cons a xs, ys)
  | (Op.ins a, (xs, ys)) => (xs, ConsList.cons a ys)

/-- **edit-defn**: the junction `[base,step]` of the two arms, B&dM's algebra of `edit`. -/
@[expose] public def baseStepFn :
    (Fobj Unit (Op A) (dPair A)).carrier → Str A × Str A
  | Sum.inl u => baseFn u
  | Sum.inr q => stepFn q

/-- **edit-defn**: the algebra `[base,step] : F(Op,[A]×[A])⟶[A]×[A]`. -/
@[expose] public def editAlg : Alg (F Unit (Op A)) (dPair A) :=
  graph baseStepFn

/-- **edit-defn**: `edit≜⦇[base,step]⦈`, read as the function it is. -/
@[expose] public def edit : ConsList Unit (Op A) → Str A × Str A
  | ConsList.wrap _ => (ConsList.wrap (), ConsList.wrap ())
  | ConsList.cons op es => stepFn (op, edit es)

@[simp] public theorem editFn_nil (u : Unit) :
    edit (ConsList.wrap u : ConsList Unit (Op A))
      = (ConsList.wrap (), ConsList.wrap ()) := rfl
@[simp] public theorem editFn_cpy (a : A) (es : ConsList Unit (Op A)) :
    edit (ConsList.cons (Op.cpy a) es)
      = (ConsList.cons a (edit es).1, ConsList.cons a (edit es).2) := rfl
@[simp] public theorem editFn_del (a : A) (es : ConsList Unit (Op A)) :
    edit (ConsList.cons (Op.del a) es)
      = (ConsList.cons a (edit es).1, (edit es).2) := rfl
@[simp] public theorem editFn_ins (a : A) (es : ConsList Unit (Op A)) :
    edit (ConsList.cons (Op.ins a) es)
      = ((edit es).1, ConsList.cons a (edit es).2) := rfl

/-- **edit-defn**: the catamorphism of `[base,step]` IS `editFn`. -/
public theorem edit_cata : graph edit = cataR (editAlg (A := A)) := by
  refine Eq.symm ?_
  apply hom_ext; intro es
  induction es with
  | wrap _ => exact fun p => Iff.rfl
  | cons op es ih =>
    intro p
    constructor
    · rintro ⟨p', hp', hstep⟩
      obtain rfl : p' = edit es := (ih p').mp hp'
      exact hstep
    · intro (h : p = baseStepFn (Sum.inr (op, edit es)))
      exact ⟨edit es, (ih _).mpr rfl, h⟩

/-- **edit-defn**: the algebra `[zero,π₂ succ]` of `length`. -/
@[expose] public def lenAlgFn : (Fobj Unit (Op A) (⟨Nat⟩ : RelSet.{0})).carrier → Nat
  | Sum.inl _ => Nat.zero
  | Sum.inr p => Nat.succ p.2

/-- **edit-defn**: `length≜⦇[zero,π₂ succ]⦈` is the list length `clen`. -/
public theorem length_cata :
    (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
      = cataR (graph (lenAlgFn (A := A))) := by
  refine Eq.symm ?_
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

/-- **edit-defn**: `α≜[nil,cons]` — the initial algebra of edit sequences: the empty sequence, or
    one operation in front of a sequence. A `def` so that §9.2's statements print `α`. -/
@[expose] public def α : Alg (F Unit (Op A)) (dEdit A) :=
  graph con

/-- **edit-defn**: `R≜length≤length°`. -/
@[expose] public def R {A : Type} : dEdit A ⟶ dEdit A := fun es fs => clen es ≤ clen fs

/-- The note writes the section's ordering `≼`, the numeric order on lengths keeping `≤`. -/
notation "≼" => R

public theorem R_eq :
    (R (A := A)) = (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0})) ≫ leRel
      ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
  apply hom_ext; intro es fs
  constructor
  · intro h; exact ⟨clen es, rfl, clen fs, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    obtain rfl : m = clen es := hm
    obtain rfl : n = clen fs := hn
    exact hmn

/-- **edit-defn**, pointwise: `es R fs` iff `es` is no longer than `fs`. -/
public theorem R_apply (es fs : ConsList Unit (Op A)) : (R (A := A)) es fs ↔ clen es ≤ clen fs :=
  Iff.rfl

public theorem R_recip_trans : (R (A := A))° ≫ (R (A := A))° ⊑ (R (A := A))° :=
  le_iff.mpr fun es gs h => by
    obtain ⟨fs, h1, h2⟩ := h
    exact Nat.le_trans (h2 : clen gs ≤ clen fs) (h1 : clen fs ≤ clen es)

/-- **edit-defn** (B&dM p.226, exercise): `α` preserves `R` whatever the two operations are —
    `[e]⧺xs` has length `1+length(xs)` for every `e`, so Proposition 9.4 may take `U≜⊤`. -/
public theorem α_pres_R :
    (FB Unit).map (relTop : dE (Op A) ⟶ dE (Op A)) (R (A := A)) ≫ α ⊑ α ≫ (R (A := A)) :=
  le_iff.mpr fun u es h => by
    obtain ⟨v, hv, hcon⟩ := h
    obtain rfl : es = con v := hcon
    refine ⟨con u, rfl, ?_⟩
    cases u with
    | inl _ => cases v with
      | inl _ => exact Nat.le_refl _
      | inr _ => exact hv.elim
    | inr p => cases v with
      | inl _ => exact hv.elim
      | inr q => exact Nat.succ_le_succ hv.2

/-- **edit-defn**: `V≜suffix°×suffix°` — `V (xs,ys) (xs',ys')` iff `xs` is a suffix of `xs'`
    and `ys` a suffix of `ys'`. -/
@[expose] public def V : dPair A ⟶ dPair A :=
  rprodMap (suffix (A := A))° (suffix (A := A))°

/-- **edit-defn** (B&dM p.226): `Q≜F(U,V)` at `U≜⊤` — any two operations, and the two remaining
    pairs of strings compared by `V`. -/
@[expose] public def Q :
    (F Unit (Op A)).obj (dPair A) ⟶ (F Unit (Op A)).obj (dPair A) :=
  Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) (V)

/-- **edit-defn**: `unstep ([a]⧺xs,[])=[(del a,(xs,[]))]`,
    `unstep ([],[b]⧺ys)=[(ins b,([],ys))]`, and
    `unstep ([a]⧺xs,[b]⧺ys)=(a=b→[(cpy a,(xs,ys))],[(del a,(xs,[b]⧺ys)),(ins b,([a]⧺xs,ys))])`
    — the thinned decompositions, a copy beating a delete and an insert where available. -/
@[expose] public def unstepFn [DecidableEq A] :
    Str A × Str A →
      ConsList Unit (Op A × (Str A × Str A))
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
-- `list((𝟙×mle)cons)` is the list relator at the same list type its `minL(R)` reads, and a
-- Lean `List` here would put a second list type on the one wire.
/-- **edit-laws**, fourth row: `unstep : [A]×[A]⟶[Op×([A]×[A])]`, the arrow the
    panel draws. -/
@[expose] public def unstep [DecidableEq A] :
    dPair A ⟶ dList (Op A × (dPair A).carrier) := graph unstepFn

/-- **edit-laws**, the sound half of `unstep` implementing `frac(step°,∋) thin(U×V)`:
    everything `unstep` returns really is a decomposition, `step (unstep p) = p`. -/
public theorem unstep_sound [DecidableEq A]
    (p : Str A × Str A)
    (q : Op A × (Str A × Str A)) (h : inlistP (unstepFn p) q) :
    stepFn q = p := by
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
public theorem unstep_complete [DecidableEq A]
    (p : Str A × Str A)
    (q : Op A × (Str A × Str A))
    (h : stepFn q = p) :
    ∃ q', inlistP (unstepFn p) q' ∧ V q'.2 q.2 := by
  obtain ⟨op, x, y⟩ := q
  cases op with
  | cpy a =>
    subst h
    refine ⟨(Op.cpy a, (x, y)), ?_, ⟨suffixP.refl x, suffixP.refl y⟩⟩
    simp [baseStepFn, stepFn, unstepFn, inlistP]
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
        simp [baseStepFn, stepFn, unstepFn, inlistP]
      · subst h
        refine ⟨(Op.del a, (x, ConsList.cons b ys)), ?_,
          ⟨suffixP.refl x, suffixP.refl (ConsList.cons b ys)⟩⟩
        simp [baseStepFn, stepFn, unstepFn, inlistP, if_neg hab]
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
        simp [baseStepFn, stepFn, unstepFn, inlistP]
      · subst h
        refine ⟨(Op.ins b, (ConsList.cons a xs, y)), ?_,
          ⟨suffixP.refl (ConsList.cons a xs), suffixP.refl y⟩⟩
        simp [baseStepFn, stepFn, unstepFn, inlistP, if_neg hab]

/-! ## `edit-laws` — monotonicity, Proposition 9.2 at `length` -/

public theorem lenAlg_comm :
    graph con ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
      = (F Unit (Op A)).map (graph clen) ≫ graph lenAlgFn := by
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
    (F Unit (Op A)).map leRel ≫ graph lenAlgFn ⊑ graph lenAlgFn ≫ leRel :=
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

/-- `F(length)` is simple: `F(length°)F(length)⊑F(𝟙)=𝟙`, `length` a map and `F` monotonic. -/
public theorem map_length_simple :
    (F Unit (Op A)).map ((graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
      ≫ (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0})) ⊑ 𝟙 _ := by
  rw [← (F Unit (Op A)).map_comp, ← (F Unit (Op A)).map_id]
  exact (F Unit (Op A)).map_mono (graph_map clen).2

/-- **edit-laws**, second row's monotonicity `F(R)α⊑αR`: Proposition 9.2 at
    `length≜⦇[zero,π₂ succ]⦈`, `succ` monotonic on `≤`, so `cons` is monotonic on `R`.  One step
    per fact: expand `R`, `length` entire, `length` a fold, `F(length)` simple, `succ` monotonic,
    the fold back, `R` back. -/
public theorem edit_mono :
    (F Unit (Op A)).map (R (A := A)) ≫ α ⊑ α ≫ R (A := A) :=
  calc (F Unit (Op A)).map (R (A := A)) ≫ α
      _ = (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ (F Unit (Op A)).map leRel
          ≫ (F Unit (Op A)).map ((graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
          ≫ α := by
        rw [R_eq, (F Unit (Op A)).map_comp, (F Unit (Op A)).map_comp, Cat.assoc, Cat.assoc]
      _ ⊑ (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ (F Unit (Op A)).map leRel
          ≫ (F Unit (Op A)).map ((graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
          ≫ α ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))° :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ (by
          have h := comp_mono_left (α)
            (map_entire_le (graph_map (A := dEdit A) (B := (⟨Nat⟩ : RelSet.{0})) clen))
          rw [Cat.comp_id] at h
          exact h)))
      _ = (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ (F Unit (Op A)).map leRel
          ≫ (F Unit (Op A)).map ((graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
          ≫ (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ graph lenAlgFn ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
        have h := congrArg (fun Z =>
          (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
            ≫ (F Unit (Op A)).map leRel
            ≫ (F Unit (Op A)).map ((graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
            ≫ Z ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°) (lenAlg_comm (A := A))
        dsimp only at h; rw [Cat.assoc, Cat.assoc] at h
        exact h
      _ ⊑ (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ (F Unit (Op A)).map leRel
          ≫ graph lenAlgFn ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
        have h := comp_mono_right (map_length_simple (A := A))
          (graph lenAlgFn ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
        rw [Cat.id_comp, Cat.assoc] at h
        exact comp_mono_left _ (comp_mono_left _ h)
      _ ⊑ (F Unit (Op A)).map (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))
          ≫ graph lenAlgFn ≫ leRel ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
        have h := comp_mono_right (lenAlg_mono (A := A))
          (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°
        rw [Cat.assoc, Cat.assoc] at h
        exact comp_mono_left _ h
      _ = α ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0})) ≫ leRel
          ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))° := by
        have h := (congrArg
          (fun Z => Z ≫ leRel ≫ (graph clen : dEdit A ⟶ (⟨Nat⟩ : RelSet.{0}))°)
          (lenAlg_comm (A := A))).symm
        rw [Cat.assoc, Cat.assoc] at h
        exact h
      _ = α ≫ R (A := A) := by rw [R_eq]

calc_steps edit_mono

/-- Theorem 9.2 asks for monotonicity at the mirrored `R°`, which `cons` also has. -/
public theorem edit_mono_recip : Freyd.Alg.Pres (F := F Unit (Op A)) (α) (R (A := A))° :=
  (Freyd.Alg.pres_recip_iff (graph_map con) (F_preservesRecip Unit (Op A))).mp edit_mono

/-! ## `edit-laws` — the `V` condition, B&dM p.226

  The book's route: the `tail` rows first, from the book's informal argument (in `es`, take the
  first operation that writes to the shortened string: an `ins` goes, a `cpy` weakens to a `del`),
  then the `suffix` rows from them by `suffix = tail*` and `B A ⊑ C B ⟹ B A* ⊑ C* B`. -/

/-- `tail : [A] → [A]`. -/
@[expose] public def tail : Str A → Str A
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons _ x => x

/-- B&dM p.226, target side: drop the first operation that writes to the target — an `ins(b)`
    goes, a `cpy(b)` becomes `del(b)`. -/
@[expose] public def drop₂ : ConsList Unit (Op A) → ConsList Unit (Op A)
  | ConsList.wrap u => ConsList.wrap u
  | ConsList.cons (Op.cpy a) es => ConsList.cons (Op.del a) es
  | ConsList.cons (Op.del a) es => ConsList.cons (Op.del a) (drop₂ es)
  | ConsList.cons (Op.ins _) es => es

/-- The source side, mirrored: a `del(a)` goes, a `cpy(a)` becomes `ins(a)`. -/
@[expose] public def drop₁ : ConsList Unit (Op A) → ConsList Unit (Op A)
  | ConsList.wrap u => ConsList.wrap u
  | ConsList.cons (Op.cpy a) es => ConsList.cons (Op.ins a) es
  | ConsList.cons (Op.del _) es => es
  | ConsList.cons (Op.ins a) es => ConsList.cons (Op.ins a) (drop₁ es)

/-- `dropTgt` leaves the source and drops the head of the target. -/
public theorem editFn_dropTgt : ∀ es : ConsList Unit (Op A),
    edit (drop₂ es) = ((edit es).1, tail (edit es).2)
  | ConsList.wrap _ => rfl
  | ConsList.cons (Op.cpy _) _ => rfl
  | ConsList.cons (Op.del _) es => by simp only [drop₂, editFn_del, editFn_dropTgt es]
  | ConsList.cons (Op.ins _) _ => rfl

/-- `editFn_dropTgt` with the pair named: `edit(es) = (x,y)` gives `edit(drop₂(es)) = (x,tail(y))`. -/
public theorem editFn_dropTgt_of_eq (es : ConsList Unit (Op A)) (x y : Str A)
    (h : edit es = (x, y)) : edit (drop₂ es) = (x, tail y) := by
  rw [editFn_dropTgt es, h]

/-- `dropSrc` drops the head of the source and leaves the target. -/
public theorem editFn_dropSrc : ∀ es : ConsList Unit (Op A),
    edit (drop₁ es) = (tail (edit es).1, (edit es).2)
  | ConsList.wrap _ => rfl
  | ConsList.cons (Op.cpy _) _ => rfl
  | ConsList.cons (Op.del _) _ => rfl
  | ConsList.cons (Op.ins _) es => by simp only [drop₁, editFn_ins, editFn_dropSrc es]

public theorem clen_dropTgt : ∀ es : ConsList Unit (Op A), clen (drop₂ es) ≤ clen es
  | ConsList.wrap _ => Nat.le_refl _
  | ConsList.cons (Op.cpy _) _ => Nat.le_refl _
  | ConsList.cons (Op.del _) es => Nat.succ_le_succ (clen_dropTgt es)
  | ConsList.cons (Op.ins _) _ => Nat.le_succ _

public theorem clen_dropSrc : ∀ es : ConsList Unit (Op A), clen (drop₁ es) ≤ clen es
  | ConsList.wrap _ => Nat.le_refl _
  | ConsList.cons (Op.cpy _) _ => Nat.le_refl _
  | ConsList.cons (Op.del _) _ => Nat.le_succ _
  | ConsList.cons (Op.ins _) es => Nat.succ_le_succ (clen_dropSrc es)

/-! ### `⟨𝟙,drop⟩` is a fold

  `dropTgt` is no fold — at `cpy(b)` it keeps the tail as it is, which the dropped tail has lost —
  but the pair `⟨𝟙,dropTgt⟩` is: each step rebuilds the sequence and drops from it.  The two leaf
  lemmas behind `edit-tail` are then calculations with fold laws: the universal property, an
  invariant of the fold (`relCata_le_of_prefixed`), and `⟨R,S⟩π₂ = S` for an entire `R`. -/

/-- `⟨R,S⟩π₂ = S` when `R` is entire: the `dom R` of `pair_outr` is then `𝟙`. -/
public theorem pair_outr_of_entire {a b c : RelSet.{0}} {P : RelProd a b} {R : c ⟶ a}
    (hR : Entire R) (S : c ⟶ b) : P.pair R S ≫ P.π₂ = S := by
  rw [RelProd.pair_outr, hR, Cat.id_comp]

/-- `𝟙` is entire. -/
public theorem entire_id {a : RelSet.{0}} : Entire (𝟙 a) := by
  rw [← graph_id]; exact graph_entire _

/-- `⟨𝟙,S⟩π₂ = S`. -/
public theorem pair_id_outr {a b : RelSet.{0}} {P : RelProd a b} (S : a ⟶ b) :
    P.pair (𝟙 a) S ≫ P.π₂ = S :=
  pair_outr_of_entire entire_id S

/-- `⟨f,S⟩π₂ = S` for a function `f`. -/
public theorem pair_graph_outr {a b c : RelSet.{0}} {P : RelProd a b} (f : c.carrier → a.carrier)
    (S : c ⟶ b) : P.pair (graph f) S ≫ P.π₂ = S :=
  pair_outr_of_entire (graph_entire f) S

/-- `(f×S)π₂ = π₂S` for a function `f`. -/
public theorem rprodMap_graph_outr {A a' B b' : RelSet.{0}} (f : A.carrier → a'.carrier) (S : B ⟶ b') :
    rprodMap (graph f) S ≫ (relProd a' b').π₂ = (relProd A B).π₂ ≫ S := by
  rw [← prodMap_eq_rprodMap]; exact prodMap_outr_eq_of_entire _ _ _ (graph_entire f)

/-- The step of `⟨𝟙,dropTgt⟩`: `cpy(b)` rebuilds and drops to `del(b)`, `ins(b)` rebuilds and
    drops itself, `del(a)` goes in front of both. -/
@[expose] public def dropTgtStep :
    Op A → ConsList Unit (Op A) × ConsList Unit (Op A) → ConsList Unit (Op A) × ConsList Unit (Op A)
  | Op.cpy b, (es, ds) => (ConsList.cons (Op.cpy b) es, ConsList.cons (Op.del b) es)
  | Op.del a, (es, ds) => (ConsList.cons (Op.del a) es, ConsList.cons (Op.del a) ds)
  | Op.ins b, (es, ds) => (ConsList.cons (Op.ins b) es, es)

/-- The step of `⟨𝟙,dropSrc⟩`, mirrored. -/
@[expose] public def dropSrcStep :
    Op A → ConsList Unit (Op A) × ConsList Unit (Op A) → ConsList Unit (Op A) × ConsList Unit (Op A)
  | Op.cpy a, (es, ds) => (ConsList.cons (Op.cpy a) es, ConsList.cons (Op.ins a) es)
  | Op.del a, (es, ds) => (ConsList.cons (Op.del a) es, es)
  | Op.ins b, (es, ds) => (ConsList.cons (Op.ins b) es, ConsList.cons (Op.ins b) ds)

/-- The algebra of `⟨𝟙,dropTgt⟩`: `nil ↦ ([],[])`, then `dropTgtStep`. -/
@[expose] public def h₂ :
    Alg (F Unit (Op A)) (⟨ConsList Unit (Op A) × ConsList Unit (Op A)⟩ : RelSet.{0}) :=
  consScalarAlg (fun _ => (ConsList.wrap (), ConsList.wrap ())) dropTgtStep

/-- The algebra of `⟨𝟙,dropSrc⟩`. -/
@[expose] public def h₁ :
    Alg (F Unit (Op A)) (⟨ConsList Unit (Op A) × ConsList Unit (Op A)⟩ : RelSet.{0}) :=
  consScalarAlg (fun _ => (ConsList.wrap (), ConsList.wrap ())) dropSrcStep

/-- The step of `⟨edit, edit(𝟙×tail)⟩`, read off `step` with the target's head dropped. -/
@[expose] public def editTgtStep :
    Op A → (Str A × Str A) × (Str A × Str A) → (Str A × Str A) × (Str A × Str A)
  | Op.cpy b, ((x, y), (x', y')) => ((ConsList.cons b x, ConsList.cons b y), (ConsList.cons b x, y))
  | Op.del a, ((x, y), (x', y')) => ((ConsList.cons a x, y), (ConsList.cons a x', y'))
  | Op.ins b, ((x, y), (x', y')) => ((x, ConsList.cons b y), (x, y))

/-- The step of `⟨edit, edit(tail×𝟙)⟩`, mirrored. -/
@[expose] public def editSrcStep :
    Op A → (Str A × Str A) × (Str A × Str A) → (Str A × Str A) × (Str A × Str A)
  | Op.cpy a, ((x, y), (x', y')) => ((ConsList.cons a x, ConsList.cons a y), (x, ConsList.cons a y))
  | Op.del a, ((x, y), (x', y')) => ((ConsList.cons a x, y), (x, y))
  | Op.ins b, ((x, y), (x', y')) => ((x, ConsList.cons b y), (x', ConsList.cons b y'))

/-- The algebra of `⟨edit, edit(𝟙×tail)⟩`. -/
@[expose] public def k₂ : Alg (F Unit (Op A)) (⟨(Str A × Str A) × (Str A × Str A)⟩ : RelSet.{0}) :=
  consScalarAlg (fun _ => ((ConsList.wrap (), ConsList.wrap ()), (ConsList.wrap (), ConsList.wrap ())))
    editTgtStep

/-- The algebra of `⟨edit, edit(tail×𝟙)⟩`. -/
@[expose] public def k₁ : Alg (F Unit (Op A)) (⟨(Str A × Str A) × (Str A × Str A)⟩ : RelSet.{0}) :=
  consScalarAlg (fun _ => ((ConsList.wrap (), ConsList.wrap ()), (ConsList.wrap (), ConsList.wrap ())))
    editSrcStep

/-- Universal property: `⟨𝟙,dropTgt⟩ = ⦇dropTgtAlg⦈`. -/
public theorem dropTgt_fold :
    (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (graph drop₂) = cataR (h₂ (A := A)) := by
  rw [pair_eq_rpair, ← graph_id, rpair_graph]
  exact consFold_unique _ _ _ (fun _ => rfl) fun o _ => by cases o <;> rfl

/-- Universal property: `⟨𝟙,dropSrc⟩ = ⦇dropSrcAlg⦈`. -/
public theorem dropSrc_fold :
    (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (graph drop₁) = cataR (h₁ (A := A)) := by
  rw [pair_eq_rpair, ← graph_id, rpair_graph]
  exact consFold_unique _ _ _ (fun _ => rfl) fun o _ => by cases o <;> rfl

/-- Universal property: `⟨edit, edit(𝟙×tail)⟩ = ⦇editTgtAlg⦈`. -/
public theorem edit_tail_snd_fold :
    (relProd (dPair A) (dPair A)).pair (graph edit)
        (graph edit ≫ rprodMap (𝟙 (dList A)) (graph tail)) = cataR (k₂ (A := A)) := by
  rw [pair_eq_rpair, ← graph_id, rprodMap_graph_eq, graph_comp, rpair_graph]
  exact consFold_unique _ _ _ (fun _ => rfl) fun o _ => by cases o <;> rfl

/-- Universal property: `⟨edit, edit(tail×𝟙)⟩ = ⦇editSrcAlg⦈`. -/
public theorem edit_tail_fst_fold :
    (relProd (dPair A) (dPair A)).pair (graph edit)
        (graph edit ≫ rprodMap (graph tail) (𝟙 (dList A))) = cataR (k₁ (A := A)) := by
  rw [pair_eq_rpair, ← graph_id, rprodMap_graph_eq, graph_comp, rpair_graph]
  exact consFold_unique _ _ _ (fun _ => rfl) fun o _ => by cases o <;> rfl

/-- Fusion: `⦇dropTgtAlg⦈ (edit×edit) = ⦇editTgtAlg⦈`. -/
public theorem dropTgt_edit_fusion :
    cataR (h₂ (A := A))
        ≫ rprodMap (graph (edit (A := A))) (graph edit)
      = cataR (k₂ (A := A)) := by
  rw [← dropTgt_fold, pair_eq_rpair, ← graph_id, rpair_graph, rprodMap_graph_eq,
    graph_comp]
  exact consFold_unique _ _ _ (fun _ => rfl) fun o _ => by cases o <;> rfl

/-- Fusion: `⦇dropSrcAlg⦈ (edit×edit) = ⦇editSrcAlg⦈`. -/
public theorem dropSrc_edit_fusion :
    cataR (h₁ (A := A))
        ≫ rprodMap (graph (edit (A := A))) (graph edit)
      = cataR (k₁ (A := A)) := by
  rw [← dropSrc_fold, pair_eq_rpair, ← graph_id, rpair_graph, rprodMap_graph_eq,
    graph_comp]
  exact consFold_unique _ _ _ (fun _ => rfl) fun o _ => by cases o <;> rfl

/-- Invariant of the fold: `⦇dropTgtAlg⦈ ⊑ ⟨𝟙,R°⟩` — the dropped sequence is never longer. -/
public theorem dropTgt_fold_le :
    cataR (h₂ (A := A)) ⊑ (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (R (A := A))° := by
  rw [cataR_eq_relCata, pair_eq_rpair]
  refine relCata_le_of_prefixed (initial Unit (Op A)) (le_iff.mpr ?_)
  rintro es q ⟨u, hu, v, hv, hq⟩
  obtain rfl : es = con u := hu
  obtain rfl : q = consScalarFn (fun _ => (ConsList.wrap (), ConsList.wrap ())) dropTgtStep v := hq
  rcases u with _ | ⟨o, es⟩ <;> rcases v with _ | ⟨o', es', ds'⟩
  · exact ⟨(id_apply _ _).mpr rfl, Nat.le_refl _⟩
  · exact hv.elim
  · exact hv.elim
  · obtain ⟨ho, hes, hds⟩ := hv
    obtain rfl : o = o' := ho
    obtain rfl : es = es' := (id_apply _ _).mp hes
    cases o
    · exact ⟨(id_apply _ _).mpr rfl, Nat.le_refl _⟩
    · exact ⟨(id_apply _ _).mpr rfl, Nat.succ_le_succ hds⟩
    · exact ⟨(id_apply _ _).mpr rfl, Nat.le_succ _⟩

/-- Invariant of the fold: `⦇dropSrcAlg⦈ ⊑ ⟨𝟙,R°⟩`. -/
public theorem dropSrc_fold_le :
    cataR (h₁ (A := A)) ⊑ (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (R (A := A))° := by
  rw [cataR_eq_relCata, pair_eq_rpair]
  refine relCata_le_of_prefixed (initial Unit (Op A)) (le_iff.mpr ?_)
  rintro es q ⟨u, hu, v, hv, hq⟩
  obtain rfl : es = con u := hu
  obtain rfl : q = consScalarFn (fun _ => (ConsList.wrap (), ConsList.wrap ())) dropSrcStep v := hq
  rcases u with _ | ⟨o, es⟩ <;> rcases v with _ | ⟨o', es', ds'⟩
  · exact ⟨(id_apply _ _).mpr rfl, Nat.le_refl _⟩
  · exact hv.elim
  · exact hv.elim
  · obtain ⟨ho, hes, hds⟩ := hv
    obtain rfl : o = o' := ho
    obtain rfl : es = es' := (id_apply _ _).mp hes
    cases o
    · exact ⟨(id_apply _ _).mpr rfl, Nat.le_refl _⟩
    · exact ⟨(id_apply _ _).mpr rfl, Nat.le_succ _⟩
    · exact ⟨(id_apply _ _).mpr rfl, Nat.succ_le_succ hds⟩

/-- `dropTgt` never lengthens: `dropTgt ⊑ R°`. -/
public theorem dropTgt_le : (graph drop₂ : dEdit A ⟶ dEdit A) ⊑ (R (A := A))° :=
  calc (graph drop₂ : dEdit A ⟶ dEdit A)
      _ = (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (graph drop₂)
            ≫ (relProd (dEdit A) (dEdit A)).π₂ := (pair_id_outr _).symm
      _ = cataR h₂ ≫ (relProd (dEdit A) (dEdit A)).π₂ := congrArg (· ≫ _) dropTgt_fold
      _ ⊑ (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (R (A := A))°
            ≫ (relProd (dEdit A) (dEdit A)).π₂ := comp_mono_right dropTgt_fold_le _
      _ = (R (A := A))° := pair_id_outr _

calc_steps dropTgt_le

/-- `dropSrc` never lengthens: `dropSrc ⊑ R°`. -/
public theorem dropSrc_le : (graph drop₁ : dEdit A ⟶ dEdit A) ⊑ (R (A := A))° :=
  calc (graph drop₁ : dEdit A ⟶ dEdit A)
      _ = (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (graph drop₁)
            ≫ (relProd (dEdit A) (dEdit A)).π₂ := (pair_id_outr _).symm
      _ = cataR h₁ ≫ (relProd (dEdit A) (dEdit A)).π₂ := congrArg (· ≫ _) dropSrc_fold
      _ ⊑ (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (R (A := A))°
            ≫ (relProd (dEdit A) (dEdit A)).π₂ := comp_mono_right dropSrc_fold_le _
      _ = (R (A := A))° := pair_id_outr _

calc_steps dropSrc_le

/-- `edit (𝟙×tail) = dropTgt edit`. -/
public theorem edit_dropTgt :
    graph (edit (A := A)) ≫ rprodMap (𝟙 (dList A)) (graph tail)
      = graph drop₂ ≫ graph edit :=
  calc graph (edit (A := A)) ≫ rprodMap (𝟙 (dList A)) (graph tail)
      _ = (relProd (dPair A) (dPair A)).pair (graph edit)
              (graph edit ≫ rprodMap (𝟙 (dList A)) (graph tail))
            ≫ (relProd (dPair A) (dPair A)).π₂ := (pair_graph_outr _ _).symm
      _ = cataR k₂ ≫ (relProd (dPair A) (dPair A)).π₂ :=
            congrArg (· ≫ _) edit_tail_snd_fold
      _ = cataR h₂
            ≫ rprodMap (graph edit) (graph edit)
            ≫ (relProd (dPair A) (dPair A)).π₂ := by rw [← Cat.assoc, dropTgt_edit_fusion]
      _ = cataR h₂ ≫ (relProd (dEdit A) (dEdit A)).π₂ ≫ graph edit :=
            congrArg (cataR h₂ ≫ ·) (rprodMap_graph_outr _ _)
      _ = (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (graph drop₂)
            ≫ (relProd (dEdit A) (dEdit A)).π₂ ≫ graph edit :=
            congrArg (· ≫ _) dropTgt_fold.symm
      _ = graph drop₂ ≫ graph edit := by rw [← Cat.assoc, pair_id_outr]

calc_steps edit_dropTgt

/-- `edit (tail×𝟙) = dropSrc edit`. -/
public theorem edit_dropSrc :
    graph (edit (A := A)) ≫ rprodMap (graph tail) (𝟙 (dList A))
      = graph drop₁ ≫ graph edit :=
  calc graph (edit (A := A)) ≫ rprodMap (graph tail) (𝟙 (dList A))
      _ = (relProd (dPair A) (dPair A)).pair (graph edit)
              (graph edit ≫ rprodMap (graph tail) (𝟙 (dList A)))
            ≫ (relProd (dPair A) (dPair A)).π₂ := (pair_graph_outr _ _).symm
      _ = cataR k₁ ≫ (relProd (dPair A) (dPair A)).π₂ :=
            congrArg (· ≫ _) edit_tail_fst_fold
      _ = cataR h₁
            ≫ rprodMap (graph edit) (graph edit)
            ≫ (relProd (dPair A) (dPair A)).π₂ := by rw [← Cat.assoc, dropSrc_edit_fusion]
      _ = cataR h₁ ≫ (relProd (dEdit A) (dEdit A)).π₂ ≫ graph edit :=
            congrArg (cataR h₁ ≫ ·) (rprodMap_graph_outr _ _)
      _ = (relProd (dEdit A) (dEdit A)).pair (𝟙 (dEdit A)) (graph drop₁)
            ≫ (relProd (dEdit A) (dEdit A)).π₂ ≫ graph edit :=
            congrArg (· ≫ _) dropSrc_fold.symm
      _ = graph drop₁ ≫ graph edit := by rw [← Cat.assoc, pair_id_outr]

calc_steps edit_dropSrc

/-- **edit-tail** (B&dM p.226): `edit (𝟙×tail)⊑R° edit` — dropping the head of the target
    string leaves a pair that an edit sequence no longer reaches. -/
public theorem edit_tail_snd :
    graph (edit (A := A)) ≫ rprodMap (𝟙 (dList A)) (graph tail)
      ⊑ (R (A := A))° ≫ graph edit :=
  calc graph (edit (A := A)) ≫ rprodMap (𝟙 (dList A)) (graph tail)
      _ = graph drop₂ ≫ graph edit := edit_dropTgt
      _ ⊑ (R (A := A))° ≫ graph edit := comp_mono_right dropTgt_le _

calc_steps edit_tail_snd

/-- **edit-tail** (B&dM p.226): `edit (tail×𝟙)⊑R° edit`, the same for the source string. -/
public theorem edit_tail_fst :
    graph (edit (A := A)) ≫ rprodMap (graph tail) (𝟙 (dList A))
      ⊑ (R (A := A))° ≫ graph edit :=
  calc graph (edit (A := A)) ≫ rprodMap (graph tail) (𝟙 (dList A))
      _ = graph drop₁ ≫ graph edit := edit_dropSrc
      _ ⊑ (R (A := A))° ≫ graph edit := comp_mono_right dropSrc_le _

calc_steps edit_tail_fst

/-- `suffix = tail*`: a suffix is what some number of `tail`s leaves. -/
public theorem suffix_eq_star_tail : (suffix : dList A ⟶ dList A) = star (graph tail) := by
  refine le_antisymm (le_iff.mpr fun x y h => ?_) ?_
  · induction x generalizing y with
    | wrap _ =>
      obtain rfl : y = ConsList.wrap () := h
      exact le_iff.mp (id_le_star _) _ _ ((id_apply _ _).mpr rfl)
    | cons a x ih =>
      rcases (h : y = ConsList.cons a x ∨ suffixP y x) with rfl | h
      · exact le_iff.mp (id_le_star _) _ _ ((id_apply _ _).mpr rfl)
      · exact le_iff.mp (comp_star_le _) _ _ ⟨x, rfl, ih y h⟩
  · show mu _ ⊑ _
    refine mu_le (le_iff.mpr fun x z h => ?_)
    unfold starBody at h; rw [union_apply, id_apply] at h
    rcases h with rfl | ⟨y, hy, hz⟩
    · exact suffixP.refl x
    · obtain rfl : y = tail x := hy
      cases x with
      | wrap _ => exact hz
      | cons _ _ => exact Or.inr hz

/-- `𝟙×T* = (𝟙×T)*`: closing the second component is closing the pair. -/
public theorem rprodMap_id_star {X Y : RelSet.{0}} (T : Y ⟶ Y) :
    rprodMap (𝟙 X) (star T) = star (rprodMap (𝟙 X) T) := by
  refine le_antisymm (le_iff.mpr fun ⟨a, b⟩ ⟨a', b'⟩ h => ?_)
    (star_le_of_preorder ?_ ?_ (rprodMap_mono (le_refl _) (le_star T)))
  · obtain ⟨hx, hy⟩ := h
    obtain rfl : a = a' := (id_apply _ _).mp hx
    have key : star T ⊑ (fun b b' => ∀ a, star (rprodMap (𝟙 X) T) (a, b) (a, b') : Y ⟶ Y) := by
      show mu _ ⊑ _
      refine mu_le (le_iff.mpr fun b b' h => ?_)
      unfold starBody at h; rw [union_apply, id_apply] at h
      rcases h with rfl | ⟨c, hT, hY⟩
      · exact fun a => le_iff.mp (id_le_star _) _ _ ((id_apply _ _).mpr rfl)
      · exact fun a => le_iff.mp (comp_star_le _) _ _
          ⟨(a, c), ⟨(id_apply _ _).mpr rfl, hT⟩, hY a⟩
    exact le_iff.mp key b b' hy a
  · rw [← rprodMap_id]; exact rprodMap_mono (le_refl _) (id_le_star T)
  · rw [rprodMap_comp, Cat.id_comp]; exact rprodMap_mono (le_refl _) (star_trans T)

/-- `T*×𝟙 = (T×𝟙)*`: closing the first component is closing the pair. -/
public theorem rprodMap_star_id {X Y : RelSet.{0}} (T : Y ⟶ Y) :
    rprodMap (star T) (𝟙 X) = star (rprodMap T (𝟙 X)) := by
  refine le_antisymm (le_iff.mpr fun ⟨b, a⟩ ⟨b', a'⟩ h => ?_)
    (star_le_of_preorder ?_ ?_ (rprodMap_mono (le_star T) (le_refl _)))
  · obtain ⟨hy, hx⟩ := h
    obtain rfl : a = a' := (id_apply _ _).mp hx
    have key : star T ⊑ (fun b b' => ∀ a, star (rprodMap T (𝟙 X)) (b, a) (b', a) : Y ⟶ Y) := by
      show mu _ ⊑ _
      refine mu_le (le_iff.mpr fun b b' h => ?_)
      unfold starBody at h; rw [union_apply, id_apply] at h
      rcases h with rfl | ⟨c, hT, hY⟩
      · exact fun a => le_iff.mp (id_le_star _) _ _ ((id_apply _ _).mpr rfl)
      · exact fun a => le_iff.mp (comp_star_le _) _ _
          ⟨(c, a), ⟨hT, (id_apply _ _).mpr rfl⟩, hY a⟩
    exact le_iff.mp key b b' hy a
  · rw [← rprodMap_id]; exact rprodMap_mono (id_le_star T) (le_refl _)
  · rw [rprodMap_comp, Cat.id_comp]; exact rprodMap_mono (star_trans T) (le_refl _)

/-- `R°` is a preorder, hence its own closure: `(R°)* = R°`. -/
public theorem R_recip_star : star (R (A := A))° = (R (A := A))° :=
  le_antisymm
    (star_le_of_preorder (le_iff.mpr fun x y h => by
        obtain rfl : x = y := (id_apply _ _).mp h
        exact Nat.le_refl _) R_recip_trans (le_refl _))
    (le_star _)

/-- **edit-laws**, second row: `edit (𝟙×suffix)⊑R° edit`, from the `tail` row by `suffix = tail*`. -/
public theorem edit_suffix_right :
    graph (edit (A := A)) ≫ rprodMap (𝟙 (dList A)) suffix
      ⊑ (R (A := A))° ≫ graph edit :=
  calc graph (edit (A := A)) ≫ rprodMap (𝟙 (dList A)) suffix
      _ = graph edit ≫ rprodMap (𝟙 (dList A)) (star (graph tail)) := by rw [suffix_eq_star_tail]
      _ = graph edit ≫ star (rprodMap (𝟙 (dList A)) (graph tail)) := by rw [rprodMap_id_star]
      _ ⊑ star (R (A := A))° ≫ graph edit := star_simulation edit_tail_snd
      _ = (R (A := A))° ≫ graph edit := by rw [R_recip_star]

calc_steps edit_suffix_right

/-- **edit-laws**, second row: `edit (suffix×𝟙)⊑R° edit`, the same for the source string. -/
public theorem edit_suffix_left :
    graph (edit (A := A)) ≫ rprodMap suffix (𝟙 (dList A))
      ⊑ (R (A := A))° ≫ graph edit :=
  calc graph (edit (A := A)) ≫ rprodMap suffix (𝟙 (dList A))
      _ = graph edit ≫ rprodMap (star (graph tail)) (𝟙 (dList A)) := by rw [suffix_eq_star_tail]
      _ = graph edit ≫ star (rprodMap (graph tail) (𝟙 (dList A))) := by rw [rprodMap_star_id]
      _ ⊑ star (R (A := A))° ≫ graph edit := star_simulation edit_tail_fst
      _ = (R (A := A))° ≫ graph edit := by rw [R_recip_star]

calc_steps edit_suffix_left

/-- `edit-V`, first step: `V°=suffix×suffix` splits into `(suffix×𝟙)(𝟙×suffix)`. -/
public theorem edit_Vrecip_step1 :
    graph (edit (A := A)) ≫ (V)°
      = graph edit ≫ rprodMap (suffix (A := A)) (𝟙 (dList A))
          ≫ rprodMap (𝟙 (dList A)) (suffix (A := A)) := by
  rw [rprodMap_comp, Cat.comp_id, Cat.id_comp, V, rprodMap_recip]
  simp only [Allegory.recip_recip]

/-- `edit-V`, second step: `edit (suffix×𝟙)⊑R° edit` (`edit_suffix_left`). -/
public theorem edit_Vrecip_step2 :
    graph (edit (A := A)) ≫ rprodMap (suffix (A := A)) (𝟙 (dList A))
        ≫ rprodMap (𝟙 (dList A)) (suffix (A := A))
      ⊑ (R (A := A))° ≫ graph edit ≫ rprodMap (𝟙 (dList A)) (suffix (A := A)) := by
  have h := comp_mono_right (edit_suffix_left (A := A))
    (rprodMap (𝟙 (dList A)) (suffix (A := A)))
  simpa only [Cat.assoc] using h

/-- `edit-V`, third step: `edit (𝟙×suffix)⊑R° edit` (`edit_suffix_right`). -/
public theorem edit_Vrecip_step3 :
    (R (A := A))° ≫ graph edit ≫ rprodMap (𝟙 (dList A)) (suffix (A := A))
      ⊑ (R (A := A))° ≫ (R (A := A))° ≫ graph edit :=
  comp_mono_left _ edit_suffix_right

/-- `edit-V`, fourth step: `R°` is transitive (`R_recip_trans`). -/
public theorem edit_Vrecip_step4 :
    (R (A := A))° ≫ (R (A := A))° ≫ graph (edit (A := A)) ⊑ (R (A := A))° ≫ graph edit := by
  have h := comp_mono_right (R_recip_trans (A := A)) (graph (edit (A := A)))
  simpa only [Cat.assoc] using h

/-- **edit-V**: `edit V°⊑R° edit` at `V≜suffix°×suffix°` — shorten one output, then the other,
    never lengthening. -/
public theorem edit_Vrecip :
    graph (edit (A := A)) ≫ (V)° ⊑ (R (A := A))° ≫ graph edit :=
  calc graph (edit (A := A)) ≫ (V)°
      _ = _ := edit_Vrecip_step1
      _ ⊑ _ := edit_Vrecip_step2
      _ ⊑ _ := edit_Vrecip_step3
      _ ⊑ _ := edit_Vrecip_step4

/-- **edit-laws**, second row: Proposition 9.4's `hV`, `V edit°⊑edit° R`. -/
public theorem edit_V :
    V ≫ (graph (edit (A := A)))° ⊑ (graph edit)° ≫ (R (A := A)) := by
  have h := recip_mono (edit_Vrecip (A := A))
  rw [Allegory.recip_comp, Allegory.recip_comp] at h
  exact h

/-! ### `edit-thin` — Proposition 9.4 at `Q≜F(⊤,V)`, one step per fact (B&dM p.226) -/

/-- The bifunctor `F(A,B)=1+(A×B)` preserves composition in both arguments at once. -/
public theorem Fbimap_comp {L E E' E'' : Type} {C C' C'' : RelSet.{0}} (U : dE E ⟶ dE E')
    (V : C ⟶ C') (U' : dE E' ⟶ dE E'') (V' : C' ⟶ C'') :
    Fbimap L U V ≫ Fbimap L U' V' = Fbimap L (U ≫ U') (V ≫ V') :=
  Poly.bimapR_functor (clF L) U U' V V'

/-- `edit-thin`, first step: `Q≜F(⊤,V)`, and `F(⊤,V)F(𝟙,edit°)=F(⊤,V edit°)`.
    One step and not two: the exporter cannot cut `F(⊤,V)F(𝟙,edit°)` between its two beads. -/
public theorem edit_thin_step1 :
    Q ≫ (F Unit (Op A)).map ((graph (edit (A := A)))°) ≫ α
      = Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) (V ≫ (graph edit)°)
          ≫ α := by
  rw [Q, ← Cat.assoc]
  congr 1
  exact (Fbimap_comp _ _ _ _).trans (by rw [Cat.comp_id])

/-- `edit-thin`, second step: Proposition 9.4's `V edit°⊑edit° R` (`edit_V`) under `F(U,−)`. -/
public theorem edit_thin_step2 :
    Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) (V ≫ (graph (edit (A := A)))°)
        ≫ α
      ⊑ Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) ((graph edit)° ≫ (R (A := A)))
          ≫ α :=
  comp_mono_right (le_iff.mpr fun u w h => by
    cases u with
    | inl _ => cases w with
      | inl _ => exact h
      | inr _ => exact h.elim
    | inr p => cases w with
      | inl _ => exact h.elim
      | inr q => exact ⟨h.1, le_iff.mp edit_V _ _ h.2⟩) _

/-- `edit-thin`, third step: `F(U,edit° R)=F(𝟙,edit°)F(U,R)`. -/
public theorem edit_thin_step3 :
    Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) ((graph (edit (A := A)))° ≫ (R (A := A)))
        ≫ α
      = (F Unit (Op A)).map ((graph (edit (A := A)))°)
          ≫ Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) (R (A := A)) ≫ α := by
  rw [← Cat.assoc]
  congr 1
  exact ((Fbimap_comp _ _ _ _).trans (by rw [Cat.id_comp])).symm

/-- `edit-thin`, fourth step: Proposition 9.4's `F(U,R)α⊑αR` at `U≜⊤` — `cons` adds one to both
    lengths whatever the two operations are. -/
public theorem edit_thin_step4 :
    (F Unit (Op A)).map ((graph (edit (A := A)))°)
        ≫ Fbimap Unit (topMor (dE (Op A)) (dE (Op A))) (R (A := A)) ≫ α
      ⊑ (F Unit (Op A)).map ((graph edit)°) ≫ α ≫ (R (A := A)) :=
  comp_mono_left _ (le_trans
    (comp_mono_right ((FB Unit).map_mono (le_relTop _) (le_refl (R (A := A)))) _) α_pres_R)

/-- **edit-laws**, second row: Theorem 9.2's thinning condition, Proposition 9.4 at `U≜⊤` and
    `V≜suffix°×suffix°`.  The `base` summand needs only reflexivity of `R`; on the `step`
    summand `U≜⊤` leaves the operation free and `edit_V` supplies the shorter sequence for the
    `V`-smaller pair of strings, which `cons` then lengthens by one on both sides. -/
public theorem edit_thin_condition :
    Q ≫ (F Unit (Op A)).map ((graph (edit (A := A)))°) ≫ α
      ⊑ (F Unit (Op A)).map ((graph edit)°) ≫ α ≫ (R (A := A)) :=
  calc Q ≫ (F Unit (Op A)).map ((graph (edit (A := A)))°) ≫ α
      _ = _ := edit_thin_step1
      _ ⊑ _ := edit_thin_step2
      _ = _ := edit_thin_step3
      _ ⊑ _ := edit_thin_step4

/-- **edit-laws**, second row (B&dM p.226): a shortest edit sequence is the least fixed point
    of `(μX : [base,step]° thin Q P([nil,(𝟙×X)cons]) est(R))` — Theorem 9.2 at `Q≜F(⊤,V)`,
    `U≜⊤`, `V≜suffix°×suffix°`.  `H = ⦇α⦈·⦇[base,step]⦈°` collapses to `edit°` by reflection
    (`AOP.A6_ConsList.cataR_con`). -/
public theorem edit_laws :
    mu (fun X : dPair A ⟶ dEdit A =>
        Λ ((editAlg (A := A))°) ≫ thinRel (Q)
          ≫ powerRel ((F Unit (Op A)).map X ≫ α) ≫ est (R (A := A)))
      ⊑ Λ ((graph (edit (A := A)))°) ≫ est (R (A := A)) := by
  have hH : (relCata (editAlg (A := A)))° ≫ relCata (α)
      = (graph (edit (A := A)))° := by
    unfold α; rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, ← edit_cata]
    exact Cat.comp_id _
  have key := dynamic_programming_thin (F := F Unit (Op A))
    (initial Unit (Op A)) (h := α) (T := editAlg (A := A)) («≤» := (R (A := A)))
    (Q := Q) (graph_map con) edit_mono_recip R_recip_trans
    (by simp only [ThinCondition, H]; rw [hH]; exact edit_thin_condition)
  simp only [H, M] at key; rwa [hH] at key


/-! ## `edit-laws`, third row: Proposition 9.1 at the `step` summand

  `base` returns `([],[])` and no `step` returns it, so the body's thinning splits and the third
  row is the `step` arm alone.  That is `AOP.A9_1`'s `thin_summand_le` at `ι ≜ Sum.inr`, the one
  summand lemma the snoc-direction rows also use: its arm relator `Fᵢ` is whichever side of the
  product the recursion sits on — `−×E` there, the element-first `E×−` here. -/

/-- **edit-defn**: `step`, the second arm of `[base,step]`.  The note writes the third row at
    this arm alone, so the arm has the name the note gives it. -/
@[expose] public def step : (⟨Op A × (dPair A).carrier⟩ : RelSet.{0}) ⟶ dPair A :=
  graph stepFn

/-- `step` never returns the empty pair — `cpy` and `del` put a character on the left string,
    `ins` one on the right — and `base` returns nothing else.  This is Proposition 9.1's
    disjointness hypothesis at `[base,step]`. -/
public theorem step_ne_base (q : Op A × (dPair A).carrier) :
    stepFn q ≠ ((ConsList.wrap () : Str A), ConsList.wrap ()) := by
  obtain ⟨op, p⟩ := q
  cases op with
  | cpy a => intro h; injection h with h1 _; cases h1
  | del a => intro h; injection h with h1 _; cases h1
  | ins a => intro h; injection h with _ h2; cases h2

/-- **edit-defn**: `base`, the first arm of `[base,step]`, returning `([],[])`. -/
@[expose] public def base : dL Unit ⟶ dPair A := graph baseFn

/-- **edit-defn**: the algebra IS the junction `[base,step]` of its two arms, as B&dM write it. -/
public theorem editAlg_junc :
    editAlg (A := A)
      = junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) base step :=
  hom_ext fun u v => by
    cases u with
    | inl d =>
      cases d; simp [editAlg, base, junc, graph, sumCop]
      exact ⟨fun h => ⟨(), h⟩, fun ⟨(), h⟩ => h⟩
    | inr q => simp [editAlg, step, junc, graph, sumCop]; exact Iff.rfl

/-- **edit-defn**: `empty`, the predicate on `(xs,ys)` with both lists empty. -/
@[expose] public def emptyP (p : Str A × Str A) : Prop :=
  p = ((ConsList.wrap () : Str A), ConsList.wrap ())

/-- `empty` as an arrow: the coreflexive of `emptyP`. -/
@[expose] public def empty : dPair A ⟶ dPair A := corefl emptyP

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.emptyP] public meta def unexpandEmptyP : Unexpander
  | `($_ $p) => `($(mkIdent `empty) $p)
  | _ => `($(mkIdent `empty))

/-! ### `edit-defn`, one declaration per line of the note's display -/

/-- **edit-defn**: every `Op` is a `cpy`, a `del` or an `ins`. -/
public theorem op_cases (o : Op A) :
    (∃ a, o = Op.cpy a) ∨ (∃ a, o = Op.del a) ∨ ∃ a, o = Op.ins a := by
  cases o with
  | cpy a => exact Or.inl ⟨a, rfl⟩
  | del a => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | ins a => exact Or.inr (Or.inr ⟨a, rfl⟩)

/-- **edit-defn**: the base bifunctor `F(A,B)=𝟏+(A×B)`. -/
public theorem F_obj (A B : RelSet.{0}) :
    (FB Unit).obj A B = ⟨Unit ⊕ (A.carrier × B.carrier)⟩ := rfl

/-- **edit-defn**: `F(𝟙,edit°)`, the base bifunctor at the identity on `Op` and the converse of
    `edit`: an operation kept, a pair of strings taken back to an edit sequence that edits to it. -/
@[expose] public def FeditR := (FB Unit).map (𝟙 (dE (Op A))) (graph (edit (A := A)))°

/-- **edit-defn**: the edit sequences' initial algebra IS the junction `α=[nil,cons]` of its two
    constructors, at the empty leaf. -/
public theorem con_eq_junc :
    graph (con (L := Unit) (E := Op A))
      = junc (sumCop (dL Unit) ⟨Op A × ConsList Unit (Op A)⟩) τ consR :=
  hom_ext fun u es => by
    cases u with
    | inl d =>
      cases d; simp [junc, graph, sumCop, τ, con]
      exact ⟨fun h => ⟨(), h⟩, fun ⟨(), h⟩ => h⟩
    | inr p => simp [junc, graph, sumCop, consR, con]


/-- **edit-defn**: `V≜suffix°×suffix°`. -/
public theorem V_eq : V = rprodMap (suffix (A := A))° (suffix (A := A))° := rfl

/-- **edit-defn**: `empty` holds exactly at `(([],[]),([],[]))`. -/
public theorem empty_iff (p q : Str A × Str A) :
    empty p q ↔ p = q ∧ p = (ConsList.wrap (), ConsList.wrap ()) := Iff.rfl

/-- **edit-defn**: `unstep ([],[])=[]`. -/
public theorem unstep_nil [DecidableEq A] :
    unstepFn ((ConsList.wrap (), ConsList.wrap ()) : Str A × Str A)
      = ConsList.wrap () := rfl
/-- **edit-defn**: `unstep ([a]⧺xs,[])=[(del a,(xs,[]))]`. -/
public theorem unstep_del [DecidableEq A] (a : A) (xs : Str A) :
    unstepFn (ConsList.cons a xs, ConsList.wrap ())
      = ConsList.cons (Op.del a, (xs, ConsList.wrap ())) (ConsList.wrap ()) := rfl
/-- **edit-defn**: `unstep ([],[b]⧺ys)=[(ins b,([],ys))]`. -/
public theorem unstep_ins [DecidableEq A] (b : A) (ys : Str A) :
    unstepFn (ConsList.wrap (), ConsList.cons b ys)
      = ConsList.cons (Op.ins b, (ConsList.wrap (), ys)) (ConsList.wrap ()) := rfl
/-- **edit-defn**: `unstep ([a]⧺xs,[b]⧺ys)`, a copy where the heads agree, else a delete and an
    insert. -/
public theorem unstep_cons [DecidableEq A] (a b : A) (xs ys : Str A) :
    unstepFn (ConsList.cons a xs, ConsList.cons b ys)
      = if a = b then ConsList.cons (Op.cpy a, (xs, ys)) (ConsList.wrap ())
        else ConsList.cons (Op.del a, (xs, ConsList.cons b ys))
          (ConsList.cons (Op.ins b, (ConsList.cons a xs, ys)) (ConsList.wrap ())) := rfl

/-- `edit-disj`, first step: `base` returns only `([],[])`, so `base°=empty base°`. -/
public theorem edit_disj_step1 :
    step (A := A) ≫ (base (A := A))° = step ≫ empty ≫ (base (A := A))° := by
  congr 1
  exact hom_ext fun p d => ⟨fun h => ⟨p, ⟨rfl, h⟩, h⟩, fun ⟨_, ⟨h1, _⟩, h2⟩ => h1 ▸ h2⟩

/-- `edit-disj`, second step: `step empty=𝟘`, no `step` returns `([],[])` (`step_ne_base`). -/
public theorem edit_disj_step2 :
    step (A := A) ≫ empty ≫ (base (A := A))° = 𝟘 ≫ (base (A := A))° := by
  rw [← Cat.assoc]
  congr 1
  exact hom_ext fun q p => ⟨fun ⟨_, h1, _, h2⟩ => absurd (h1.symm.trans h2) (step_ne_base q),
    fun h => h.elim⟩

/-- **edit-disj** (B&dM p.227): `base` and `step` have disjoint ranges, `step base°=𝟘` —
    Proposition 9.1's hypothesis. -/
public theorem edit_disj : step (A := A) ≫ (base (A := A))° = 𝟘 :=
  calc step (A := A) ≫ (base (A := A))°
      _ = _ := edit_disj_step1
      _ = _ := edit_disj_step2
      _ = 𝟘 := hom_ext fun _ _ => ⟨fun ⟨_, h, _⟩ => h.elim, fun h => h.elim⟩

/-- The `step` arm of `F(X)[nil,cons]` is the note's `(𝟙×X)cons`: `F(X)` keeps the operation and
    recurses in the second component. -/
public theorem arm_Fmap_con (X : dPair A ⟶ dEdit A)
    (p : Op A × (dPair A).carrier) (z : (dEdit A).carrier) :
    (rprodMap (𝟙 (dE (Op A))) X ≫ consR) p z
      ↔ ((F Unit (Op A)).map X ≫ α) (Sum.inr p) z := by
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
    `ι ≜ Sum.inr`, whose `Qᵢ` at `Q ≜ F(⊤,V)` is `U×V` with `U ≜ ⊤`. -/
public theorem edit_branch (X : dPair A ⟶ dEdit A) :
    Λ ((step (A := A))°)
        ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
        ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))
      ⊑ Λ ((editAlg (A := A))°) ≫ thinRel (Q)
          ≫ powerRel ((F Unit (Op A)).map X ≫ α) ≫ est (R (A := A)) := by
  have hmap : (Relator.prod (Relator.const (dE (Op A)))
      (Relator.idRelator RelSet.{0})).map X = rprodMap (𝟙 (dE (Op A))) X :=
    prodMap_eq_rprodMap _ _
  have key := RelSet.thin_summand_le
    (Fᵢ := Relator.prod (Relator.const (dE (Op A))) (Relator.idRelator RelSet.{0}))
    (F := F Unit (Op A)) (T := editAlg (A := A)) (Q := Q) (X := X)
    (h := α) (R := (R (A := A))) (Vᵢ := step) (Uᵢ := consR)
    (Qᵢ := rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
    Sum.inr (graph_map _) (fun _ _ => Iff.rfl) (fun _ _ h => h)
    (fun p z => by rw [hmap]; exact arm_Fmap_con X p z)
    (fun w p y hstep hT => by
      cases w with
      | inl d =>
        have hy : baseStepFn (Sum.inr p)
            = ((ConsList.wrap () : Str A), ConsList.wrap ()) :=
          Eq.trans (Eq.symm hstep) hT
        exact absurd hy (step_ne_base p)
      | inr q => exact ⟨q, rfl⟩)
  rwa [hmap] at key

/-! ## edit-laws, third row: Proposition 9.1 splits the body into the book's `X` (p.227) -/

/-- `base` and `step` have disjoint ranges, seen from `base`'s end: `base step°=𝟘`. -/
public theorem edit_disj' : base (A := A) ≫ (step (A := A))° = 𝟘 :=
  hom_ext fun _ q => ⟨fun ⟨_, h1, h2⟩ => step_ne_base q (h2.symm.trans h1), fun h => h.elim⟩

/-- `Q≜F(⊤,V)` is the sum `𝟙+(⊤×V)` of its two summands. -/
public theorem Q_eq_sumMap :
    Q = sumMap (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩)
      (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) (𝟙 (dL Unit))
      (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V)) :=
  hom_ext fun u w => by
    cases u <;> cases w <;>
      simp [Q, Fbimap, Poly.bimapR, clF, sumMap, junc, sumCop, rprodMap, graph, instHasRelProd]

/-- `F(X)[nil,cons]=[nil,(𝟙×X)cons]`: `F(X)` leaves the leaf alone and recurses in the pair. -/
public theorem Fα_junc (X : dPair A ⟶ dEdit A) :
    (F Unit (Op A)).map X ≫ α
      = junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) τ
          (rprodMap (𝟙 (dE (Op A))) X ≫ consR) :=
  hom_ext fun u z => by
    cases u with
    | inl d =>
      cases d
      simp [Fbimap, Poly.bimapR, clF, junc, sumCop, τ, α, graph, con, F, Fmap]
      constructor
      · rintro ⟨y | y, hy, hz⟩
        · exact ⟨_, hz⟩
        · exact hy.elim
      · rintro ⟨y, hz⟩
        exact ⟨Sum.inl y, trivial, hz⟩
    | inr p =>
      refine (arm_Fmap_con X p z).symm.trans ⟨fun h => Or.inr ⟨p, by simp [sumCop, graph], h⟩, ?_⟩
      rintro (⟨y, hy, _⟩ | ⟨q, hq, h⟩)
      · simp [sumCop, graph] at hy
      · obtain rfl : q = p := by
          simp [sumCop, graph] at hq
          first | exact hq | exact hq.symm
        exact h

/-- The body of `edit_laws` read at the junction `[base,step]`: the algebra, `Q` and `F(X)α` each
    written as the two arms Proposition 9.1 takes.  One law: a term mixing `F`'s object with the
    raw sum would not be one picture. -/
public theorem edit_body_junc (X : dPair A ⟶ dEdit A) :
    Λ ((editAlg (A := A))°) ≫ thinRel (Q) ≫ powerRel ((F Unit (Op A)).map X ≫ α)
        ≫ est (R (A := A))
      = Λ ((junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) base step)°)
          ≫ thinRel (sumMap (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩)
              (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) (𝟙 (dL Unit))
              (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V)))
          ≫ powerRel (junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) τ
              (rprodMap (𝟙 (dE (Op A))) X ≫ consR)) ≫ est (R (A := A)) := by
  rw [editAlg_junc, Q_eq_sumMap, Fα_junc]

/-- **Proposition 9.1** at `[base,step]`: their ranges are disjoint (`edit_disj`), so the body
    runs the `base` problem on `ran(base)` and the `step` problem on `ran(step)`.  A law of its own
    because a `calc` step applies one law, and the disjointness proofs would be two more. -/
public theorem edit_disjoint_ranges (X : dPair A ⟶ dEdit A) :
    Λ ((junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) base step)°)
        ≫ thinRel (sumMap (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩)
            (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) (𝟙 (dL Unit))
            (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V)))
        ≫ powerRel (junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) τ
            (rprodMap (𝟙 (dE (Op A))) X ≫ consR)) ≫ est (R (A := A))
      = (Freyd.Alg.ran (base (A := A)) ≫ Λ ((base (A := A))°) ≫ thinRel (𝟙 (dL Unit))
            ≫ powerRel τ ≫ est (R (A := A)))
        ∪ (Freyd.Alg.ran (step (A := A)) ≫ Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
            ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))) :=
  RelSet.dp_disjoint_ranges edit_disj edit_disj'

/-- The `base` branch of Proposition 9.1 is `nil` on the empty pair: `base°` decomposes `([],[])`
    one way, so the set is a singleton and `est(R)` returns its one member. -/
public theorem edit_base_branch :
    Freyd.Alg.ran (base (A := A)) ≫ Λ ((base (A := A))°) ≫ powerRel τ ≫ est (R (A := A))
      = empty ≫ (base (A := A))° ≫ τ := by
  apply hom_ext; intro p e
  rw [Λ_eq_classifier]
  constructor
  · rintro ⟨p₁, ⟨hid, u, hu1, hu2⟩, S, hS, T, hT, hest⟩
    obtain ⟨hTe, _⟩ := (est_apply _ _ _).mp hest
    obtain ⟨x, hx, hxe⟩ := ((powerRel_apply _ _ _).mp hT).2 e hTe
    obtain rfl : S = _ := hS
    exact ⟨p, ⟨rfl, hu1⟩, x, hu1, hxe⟩
  · rintro ⟨p₂, ⟨rfl, hp⟩, u, hu, he⟩
    refine ⟨p, ⟨rfl, u, hu, hu⟩, fun x => base x p, rfl, fun y => y = e, ?_, ?_⟩
    · refine (powerRel_apply _ _ _).mpr ⟨fun x hx => ⟨e, ?_, rfl⟩, fun y hy => ⟨u, hu, hy ▸ he⟩⟩
      cases x; cases u; exact he
    · exact (est_apply _ _ _).mpr ⟨rfl, fun z hz => hz ▸ Nat.le_refl _⟩

/-- `ran(step)` holds exactly off the empty pair: any other pair is `step` of a `del` or an `ins`. -/
public theorem ran_step_iff (p q : Str A × Str A) :
    Freyd.Alg.ran (step (A := A)) p q ↔ p = q ∧ ¬ emptyP p := by
  constructor
  · rintro ⟨hpq, s, hs, _⟩
    exact ⟨hpq, fun he => step_ne_base s (hs.symm.trans he)⟩
  · rintro ⟨rfl, hne⟩
    refine ⟨rfl, ?_⟩
    obtain ⟨xs, ys⟩ := p
    cases xs with
    | wrap u =>
      cases u
      cases ys with
      | wrap v => cases v; exact absurd rfl hne
      | cons b ys => exact ⟨(Op.ins b, (ConsList.wrap (), ys)), rfl, rfl⟩
    | cons a xs => exact ⟨(Op.del a, (xs, ys)), rfl, rfl⟩

/-- `list(S)×list(S)` relates pairs of the same lengths, so it keeps `empty` both ways. -/
public theorem emptyP_listP {x y : RelSet.{0}} (S : x ⟶ y) (p : Str x.carrier × Str x.carrier)
    (m : Str y.carrier × Str y.carrier) (h1 : listP S p.1 m.1) (h2 : listP S p.2 m.2) :
    emptyP p ↔ emptyP m := by
  obtain ⟨xs, ys⟩ := p
  obtain ⟨xs', ys'⟩ := m
  cases xs <;> cases xs' <;> cases ys <;> cases ys' <;> simp_all [emptyP, listP, clP]

/-- **`ran(step)` is STRICTLY natural** in the alphabet: `list(S)×list(S)` relates an empty pair
    only to an empty pair, so it commutes with the coreflexive on the non-empty ones. -/
public theorem ran_step_strictNatural :
    StrictNatural (Relator.prod listRelator listRelator) (Relator.prod listRelator listRelator)
      (fun a => Freyd.Alg.ran (step (A := a.carrier))) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _]
  apply hom_ext; intro p q
  constructor
  · rintro ⟨m, hm, hr⟩
    obtain ⟨rfl, hne⟩ := (ran_step_iff _ _).mp hr
    exact ⟨p, (ran_step_iff _ _).mpr
      ⟨rfl, fun he => hne ((emptyP_listP S p m hm.1 hm.2).mp he)⟩, hm⟩
  · rintro ⟨m, hr, hm⟩
    obtain ⟨rfl, hne⟩ := (ran_step_iff _ _).mp hr
    exact ⟨q, hm, (ran_step_iff _ _).mpr
      ⟨rfl, fun he => hne ((emptyP_listP S p q hm.1 hm.2).mpr he)⟩⟩

/-- **edit-laws**, third row (B&dM p.227): Proposition 9.1 at `[base,step]` turns the body of
    `edit_laws` into the book's `X=(empty→nil,(step°)%∋ thin(U×V)P((𝟙×X)cons)est(R))`.  The
    conditional is the union of its two guarded arms: `cond` needs a Boolean allegory, which
    `Rel(Set)` is only classically. -/
public theorem edit_body_split (X : dPair A ⟶ dEdit A) :
    Λ ((editAlg (A := A))°) ≫ thinRel (Q) ≫ powerRel ((F Unit (Op A)).map X ≫ α)
        ≫ est (R (A := A))
      = (empty ≫ (base (A := A))° ≫ τ)
        ∪ (Freyd.Alg.ran (step (A := A)) ≫ Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
            ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))) :=
  calc Λ ((editAlg (A := A))°) ≫ thinRel (Q) ≫ powerRel ((F Unit (Op A)).map X ≫ α)
        ≫ est (R (A := A))
      = Λ ((junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) base step)°)
          ≫ thinRel (sumMap (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩)
              (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) (𝟙 (dL Unit))
              (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V)))
          ≫ powerRel (junc (sumCop (dL Unit) ⟨Op A × (dPair A).carrier⟩) τ
              (rprodMap (𝟙 (dE (Op A))) X ≫ consR)) ≫ est (R (A := A)) := edit_body_junc X
    _ = (Freyd.Alg.ran (base (A := A)) ≫ Λ ((base (A := A))°) ≫ thinRel (𝟙 (dL Unit))
            ≫ powerRel τ ≫ est (R (A := A)))
        ∪ (Freyd.Alg.ran (step (A := A)) ≫ Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
            ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))) :=
        edit_disjoint_ranges X
    _ = (Freyd.Alg.ran (base (A := A)) ≫ Λ ((base (A := A))°) ≫ powerRel τ ≫ est (R (A := A)))
        ∪ (Freyd.Alg.ran (step (A := A)) ≫ Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
            ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))) := by
        rw [RelSet.thinRel_id, Cat.id_comp]
    _ = (empty ≫ (base (A := A))° ≫ τ)
        ∪ (Freyd.Alg.ran (step (A := A)) ≫ Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
            ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))) := by
        rw [edit_base_branch]

calc_steps Freyd.Alg.RelSet.Edit.edit_body_split

/-- **edit-laws** (B&dM p.227): `edit_laws` with its body split by Proposition 9.1 — the least
    fixed point of the book's `X=(empty→nil,(step°)%∋ thin(U×V)P((𝟙×X)cons)est(R))` is a
    shortest edit sequence. -/
public theorem edit_X :
    mu (fun X : dPair A ⟶ dEdit A =>
        (empty ≫ (base (A := A))° ≫ τ)
        ∪ (Freyd.Alg.ran (step (A := A)) ≫ Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
            ≫ powerRel (rprodMap (𝟙 (dE (Op A))) X ≫ consR) ≫ est (R (A := A))))
      ⊑ Λ ((graph (edit (A := A)))°) ≫ est (R (A := A)) := by
  have h := edit_laws (A := A)
  simp only [edit_body_split] at h
  exact h

/-! ## edit-laws, fourth row: `unstep` IS the thinned decomposition -/

/-- **edit-laws**, fourth row: `unstep` implements `frac(step°,∋) thin(U×V)` — the note's own
    claim for that row, and the two halves of `thinRel` are exactly `unstep`'s two.  Read as a
    set: `setify(unstep p)` is a subset of `p`'s decompositions (`unstep_sound`) that still
    dominates all of them (`unstep_complete`), which is what a thinning is.  `U≜⊤` on the
    operation leaves the three comparable and `V` orders the two strings. -/
public theorem unstep_thins [DecidableEq A] :
    unstep ≫ setify
      ⊑ Λ ((step (A := A))°)
          ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V)) := by
  rw [le_iff]
  rintro p Y ⟨L, rfl, rfl⟩
  refine ⟨fun q => step q p, by rw [Λ_eq_classifier]; rfl, ?_, ?_⟩
  · intro q hq
    exact (unstep_sound p q hq).symm
  · intro q hq
    obtain ⟨q', hq', hV⟩ := unstep_complete p q (hq : p = baseStepFn (Sum.inr q)).symm
    exact ⟨q', ⟨topMor_apply q'.1 q.1, hV⟩, hq'⟩

/-- **edit-laws**, fourth row (B&dM p.228): `unstep list((𝟙×mle)cons)minL(R)` refines the branch
    `(step°)%∋ thin(U×V)P((𝟙×X)cons)est(R)` — `unstep` implements `(step°)%∋ thin(U×V)`
    (`unstep_thins`) and `minL(R)` implements `est(R)`, the list standing in for the set it
    `setify`s to (`CL.list_comp_minL_le`, `setify`'s lax naturality). -/
public theorem edit_prog [DecidableEq A] (mle : dPair A ⟶ dEdit A) :
    unstep ≫ ListRel.list (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ minL((R (A := A)))
      ⊑ Λ ((step (A := A))°)
          ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
          ≫ powerRel (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ est (R (A := A)) :=
  calc unstep ≫ ListRel.list (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ minL((R (A := A)))
      ⊑ unstep ≫ ListRel.setify
          ≫ powerRel (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ est (R (A := A)) :=
        comp_mono_left unstep (CL.list_comp_minL_le _ _)
    _ = (unstep ≫ ListRel.setify)
          ≫ powerRel (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ est (R (A := A)) := by
        rw [← Cat.assoc]
    _ ⊑ (Λ ((step (A := A))°)
            ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V)))
          ≫ powerRel (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ est (R (A := A)) :=
        comp_mono_right unstep_thins _
    _ = Λ ((step (A := A))°)
          ≫ thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
          ≫ powerRel (rprodMap (𝟙 (dE (Op A))) mle ≫ consR) ≫ est (R (A := A)) := by
        rw [Cat.assoc]

/-! ## The beads of the `edit` panels, and what the environment says about them -/

/-- **`est(R)` is LAX natural** in the alphabet: `E(list(Op(S)))est(R) ⊑ est(R)list(Op(S))`.
    `R` compares LENGTHS and `Op(S)` relates an operation only to one of the same shape, so
    `list(Op(S))` relates sequences of equal length: a shortest sequence of the image comes from a
    member of the set, and that member is shortest there.  Not STRICT — the right side asks every
    member of the set for an image, which a relation that is not entire need not give. -/
public theorem est_R_laxNatural :
    LaxNatural (op.comp listRelator) ((op.comp listRelator).comp powerRelator)
      (fun a => est (R (A := a.carrier))) := by
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
    are — `𝟏 + Op×[Op]` — which is what `[nil,cons]`'s two ends read as.  `F Unit (Op A)` holds
    the alphabet FIXED, so its own `map` moves the tail alone and states no naturality in `A`. -/
@[expose] public def opF : Relator RelSet.{0} RelSet.{0} :=
  Relator.sum (Relator.const (dL Unit)) (Relator.prod op (op.comp listRelator))

/-- `F(Op(S),list(Op(S)))` is the lane stack's own action: the leaf arm untouched, the pair arm
    moving the operation and the tail together.  `Fbimap` is the action `alphaR_natural` is
    written in, and the two agree pointwise. -/
public theorem opF_map {x y : RelSet.{0}} (S : x ⟶ y) :
    opF.map S = Fbimap Unit (opRel S) (list (opRel S)) := by
  apply hom_ext; intro u v
  cases u <;> cases v <;>
    simp [opF, Relator.sum, Relator.prod, Relator.const, Relator.comp, sumMap,
      junc, RelProd.pair, prodMap, graph, Fbimap, clF, Poly.bimapR, instPositiveAllegory, instHasRelProd, sumCop,
      op, listRelator, clRelator, Relator.const, cl, clP, list, listP, list, listP] <;> first | grind | exact Subsingleton.elim _ _

/-- **`[nil,cons]` is STRICTLY natural** in the alphabet: `F(Op(S),list(Op(S)))[nil,cons] =
    [nil,cons]list(Op(S))`.  `ListRel.alphaR_natural` at the alphabet `Op(A)`, with the lane
    stack's action put in place of `Fbimap`'s — the canonical home is `A5_6_ListCombinators`, and
    this specialisation belongs beside it once that file is free. -/
public theorem con_strictNatural :
    StrictNatural (op.comp listRelator) opF
      (fun a => (graph con : Alg (F Unit (Op a.carrier)) (dEdit a.carrier))) := by
  intro x y S
  rw [opF_map]
  exact (ListRel.alphaR_natural (opRel S)).symm

/-- The `F` lane at the PAIR carrier: `𝟏 + Op×([A]×[A])`, the source of `[base,step]`. -/
@[expose] public def Pair.F : Relator RelSet.{0} RelSet.{0} :=
  Relator.sum (Relator.const (dL Unit))
    (Relator.prod op (Relator.prod listRelator listRelator))

public theorem Pair.F_map {x y : RelSet.{0}} (S : x ⟶ y) :
    Pair.F.map S = Fbimap Unit (opRel S) (rprodMap (list S) (list S)) := by
  apply hom_ext; intro u v
  cases u <;> cases v <;>
    simp [Pair.F, Relator.sum, Relator.prod, Relator.const, Relator.comp, sumMap, junc,
      RelProd.pair, prodMap, rprodMap, graph, Fbimap, clF, Poly.bimapR, instPositiveAllegory, instHasRelProd, sumCop,
      op, listRelator, clRelator, Relator.const, cl, clP, list, listP, list, listP] <;> first | grind | exact Subsingleton.elim _ _

/-- **`[base,step]` is LAX natural** in the alphabet: `F(Op(S),S×S)[base,step] ⊑
    [base,step](list(S)×list(S))`.  Not STRICT — `cpy a` writes ONE character into BOTH outputs, so
    the right side may send the two copies to two different characters of the new alphabet where
    the left side, which chooses the operation first, can only send them to one. -/
public theorem Pair.editAlg_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) Pair.F
      (fun a => editAlg (A := a.carrier)) := by
  intro x y S
  rw [Pair.F_map]
  refine le_iff.mpr fun u q => ?_
  rintro ⟨v, hv, rfl⟩
  rcases u with d | ⟨op, xs, ys⟩ <;> rcases v with d' | ⟨op', xs', ys'⟩
  · simp_all [Fbimap, clF, Poly.bimapR, editAlg, graph, baseStepFn, baseFn, stepFn, Relator.prod, prodMap, RelProd.pair,
      instHasRelProd, rprodMap, listRelator, clRelator, Relator.const, cl, clP, list, listP, list, listP]
  · exact (hv : False).elim
  · exact (hv : False).elim
  · rcases op with a | a | a <;> rcases op' with b | b | b <;>
      simp_all [Fbimap, clF, Poly.bimapR, editAlg, graph, baseStepFn, baseFn, stepFn, Relator.prod, prodMap, RelProd.pair,
        instHasRelProd, rprodMap, opRel, opP, listRelator, clRelator, Relator.const, cl, clP, list, listP, list, listP]

/-- **`step` is LAX natural** — the `inr` arm of `editAlg_laxNatural`, at the arm's own lane
    `Op×([A]×[A])`, which is the relator `edit-laws`' third row draws. -/
public theorem step_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator)
      (Relator.prod op (Relator.prod listRelator listRelator))
      (fun a => step (A := a.carrier)) := by
  intro x y S
  refine le_iff.mpr fun u q => ?_
  rintro ⟨v, hv, rfl⟩
  obtain ⟨op, xs, ys⟩ := u
  obtain ⟨op', xs', ys'⟩ := v
  rcases op with a | a | a <;> rcases op' with b | b | b <;>
    simp_all [step, graph, baseStepFn, stepFn, Relator.prod, prodMap, RelProd.pair, instHasRelProd,
      rprodMap, op, opRel, opP, listRelator, clRelator, Relator.const, cl, clP, list, listP, list, listP]

/-- An edit sequence and one it is `Op(S)`-related to reconstitute `S`-related strings: every
    operation puts its own character where the related operation puts the related one. -/
public theorem editFn_rel {x y : RelSet.{0}} (S : x ⟶ y) :
    ∀ (es : ConsList Unit (Op x.carrier)) (fs : ConsList Unit (Op y.carrier)),
      listP (opRel S) es fs →
      listP S (edit es).1 (edit fs).1 ∧ listP S (edit es).2 (edit fs).2 := by
  intro es
  induction es with
  | wrap u => rintro (fs | ⟨op', fs⟩) h <;> simp_all [opRel, opP, listP, clP]
  | cons op es ih =>
    rintro (fs | ⟨op', fs⟩) h
    · simp_all [opRel, opP, listP, clP]
    · obtain ⟨h1, h2⟩ := ih fs h.2
      rcases op with a | a | a <;> rcases op' with b | b | b <;>
        simp_all [opRel, opP, listP, clP]

/-- **`edit` is LAX natural**: `list(Op(S))edit ⊑ edit(list(S)×list(S))`.  Not STRICT — a `cpy`
    writes ONE character into BOTH strings, so a pair whose two copies of it are sent to different
    characters of the new alphabet is reached by no edit sequence. -/
public theorem edit_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (op.comp listRelator)
      (fun a => graph (edit (A := a.carrier))) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _]
  refine le_iff.mpr fun es p => ?_
  rintro ⟨fs, hfs, rfl⟩
  obtain ⟨h1, h2⟩ := editFn_rel S es fs hfs
  exact ⟨edit es, rfl, h1, h2⟩

/-- **`minL(R)` is LAX natural**: `list(list(Op(S)))minL(R) ⊑ minL(R)list(Op(S))`.  The
    argument of `est_R_laxNatural` with the LIST standing in for the set it `setify`s to: a shortest
    member of the image list comes from a member of the original, of the same length, and every
    other member of the original has an image of its own length. -/
public theorem minL_R_laxNatural :
    LaxNatural (op.comp listRelator) ((op.comp listRelator).comp listRelator)
      (fun a => CL.minL (R (A := a.carrier))) := by
  intro x y S
  refine le_iff.mpr fun ess r => ?_
  rintro ⟨fss, hff, hmin⟩
  obtain ⟨hr, hleast⟩ := (minL_apply _ _ _).mp hmin
  obtain ⟨hfwd, hbwd⟩ := listP_inlistP_split (list (opRel S)) ess fss hff
  obtain ⟨w, hw, hwr⟩ := hbwd r hr
  refine ⟨w, (minL_apply _ _ _).mpr ⟨hw, fun z hz => ?_⟩, hwr⟩
  obtain ⟨v, hzv, hv⟩ := hfwd z hz
  show clen w ≤ clen z
  rw [Van.listP_clen (P := opRel S) hwr, Van.listP_clen (P := opRel S) hzv]
  exact hleast v hv

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
@[expose] public def cand (a : A) (xs : Str A) : Op A × (dPair A).carrier :=
  (Op.del a, (xs, ConsList.wrap ()))

/-- `V` pointwise: each string of `p` is a suffix of the corresponding string of `q`. -/
public theorem V_apply (p q : (dPair A).carrier) :
    V p q ↔ suffixP p.1 q.1 ∧ suffixP p.2 q.2 := Iff.rfl

/-- `Op×([A]×[A])`'s action pointwise, the lane `edit-branch`'s thinning bead runs on. -/
public theorem stepF_apply {x y : RelSet.{0}} (S : x ⟶ y)
    (p : Op x.carrier × (dPair x.carrier).carrier)
    (q : Op y.carrier × (dPair y.carrier).carrier) :
    (Relator.prod op (Relator.prod listRelator listRelator)).map S p q
      ↔ opP S p.1 q.1 ∧ listP S p.2.1 q.2.1 ∧ listP S p.2.2 q.2.2 := by
  simp [Relator.prod, prodMap, RelProd.pair, instHasRelProd, op, listRelator, clRelator, Relator.const, cl, clP, listP,
    opRel, list, graph]

/-- `F(Op(S),S×S)`'s action on the `step` summand, the lane `edit-laws`' thinning bead runs on. -/
public theorem Pair.F_apply_inr {x y : RelSet.{0}} (S : x ⟶ y)
    (p : Op x.carrier × (dPair x.carrier).carrier)
    (q : Op y.carrier × (dPair y.carrier).carrier) :
    Pair.F.map S (Sum.inr p) (Sum.inr q)
      ↔ opP S p.1 q.1 ∧ listP S p.2.1 q.2.1 ∧ listP S p.2.2 q.2.2 := by
  rw [Pair.F_map]
  simp [Fbimap, clF, Poly.bimapR, rprodMap, opRel, list, cl, listP]

public theorem toU_short : listP toU shortB shortU := ⟨rfl, rfl⟩

public theorem toU_long : listP toU longB longU := ⟨rfl, rfl, rfl⟩

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
public theorem Pair.thin_Q_not_lax_natural :
    ¬ LaxNatural (Pair.F.comp powerRelator) (Pair.F.comp powerRelator)
      (fun a : RelSet.{0} => thinRel (Q (A := a.carrier))) := by
  intro hlax
  obtain ⟨W, hthin, hpow⟩ :=
    le_iff.mp (hlax toU)
      (fun z => z = Sum.inr (cand true shortB) ∨ z = Sum.inr (cand true longB))
      (fun z => z = Sum.inr (cand () shortU))
      ⟨fun z => z = Sum.inr (cand () shortU) ∨ z = Sum.inr (cand () longU),
        (powerRel_apply _ _ _).mpr
          ⟨fun p hp => by
              rcases hp with rfl | rfl
              · exact ⟨Sum.inr (cand () shortU), (Pair.F_apply_inr _ _ _).mpr ⟨rfl, toU_short, rfl⟩, Or.inl rfl⟩
              · exact ⟨Sum.inr (cand () longU), (Pair.F_apply_inr _ _ _).mpr ⟨rfl, toU_long, rfl⟩, Or.inr rfl⟩,
           fun q hq => by
              rcases hq with rfl | rfl
              · exact ⟨Sum.inr (cand true shortB), Or.inl rfl, (Pair.F_apply_inr _ _ _).mpr ⟨rfl, toU_short, rfl⟩⟩
              · exact ⟨Sum.inr (cand true longB), Or.inr rfl, (Pair.F_apply_inr _ _ _).mpr ⟨rfl, toU_long, rfl⟩⟩⟩,
        (thinRel_pt _ _ _).mpr
          ⟨fun y hy => Or.inl hy,
           fun z hz => by
             rcases hz with rfl | rfl
             · exact ⟨Sum.inr (cand () shortU), ⟨topMor_apply _ _, suffixP.refl _, rfl⟩, rfl⟩
             · exact ⟨Sum.inr (cand () shortU), ⟨topMor_apply _ _, shortU_suffix_longU, rfl⟩, rfl⟩⟩⟩
  obtain ⟨hsub, hdom⟩ := (thinRel_pt _ _ _).mp hthin
  obtain ⟨w, hwQ, hwW⟩ := hdom (Sum.inr (cand true longB)) (Or.inr rfl)
  obtain ⟨hfwd, -⟩ := (powerRel_apply _ _ _).mp hpow
  rcases hsub w hwW with rfl | rfl
  · exact short_not_suffix_long hwQ.2.1
  · obtain ⟨q, hq, rfl⟩ := hfwd _ hwW
    exact toU_long_not_short ((Pair.F_apply_inr _ _ _).mp hq).2.1

/-- **`thin(⊤×V)` is not even lax natural** — `edit-branch`'s thinning bead, at the same witness:
    the operations are `⊤`-comparable either way, so the whole verdict rests on `V`, which is the
    one of `thin(Q)` with the sum injection dropped. -/
public theorem thin_UV_not_lax_natural :
    ¬ LaxNatural ((Relator.prod op (Relator.prod listRelator listRelator)).comp powerRelator)
      ((Relator.prod op (Relator.prod listRelator listRelator)).comp powerRelator)
      (fun a : RelSet.{0} =>
        thinRel (rprodMap (topMor (dE (Op a.carrier)) (dE (Op a.carrier))) (V (A := a.carrier)))) := by
  intro hlax
  obtain ⟨W, hthin, hpow⟩ :=
    le_iff.mp (hlax toU)
      (fun z => z = cand true shortB ∨ z = cand true longB)
      (fun z => z = cand () shortU)
      ⟨fun z => z = cand () shortU ∨ z = cand () longU,
        (powerRel_apply _ _ _).mpr
          ⟨fun p hp => by
              rcases hp with rfl | rfl
              · exact ⟨cand () shortU, (stepF_apply _ _ _).mpr ⟨rfl, toU_short, rfl⟩, Or.inl rfl⟩
              · exact ⟨cand () longU, (stepF_apply _ _ _).mpr ⟨rfl, toU_long, rfl⟩, Or.inr rfl⟩,
           fun q hq => by
              rcases hq with rfl | rfl
              · exact ⟨cand true shortB, Or.inl rfl, (stepF_apply _ _ _).mpr ⟨rfl, toU_short, rfl⟩⟩
              · exact ⟨cand true longB, Or.inr rfl, (stepF_apply _ _ _).mpr ⟨rfl, toU_long, rfl⟩⟩⟩,
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

/-- **`R` is not even lax natural** in the alphabet: an image sequence may use a character with no
    preimage.  At the empty relation on `Bool`, `[]` is `R`-below `[cpy true]`, which no sequence
    reaches through `list(Op(𝟘))`. -/
public theorem R_not_lax_natural :
    ¬ LaxNatural (op.comp listRelator) (op.comp listRelator)
      (fun a : RelSet.{0} => (R (A := a.carrier))) := by
  intro hlax
  obtain ⟨fs₀, -, hfs₀⟩ := le_iff.mp (hlax (fun _ _ => False : dE Bool ⟶ dE Bool))
    (ConsList.wrap () : ConsList Unit (Op Bool)) (ConsList.cons (Op.cpy true) (ConsList.wrap ()))
    ⟨ConsList.wrap (), by simp [Relator.comp, listRelator, clRelator, Relator.const, cl, clP, list, listP, op, list, listP], Nat.zero_le _⟩
  rcases fs₀ with _ | ⟨op, t⟩
  · simp [Relator.comp, listRelator, clRelator, Relator.const, cl, clP, list, listP, op, list, listP] at hfs₀
  · rcases op with a | a | a <;>
      simp [Relator.comp, listRelator, clRelator, Relator.const, cl, clP, list, listP, op, list, listP, opRel, opP] at hfs₀

/-- **`Q` is not even lax natural** in the alphabet: `Q` puts above a decomposition one whose
    operation carries any character, and an alphabet map that misses `false` has no preimage of
    `del false`. -/
public theorem Pair.Q_not_lax_natural :
    ¬ LaxNatural Pair.F Pair.F (fun a : RelSet.{0} => Q (A := a.carrier)) := by
  intro hlax
  obtain ⟨v₀, -, hv₀⟩ := le_iff.mp (hlax (graph (fun _ : Unit => true) : dE Unit ⟶ dE Bool))
    (Sum.inr (cand () (ConsList.wrap ())))
    (Sum.inr (cand false (ConsList.cons false (ConsList.wrap ()))))
    ⟨Sum.inr (cand true (ConsList.wrap ())), (Pair.F_apply_inr _ _ _).mpr ⟨rfl, rfl, rfl⟩,
      (show Q (A := Bool) (Sum.inr (cand true (ConsList.wrap ())))
          (Sum.inr (cand false (ConsList.cons false (ConsList.wrap ())))) from
        ⟨topMor_apply _ _, (V_apply _ _).mpr ⟨Or.inr rfl, rfl⟩⟩)⟩
  rcases v₀ with d | p
  · rw [Pair.F_map] at hv₀; exact hv₀
  · obtain ⟨hop, -⟩ := (Pair.F_apply_inr _ _ _).mp hv₀
    rcases p with ⟨a | a | a, _⟩ <;> simp [opP, graph, cand] at hop

/-- **`F(⊤,V)` is not even lax natural**: it is `Q` itself, spelled as the bifunctor. -/
public theorem Pair.Fbimap_top_V_not_lax_natural :
    ¬ LaxNatural Pair.F Pair.F (fun a : RelSet.{0} =>
      Fbimap Unit (topMor (dE (Op a.carrier)) (dE (Op a.carrier))) (V (A := a.carrier))) :=
  Pair.Q_not_lax_natural

/-- The lane stack `𝟏 + Op×K` of the edit pictures acts as the bifunctor: `F(Op(S),K(S))`. -/
public theorem sumOp_map (K : Relator RelSet.{0} RelSet.{0}) {x y : RelSet.{0}} (S : x ⟶ y) :
    (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op) K)).map S
      = Fbimap Unit (opRel S) (K.map S) := by
  apply hom_ext; intro u v
  cases u <;> cases v <;>
    simp [Relator.sum, Relator.prod, Relator.const, Relator.comp, Relator.idRelator, sumMap,
      junc, RelProd.pair, prodMap, graph, Fbimap, clF, Poly.bimapR, instPositiveAllegory, instHasRelProd, sumCop,
      op] <;> first | grind | exact Subsingleton.elim _ _

/-- **`[zero,π₂ succ]` is LAX natural** in the alphabet: `F(Op(S),𝟙)` keeps the tail's length. -/
public theorem lenAlg_laxNatural :
    LaxNatural (Relator.const (⟨Nat⟩ : RelSet.{0}))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.const (⟨Nat⟩ : RelSet.{0}))))
      (fun a : RelSet.{0} => graph (lenAlgFn (A := a.carrier))) := by
  intro x y S
  refine le_iff.mpr fun u n h => ?_
  obtain ⟨u', hu, hn⟩ := h
  rw [sumOp_map] at hu
  refine ⟨lenAlgFn u, rfl, ?_⟩
  show lenAlgFn u = n
  rw [(hn : n = lenAlgFn u')]
  rcases u with d | p <;> rcases u' with d' | p'
  · rfl
  · exact hu.elim
  · exact hu.elim
  · exact congrArg (· + 1) hu.2

/-- **`F(⊤,W)` is not even lax natural** in the alphabet, whatever `W`: at `() ↦ true` the image
    `(cpy true, c')` sits under `(cpy false, w')` by `⊤`, and `cpy false` has no preimage. -/
public theorem Fbimap_top_not_laxNatural {F₂ G₂ : Relator RelSet.{0} RelSet.{0}}
    (W : ∀ a : RelSet.{0}, G₂.obj a ⟶ F₂.obj a) (c : (G₂.obj (dE Unit)).carrier)
    (c' : (G₂.obj (dE Bool)).carrier) (w' : (F₂.obj (dE Bool)).carrier)
    (hc : G₂.map (graph (fun _ : Unit => true) : dE Unit ⟶ dE Bool) c c')
    (hw : W (dE Bool) c' w') :
    ¬ LaxNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op) F₂))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op) G₂))
      (fun a => Fbimap Unit (topMor (dE (Op a.carrier)) (dE (Op a.carrier))) (W a)) := by
  intro hlax
  obtain ⟨v, -, hv⟩ := le_iff.mp (hlax (graph (fun _ : Unit => true) : dE Unit ⟶ dE Bool))
    (Sum.inr (Op.cpy (), c)) (Sum.inr (Op.cpy false, w'))
    ⟨Sum.inr (Op.cpy true, c'), by rw [sumOp_map]; exact ⟨by simp [Poly.bimapR, opRel, opP, graph], hc⟩,
      ⟨topMor_apply _ _, hw⟩⟩
  rw [sumOp_map] at hv
  rcases v with d | ⟨o, e⟩
  · exact hv
  · rcases o with a | a | a <;> simp [Fbimap, clF, Poly.bimapR, opRel, opP, graph] at hv

/-- `([],[])` is related to `([],[])` by the pair lanes, whatever `S`. -/
public theorem listLanes_nil {x y : RelSet.{0}} (S : x ⟶ y) :
    (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
        (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)).map S
      (ConsList.wrap (), ConsList.wrap ()) (ConsList.wrap (), ConsList.wrap ()) := by
  rw [show (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)).map S = rprodMap (list S) (list S)
    from prodMap_eq_rprodMap _ _]
  exact ⟨rfl, rfl⟩

/-- `F(⊤,V)`, at the lanes the step pictures read. -/
public theorem Fbimap_top_V_not_laxNatural :
    ¬ LaxNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
            (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
            (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))))
      (fun a => Fbimap Unit (topMor (dE (Op a.carrier)) (dE (Op a.carrier))) (V (A := a.carrier))) :=
  by
  refine Fbimap_top_not_laxNatural (F₂ := Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator) (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)) (G₂ := Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator) (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)) (fun a => V (A := a.carrier))
    (ConsList.wrap (), ConsList.wrap ())
    (ConsList.wrap (), ConsList.wrap ()) (ConsList.wrap (), ConsList.wrap ())
    (listLanes_nil _) ?_
  exact (V_apply _ _).mpr ⟨rfl, rfl⟩

/-- `F(⊤,V edit°)`, at the lanes the step pictures read. -/
public theorem Fbimap_top_Vedit_not_laxNatural :
    ¬ LaxNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator)))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
            (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))))
      (fun a => Fbimap Unit (topMor (dE (Op a.carrier)) (dE (Op a.carrier)))
        (V (A := a.carrier) ≫ (graph (edit (A := a.carrier)))°)) :=
  by
  refine Fbimap_top_not_laxNatural (F₂ := Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator) (G₂ := Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator) (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))
    (fun a => V (A := a.carrier) ≫ (graph (edit (A := a.carrier)))°)
    (ConsList.wrap (), ConsList.wrap ()) (ConsList.wrap (), ConsList.wrap ()) (ConsList.wrap ())
    (listLanes_nil _) ?_
  exact ⟨(ConsList.wrap (), ConsList.wrap ()), (V_apply _ _).mpr ⟨rfl, rfl⟩, rfl⟩

/-- `F(⊤,edit° R)`, at the lanes the step pictures read. -/
public theorem Fbimap_top_editR_not_laxNatural :
    ¬ LaxNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator)))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
            (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))))
      (fun a => Fbimap Unit (topMor (dE (Op a.carrier)) (dE (Op a.carrier)))
        ((graph (edit (A := a.carrier)))° ≫ (R (A := a.carrier)))) :=
  by
  refine Fbimap_top_not_laxNatural (F₂ := Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator) (G₂ := Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator) (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))
    (fun a => (graph (edit (A := a.carrier)))° ≫ (R (A := a.carrier)))
    (ConsList.wrap (), ConsList.wrap ()) (ConsList.wrap (), ConsList.wrap ()) (ConsList.wrap ())
    (listLanes_nil _) ?_
  exact ⟨ConsList.wrap (), rfl, Nat.le_refl _⟩

/-- `F(⊤,R)`, at the lanes the step pictures read. -/
public theorem Fbimap_top_R_not_laxNatural :
    ¬ LaxNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator)))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) op)
          (Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator)))
      (fun a => Fbimap Unit (topMor (dE (Op a.carrier)) (dE (Op a.carrier))) (R (A := a.carrier))) :=
  by
  refine Fbimap_top_not_laxNatural (F₂ := Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator) (G₂ := Relator.comp (Relator.comp (Relator.idRelator RelSet.{0}) op) listRelator) (fun a => (R (A := a.carrier)))
    (ConsList.wrap ()) (ConsList.wrap ())
    (ConsList.wrap ()) rfl ?_
  exact Nat.le_refl _

/-- **`R°` is not even lax natural**, at the alphabet map `() ↦ true`: `[cpy false]` is no longer
    than the image `[cpy true]` of `[cpy ()]`, and has no preimage. -/
public theorem R_recip_not_lax_natural :
    ¬ LaxNatural (op.comp listRelator) (op.comp listRelator)
      (fun a : RelSet.{0} => (R (A := a.carrier))°) := by
  intro hlax
  obtain ⟨fs₀, -, hfs₀⟩ := le_iff.mp (hlax (graph (fun _ : Unit => true) : dE Unit ⟶ dE Bool))
    (ConsList.cons (Op.cpy ()) (ConsList.wrap ())) (ConsList.cons (Op.cpy false) (ConsList.wrap ()))
    ⟨ConsList.cons (Op.cpy true) (ConsList.wrap ()),
      by simp [Relator.comp, listRelator, clRelator, Relator.const, cl, clP, list, listP, op, list, listP, opRel, opP, graph], Nat.le_refl _⟩
  rcases fs₀ with _ | ⟨op, t⟩
  · simp [Relator.comp, listRelator, clRelator, Relator.const, cl, clP, list, listP, op, list, listP] at hfs₀
  · rcases op with a | a | a <;>
      simp [Relator.comp, listRelator, clRelator, Relator.const, cl, clP, list, listP, op, list, listP, opRel, opP, graph] at hfs₀

/-- A suffix of the image of a list is the image of a suffix of the list. -/
public theorem suffixP_listP {x y : RelSet.{0}} (S : x ⟶ y) :
    ∀ (xs : ConsList Unit x.carrier) (xs' zs' : ConsList Unit y.carrier),
      listP S xs xs' → suffixP zs' xs' → ∃ zs, suffixP zs xs ∧ listP S zs zs'
  | ConsList.wrap _, ConsList.wrap _, zs', _, hs => by
      obtain rfl : zs' = ConsList.wrap () := hs
      exact ⟨ConsList.wrap (), rfl, rfl⟩
  | ConsList.wrap _, ConsList.cons _ _, _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, _, h, _ => h.elim
  | ConsList.cons a xs, ConsList.cons b xs', zs', h, hs => by
      rcases (hs : zs' = ConsList.cons b xs' ∨ suffixP zs' xs') with rfl | hs
      · exact ⟨ConsList.cons a xs, Or.inl rfl, h⟩
      · obtain ⟨zs, hz, hzs⟩ := suffixP_listP S xs xs' zs' h.2 hs
        exact ⟨zs, Or.inr hz, hzs⟩

/-- **`V°` is LAX natural**: a pair of suffixes of an image pair is the image of a pair of
    suffixes (`suffixP_listP`).  Not STRICT — a suffix of the original need not have an image. -/
public theorem V_recip_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (Relator.prod listRelator listRelator)
      (fun a : RelSet.{0} => (V (A := a.carrier))°) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _]
  refine le_iff.mpr fun p q h => ?_
  obtain ⟨p', ⟨h1, h2⟩, hV⟩ := h
  obtain ⟨z1, hz1, hl1⟩ := suffixP_listP S p.1 p'.1 q.1 h1 hV.1
  obtain ⟨z2, hz2, hl2⟩ := suffixP_listP S p.2 p'.2 q.2 h2 hV.2
  exact ⟨(z1, z2), ⟨hz1, hz2⟩, hl1, hl2⟩

/-- **`tail` is LAX natural**: the tail of an image list is the image of the tail. -/
public theorem tail_laxNatural {x y : RelSet.{0}} (S : x ⟶ y) :
    list S ≫ (graph tail : dList y.carrier ⟶ dList y.carrier) ⊑ graph tail ≫ list S :=
  le_iff.mpr fun xs zs ⟨ys, h, hz⟩ => by
    obtain rfl : zs = tail ys := hz
    refine ⟨tail xs, rfl, ?_⟩
    match xs, ys, h with
    | ConsList.wrap _, ConsList.wrap _, _ => exact rfl
    | ConsList.cons _ _, ConsList.cons _ _, h => exact h.2
    | ConsList.wrap _, ConsList.cons _ _, h => exact h.elim
    | ConsList.cons _ _, ConsList.wrap _, h => exact h.elim

/-- **`𝟙×tail` is LAX natural** (`tail_laxNatural` on the second lane). -/
public theorem tail_snd_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (Relator.prod listRelator listRelator)
      (fun a : RelSet.{0} => rprodMap (𝟙 (dList a.carrier)) (graph tail)) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _, rprodMap_comp, rprodMap_comp]
  exact rprodMap_mono (le_iff.mpr fun a c ⟨b, hab, hbc⟩ =>
    ⟨a, (id_apply _ _).mpr rfl, ((id_apply _ _).mp hbc) ▸ hab⟩) (tail_laxNatural S)

/-- **`(𝟙×tail)*` is LAX natural**: `B A ⊑ C B ⟹ B A* ⊑ C* B` on `tail_snd_laxNatural`. -/
public theorem tail_snd_star_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (Relator.prod listRelator listRelator)
      (fun a : RelSet.{0} => star (rprodMap (𝟙 (dList a.carrier)) (graph tail))) :=
  fun S => star_simulation (tail_snd_laxNatural S)

/-- **`𝟙×tail*` is LAX natural**: it is `(𝟙×tail)*` (`rprodMap_id_star`). -/
public theorem id_tail_star_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (Relator.prod listRelator listRelator)
      (fun a : RelSet.{0} => rprodMap (𝟙 (dList a.carrier)) (star (graph tail))) := by
  intro x y S
  show _ ≫ rprodMap (𝟙 _) (star (graph tail)) ⊑ rprodMap (𝟙 _) (star (graph tail)) ≫ _
  rw [rprodMap_id_star, rprodMap_id_star]
  exact tail_snd_star_laxNatural S

/-- `list(Op(S))` carries `dropTgt` across: the same position writes to the target. -/
public theorem listP_dropTgt {x y : RelSet.{0}} (S : x ⟶ y) :
    ∀ (xs : ConsList Unit (Op x.carrier)) (ys : ConsList Unit (Op y.carrier)),
      listP (opRel S) xs ys → listP (opRel S) (drop₂ xs) (drop₂ ys)
  | ConsList.wrap _, ConsList.wrap _, h => h
  | ConsList.cons (Op.cpy _) _, ConsList.cons (Op.cpy _) _, h => h
  | ConsList.cons (Op.del _) xs, ConsList.cons (Op.del _) ys, h => ⟨h.1, listP_dropTgt S xs ys h.2⟩
  | ConsList.cons (Op.ins _) _, ConsList.cons (Op.ins _) _, h => h.2
  | ConsList.cons (Op.cpy _) _, ConsList.cons (Op.del _) _, h
  | ConsList.cons (Op.cpy _) _, ConsList.cons (Op.ins _) _, h
  | ConsList.cons (Op.del _) _, ConsList.cons (Op.cpy _) _, h
  | ConsList.cons (Op.del _) _, ConsList.cons (Op.ins _) _, h
  | ConsList.cons (Op.ins _) _, ConsList.cons (Op.cpy _) _, h
  | ConsList.cons (Op.ins _) _, ConsList.cons (Op.del _) _, h => h.1.elim
  | ConsList.wrap _, ConsList.cons _ _, h | ConsList.cons _ _, ConsList.wrap _, h => h.elim

/-- **`dropTgt` is LAX natural** in the alphabet (`listP_dropTgt`). -/
public theorem dropTgt_laxNatural :
    LaxNatural (op.comp listRelator) (op.comp listRelator)
      (fun a : RelSet.{0} => (graph drop₂ : dEdit a.carrier ⟶ dEdit a.carrier)) := by
  intro x y S
  refine le_iff.mpr fun xs zs ⟨ys, h, hz⟩ => ?_
  obtain rfl : zs = drop₂ ys := hz
  exact ⟨drop₂ xs, rfl, listP_dropTgt S xs ys h⟩

/-- Lax natural transformations compose: `ψ` then `φ`. -/
public theorem laxNatural_vcomp {F G H : Relator RelSet.{0} RelSet.{0}}
    {φ : ∀ x : RelSet.{0}, G.obj x ⟶ F.obj x} {ψ : ∀ x : RelSet.{0}, H.obj x ⟶ G.obj x}
    (hψ : LaxNatural G H ψ) (hφ : LaxNatural F G φ) : LaxNatural F H (fun x => ψ x ≫ φ x) := by
  intro x y S
  calc H.map S ≫ ψ y ≫ φ y = (H.map S ≫ ψ y) ≫ φ y := (Cat.assoc _ _ _).symm
    _ ⊑ (ψ x ≫ G.map S) ≫ φ y := comp_mono_right (hψ S) _
    _ = ψ x ≫ G.map S ≫ φ y := Cat.assoc _ _ _
    _ ⊑ ψ x ≫ φ x ≫ F.map S := comp_mono_left _ (hφ S)
    _ = (ψ x ≫ φ x) ≫ F.map S := (Cat.assoc _ _ _).symm

/-- `𝟙` is lax natural. -/
public theorem id_laxNatural {F : Relator RelSet.{0} RelSet.{0}} :
    LaxNatural F F (fun x : RelSet.{0} => 𝟙 (F.obj x)) := by
  intro x y S
  rw [Cat.comp_id, Cat.id_comp]
  exact le_iff.mpr fun _ _ h => h

/-- **`⦇h₂⦈ = ⟨𝟙,drop₂⟩` is LAX natural**: a pair of lax natural transformations. -/
public theorem dropTgt_fold_laxNatural :
    LaxNatural (Relator.prod (op.comp listRelator) (op.comp listRelator)) (op.comp listRelator)
      (fun a : RelSet.{0} => cataR (h₂ (A := a.carrier))) := by
  intro x y S
  dsimp only
  rw [← dropTgt_fold, ← dropTgt_fold]
  exact laxNatural_pair id_laxNatural dropTgt_laxNatural S

/-- **`⟨edit, edit(𝟙×tail)⟩` is LAX natural**: a pair of lax natural transformations. -/
public theorem edit_tail_snd_pair_laxNatural :
    LaxNatural (Relator.prod (Relator.prod listRelator listRelator)
        (Relator.prod listRelator listRelator)) (op.comp listRelator)
      (fun a : RelSet.{0} => (relProd (dPair a.carrier) (dPair a.carrier)).pair (graph edit)
        (graph edit ≫ rprodMap (𝟙 (dList a.carrier)) (graph tail))) :=
  laxNatural_pair edit_laxNatural (laxNatural_vcomp edit_laxNatural tail_snd_laxNatural)

/-- **`⦇k₂⦈ = ⟨edit, edit(𝟙×tail)⟩` is LAX natural**. -/
public theorem editTgt_fold_laxNatural :
    LaxNatural (Relator.prod (Relator.prod listRelator listRelator)
        (Relator.prod listRelator listRelator)) (op.comp listRelator)
      (fun a : RelSet.{0} => cataR (k₂ (A := a.carrier))) := by
  intro x y S
  dsimp only
  rw [← edit_tail_snd_fold, ← edit_tail_snd_fold]
  exact edit_tail_snd_pair_laxNatural S

/-- **`⟨𝟙,R°⟩` is not lax natural**: followed by `outr`, which is, it is `R°`, which is not. -/
public theorem pair_id_R_recip_not_lax_natural :
    ¬ LaxNatural (Relator.prod (op.comp listRelator) (op.comp listRelator)) (op.comp listRelator)
      (fun a : RelSet.{0} =>
        (relProd (dEdit a.carrier) (dEdit a.carrier)).pair (𝟙 (dEdit a.carrier)) (R (A := a.carrier))°) :=
  fun h => R_recip_not_lax_natural fun S => by
    have e : ∀ a : RelSet.{0}, (relProd (dEdit a.carrier) (dEdit a.carrier)).pair (𝟙 (dEdit a.carrier))
        (R (A := a.carrier))° ≫ (relProd ((op.comp listRelator).obj a) ((op.comp listRelator).obj a)).π₂
          = (R (A := a.carrier))° := fun _ => pair_id_outr _
    have h2 := laxNatural_vcomp h (outr_laxNatural (op.comp listRelator) (op.comp listRelator)) S
    dsimp only at h2 ⊢
    rw [e, e] at h2
    exact h2

/-- **`(R°)*` is not lax natural**: it is `R°` (`R_recip_star`), which is not. -/
public theorem R_recip_star_not_lax_natural :
    ¬ LaxNatural (op.comp listRelator) (op.comp listRelator)
      (fun a : RelSet.{0} => star (R (A := a.carrier))°) := by
  simpa only [R_recip_star] using R_recip_not_lax_natural

/-- **`base°` is LAX natural**: only `([],[])` is related to `([],[])` by `list(S)×list(S)`. -/
public theorem base_recip_laxNatural :
    LaxNatural (Relator.const (dL Unit)) (Relator.prod listRelator listRelator)
      (fun a : RelSet.{0} => (base (A := a.carrier))°) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _]
  refine le_iff.mpr fun p d h => ?_
  obtain ⟨q, ⟨h1, h2⟩, hd⟩ := h
  obtain rfl : q = ((ConsList.wrap () : ConsList Unit y.carrier), ConsList.wrap ()) := hd
  refine ⟨d, ?_, rfl⟩
  obtain ⟨xs, ys⟩ := p
  cases xs with
  | cons _ _ => exact h1.elim
  | wrap _ => cases ys with
    | cons _ _ => exact h2.elim
    | wrap _ => rfl

/-- **`empty` is LAX natural**, for the reason `base°` is. -/
public theorem empty_laxNatural :
    LaxNatural (Relator.prod listRelator listRelator) (Relator.prod listRelator listRelator)
      (fun a : RelSet.{0} => empty (A := a.carrier)) := by
  intro x y S
  rw [show (Relator.prod listRelator listRelator).map S = rprodMap (list S) (list S) from
    prodMap_eq_rprodMap _ _]
  refine le_iff.mpr fun p q h => ?_
  obtain ⟨m, hG, hmq, hm⟩ := h
  subst hmq
  subst hm
  obtain ⟨xs, ys⟩ := p
  refine ⟨(xs, ys), ⟨rfl, ?_⟩, hG⟩
  obtain ⟨h1, h2⟩ := hG
  cases xs with
  | cons _ _ => exact h1.elim
  | wrap _ => cases ys with
    | cons _ _ => exact h2.elim
    | wrap _ => rfl

/-- **`length` is LAX natural**: `list(Op(S))` relates sequences of one length. -/
public theorem clen_laxNatural :
    LaxNatural (Relator.const (⟨Nat⟩ : RelSet.{0})) (op.comp listRelator)
      (fun a : RelSet.{0} => (graph clen : dEdit a.carrier ⟶ (⟨Nat⟩ : RelSet.{0}))) := by
  intro x y S
  refine le_iff.mpr fun es n h => ?_
  obtain ⟨fs, hfs, hn⟩ := h
  refine ⟨clen es, rfl, ?_⟩
  rw [(hn : n = clen fs), Van.listP_clen (P := opRel S) hfs]
  exact rfl

/-! ## `edit-tabulation` (B&dM pp.227-229): `mle` computed column by column -/

section Tabulation

variable {A : Type}

public instance instInhabitedCL : Inhabited (Str A) := ⟨ConsList.wrap ()⟩

/-- `head : [A] → A`; the tabulation only takes it of a non-empty column. -/
@[expose] public def head [Inhabited A] : Str A → A
  | ConsList.wrap _ => default
  | ConsList.cons a _ => a

/-- `init : [A] → [A]`, the list without its last element. -/
@[expose] public def init : Str A → Str A
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons _ (ConsList.wrap _) => ConsList.wrap ()
  | ConsList.cons a (ConsList.cons b x) => ConsList.cons a (init (ConsList.cons b x))

/-- `last : [A] → A`; the tabulation only takes it of a non-empty column. -/
@[expose] public def last [Inhabited A] : Str A → A
  | ConsList.wrap _ => default
  | ConsList.cons a (ConsList.wrap _) => a
  | ConsList.cons _ (ConsList.cons b x) => last (ConsList.cons b x)

/-- `zip : [A]×[B] → [A×B]`, cut to the shorter list. -/
@[expose] public def zip {B : Type} : Str A → ConsList Unit B → ConsList Unit (A × B)
  | ConsList.wrap _, ConsList.wrap _ => ConsList.wrap ()
  | ConsList.wrap _, ConsList.cons _ _ => ConsList.wrap ()
  | ConsList.cons _ _, ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons a x, ConsList.cons b y => ConsList.cons (a, b) (zip x y)

/-- `bmin(Q) : A×A → A`, B&dM's `bmin R = (R → outl, outr)`: the left one when it is `Q`-below the
    right one, the right one otherwise. -/
@[expose] public def bmin {X : RelSet.{0}} (Q : X ⟶ X) [∀ a b, Decidable (Q a b)]
    (p : X.carrier × X.carrier) : X.carrier :=
  if Q p.1 p.2 then p.1 else p.2

public instance instDecR (es fs : (dEdit A).carrier) : Decidable ((R (A := A)) es fs) :=
  inferInstanceAs (Decidable (clen es ≤ clen fs))

end Tabulation

variable [DecidableEq A]

/-- **edit-tabulation**: `mle`, the recursive characterisation of the program `edit-laws` states
    (B&dM p.228): a copy where the heads agree, otherwise the `R`-better of a delete and an
    insert. -/
@[expose] public def mle : Str A × Str A → ConsList Unit (Op A)
  | (ConsList.wrap _, ConsList.wrap _) => ConsList.wrap ()
  | (ConsList.cons a xs, ConsList.wrap _) => ConsList.cons (Op.del a) (mle (xs, ConsList.wrap ()))
  | (ConsList.wrap _, ConsList.cons b ys) => ConsList.cons (Op.ins b) (mle (ConsList.wrap (), ys))
  | (ConsList.cons a xs, ConsList.cons b ys) =>
      if a = b then ConsList.cons (Op.cpy a) (mle (xs, ys))
      else bmin (R (A := A)) (ConsList.cons (Op.del a) (mle (xs, ConsList.cons b ys)),
                          ConsList.cons (Op.ins b) (mle (ConsList.cons a xs, ys)))
termination_by p => clen p.1 + clen p.2
decreasing_by all_goals (simp only [clen]; omega)

/-- **edit-tabulation**: `column(xs)(ys)=[mle(u,ys)∣u←tails(xs)]`. -/
@[expose] public def column (xs ys : Str A) : ConsList Unit (ConsList Unit (Op A)) :=
  cmap (fun u => mle (u, ys)) (tailsFn xs)

/-- **edit-tabulation**: `fstcol=list(del) tails`, the rightmost column. -/
@[expose] public def fstcol (xs : Str A) : ConsList Unit (ConsList Unit (Op A)) :=
  tailsFn (cmap Op.del xs)

namespace Tab

/-- **edit-tabulation**: `base(b,u)=[[ins(b)]⧺u]`, the bottom entry of the next column. -/
@[expose] public def base (p : A × ConsList Unit (Op A)) :
    ConsList Unit (ConsList Unit (Op A)) :=
  ConsList.cons (ConsList.cons (Op.ins p.1) p.2) (ConsList.wrap ())

/-- **edit-tabulation**: `step(b)((a,(u,v)),ws)=(a=b→[[cpy(a)]⧺v]⧺ws,[bmin(R)([del(a)]⧺w,[ins(b)]⧺u)]⧺ws)`
    with `w=head(ws)`: the entry above `ws` in the next column. -/
@[expose] public def step (b : A)
    (q : A × (ConsList Unit (Op A) × ConsList Unit (Op A)))
    (ws : ConsList Unit (ConsList Unit (Op A))) : ConsList Unit (ConsList Unit (Op A)) :=
  if q.1 = b then ConsList.cons (ConsList.cons (Op.cpy q.1) q.2.2) ws
  else ConsList.cons (bmin (R (A := A)) (ConsList.cons (Op.del q.1) (head ws),
                                     ConsList.cons (Op.ins b) q.2.1)) ws

end Tab

/-- **edit-tabulation**: `nextcol(xs)(b,us)=⦇[base(b,last(us)),step(b)]⦈(xus)`,
    `xus=zip(xs,zip(init(us),tail(us)))`. -/
@[expose] public def nextcol (xs : Str A)
    (p : A × ConsList Unit (ConsList Unit (Op A))) :
    ConsList Unit (ConsList Unit (Op A)) :=
  cfold (fun _ => Tab.base (p.1, last p.2)) (Tab.step p.1) (zip xs (zip (init p.2) (tail p.2)))

theorem nextcol_cons (a b : A) (x : Str A) (u v : ConsList Unit (Op A))
    (t : ConsList Unit (ConsList Unit (Op A))) :
    nextcol (ConsList.cons a x) (b, ConsList.cons u (ConsList.cons v t))
      = Tab.step b (a, (u, v)) (nextcol x (b, ConsList.cons v t)) := by
  cases t <;> rfl

/-- The top entry of `column(xs)(ys)` is `mle(xs,ys)`. -/
theorem column_top (xs ys : Str A) :
    ∃ t, column xs ys = ConsList.cons (mle (xs, ys)) t := by
  cases xs with
  | wrap u => cases u; exact ⟨_, rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- **edit-tabulation**: `mle(xs,ys)=head(column(xs,ys))`. -/
public theorem mle_head_column (xs ys : Str A) :
    mle (xs, ys) = head (column xs ys) := by
  obtain ⟨t, ht⟩ := column_top xs ys
  rw [ht]; rfl

theorem mle_nil_right (u : Unit) : ∀ xs : Str A,
    mle (xs, ConsList.wrap u) = cmap Op.del xs
  | ConsList.wrap _ => by rw [mle]; rfl
  | ConsList.cons a xs => by rw [mle, mle_nil_right () xs]; rfl

/-- **edit-laws**, the specification `mle` is derived from: `mle ⊑ Λ(edit°) est(≤)`, a shortest
    edit sequence among those that edit back to the given pair.  Stated, not yet proved. -/
@[expose] public def mleSpec : Prop :=
  (graph mle : dPair A ⟶ dEdit A) ⊑ Λ ((graph (edit (A := A)))°) ≫ est (R (A := A))

theorem tails_cmap {A B : Type} (f : A → B) : ∀ xs : Str A,
    tailsFn (cmap f xs) = cmap (cmap f) (tailsFn xs)
  | ConsList.wrap _ => rfl
  | ConsList.cons a xs => by
      show ConsList.cons _ (tailsFn (cmap f xs)) = _
      rw [tails_cmap f xs]; rfl

/-- **edit-tabulation**: the rightmost column is `fstcol(xs)`. -/
public theorem column_nil (xs : Str A) (u : Unit) :
    column xs (ConsList.wrap u) = fstcol xs := by
  show cmap _ (tailsFn xs) = tailsFn (cmap Op.del xs)
  rw [tails_cmap, show (fun v => mle (v, ConsList.wrap u)) = cmap Op.del from
    funext (mle_nil_right u)]

/-- **edit-tabulation**: `column(xs)([b]⧺ys)=nextcol(xs)(b,column(xs)(ys))` — each column is
    built from the one to its right. -/
public theorem column_cons (b : A) (ys : Str A) : ∀ xs : Str A,
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
public theorem column_cata (xs : Str A) :
    (graph (column xs) : dList A ⟶ ⟨ConsList Unit (ConsList Unit (Op A))⟩)
      = cataR (consScalarAlg (fun _ => fstcol xs) (fun b us => nextcol xs (b, us))) :=
  consFold_unique _ _ _ (column_nil xs) (fun b ys => column_cons b ys xs)

/-! ### `mle-step`: one run of `mle` on `([a,b],[b])`, `a≠b`, one theorem per row of the note's table

The relational rows are RUN on the two-array relations of `A6_FinRel`: each spec relation is cut
down to a finite domain that holds every pair it relates there, built as a `FinRel`, and the row's
value is that `FinRel` evaluated. -/

section MleRun

/-- `suffixP x y`, decided by walking `y`. -/
instance decSuffixP : ∀ x y : Str A, Decidable (suffixP x y)
  | x, ConsList.wrap _ => inferInstanceAs (Decidable (x = ConsList.wrap ()))
  | x, ConsList.cons b y =>
      have := decSuffixP x y
      inferInstanceAs (Decidable (x = ConsList.cons b y ∨ suffixP x y))

/-- `thin(Q)`'s order `⊤×V` as a `RelRep` test: its two suffix tests. -/
def topV : RelRep (Op A × (Str A × Str A)) (Op A × (Str A × Str A)) :=
  .test fun w z => decide (suffixP w.2.1 z.2.1) && decide (suffixP w.2.2 z.2.2)

theorem rel_topV : (topV (A := A)).rel = rprodMap (topMor (dE (Op A)) (dE (Op A))) (V) :=
  hom_ext fun w z => by
    simp only [topV, RelRep.rel, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun h => ⟨topMor_apply _ _, h⟩, fun h => h.2⟩

omit [DecidableEq A] in
theorem self_mem_tails : ∀ x : Str A, x ∈ CL.toList (tailsFn x)
  | ConsList.wrap () => by simp [tailsFn, CL.toList]
  | ConsList.cons _ _ => by simp [tailsFn, CL.toList]

omit [DecidableEq A] in
theorem inlistP_iff_mem {α : Type} : ∀ (xs : ConsList Unit α) (w : α), inlistP xs w ↔ w ∈ CL.toList xs
  | ConsList.wrap _, _ => by simp [inlistP, CL.toList]
  | ConsList.cons b x, w => by simp [inlistP, CL.toList, inlistP_iff_mem x w]

omit [DecidableEq A] in
/-- The candidate decompositions of `p`: an operation on a letter of `p` beside a suffix of each
    string — the finite domain `step°` is restricted to. -/
def stepDom (p : Str A × Str A) : List (Op A × (Str A × Str A)) :=
  ((CL.toList p.1).flatMap (fun c => [Op.cpy c, Op.del c]) ++ (CL.toList p.2).map Op.ins).flatMap fun o =>
    (CL.toList (tailsFn p.1)).flatMap fun x => (CL.toList (tailsFn p.2)).map fun y => (o, (x, y))

omit [DecidableEq A] in
/-- The restriction loses nothing: every decomposition of `p` is a candidate. -/
theorem stepDom_complete {q : Op A × (Str A × Str A)} {p : Str A × Str A} (h : stepFn q = p) :
    q ∈ stepDom p := by
  obtain ⟨o, x, y⟩ := q
  subst h
  have hx := self_mem_tails x
  have hy := self_mem_tails y
  cases o with
  | cpy c =>
    show _ ∈ stepDom (ConsList.cons c x, ConsList.cons c y)
    refine List.mem_flatMap.2 ⟨Op.cpy c, ?_, List.mem_flatMap.2 ⟨x, ?_, List.mem_map.2 ⟨y, ?_, rfl⟩⟩⟩ <;>
      simp [CL.toList, tailsFn, hx, hy]
  | del c =>
    show _ ∈ stepDom (ConsList.cons c x, y)
    refine List.mem_flatMap.2 ⟨Op.del c, ?_, List.mem_flatMap.2 ⟨x, ?_, List.mem_map.2 ⟨y, ?_, rfl⟩⟩⟩ <;>
      simp [CL.toList, tailsFn, hx, hy]
  | ins c =>
    show _ ∈ stepDom (x, ConsList.cons c y)
    refine List.mem_flatMap.2 ⟨Op.ins c, ?_, List.mem_flatMap.2 ⟨x, ?_, List.mem_map.2 ⟨y, ?_, rfl⟩⟩⟩ <;>
      simp [CL.toList, tailsFn, hx, hy]

omit [DecidableEq A] in
/-- `step` on the candidate domain of `p`, a finite graph. -/
def stepFin (p : Str A × Str A) : FinRel (Op A × (Str A × Str A)) (Str A × Str A) :=
  FinRel.ofList ((stepDom p).map fun q => (q, stepFn q))

/-- `step°` at `p` is the lookup of `p` in the converse of the finite graph. -/
theorem step_recip_lookup (p : Str A × Str A) (q : Op A × (Str A × Str A)) :
    stepFn q = p ↔ q ∈ (stepFin p).conv.scanLookup p := by
  constructor
  · intro h
    refine List.mem_filterMap.2 ⟨(p, q), ?_, by simp [FinRel.sel]⟩
    rw [FinRel.toList_conv, stepFin, FinRel.toList_ofList, List.map_map]
    exact List.mem_map.2 ⟨q, stepDom_complete h, by simp [h]⟩
  · intro hq
    obtain ⟨⟨k, q'⟩, hm, hs⟩ := List.mem_filterMap.1 hq
    rw [FinRel.toList_conv, stepFin, FinRel.toList_ofList, List.map_map] at hm
    obtain ⟨q'', _, he⟩ := List.mem_map.1 hm
    simp only [Function.comp, Prod.swap, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    unfold FinRel.sel at hs
    split at hs
    · rename_i hc; cases hs; simpa using hc
    · cases hs

omit [DecidableEq A] in
/-- `cmap(g)` run on `RelRep`: the list held as the pairs `((),x)`, composed with the graph of `g`,
    and looked up at `()`. -/
theorem cmap_of_comp {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → β) (xs : ConsList Unit α)
    (T : FinRel Unit β)
    (hT : RelRep.comp (.pairs (FinRel.ofList ((CL.toList xs).map ((), ·)))) (.fn g) = some (.pairs T)) :
    cmap g xs = CL.ofList (T.scanLookup ()) := by
  simp only [RelRep.comp, Option.some.injEq, RelRep.pairs.injEq] at hT
  subst hT
  rw [cmap_eq_ofList_map, FinRel.scanLookup, FinRel.toList_map, FinRel.toList_ofList]
  congr 1
  induction CL.toList xs <;> simp_all [FinRel.sel]

/-- `thin(Q)` keeps the whole of a finite set on which `Q`, held as the `RelRep` `T` and met with the
    set's square, is the diagonal. -/
theorem thin_of_square {α : RelSet.{0}} [DecidableEq α.carrier] (Q : α ⟶ α) (T : RelRep α.carrier α.carrier)
    (hT : T.rel = Q) (xs : List α.carrier) (r : FinRel α.carrier α.carrier)
    (hr : RelRep.inter (.pairs (FinRel.square xs)) T = .pairs r) (hc : r.toList = xs.map fun x => (x, x))
    (Y : (RelSet.pow α).carrier) :
    thinRel Q (fun q => q ∈ xs) Y ↔ Y = fun q => q ∈ xs := by
  cases hr
  have hQ : ∀ w z, w ∈ xs → z ∈ xs → (Q w z ↔ w = z) := fun w z hw hz => by
    have h := FinRel.mem_filter_square (fun k v => T.mem k v = true) xs w z
    rw [hc, List.mem_map, RelRep.mem_iff_rel, hT] at h
    exact ⟨fun hq => by
      obtain ⟨x, _, e⟩ := h.2 ⟨hw, hz, hq⟩
      simp only [Prod.mk.injEq] at e
      exact e.1.symm.trans e.2, fun e => (h.1 ⟨w, hw, by rw [e]⟩).2.2⟩
  rw [thinRel_pt]
  constructor
  · rintro ⟨hsub, hdom⟩
    funext q
    apply propext
    refine ⟨hsub q, fun hq => ?_⟩
    obtain ⟨w, hw, hY⟩ := hdom q hq
    exact ((hQ w q (hsub w hY) hq).1 hw) ▸ hY
  · rintro rfl
    exact ⟨fun _ h => h, fun z hz => ⟨z, (hQ z z hz hz).2 rfl, hz⟩⟩

omit [DecidableEq A] in
/-- `minL(Q)` reads the least members off `Q` filtered by `FinRel` to the list's square. -/
theorem minL_of_square {α : Type} (Q : dE α ⟶ dE α) [∀ a b, Decidable (Q a b)] (xs : ConsList Unit α)
    (w : α) : minL(Q) xs w ↔ w ∈ CL.toList xs ∧
      ∀ z ∈ CL.toList xs, (w, z) ∈ (FinRel.filter Q (FinRel.square (CL.toList xs))).toList := by
  rw [minL_apply, inlistP_iff_mem]
  exact and_congr_right fun hw => forall_congr' fun z => by
    rw [inlistP_iff_mem, FinRel.mem_filter_square]
    exact ⟨fun h hz => ⟨hw, hz, h hz⟩, fun h hz => (h hz).2.2⟩

variable {a b : A}

/-- **mle-step**, `Λ(step°)`: the decompositions of `([a,b],[b])` are a `del` and an `ins`, no `cpy`
    since the heads differ — `step` on the candidate domain, conversed and looked up. -/
public theorem run_step_recip (hab : a ≠ b) :
    (fun q : Op A × (Str A × Str A) =>
        stepFn q = (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.cons b (ConsList.wrap ())))
      = fun q => q = (Op.del a, (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ())))
        ∨ q = (Op.ins b, (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ())) := by
  funext q
  apply propext
  rw [step_recip_lookup]
  simp [FinRel.scanLookup, FinRel.toList_conv, stepFin, FinRel.toList_ofList, stepDom, CL.toList, tailsFn,
    FinRel.sel, stepFn, hab, Ne.symm hab]

/-- **mle-step**, `thin(Q)`: neither decomposition has its strings `V`-below the other's — `⊤×V`
    filtered to the set's square is its diagonal — so the thinning keeps both. -/
public theorem run_thin (Y : Op A × (Str A × Str A) → Prop) :
    thinRel (rprodMap (topMor (dE (Op A)) (dE (Op A))) (V))
        (fun q : Op A × (Str A × Str A) =>
          q = (Op.del a, (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ())))
          ∨ q = (Op.ins b, (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ()))) Y
      ↔ Y = fun q => q = (Op.del a, (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ())))
        ∨ q = (Op.ins b, (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ())) := by
  have h := thin_of_square _ topV rel_topV
    [(Op.del a, (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ()))),
     (Op.ins b, (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ()))] _ rfl
    (by simp [FinRel.filter, FinRel.square, FinRel.toList_ofList, RelRep.mem, topV, suffixP]) Y
  simpa only [List.mem_cons, List.mem_nil_iff, or_false] using h

/-- **mle-step**, `unstep`: both decompositions survive the thinning, as a list. -/
public theorem run_unstep (hab : a ≠ b) :
    unstepFn (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.cons b (ConsList.wrap ()))
      = ConsList.cons (Op.del a, (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ())))
          (ConsList.cons (Op.ins b, (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ()))
            (ConsList.wrap ())) := by
  rw [unstep_cons, if_neg hab]

/-- **mle-step**, the recursive `mle` on the `del` rest: `mle([b],[b])=[cpy b]`. -/
public theorem run_rest_cpy :
    mle (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ()))
      = ConsList.cons (Op.cpy b) (ConsList.wrap ()) := by
  rw [mle, if_pos rfl, mle]

/-- **mle-step**, the recursive `mle` on the `ins` rest: `mle([a,b],[])=[del a,del b]`. -/
public theorem run_rest_del :
    mle (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ())
      = ConsList.cons (Op.del a) (ConsList.cons (Op.del b) (ConsList.wrap ())) := by
  rw [mle, mle, mle]

/-- **mle-step**, `list((𝟙×mle)cons)` on `unstep`'s list: each operation put in front of its rest's
    sequence. -/
public theorem run_list_cons :
    cmap (fun q : Op A × (Str A × Str A) => ConsList.cons q.1 (mle q.2))
        (ConsList.cons (Op.del a, (ConsList.cons b (ConsList.wrap ()), ConsList.cons b (ConsList.wrap ())))
          (ConsList.cons (Op.ins b, (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.wrap ()))
            (ConsList.wrap ())))
      = ConsList.cons (ConsList.cons (Op.del a) (ConsList.cons (Op.cpy b) (ConsList.wrap ())))
          (ConsList.cons (ConsList.cons (Op.ins b) (ConsList.cons (Op.del a)
            (ConsList.cons (Op.del b) (ConsList.wrap ())))) (ConsList.wrap ())) := by
  rw [cmap_of_comp _ _ _ rfl]
  simp [FinRel.scanLookup, FinRel.toList, FinRel.map, FinRel.ofList, FinRel.sel, CL.toList, CL.ofList,
    run_rest_cpy, run_rest_del]

omit [DecidableEq A] in
/-- **mle-step**, `minL(R)`: the shorter sequence is the only `R`-least one — `R` filtered to the
    list's square relates the longer one to nothing shorter-or-equal but itself. -/
public theorem run_minL (w : ConsList Unit (Op A)) :
    minL((R (A := A))) (ConsList.cons (ConsList.cons (Op.del a) (ConsList.cons (Op.cpy b) (ConsList.wrap ())))
          (ConsList.cons (ConsList.cons (Op.ins b) (ConsList.cons (Op.del a)
            (ConsList.cons (Op.del b) (ConsList.wrap ())))) (ConsList.wrap ()))) w
      ↔ w = ConsList.cons (Op.del a) (ConsList.cons (Op.cpy b) (ConsList.wrap ())) := by
  rw [minL_of_square]
  simp [FinRel.filter, FinRel.square, FinRel.toList_ofList, CL.toList, R, clen]
  exact ⟨fun h => h.2.1, fun h => ⟨Or.inl h, h, Or.inl h⟩⟩

/-- **mle-step**, the whole run: `mle([a,b],[b])=[del a,cpy b]`. -/
public theorem run_mle (hab : a ≠ b) :
    mle (ConsList.cons a (ConsList.cons b (ConsList.wrap ())), ConsList.cons b (ConsList.wrap ()))
      = ConsList.cons (Op.del a) (ConsList.cons (Op.cpy b) (ConsList.wrap ())) := by
  have h := run_list_cons (a := a) (b := b)
  simp only [cmap, ConsList.cons.injEq, and_true, true_and] at h
  rw [mle, if_neg hab, h.1, h.2]
  simp [bmin, R, clen]

end MleRun

-- printing-only unexpanders: the edit sequences and the string pairs under the note's names.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.dEdit] public meta def unexpandDEdit : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "[Op]")))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.dPair] public meta def unexpandDPair : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "Str(A)×Str(A)")))

end Freyd.Alg.RelSet.Edit

-- Rules, not renames: each prints a constant under the name another constant already owns — a
-- step function under its algebra's letter (`h₂`…), a function under its graph (`step`, `base`,
-- `unstep`) — and two constants of one namespace cannot both print bare under one name.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.dropTgtStep] public meta def Freyd.Alg.RelSet.Edit.unexpandDropTgtStep : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "h₂")))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.dropSrcStep] public meta def Freyd.Alg.RelSet.Edit.unexpandDropSrcStep : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "h₁")))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.editTgtStep] public meta def Freyd.Alg.RelSet.Edit.unexpandEditTgtStep : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "k₂")))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.editSrcStep] public meta def Freyd.Alg.RelSet.Edit.unexpandEditSrcStep : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "k₁")))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.FeditR]public meta def Freyd.Alg.RelSet.Edit.unexpandFeditR : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "F(𝟙,edit°)")))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.unstepFn] public meta def Freyd.Alg.RelSet.Edit.unexpandEditUnstepFn : Unexpander
  | _ => `($(mkIdent `unstep))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.stepFn] public meta def Freyd.Alg.RelSet.Edit.unexpandEditStepFn : Unexpander
  | _ => `($(mkIdent `step))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.baseFn] public meta def Freyd.Alg.RelSet.Edit.unexpandEditBaseFn : Unexpander
  | _ => `($(mkIdent `base))
-- `Op`'s alphabet is an inductive's parameter, which a type position cannot leave implicit.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.Op] public meta def Freyd.Alg.RelSet.Edit.unexpandEditOp : Unexpander
  | _ => `($(mkIdent `Op))

-- printing-only: the note's names for this section's declarations.
-- The edit lanes are the base functor `F` of the section; the carrier is the wire under it.
-- A rule, not a rename: `con_strictNatural` states `opF` beside `CL.F`, and the note writes both
-- `F`, which no namespace can print bare at once.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Edit.opF] public meta def Freyd.Alg.RelSet.Edit.unexpandEditOpF : Unexpander | _ => `($(mkIdent `F))
