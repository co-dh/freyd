/-
  `diag.S2_124` — Freyd & Scedrov §2.124, `𝟙 ∩ S R° = Dom (R ∩ S)`, proved DIAGRAMMATICALLY.

  This file replaces `Freyd/S2_124.lean`, which built a Frobenius calculus from scratch on a private
  `Rel A B := A → B → Prop` in order to check the companion picture `diag/S2_124.typ`.  Everything in
  its first half — the generators, the (co)monoid and Frobenius equations, converse, the monoidal
  laws — is `diag/CB.lean` said twice, so it is gone; and its extra axiom
  `adequacy` (`Δ;(R ⊗ R);∇ = R`) is `meet_idem`, a theorem.  What is left is what was actually its
  own: the normal form `W` and the two identities the drawn proof rests on.

  They are now stated over an ARBITRARY cartesian bicategory of relations rather than over `Rel`.
  The old header explained why they were not: a point-free derivation "would additionally need the
  monoidal-coherence lemmas (associator/unitor naturality) as rewrite steps — the bookkeeping string
  diagrams suppress; that infrastructure is not built here".  On this branch there is no such
  bookkeeping to build: `diag/Monoidal.lean` is STRICT, so the pictures' suppressed unitors and
  associators are identities and the proofs below are the derivations with nothing hidden.

  The route is the picture's, NOT Freyd's.  Freyd proves §2.124 from the modular law; here both sides
  are driven to `W = Δ;(Δ ⊗ 𝟙);((𝟙 ⊗ R) ⊗ S);(𝟙 ⊗ cap)` and the modular law is used only inside
  `dom_cd`, in the one step (`meet_top_eq_conv`) where a top has to be turned back into a converse.

  `Freyd.Alg.dom_inter` (`Freyd/S2_10.lean`) is the same statement for allegories, and by
  `allegoryOfCartBicat` it already transfers here.  This is a second, independent proof of a
  book-numbered result, kept because it is the one `diag/S2_124.typ` draws.
-/
import diag.CB_Allegory

universe v u

namespace Freyd.Diag

open Freyd
open scoped Word SymMonCat
open CartBicat

variable {O : Type u} [CartBicat.{v} O]

/-! ### The two maps the pictures draw as a bent wire

In the non-strict tower these are named definitions, `keepFst = (𝟙 ⊗ !);ρ` and
`capKeep = α;(𝟙 ⊗ cap);ρ`, precisely so that no proof can hide the coherence arrows inside them.
Strictness deletes both: `ρ` and `α` are identities, so `keepFst a b` IS `𝟙_a ⊗ !_b` and
`capKeep a b` IS `𝟙_a ⊗ cap_b`, and a definition for either would be a name for a term that is
already one generator wide.  They are written out at their use sites below. -/

/-- DOMAIN, Freyd §2.122: `Dom R = 𝟙 ∩ R R°`. -/
def Dom {a b : Word O} (R : a ⟶ b) : a ⟶ a := meet (𝟙 a) (R ≫ conv R)

/-- The normal form both sides of §2.124 are driven to:
    `W = Δ;(Δ ⊗ 𝟙);((𝟙 ⊗ R) ⊗ S);(𝟙 ⊗ cap)`  (`Δ;(Δ ⊗ 𝟙)` is the three-way copy). -/
def W {a b : Word O} (R S : a ⟶ b) : a ⟶ a :=
  Δ ≫ (Δ ⊗ₕ 𝟙 a) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ S) ≫ (𝟙 a ⊗ₕ cap b)

/-! ### Two preliminaries -/

/-- An arrow into the unit object restricts the identity: `𝟙 ∩ (L;?) = Δ;(𝟙 ⊗ L)`.  This is the
    step that turns a discarded strand back into a meet — the picture draws both as "keep the wire
    only where `L` is defined".

    In the non-strict tower this proof first needs `(𝟙 ⊗ ?);∇ = ρ`, the unit law (7) with the
    unitor moved across.  With `ρ = 𝟙` that lemma IS the unit law, so it is gone. -/
theorem «meet_?» {a : Word O} (L : a ⟶ (𝕀 : Word O)) :
    meet (𝟙 a) (L ≫ «?») = Δ ≫ (𝟙 a ⊗ₕ L) := by
  have hsplit : (𝟙 a ⊗ₕ (L ≫ «?» (n := a))) = (𝟙 a ⊗ₕ L) ≫ (𝟙 a ⊗ₕ «?» (n := a)) := by
    rw [← SymMonCat.tensHom_comp, Cat.comp_id]
  have htail : (𝟙 a ⊗ₕ L) ≫ (𝟙 a ⊗ₕ «?» (n := a)) ≫ ∇ = (𝟙 a ⊗ₕ L) := by
    rw [«∇_unit»]; exact Cat.comp_id _
  dsimp [meet]
  rw [hsplit]
  simp only [Cat.assoc]
  rw [htail]

/-- THE MODULAR LAW ON THE OTHER SIDE, `RS ∩ T ≤ R(S ∩ R°T)` — `modular_of_frobenius` read through
    the converse, which is an order isomorphism (`conv_mono`, `conv_conv`) and turns each of `≫`,
    `∩` around (`conv_comp`, `conv_inter`). -/
theorem modular_right {a b c : Word O} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    meet (R ≫ S) T ≤ R ≫ meet S (conv R ≫ T) := by
  have h := conv_mono (modular_of_frobenius (conv S) (conv R) (conv T))
  simp only [conv_comp, conv_inter, conv_conv] at h
  exact h

/-! ### The two identities the drawn proof rests on -/

/-- **Lemma 1.**  `Dom P = Δ;(𝟙 ⊗ P);(𝟙 ⊗ !)`.

    `Dom P = 𝟙 ∩ P P°` names `P` twice; this form names it once and throws its output away.  The
    collapse is `𝟙 ∩ P P° = 𝟙 ∩ P⊤`: one direction is `P° ≤ ⊤`, and the other is the only place in
    this file where the modular law is spent — `modular_right` at `S := ⊤` turns the discarded
    strand back into `P°`, because `⊤ ∩ P° = P°`. -/
theorem dom_cd {a b : Word O} (P : a ⟶ b) :
    Dom P = Δ ≫ (𝟙 a ⊗ₕ P) ≫ (𝟙 a ⊗ₕ «!») := by
  have hshape : Δ ≫ (𝟙 a ⊗ₕ P) ≫ (𝟙 a ⊗ₕ «!») = meet (𝟙 a) (P ≫ top b a) := by
    have hsplit : (𝟙 a ⊗ₕ P) ≫ (𝟙 a ⊗ₕ «!») = (𝟙 a ⊗ₕ (P ≫ «!»)) := by
      rw [← SymMonCat.tensHom_comp, Cat.comp_id]
    dsimp [top]
    rw [← Cat.assoc P («!») («?»), «meet_?» (P ≫ «!»), ← hsplit]
  rw [hshape]
  dsimp [Dom]
  refine OrderedCat.«≤_antisymm» ?_ ?_
  · exact meet_mono (OrderedCat.«≤_refl» _)
      (OrderedCat.comp_mono (OrderedCat.«≤_refl» P) («≤_top» (conv P)))
  · refine meet_glb («meet_≤_left» _ _) ?_
    have hmod := modular_right P (top b a) (𝟙 a)
    rw [Cat.comp_id, meet_comm (top b a) (conv P), meet_top] at hmod
    rw [meet_comm (𝟙 a) (P ≫ top b a)]
    exact hmod

/-- **Lemma 2.**  `(𝟙 ⊗ P°);∇ = (Δ ⊗ 𝟙);((𝟙 ⊗ P) ⊗ 𝟙);(𝟙 ⊗ cap)`.

    The move that turns a converse into a witness: copy the surviving wire, run `P` FORWARD on the
    copy, and cap its output against the wire that was already there.  `«cap_tens_∇»` is the
    box-carrying merge-from-a-cap, and `conv_slide` is what lets `P°` on one strand be read as `P` on
    the other.  The associator naturality of the non-strict proof is now one `tensHom_assoc`. -/
theorem cv_merge {a b : Word O} (P : a ⟶ b) :
    (𝟙 a ⊗ₕ conv P) ≫ ∇
      = (Δ ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ P) ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ cap b) := by
  calc (𝟙 a ⊗ₕ conv P) ≫ ∇
      = (Δ ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ ((𝟙 a ⊗ₕ conv P) ≫ cap a)) := («cap_tens_∇» (conv P)).symm
    _ = (Δ ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ ((P ⊗ₕ 𝟙 b) ≫ cap b)) := by rw [← conv_slide]
    _ = (Δ ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ (P ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_comp, Cat.comp_id]
    _ = (Δ ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ P) ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_assoc]

/-! ### §2.124 — both sides to the same normal form -/

/-- Left side: `𝟙 ∩ S R° = W`.  Apply Lemma 2 at `R`, then the two copy trees are the same one:
    both sides are `Δ;((Δ;(𝟙 ⊗ R)) ⊗ S);(𝟙 ⊗ cap)`, by functoriality of `⊗` alone. -/
theorem left_eq_W {a b : Word O} (R S : a ⟶ b) : meet (𝟙 a) (S ≫ conv R) = W R S := by
  dsimp [meet, W]
  calc Δ ≫ (𝟙 a ⊗ₕ (S ≫ conv R)) ≫ ∇
      = Δ ≫ ((𝟙 a ⊗ₕ S) ≫ (𝟙 a ⊗ₕ conv R)) ≫ ∇ := by
        rw [← SymMonCat.tensHom_comp, Cat.comp_id]
    _ = Δ ≫ (𝟙 a ⊗ₕ S) ≫ (𝟙 a ⊗ₕ conv R) ≫ ∇ := by simp only [Cat.assoc]
    _ = Δ ≫ (𝟙 a ⊗ₕ S) ≫ (Δ ⊗ₕ 𝟙 b) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [cv_merge R]
    _ = Δ ≫ ((𝟙 a ⊗ₕ S) ≫ (Δ ⊗ₕ 𝟙 b)) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ cap b) := by
        simp only [Cat.assoc]
    _ = Δ ≫ (Δ ⊗ₕ S) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ 𝟙 b) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_comp, Cat.id_comp, Cat.comp_id]
    _ = Δ ≫ ((Δ ⊗ₕ S) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ 𝟙 b)) ≫ (𝟙 a ⊗ₕ cap b) := by
        simp only [Cat.assoc]
    _ = Δ ≫ ((Δ ≫ (𝟙 a ⊗ₕ R)) ⊗ₕ S) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_comp, Cat.comp_id]
    _ = Δ ≫ ((Δ ⊗ₕ 𝟙 a) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_comp, Cat.id_comp]
    _ = Δ ≫ (Δ ⊗ₕ 𝟙 a) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ S) ≫ (𝟙 a ⊗ₕ cap b) := by
        simp only [Cat.assoc]

/-- Right side: `Dom (R ∩ S) = W`.  Lemma 1 at `R ∩ S`, then `∇;! = cap` unfolds the meet into the
    picture's cap, and `Δ_assoc` — coassociativity (8) — identifies the two copy trees. -/
theorem right_eq_W {a b : Word O} (R S : a ⟶ b) : Dom (meet R S) = W R S := by
  rw [dom_cd (meet R S)]
  dsimp [W]
  calc Δ ≫ (𝟙 a ⊗ₕ meet R S) ≫ (𝟙 a ⊗ₕ «!»)
      = Δ ≫ (𝟙 a ⊗ₕ (meet R S ≫ «!»)) := by
        rw [← SymMonCat.tensHom_comp, Cat.comp_id]
    _ = Δ ≫ (𝟙 a ⊗ₕ (Δ ≫ (R ⊗ₕ S) ≫ cap b)) := by
        dsimp [meet, cap]; simp only [Cat.assoc]
    _ = Δ ≫ (𝟙 a ⊗ₕ Δ) ≫ (𝟙 a ⊗ₕ (R ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp, Cat.comp_id, Cat.comp_id]
    _ = (Δ ≫ (𝟙 a ⊗ₕ Δ)) ≫ (𝟙 a ⊗ₕ (R ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap b) := (Cat.assoc _ _ _).symm
    _ = (Δ ≫ (Δ ⊗ₕ 𝟙 a)) ≫ (𝟙 a ⊗ₕ (R ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap b) := by rw [← Δ_assoc]
    _ = Δ ≫ (Δ ⊗ₕ 𝟙 a) ≫ (𝟙 a ⊗ₕ (R ⊗ₕ S)) ≫ (𝟙 a ⊗ₕ cap b) := Cat.assoc _ _ _
    _ = Δ ≫ (Δ ⊗ₕ 𝟙 a) ≫ ((𝟙 a ⊗ₕ R) ⊗ₕ S) ≫ (𝟙 a ⊗ₕ cap b) := by
        rw [← SymMonCat.tensHom_assoc]

/-- **§2.124.**  `𝟙 ∩ S R° = Dom (R ∩ S)` — Freyd's "a lemma we will use repeatedly", by driving
    both sides to `W`.  The allegory-level statement, which Freyd proves from the modular law
    directly, is `Freyd.Alg.dom_inter`. -/
theorem dom_inter_diag {a b : Word O} (R S : a ⟶ b) :
    meet (𝟙 a) (S ≫ conv R) = Dom (meet R S) :=
  (left_eq_W R S).trans (right_eq_W R S).symm

/-! ### §2.13 — what §2.124 is repeatedly used FOR -/

/-- **`R ∩ S` is entire iff `𝟙 ≤ R S°`** — Freyd §2.13 read through §2.124, B&dM 4.18.

    `Total` is Freyd's `Entire`, `𝟙 ≤ P P°`, so the left side names `R ∩ S` twice and the right side
    names each of `R`, `S` once.  That is the whole content: the meet on the left is not needed to
    ASK the question, only to answer it.  `Freyd.Alg.entire_inter_iff` (`AOP/A4_2.lean`) is the same
    statement for a bare allegory, where it is `Iff.rfl` on top of `dom_inter` because there `⊑` is
    *defined* as `X ∩ Y = X`; here `≤` is primitive, so both directions are real steps.

    Written as two explicit `«≤_trans»` chains rather than `rw`s, so that the argument sits in the
    proof TERM where `diag-export --proof` can draw it. -/
theorem entire_inter_iff {a b : Word O} (R S : a ⟶ b) :
    Total (meet R S) ↔ (𝟙 a) ≤ (R ≫ conv S) := by
  constructor
  · intro h
    -- `𝟙 ≤ (R ∩ S)(R ∩ S)° ≤ R S°`: monotone in each factor, and nothing else is used.  This is
    -- the direction that holds in any allegory-like setting, modular law or not.
    exact OrderedCat.«≤_trans» h
      (OrderedCat.comp_mono («meet_≤_left» R S) (conv_mono («meet_≤_right» R S)))
  · intro h
    -- The other way needs §2.124, which is where the modular law is spent.  That link is an
    -- EQUALITY and is stated as one, so the drawn chain shows it as `=` rather than hiding it
    -- among the `≤`s.
    -- The `Dom` is unfolded in the step, not left folded: `diag-export` draws a term, and `Dom P`
    -- has no shape in the picture language — it would come out as one opaque box where the whole
    -- content is the meet inside it.
    calc (𝟙 a) ≤ meet (𝟙 a) (R ≫ conv S) := meet_glb (OrderedCat.«≤_refl» _) h
      _ = meet (𝟙 a) (meet S R ≫ conv (meet S R)) := by
            rw [dom_inter_diag S R]; rfl
      _ ≤ meet R S ≫ conv (meet R S) := by rw [meet_comm R S]; exact «meet_≤_right» _ _

end Freyd.Diag
