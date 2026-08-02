/-
  `diag.CB_Derived` — the operations AOP needs, DERIVED from `CartBicat`.  Nothing here is an axiom.

  functorialSemanticsForRelationalTheories.pdf §4, pp. 18–22.  The meet `◁;(R ⊗ S);▷` is the
  paper's `∩` (p. 22, "every hom-set is a meet semi-lattice") and `⊤ := !;?` is its unit.  In the
  non-strict tower they come before the wire-bending converse because they are defined at a single
  object and so need no associator; here the monoidal structure is strict and no result in `diag/`
  needs one, so the ordering is only the paper's.
-/
import diag.CB

universe v u

namespace Freyd.Diag

open Freyd
open scoped Word SymMonCat
open CartBicat

variable {O : Type u} [CartBicat.{v} O]

/-- The CONVOLUTION `◁;(R ⊗ S);▷`
    (functorialSemanticsForRelationalTheories.pdf p. 22).  Copy the input, run `R` and `S` on the
    two copies, then merge — the merge forces the two results to coincide, so this is `R ∩ S`. -/
def meet {a b : Word O} (R S : a ⟶ b) : a ⟶ b := ◁ ≫ (R ⊗ₕ S) ≫ ▷

/-- `⊤ := !;?`, the maximum arrow: discard everything, then create everything.  The unit of
    `meet` (functorialSemanticsForRelationalTheories.pdf p. 22). -/
def top (a b : Word O) : a ⟶ b := ⊸ ≫ ⟜

/-- Every arrow is below `⊤`.  Lax counit (43) sends `R;!` under `!`, and (40) supplies the `?`. -/
theorem «≤_top» {a b : Word O} (R : a ⟶ b) : R ≤ (top a b) := by
  -- `R = R;𝟙 ≤ R;(!;?) = (R;!);? ≤ !;? = ⊤`.
  have h1 : (R ≫ 𝟙 b) ≤ (R ≫ ⊸ ≫ ⟜) :=
    OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («𝟙≤!?» b)
  -- Both `⊸`s and both `⟜`s are named: `top a b` is `⊸ₐ ⟜_b`, and a statement whose ends are
  -- `a` and `b` cannot say which object the `𝕀` in the middle came from.
  have h2 : ((R ≫ «!» (n := b)) ≫ «?» (n := b)) ≤ («!» (n := a) ≫ «?» (n := b)) :=
    OrderedCat.comp_mono (lax_! R) (OrderedCat.«≤_refl» («?» (n := b)))
  rw [Cat.comp_id] at h1
  rw [Cat.assoc] at h2
  exact OrderedCat.«≤_trans» h1 h2

/-- `⊤` is the unit of the meet: `R ∩ ⊤ = R`
    (functorialSemanticsForRelationalTheories.pdf p. 22, unitality in Lemma 4.11).  The `⊤` strand
    is discarded by the counit law (10) and re-absorbed by the unit law (7).  With `ρ = 𝟙` there is
    no unitor left to move `R` past, so the naturality step of the non-strict proof is gone. -/
theorem meet_top {a b : Word O} (R : a ⟶ b) : meet R (top a b) = R := by
  -- Stage the `⊗`: `R ⊗ (⊸ ⟜) = (R ⊗ ⊸) (𝟙 ⊗ ⟜)`.
  have hR : (R ⊗ₕ («!» (n := a) ≫ «?» (n := b))) = (R ⊗ₕ ⊸) ≫ (𝟙 b ⊗ₕ ⟜) := by
    rw [← SymMonCat.tensHom_comp, Cat.comp_id]
  -- `R ⊗ ⊸` is `(𝟙 ⊗ ⊸) R`, since `R ⊗ 𝟙_I` IS `R`.
  have hsplit : (R ⊗ₕ «!» (n := a)) = (𝟙 a ⊗ₕ «!» (n := a)) ≫ R := by
    calc (R ⊗ₕ ⊸)
        = (𝟙 a ⊗ₕ ⊸) ≫ (R ⊗ₕ 𝟙 (𝕀 : Word O)) := (tensHom_split' _ _).symm
      _ = (𝟙 a ⊗ₕ ⊸) ≫ R := by rw [SymMonCat.tensHom_runit]
  have hun : (R ⊗ₕ «!» (n := a)) ≫ (𝟙 b ⊗ₕ ⟜) ≫ ▷ = (R ⊗ₕ «!» (n := a)) := by
    rw [«∇_unit»]; exact Cat.comp_id _
  dsimp [meet, top]
  calc ◁ ≫ (R ⊗ₕ («!» (n := a) ≫ «?» (n := b))) ≫ ▷
      = ◁ ≫ ((R ⊗ₕ ⊸) ≫ (𝟙 b ⊗ₕ ⟜)) ≫ ▷ := by rw [hR]
    _ = ◁ ≫ (R ⊗ₕ ⊸) ≫ (𝟙 b ⊗ₕ ⟜) ≫ ▷ := by simp only [Cat.assoc]
    _ = ◁ ≫ (R ⊗ₕ ⊸) := by rw [hun]
    _ = ◁ ≫ (𝟙 a ⊗ₕ ⊸) ≫ R := by rw [hsplit]
    _ = (◁ ≫ (𝟙 a ⊗ₕ ⊸)) ≫ R := (Cat.assoc _ _ _).symm
    _ = 𝟙 a ≫ R := by rw [Δ_counit]
    _ = R := Cat.id_comp _

/-- Convolution is monotone in both arguments — immediate from `comp_mono` and `tensHom_mono`, and
    the reason `∩` needs no separate monotonicity axiom. -/
theorem meet_mono {a b : Word O} {R R' S S' : a ⟶ b}
    (hR : R ≤ R') (hS : S ≤ S') :
    (meet R S) ≤ (meet R' S') := by
  dsimp [meet]
  exact OrderedCat.comp_mono (OrderedCat.«≤_refl» _)
    (OrderedCat.comp_mono (SymMonCat.tensHom_mono hR hS) (OrderedCat.«≤_refl» _))

/-- `R ∩ S ≤ R`: the first half of the greatest-lower-bound property
    (functorialSemanticsForRelationalTheories.pdf p. 22).  Weaken the `S` strand all the way to `⊤`
    by `«≤_top»`, then `meet_top` collapses it. -/
theorem «meet_≤_left» {a b : Word O} (R S : a ⟶ b) :
    (meet R S) ≤ R := by
  have h := meet_mono (OrderedCat.«≤_refl» R) («≤_top» S)
  rw [meet_top] at h
  exact h

/-- The meet is symmetric, by cocommutativity (9) on the copy and commutativity (6) on the
    merge, bridged by naturality of the symmetry. -/
theorem meet_comm {a b : Word O} (R S : a ⟶ b) : meet R S = meet S R := by
  dsimp [meet]
  calc ◁ ≫ (R ⊗ₕ S) ≫ ▷
      = (◁ ≫ SymMonCat.swap a a) ≫ (R ⊗ₕ S) ≫ ▷ := by rw [Δ_comm]
    _ = ◁ ≫ (SymMonCat.swap a a ≫ (R ⊗ₕ S)) ≫ ▷ := by simp only [Cat.assoc]
    _ = ◁ ≫ ((S ⊗ₕ R) ≫ SymMonCat.swap b b) ≫ ▷ := by rw [← SymMonCat.swap_nat]
    _ = ◁ ≫ (S ⊗ₕ R) ≫ SymMonCat.swap b b ≫ ▷ := by simp only [Cat.assoc]
    _ = ◁ ≫ (S ⊗ₕ R) ≫ ▷ := by rw [«∇_comm»]

/-- `(R ∩ S) ∩ T` with the left-leaning copy and merge trees exposed, ready for (8) and (6). -/
theorem meet_left_staged {a b : Word O} (R S T : a ⟶ b) :
    meet (meet R S) T
      = ◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (▷ ⊗ₕ 𝟙 b) ≫ ▷ := by
  dsimp [meet]
  have hsplit : ((◁ ≫ (R ⊗ₕ S) ≫ ▷) ⊗ₕ T)
      = (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (▷ ⊗ₕ 𝟙 b) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  rw [hsplit]
  simp only [Cat.assoc]

/-- The mirror staging for `R ∩ (S ∩ T)`, right-leaning. -/
theorem meet_right_staged {a b : Word O} (R S T : a ⟶ b) :
    meet R (meet S T)
      = ◁ ≫ (𝟙 a ⊗ₕ ◁) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ ▷) ≫ ▷ := by
  dsimp [meet]
  have hsplit : (R ⊗ₕ (◁ ≫ (S ⊗ₕ T) ≫ ▷))
      = (𝟙 a ⊗ₕ ◁) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ ▷) := by
    rw [← SymMonCat.tensHom_comp, ← SymMonCat.tensHom_comp]
    simp only [Cat.id_comp, Cat.comp_id]
  rw [hsplit]
  simp only [Cat.assoc]

/-- `R ∩ S ≤ S`, the other half of the greatest-lower-bound property. -/
theorem «meet_≤_right» {a b : Word O} (R S : a ⟶ b) :
    (meet R S) ≤ S := by
  rw [meet_comm]
  exact «meet_≤_left» S R

/-- `(R ∩ S) ∩ T = R ∩ (S ∩ T)` — Freyd's `inter_assoc` (§2.11), derived.  Both staged forms are
    normalised to `◁;(𝟙 ⊗ ◁);(R ⊗ (S ⊗ T));(𝟙 ⊗ ▷);▷`: coassociativity (8) turns the left copy tree
    into the right one, associativity (6) does the same for the merge tree, and strict associativity
    re-brackets `(R ⊗ S) ⊗ T` in between.  In the non-strict tower that middle step is an insertion
    of `α α⁻¹ = 𝟙` followed by `tensAssocInv_nat`. -/
theorem meet_assoc {a b : Word O} (R S T : a ⟶ b) :
    meet (meet R S) T = meet R (meet S T) := by
  rw [meet_left_staged, meet_right_staged]
  calc ◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (▷ ⊗ₕ 𝟙 b) ≫ ▷
      = (◁ ≫ (◁ ⊗ₕ 𝟙 a)) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (▷ ⊗ₕ 𝟙 b) ≫ ▷ := (Cat.assoc _ _ _).symm
    _ = (◁ ≫ (𝟙 a ⊗ₕ ◁)) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (▷ ⊗ₕ 𝟙 b) ≫ ▷ := by rw [Δ_assoc]
    _ = ◁ ≫ (𝟙 a ⊗ₕ ◁) ≫ ((R ⊗ₕ S) ⊗ₕ T) ≫ (▷ ⊗ₕ 𝟙 b) ≫ ▷ := Cat.assoc _ _ _
    _ = ◁ ≫ (𝟙 a ⊗ₕ ◁) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (▷ ⊗ₕ 𝟙 b) ≫ ▷ := by
        rw [SymMonCat.tensHom_assoc]
    _ = ◁ ≫ (𝟙 a ⊗ₕ ◁) ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ ▷) ≫ ▷ := by rw [«∇_assoc»]

/-- `R ∩ R = R` — Freyd's `inter_idem` (§2.11), derived.  `≤` is the glb property; `≥` is exactly
    where the lax inequation (42) and the special law meet: copying `R` and running it on both
    strands can only produce more than running it once, and `◁;▷ = 𝟙` closes the loop. -/
theorem meet_idem {a b : Word O} (R : a ⟶ b) : meet R R = R := by
  refine OrderedCat.«≤_antisymm» («meet_≤_left» R R) ?_
  -- A `calc`, not a `rw` between two `have`s: this is the one law of Lemma 4.11 the paper proves in
  -- pictures, so the chain has to survive into `diag-export --proof` — and a `calc` keeps each link
  -- at its true relation, which shows that only the middle one is an inequality.
  calc R = (R ≫ ◁) ≫ ▷ := by rw [Cat.assoc, special, Cat.comp_id]
    _ ≤ (◁ ≫ (R ⊗ₕ R)) ≫ ▷ := OrderedCat.comp_mono (lax_Δ R) (OrderedCat.«≤_refl» (▷))
    _ = meet R R := by dsimp [meet]; rw [Cat.assoc]

/-- `∩` is the GREATEST lower bound: anything below both `S` and `T` is below `S ∩ T`
    (functorialSemanticsForRelationalTheories.pdf p. 22, "every hom-set is a meet semi-lattice").
    With `«meet_≤_left»`/`«meet_≤_right»` this completes the semilattice statement.
    Idempotency is what does the work — `R = R ∩ R ≤ S ∩ T`. -/
theorem meet_glb {a b : Word O} {R S T : a ⟶ b}
    (hS : R ≤ S) (hT : R ≤ T) :
    R ≤ (meet S T) := by
  have h := meet_mono hS hT
  rw [meet_idem] at h
  exact h

/-- `X ≤ Y` iff `X ∩ Y = X`.  This is the bridge between `diag`'s PRIMITIVE hom order and Freyd's
    DERIVED one (`Freyd/S2_10.lean`, where `R ⊑ S` is *defined* as `R ∩ S = R`), and it is what
    turns the `≤` forms of semi-distributivity and modularity into the equalities the `Allegory`
    class asks for. -/
theorem «meet_eq_left_of_≤» {a b : Word O} {X Y : a ⟶ b} (h : X ≤ Y) :
    meet X Y = X :=
  OrderedCat.«≤_antisymm» («meet_≤_left» X Y) (meet_glb (OrderedCat.«≤_refl» X) h)

/-- `(R ∩ S)° = R° ∩ S°` — Freyd's `recip_inter` (§2.11).

    NOT proved through Lemma 4.2 (iii) (`(R ⊗ S)° = R° ⊗ S°`), which would need the Frobenius
    structure at the COMPOSITE object `a ⊗ b` — the clause of Carboni & Walters' definition that
    `functorialSemanticsForRelationalTheories.pdf` Def. 4.1 as printed omits (see `diag/CB.lean`'s
    header).  Instead: `∩` is the greatest lower bound, and `°` is an order isomorphism
    (`conv_mono` both ways, `conv_conv`), so it carries greatest lower bounds to greatest lower
    bounds.  This keeps every arrow in the proof at a simple object. -/
theorem conv_inter {a b : Word O} (R S : a ⟶ b) :
    conv (meet R S) = meet (conv R) (conv S) := by
  refine OrderedCat.«≤_antisymm» ?_ ?_
  · exact meet_glb (conv_mono («meet_≤_left» R S))
      (conv_mono («meet_≤_right» R S))
  · -- `(R° ∩ S°)°` is below both `R` and `S`, hence below `R ∩ S`; apply `°` once more.
    have h1 : (conv (meet (conv R) (conv S))) ≤ R := by
      have h := conv_mono («meet_≤_left» (conv R) (conv S))
      rwa [conv_conv] at h
    have h2 : (conv (meet (conv R) (conv S))) ≤ S := by
      have h := conv_mono («meet_≤_right» (conv R) (conv S))
      rwa [conv_conv] at h
    have h3 := conv_mono (meet_glb h1 h2)
    rwa [conv_conv] at h3

/-- `R ≤ R R° R` — Freyd's §2.112.

    Freyd reads it off the modular law: `R ⊆ 1R ∩ R ⊆ (1 ∩ R R°) R ⊆ R R° R`.  In pictures neither
    the modular law nor a meet with `1` is needed, and the whole proof is (40) — a wire is below the
    CUT wire — applied twice.

    `R` is its own THREE-fold meet: three copies of the box between a copy tree and a merge tree.
    Cut the copy tree's stem and the pair it feeds is no longer the input but a `⟜◁`, opened out of
    nothing; cut the merge tree's output and the pair it took is no longer the output but a `▷⊸`,
    closed off.  The three boxes have not moved, and what is now drawn round them is the zig-zag
    `R R° R` (`comp_conv_comp_def`). -/
theorem le_comp_conv_comp {a b : Word O} (R : a ⟶ b) :
    R ≤ (R ≫ conv R ≫ R) := by
  -- `R ∩ R ∩ R = R`, with the copy tree leaning LEFT and the merge tree RIGHT — the two brackets
  -- that put the cut wires next to the strands they close over.
  have hthree : ◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ ▷) ≫ ▷ = R := by
    rw [← «∇_assoc», ← meet_left_staged, meet_idem, meet_idem]
  have hcup : (⟜ ⊗ₕ 𝟙 a) ≫ (◁ ⊗ₕ 𝟙 a) = (cup a ⊗ₕ 𝟙 a) := by
    dsimp only [cup]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  have hcap : (𝟙 b ⊗ₕ ▷) ≫ (𝟙 b ⊗ₕ ⊸) = (𝟙 b ⊗ₕ cap b) := by
    dsimp only [cap]; rw [← SymMonCat.tensHom_comp, Cat.id_comp]
  -- The two cut wires are the only arrows in the chain whose object no neighbour determines:
  -- `⟜`'s is the strand it opens, `⊸`'s the strand it closes.
  calc R = ◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ ▷) ≫ ▷ := hthree.symm
    _ ≤ ((⟜ ⊗ₕ 𝟙 a) ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ ▷) ≫ ▷ : a ⟶ b) :=
        OrderedCat.comp_mono («Δ≤?𝟙» a) (OrderedCat.«≤_refl» _)
    _ ≤ ((⟜ ⊗ₕ 𝟙 a) ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ ▷) ≫ (𝟙 b ⊗ₕ ⊸) :
          a ⟶ b) := by
        refine OrderedCat.comp_mono (OrderedCat.«≤_refl» _) ?_
        refine OrderedCat.comp_mono (OrderedCat.«≤_refl» _) ?_
        refine OrderedCat.comp_mono (OrderedCat.«≤_refl» _) ?_
        exact OrderedCat.comp_mono (OrderedCat.«≤_refl» _) («∇≤𝟙!» b)
    _ = ((cup a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ cap b) : a ⟶ b) := by
        rw [← Cat.assoc, hcup, hcap]
    _ = R ≫ conv R ≫ R := (comp_conv_comp_def R).symm

/-- `R ≤ R R° R` by the OTHER route, reaching the zig-zag from the cap end.

    A SECOND PROOF OF ONE STATEMENT, which is duplication, and it is here for one reason: the note
    contrasts the two, and a picture may only be exported from a declaration.  `le_comp_conv_comp`
    is the canonical one — cite that.

    The two spend different laws.  That one starts from `R ∩ R ∩ R = R` and cuts BOTH trees.  This
    one never mentions `∩`: a copy tree whose last two legs are capped back is a bare wire, so `R`
    may be written with that tree behind it; `lax_Δ` then walks the two copy dots back THROUGH the
    box, which is what makes the three copies; and only the surviving copy tree is cut.  One cut
    instead of two, with `lax_Δ` paying for the other. -/
theorem le_comp_conv_comp_of_lax {a b : Word O} (R : a ⟶ b) :
    R ≤ (R ≫ conv R ≫ R) := by
  -- A copy meeting a cap is a discard: `special` collapses the bubble and `⊸` is what is left.
  have hcapfold : (◁ : b ⟶ b ⊗ b) ≫ cap b = ⊸ := by
    dsimp [cap]; rw [← Cat.assoc, special, Cat.id_comp]
  -- …so the three-legged copy tree with its last two legs capped is the bare wire.
  have hstraight : ◁ ≫ (◁ ⊗ₕ 𝟙 b) ≫ (𝟙 b ⊗ₕ cap b) = 𝟙 b :=
    calc ◁ ≫ (◁ ⊗ₕ 𝟙 b) ≫ (𝟙 b ⊗ₕ cap b)
        = (◁ ≫ (◁ ⊗ₕ 𝟙 b)) ≫ (𝟙 b ⊗ₕ cap b) := (Cat.assoc _ _ _).symm
      _ = (◁ ≫ (𝟙 b ⊗ₕ ◁)) ≫ (𝟙 b ⊗ₕ cap b) := by rw [Δ_assoc]
      _ = ◁ ≫ (𝟙 b ⊗ₕ (◁ ≫ cap b)) := by
          rw [Cat.assoc, ← SymMonCat.tensHom_comp, Cat.comp_id]
      _ = ◁ ≫ (𝟙 b ⊗ₕ ⊸) := by rw [hcapfold]
      _ = 𝟙 b := Δ_counit b
  -- `lax_Δ` twice, once per copy dot: both walk back through the box and it is left behind three
  -- times.
  have hlax : R ≫ ◁ ≫ (◁ ⊗ₕ 𝟙 b) ≤ ◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) :=
    calc R ≫ ◁ ≫ (◁ ⊗ₕ 𝟙 b)
        = (R ≫ ◁) ≫ (◁ ⊗ₕ 𝟙 b) := (Cat.assoc _ _ _).symm
      _ ≤ (◁ ≫ (R ⊗ₕ R)) ≫ (◁ ⊗ₕ 𝟙 b) :=
          OrderedCat.comp_mono (lax_Δ R) (OrderedCat.«≤_refl» _)
      _ = ◁ ≫ ((R ≫ ◁) ⊗ₕ R) := by
          rw [Cat.assoc, ← SymMonCat.tensHom_comp, Cat.comp_id]
      _ ≤ ◁ ≫ ((◁ ≫ (R ⊗ₕ R)) ⊗ₕ (𝟙 a ≫ R)) :=
          OrderedCat.comp_mono (OrderedCat.«≤_refl» _)
            (SymMonCat.tensHom_mono (lax_Δ R)
              (by rw [Cat.id_comp]; exact OrderedCat.«≤_refl» R))
      _ = ◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) := by rw [SymMonCat.tensHom_comp]
  -- THE ONE CUT: what is left of the copy tree becomes the converse frame's own `⟜◁`.
  have hcup : (◁ : a ⟶ a ⊗ a) ≫ (◁ ⊗ₕ 𝟙 a) ≤ (cup a ⊗ₕ 𝟙 a) :=
    calc (◁ : a ⟶ a ⊗ a) ≫ (◁ ⊗ₕ 𝟙 a)
        ≤ (⟜ ⊗ₕ 𝟙 a) ≫ (◁ ⊗ₕ 𝟙 a) :=
          OrderedCat.comp_mono («Δ≤?𝟙» a) (OrderedCat.«≤_refl» _)
      _ = (cup a ⊗ₕ 𝟙 a) := by rw [← SymMonCat.tensHom_comp, Cat.id_comp]; rfl
  calc R = R ≫ 𝟙 b := (Cat.comp_id _).symm
    _ = R ≫ ◁ ≫ (◁ ⊗ₕ 𝟙 b) ≫ (𝟙 b ⊗ₕ cap b) := by rw [hstraight]
    _ = (R ≫ ◁ ≫ (◁ ⊗ₕ 𝟙 b)) ≫ (𝟙 b ⊗ₕ cap b) := by simp only [Cat.assoc]
    _ ≤ (◁ ≫ (◁ ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R)) ≫ (𝟙 b ⊗ₕ cap b) :=
        OrderedCat.comp_mono hlax (OrderedCat.«≤_refl» _)
    _ = (◁ ≫ (◁ ⊗ₕ 𝟙 a)) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ cap b) := by simp only [Cat.assoc]
    _ ≤ (cup a ⊗ₕ 𝟙 a) ≫ ((R ⊗ₕ R) ⊗ₕ R) ≫ (𝟙 b ⊗ₕ cap b) :=
        OrderedCat.comp_mono hcup (OrderedCat.«≤_refl» _)
    _ = R ≫ conv R ≫ R := (comp_conv_comp_def R).symm

/-! ### Every arrow is a lax MONOID homomorphism (p. 22)

  The merge/create mirror of the axioms `lax_Δ` and `lax_!`.  The paper obtains them by bending the
  comonoid pair with the converse — Lemma 4.2 (ii) and (iv) applied to (39), (40).  Both are proved
  here without bending: expand by the unit of the adjunction, duplicate the box with the comonoid
  law, contract by the counit.  Their reverses are `ineq_INJ` and `ineq_SUR` below, which do not
  hold in general.

  NUMBERING: the paper prints these two as (41), (42) (p. 22).  The numbers in `diag/CB.lean`'s
  docstrings come from an earlier printing and run three higher throughout — there (41) names the
  Frobenius law and (42), (43) the two comonoid laws used just below. -/

/-- (41): `▷;R ≤ (R ⊗ R);▷`.  In `Rel`, the left side demands the two INPUTS be equal and runs `R`
    once; the right side runs `R` on each input and demands the two RESULTS be equal.  So the
    reverse is injectivity of `R` (`ineq_INJ`). -/
theorem «lax_∇» {m n : Word O} (R : m ⟶ n) : (▷ ≫ R) ≤ ((R ⊗ₕ R) ≫ ▷) :=
  calc (▷ ≫ R : m ⊗ m ⟶ n)
      = ▷ ≫ R ≫ 𝟙 n := by rw [Cat.comp_id]
    _ ≤ ▷ ≫ R ≫ ◁ ≫ ▷ :=
        OrderedCat.comp_mono (OrderedCat.«≤_refl» _)
          (OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («𝟙≤Δ∇» n))
    _ = (▷ ≫ R ≫ ◁) ≫ ▷ := by simp only [Cat.assoc]
    _ ≤ (▷ ≫ ◁ ≫ (R ⊗ₕ R)) ≫ ▷ :=
        OrderedCat.comp_mono
          (OrderedCat.comp_mono (OrderedCat.«≤_refl» _) (lax_Δ R)) (OrderedCat.«≤_refl» _)
    _ = (▷ ≫ ◁) ≫ (R ⊗ₕ R) ≫ ▷ := by simp only [Cat.assoc]
    _ ≤ 𝟙 (m ⊗ m) ≫ (R ⊗ₕ R) ≫ ▷ :=
        OrderedCat.comp_mono («∇Δ≤𝟙» m) (OrderedCat.«≤_refl» _)
    _ = (R ⊗ₕ R) ≫ ▷ := Cat.id_comp _

/-- (42): `⟜;R ≤ ⟜`.  In `Rel`, the left side is the image of `R` and the right side is everything,
    so the reverse is surjectivity of `R` (`ineq_SUR`).  Same three steps as `«lax_∇»`, one object
    down. -/
theorem lax_? {m n : Word O} (R : m ⟶ n) : (⟜ ≫ R) ≤ (⟜) :=
  calc (⟜ ≫ R : (𝕀 : Word O) ⟶ n)
      = ⟜ ≫ R ≫ 𝟙 n := by rw [Cat.comp_id]
    _ ≤ ⟜ ≫ R ≫ ⊸ ≫ ⟜ :=
        OrderedCat.comp_mono (OrderedCat.«≤_refl» _)
          (OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («𝟙≤!?» n))
    _ = (⟜ ≫ R ≫ ⊸) ≫ ⟜ := by simp only [Cat.assoc]
    _ ≤ (⟜ ≫ ⊸) ≫ ⟜ :=
        OrderedCat.comp_mono
          (OrderedCat.comp_mono (OrderedCat.«≤_refl» _) (lax_! R)) (OrderedCat.«≤_refl» _)
    _ ≤ 𝟙 (𝕀 : Word O) ≫ ⟜ :=
        OrderedCat.comp_mono («?!≤𝟙» m) (OrderedCat.«≤_refl» _)
    _ = ⟜ := Cat.id_comp _

/-! ### Maps (functorialSemanticsForRelationalTheories.pdf pp. 20–21)

  The paper gives the map conditions twice.  (SV)/(TOT)/(INJ)/(SUR) on p. 20 are COMONOID
  conditions; (46)–(49) of Lemma 4.4 are ADJOINT conditions; the lemma says the two agree.

  We take the ADJOINT forms as the definitions, because they are literally Freyd's `Simple` and
  `Entire` (`Freyd/S2_10.lean` §2.13) — so a `diag` map and a book map are the same predicate, with
  no translation layer — and because they are the forms every downstream AOP derivation quotes.
  The comonoid forms are recorded beside them under the paper's own equation labels.

  NOT PROVED: Lemma 4.4 itself, that the two presentations agree.  The paper's proof slides a copy
  dot past a `⊗` of two boxes, which needs the Frobenius structure at a COMPOSITE object — the
  clause of Carboni & Walters' definition that Def. 4.1 as printed omits (see `diag/CB.lean`'s
  header).  Nothing below depends on it: every result here uses only the adjoint forms. -/

/-- (46), SINGLE VALUED: `R°R ≤ 𝟙`.  Freyd's `Simple` (§2.13). -/
def SingleValued {a b : Word O} (R : a ⟶ b) : Prop := (conv R ≫ R) ≤ (𝟙 b)

/-- (47), TOTAL: `𝟙 ≤ RR°`.  Freyd's `Entire` (§2.13). -/
def Total {a b : Word O} (R : a ⟶ b) : Prop := (𝟙 a) ≤ (R ≫ conv R)

/-- (48), INJECTIVE: `RR° ≤ 𝟙`. -/
def Injective {a b : Word O} (R : a ⟶ b) : Prop := (R ≫ conv R) ≤ (𝟙 a)

/-- (49), SURJECTIVE: `𝟙 ≤ R°R`. -/
def Surjective {a b : Word O} (R : a ⟶ b) : Prop := (𝟙 b) ≤ (conv R ≫ R)

/-- A MAP is single valued and total (p. 20) — equivalently, by `lemma_4_8`, an arrow whose
    converse is its right adjoint. -/
def Map {a b : Word O} (R : a ⟶ b) : Prop := SingleValued R ∧ Total R

/-- (SV) as the paper writes it on p. 20: `◁;(R ⊗ R) ≤ R;◁`, the reverse of the lax inequation
    (42).  Recorded for reference; `SingleValued` above is the form everything uses. -/
def ineq_SV {a b : Word O} (R : a ⟶ b) : Prop :=
  (◁ ≫ (R ⊗ₕ R)) ≤ (R ≫ ◁)

/-- (TOT) as the paper writes it: `! ≤ R;!`, the reverse of the lax inequation (43). -/
def ineq_TOT {a b : Word O} (R : a ⟶ b) : Prop := (⊸) ≤ (R ≫ ⊸)

/-- (INJ) as the paper writes it: `(R ⊗ R);▷ ≤ ▷;R`. -/
def ineq_INJ {a b : Word O} (R : a ⟶ b) : Prop :=
  ((R ⊗ₕ R) ≫ ▷) ≤ (▷ ≫ R)

/-- (SUR) as the paper writes it: `? ≤ ?;R`. -/
def ineq_SUR {a b : Word O} (R : a ⟶ b) : Prop := (⟜) ≤ (⟜ ≫ R)

/-- COROLLARY 4.5 (p. 21): two maps ordered by `≤` are EQUAL.  Freyd's `map_order_discrete`
    (§2.133).  Insert the unit of `R` on the left of `S` and cancel with the counit of `S`:
    `S = 𝟙S ≤ (RR°)S = R(R°S) ≤ R(S°S) ≤ R𝟙 = R`. -/
theorem cor_4_5 {a b : Word O} {R S : a ⟶ b} (hR : Map R) (hS : Map S) (h : R ≤ S) :
    R = S := by
  refine OrderedCat.«≤_antisymm» h ?_
  have h1 : (𝟙 a ≫ S) ≤ ((R ≫ conv R) ≫ S) :=
    OrderedCat.comp_mono hR.2 (OrderedCat.«≤_refl» S)
  have h2 : (conv R ≫ S) ≤ (conv S ≫ S) :=
    OrderedCat.comp_mono (conv_mono h) (OrderedCat.«≤_refl» S)
  have h3 : (R ≫ conv R ≫ S) ≤ (R ≫ 𝟙 b) :=
    OrderedCat.comp_mono (OrderedCat.«≤_refl» R) (OrderedCat.«≤_trans» h2 hS.1)
  rw [Cat.id_comp] at h1
  rw [Cat.assoc] at h1
  rw [Cat.comp_id] at h3
  exact OrderedCat.«≤_trans» h1 h3

/-! ### The shunting rules (B&dM 4.19 and 4.20)

  The workhorses of relational program calculation: a map may be moved from one side of a
  containment to the other, at the cost of its converse.  `AOP/A4_2.lean` has both for a bare
  `Allegory` (`map_shunt_right`/`map_shunt_left`); these are the same statements in the DIAGRAMMATIC
  layer, so that `diag-export` has something to draw.  Nothing is assumed that `Map` does not
  already give: `Total f` inserts `f f°` on the way out, `SingleValued f` cancels `f° f` on the way
  back, and the two directions of each rule use exactly one of them each. -/

/-- **B&dM 4.19**, shunting on the RIGHT: for a map `f`, `R f ≤ S` iff `R ≤ S f°`. -/
theorem shunt_right {a b c : Word O} {f : b ⟶ c} (hf : Map f) (R : a ⟶ b) (S : a ⟶ c) :
    (R ≫ f) ≤ S ↔ R ≤ (S ≫ conv f) := by
  constructor
  · intro h
    -- `R = R𝟙 ≤ R(f f°) = (R f) f° ≤ S f°`; only `Total f` is used.
    have h1 : (R ≫ 𝟙 b) ≤ (R ≫ f ≫ conv f) :=
      OrderedCat.comp_mono (OrderedCat.«≤_refl» R) hf.2
    have h2 : ((R ≫ f) ≫ conv f) ≤ (S ≫ conv f) :=
      OrderedCat.comp_mono h (OrderedCat.«≤_refl» (conv f))
    rw [Cat.comp_id] at h1
    rw [Cat.assoc] at h2
    exact OrderedCat.«≤_trans» h1 h2
  · intro h
    -- `R f ≤ (S f°) f = S (f° f) ≤ S𝟙 = S`; only `SingleValued f` is used.
    have h1 : (R ≫ f) ≤ ((S ≫ conv f) ≫ f) :=
      OrderedCat.comp_mono h (OrderedCat.«≤_refl» f)
    have h2 : (S ≫ conv f ≫ f) ≤ (S ≫ 𝟙 c) :=
      OrderedCat.comp_mono (OrderedCat.«≤_refl» S) hf.1
    rw [Cat.assoc] at h1
    rw [Cat.comp_id] at h2
    exact OrderedCat.«≤_trans» h1 h2

/-- **B&dM 4.20**, shunting on the LEFT: for a map `f`, `f° R ≤ S` iff `R ≤ f S`. -/
theorem shunt_left {a b c : Word O} {f : b ⟶ a} (hf : Map f) (R : b ⟶ c) (S : a ⟶ c) :
    (conv f ≫ R) ≤ S ↔ R ≤ (f ≫ S) := by
  constructor
  · intro h
    -- `R = 𝟙R ≤ (f f°) R = f (f° R) ≤ f S`; `Total f` again.
    have h1 : (𝟙 b ≫ R) ≤ ((f ≫ conv f) ≫ R) :=
      OrderedCat.comp_mono hf.2 (OrderedCat.«≤_refl» R)
    have h2 : (f ≫ conv f ≫ R) ≤ (f ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.«≤_refl» f) h
    rw [Cat.id_comp, Cat.assoc] at h1
    exact OrderedCat.«≤_trans» h1 h2
  · intro h
    -- `f° R ≤ f° (f S) = (f° f) S ≤ 𝟙S = S`; `SingleValued f` again.
    have h1 : (conv f ≫ R) ≤ (conv f ≫ f ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.«≤_refl» (conv f)) h
    have h2 : ((conv f ≫ f) ≫ S) ≤ (𝟙 a ≫ S) :=
      OrderedCat.comp_mono hf.1 (OrderedCat.«≤_refl» S)
    rw [← Cat.assoc] at h1
    rw [Cat.id_comp] at h2
    exact OrderedCat.«≤_trans» h1 h2

/-- LEMMA 4.8 (p. 21): a map's RIGHT ADJOINT is its converse — B&dM's shunting rule.

    Being a map IS the adjunction `R ⊣ R°`: `Total` is its unit and `SingleValued` its counit.  So
    any other right adjoint `S` must agree with `R°`, by the standard uniqueness argument run in
    both directions (`S ≤ R°` uses `Total R`, `R° ≤ S` uses `SingleValued R`).

    The paper's converse half — that an arrow WITH a right adjoint is a map — is not proved here:
    its proof is the diagram chase that establishes (SV) and (TOT) in comonoid form, which is
    exactly what Lemma 4.4 needs and what the note above explains is out of reach of Def. 4.1 as
    printed. -/
theorem lemma_4_8 {a b : Word O} {R : a ⟶ b} {S : b ⟶ a} (hR : Map R)
    (hunit : (𝟙 a) ≤ (R ≫ S)) (hcounit : (S ≫ R) ≤ (𝟙 b)) :
    S = conv R := by
  refine OrderedCat.«≤_antisymm» ?_ ?_
  · have h1 : (S ≫ 𝟙 a) ≤ (S ≫ R ≫ conv R) :=
      OrderedCat.comp_mono (OrderedCat.«≤_refl» S) hR.2
    have h2 : ((S ≫ R) ≫ conv R) ≤ (𝟙 b ≫ conv R) :=
      OrderedCat.comp_mono hcounit (OrderedCat.«≤_refl» (conv R))
    rw [Cat.comp_id] at h1
    rw [Cat.assoc, Cat.id_comp] at h2
    exact OrderedCat.«≤_trans» h1 h2
  · have h1 : (conv R ≫ 𝟙 a) ≤ (conv R ≫ R ≫ S) :=
      OrderedCat.comp_mono (OrderedCat.«≤_refl» (conv R)) hunit
    have h2 : ((conv R ≫ R) ≫ S) ≤ (𝟙 b ≫ S) :=
      OrderedCat.comp_mono hR.1 (OrderedCat.«≤_refl» S)
    rw [Cat.comp_id] at h1
    rw [Cat.assoc, Cat.id_comp] at h2
    exact OrderedCat.«≤_trans» h1 h2

end Freyd.Diag
