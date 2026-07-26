/-
  Freyd & Scedrov, *Categories and Allegories* §2.156:
  PARTITION (COMBINATORIAL) REPRESENTATIONS of modular lattices.

  "Let 𝓛 be a modular lattice and suppose that T : 𝓛 → Rel(S) is a representation
   of 𝓛 viewed as an allegory, as described in [2.113, 2.154].  T picks a single
   object X in S and for each R ∈ 𝓛 a binary relation on X.  T(R) is, in fact, an
   equivalence relation: it is reflexive because 0 ⊂ R and T(0) = 1; it is
   symmetric because R = R°; it is transitive because R² = R.

   For each pair R, S ∈ 𝓛, T(R) and T(S) commute (since R and S commute in 𝓛).
   Hence T is a function from 𝓛 to a family of commuting equivalence relations on
   X.  T preserves intersection and, when viewed as a function to the lattice of
   equivalence relations, it preserves ∪ (the smallest equivalence relation that
   contains a pair of commuting equivalence relations is their composition).
   Such a representation of 𝓛 is called a PARTITION REPRESENTATION or a
   COMBINATORIAL REPRESENTATION."

  Everything in that paragraph is proved here ABSTRACTLY, over an arbitrary
  target allegory ℬ in place of Rel(S):

  · `ModularLattice` + `ModularLattice.toModularLOCMonoid` — a modular lattice
    (mult := ⊔, unit := 0) is a modular lattice-ordered commutative monoid, so
    §2.113 (`instAllegoryLMonObj`) turns it into a one-object allegory and a
    representation "as described in [2.113, 2.154]" is an `AllegoryFunctor`
    out of `LMonObj 𝓛`.
  · `rep_reflexive` / `rep_symmetric` / `rep_transitive` / `rep_equivRel` —
    every `T(R)` is an equivalence relation (the three book sentences).
  · `rep_commute` — `T(R)` and `T(S)` commute.
  · `rep_meet` — T preserves intersection.
  · `EquivRel.compOfCommute`, `partition_representation` — the composition of a
    commuting pair of equivalence relations is the SMALLEST equivalence relation
    containing both, so `T(R ⊔ S) = T(R) ≫ T(S)` says T preserves ∪ into the
    lattice of equivalence relations.
  · `equivRel_modular` — the converse fact explaining why 𝓛 must be MODULAR:
    in any allegory the (commuting) equivalence relations satisfy the modular
    law with composition as join.
-/

import Freyd.S2_11
import Freyd.S2_147_MapCat
import Freyd.S2_51

universe v u v₁ v₂ u₁ u₂

namespace Freyd.Alg

/-! ## Modular lattices

  A MODULAR LATTICE with a bottom element `0`: exactly the structure the book
  feeds into §2.113 by taking multiplication `= ⊔` and unit `= 0`.  Field
  orientation mirrors `LOCMonoid` so the instance below is field-by-field. -/

/-- A MODULAR LATTICE with bottom (§2.156): lattice `(⊓, ⊔, 0)` satisfying the
    modular law `c ⩽ a → a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c`, order `a ⩽ b :⇔ a ⊓ b = a`. -/
class ModularLattice (L : Type u) where
  /-- Lattice meet. -/
  meet : L → L → L
  /-- Lattice join. -/
  join : L → L → L
  /-- Bottom element `0`. -/
  bot  : L
  meet_idem  : ∀ a, meet a a = a
  meet_comm  : ∀ a b, meet a b = meet b a
  meet_assoc : ∀ a b c, meet a (meet b c) = meet (meet a b) c
  join_idem  : ∀ a, join a a = a
  join_comm  : ∀ a b, join a b = join b a
  join_assoc : ∀ a b c, join a (join b c) = join (join a b) c
  meet_absorb : ∀ a b, meet a (join a b) = a
  join_absorb : ∀ a b, join a (meet a b) = a
  /-- `0` is the unit for `⊔` — the bottom element. -/
  bot_join : ∀ a, join bot a = a
  /-- MODULAR LAW: `c ⩽ a → a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c` (order `x ⩽ y :⇔ x ⊓ y = x`). -/
  modular : ∀ a b c, meet c a = c → meet a (join b c) = join (meet a b) c

namespace ModularLattice

variable {L : Type u} [ModularLattice L]

/-  Order facts, all phrased equationally (`a ⩽ b` is `meet a b = a`) so they
    plug straight into the `LOCMonoid` fields. -/

theorem le_trans {a b c : L} (hab : meet a b = a) (hbc : meet b c = b) :
    meet a c = a := by
  calc meet a c = meet (meet a b) c := by rw [hab]
    _ = meet a (meet b c) := (meet_assoc a b c).symm
    _ = meet a b := by rw [hbc]
    _ = a := hab

/-- `a ⊓ b ⩽ a`. -/
theorem meet_lb_left (a b : L) : meet (meet a b) a = meet a b := by
  rw [meet_comm (meet a b) a, meet_assoc, meet_idem]

/-- `a ⊓ b ⩽ b`. -/
theorem meet_lb_right (a b : L) : meet (meet a b) b = meet a b := by
  rw [← meet_assoc, meet_idem]

/-- `x ⩽ a → x ⩽ b → x ⩽ a ⊓ b` (the meet is the glb). -/
theorem le_meet {x a b : L} (h1 : meet x a = x) (h2 : meet x b = x) :
    meet x (meet a b) = x := by rw [meet_assoc, h1, h2]

-- `a ⩽ a ⊔ b` IS the absorption law `meet_absorb`, read in the order `x ⩽ y :⇔ x ⊓ y = x`.

/-- `b ⩽ a ⊔ b`. -/
theorem le_join_right (a b : L) : meet b (join a b) = b := by
  rw [join_comm]; exact meet_absorb b a

/-- Order in join form: `a ⩽ b → a ⊔ b = b`. -/
theorem join_eq_of_le {a b : L} (h : meet a b = a) : join a b = b := by
  have h2 : join (meet a b) b = b := by
    rw [meet_comm, join_comm]; exact join_absorb b a
  rw [h] at h2
  exact h2

/-- Order from join form: `a ⊔ b = b → a ⩽ b`. -/
theorem le_of_join_eq {a b : L} (h : join a b = b) : meet a b = a := by
  rw [← h]; exact meet_absorb a b

/-- `a ⩽ c → b ⩽ c → a ⊔ b ⩽ c` (the join is the lub). -/
theorem join_le {a b c : L} (ha : meet a c = a) (hb : meet b c = b) :
    meet (join a b) c = join a b := by
  apply le_of_join_eq
  rw [← join_assoc, join_eq_of_le hb]
  exact join_eq_of_le ha

/-- The join is MONOTONE: `a ⩽ b → a ⊔ c ⩽ b ⊔ c` — the `mul_mono` field. -/
theorem join_mono {a b : L} (h : meet a b = a) (c : L) :
    meet (join a c) (join b c) = join a c :=
  join_le (le_trans h (meet_absorb b c)) (le_join_right b c)

/-- `0 ⩽ a`: the unit of the l-monoid is the bottom of the lattice.  This is the
    book's "reflexive because 0 ⊂ R". -/
theorem bot_le (a : L) : meet bot a = bot := le_of_join_eq (bot_join a)

/-- The l-monoid modular law `(R ⊔ S) ⊓ T ⩽ (R ⊓ (T ⊔ S)) ⊔ S` (recip = id, so
    `T S° = T ⊔ S`), derived from lattice modularity applied at `S ⩽ T ⊔ S`:
    `(R⊔S) ⊓ T ⩽ (T⊔S) ⊓ (R⊔S) = ((T⊔S) ⊓ R) ⊔ S`. -/
theorem lmon_modular (R S T : L) :
    meet (join R S) T
      = meet (meet (join R S) T) (join (meet R (join T S)) S) := by
  have hX : meet (meet (join R S) T) (meet (join T S) (join R S))
      = meet (join R S) T :=
    le_meet (le_trans (meet_lb_right (join R S) T) (meet_absorb T S))
      (meet_lb_left (join R S) T)
  have hmod : meet (join T S) (join R S) = join (meet (join T S) R) S :=
    modular (join T S) R S (le_join_right T S)
  rw [hmod, meet_comm (join T S) R] at hX
  exact hX.symm

/-- **The §2.156 bridge**: a modular lattice with `mult := ⊔`, `unit := 0` is a
    modular lattice-ordered commutative monoid (§2.113), hence `LMonObj L` is a
    one-object allegory — "𝓛 viewed as an allegory". -/
instance toModularLOCMonoid : ModularLOCMonoid L where
  mul := join
  one := bot
  meet := meet
  join := join
  mul_assoc a b c := (join_assoc a b c).symm
  one_mul := bot_join
  mul_one a := by rw [join_comm]; exact bot_join a
  mul_comm := join_comm
  meet_idem := meet_idem
  meet_comm := meet_comm
  meet_assoc := meet_assoc
  join_idem := join_idem
  join_comm := join_comm
  join_assoc := join_assoc
  meet_absorb := meet_absorb
  join_absorb := join_absorb
  mul_mono _ _ c h := join_mono h c
  modular := lmon_modular

end ModularLattice

/-- The construction fires: a modular lattice IS a one-object allegory. -/
example {L : Type u} [ModularLattice L] : Allegory (LMonObj L) := inferInstance

/-! ## Order lemmas for allegories and allegory functors -/

section FunctorPreserves

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
variable (F : AllegoryFunctor 𝒜 ℬ)

/-- Allegory functors preserve reflexivity (`1 ⊑ R` and `map_id`). -/
theorem AllegoryFunctor.map_reflexive {a : 𝒜} {R : a ⟶ a} (h : Reflexive R) :
    Reflexive (F.map R) := by
  have h' : F.map (Cat.id a) ⊑ F.map R := F.mono h
  rwa [F.map_id] at h'

/-- Allegory functors preserve symmetry (`R° ⊑ R` and `map_recip`). -/
theorem AllegoryFunctor.map_symmetric {a : 𝒜} {R : a ⟶ a} (h : Symmetric R) :
    Symmetric (F.map R) := by
  show (F.map R)° ⊑ F.map R
  rw [← F.map_recip]
  exact F.mono h

/-- Allegory functors preserve transitivity (`R ≫ R ⊑ R` and `map_comp`). -/
theorem AllegoryFunctor.map_transitive {a : 𝒜} {R : a ⟶ a} (h : Transitive R) :
    Transitive (F.map R) := by
  show F.map R ≫ F.map R ⊑ F.map R
  rw [← F.map_comp]
  exact F.mono h

/-- Allegory functors carry equivalence relations to equivalence relations. -/
def AllegoryFunctor.mapEquivRel {a : 𝒜} (E : EquivRel a) : EquivRel (F.obj a) :=
  ⟨F.map E.E, F.map_reflexive E.refl, F.map_symmetric E.sym, F.map_transitive E.trans⟩

end FunctorPreserves

/-! ## The one-object allegory `LMonObj M`, hom-level facts -/

/-- The endo-hom-set of the one-object allegory `LMonObj M` — definitionally `M`
    itself; the abbreviation keeps the §2.156 statements readable. -/
abbrev LMonHom (M : Type u) [LOCMonoid M] : Type u :=
  (LMonObj.star : LMonObj M) ⟶ LMonObj.star

section LMonHomFacts

variable {M : Type u} [ModularLOCMonoid M]

/-- Reciprocation on `LMonObj M` is the identity: `R = R°` — the book's reason
    `T(R)` is symmetric. -/
theorem lmon_recip_eq (R : LMonHom M) : R° = R := rfl

/-- Homs of `LMonObj M` commute — the book's "R and S commute in 𝓛". -/
theorem lmon_comp_comm (R S : LMonHom M) : R ≫ S = S ≫ R :=
  LOCMonoid.mul_comm R S

variable {L : Type u} [ModularLattice L]

/-- Over the lattice bridge composition IS the lattice join (`mult := ⊔`). -/
theorem lmon_comp_eq_join (R S : LMonHom L) : R ≫ S = ModularLattice.join R S := rfl

/-- Over the lattice bridge intersection IS the lattice meet. -/
theorem lmon_inter_eq_meet (R S : LMonHom L) : R ∩ S = ModularLattice.meet R S := rfl

/-- Over the lattice bridge the identity IS the bottom `0`. -/
theorem lmon_id_eq_bot : (Cat.id (LMonObj.star : LMonObj L)) = (ModularLattice.bot : L) := rfl

/-- Over the lattice bridge every hom is transitive. -/
theorem lmon_lattice_transitive (R : LMonHom L) : Transitive R :=
  le_of_eq (ModularLattice.join_idem R)

/-- Over the lattice bridge every hom of `LMonObj L` is an equivalence relation. -/
def lmonEquivRel (R : LMonHom L) : EquivRel (LMonObj.star : LMonObj L) :=
  ⟨R, ModularLattice.bot_le R, le_refl R, lmon_lattice_transitive R⟩

end LMonHomFacts

/-! ## §2.156 — every `T(R)` is an equivalence relation, and they commute -/

section Representation

variable {ℬ : Type u₂} [Allegory.{v₂} ℬ]

section GeneralMonoid

variable {M : Type u} [ModularLOCMonoid M] (T : AllegoryFunctor (LMonObj M) ℬ)

/-- §2.156: "it is symmetric because R = R°" — `T(R)° = T(R° ) = T(R)`. -/
theorem rep_symmetric (R : LMonHom M) : (T.map R)° = T.map R := by
  have h := (T.map_recip R).symm
  rw [lmon_recip_eq R] at h
  exact h

/-- §2.156: "it is transitive because R² = R" — general l-monoid form. -/
theorem rep_transitive {R : LMonHom M} (h : R ≫ R = R) :
    T.map R ≫ T.map R = T.map R := by
  rw [← T.map_comp, h]

/-- §2.156: "T(R) and T(S) commute (since R and S commute in 𝓛)". -/
theorem rep_commute (R S : LMonHom M) :
    T.map R ≫ T.map S = T.map S ≫ T.map R := by
  rw [← T.map_comp, ← T.map_comp, lmon_comp_comm]

end GeneralMonoid

variable {L : Type u} [ModularLattice L] (T : AllegoryFunctor (LMonObj L) ℬ)

/-- §2.156: "it is reflexive because 0 ⊂ R and T(0) = 1". -/
theorem rep_reflexive (R : LMonHom L) : Reflexive (T.map R) :=
  T.map_reflexive (ModularLattice.bot_le R)

/-- §2.156: "T(R) is, in fact, an equivalence relation". -/
def rep_equivRel (R : LMonHom L) : EquivRel (T.obj LMonObj.star) :=
  T.mapEquivRel (lmonEquivRel R)

theorem rep_equivRel_carrier (R : LMonHom L) : (rep_equivRel T R).E = T.map R := rfl

/-- §2.156: "T preserves intersection" (this is `map_inter`; over the lattice
    bridge `R ∩ S` is the lattice meet, `lmon_inter_eq_meet`). -/
theorem rep_meet (R S : LMonHom L) : T.map (R ∩ S) = T.map R ∩ T.map S :=
  T.map_inter R S

/-- §2.156: T sends the lattice join to composition (this is `map_comp`; over
    the lattice bridge `R ≫ S` IS `R ⊔ S`, `lmon_comp_eq_join`). -/
theorem rep_join (R S : LMonHom L) : T.map (R ≫ S) = T.map R ≫ T.map S :=
  T.map_comp R S

end Representation

/-! ## Composition is the join in the lattice of equivalence relations

  §2.156: "the smallest equivalence relation that contains a pair of commuting
  equivalence relations is their composition" — abstract, in any allegory. -/

section EquivJoin

variable {𝒜 : Type u} [Allegory 𝒜]

/-- If `S` is reflexive then `R ⊑ R ≫ S` (pad on the right by `1 ⊑ S`). -/
theorem le_comp_of_reflexive_right {x : 𝒜} {R S : x ⟶ x} (h : Reflexive S) :
    R ⊑ R ≫ S := by
  have h1 : R ≫ Cat.id x ⊑ R ≫ S := comp_mono_left R h
  rwa [Cat.comp_id] at h1

/-- If `R` is reflexive then `S ⊑ R ≫ S` (pad on the left by `1 ⊑ R`). -/
theorem le_comp_of_reflexive_left {x : 𝒜} {R S : x ⟶ x} (h : Reflexive R) :
    S ⊑ R ≫ S := by
  have h1 : Cat.id x ≫ S ⊑ R ≫ S := comp_mono_right h S
  rwa [Cat.id_comp] at h1

namespace EquivRel

variable {x : 𝒜}

/-- The intersection of two equivalence relations is an equivalence relation
    (no commutation needed) — so "the lattice of equivalence relations" has
    meets and `rep_meet` lands in it. -/
def inter (E F : EquivRel x) : EquivRel x where
  E := E.E ∩ F.E
  refl := le_inter E.refl F.refl
  sym := by
    show (E.E ∩ F.E)° ⊑ E.E ∩ F.E
    rw [Allegory.recip_inter, E.recip_eq, F.recip_eq]
    exact le_refl _
  trans := by
    show (E.E ∩ F.E) ≫ (E.E ∩ F.E) ⊑ E.E ∩ F.E
    apply le_inter
    · exact le_trans
        (le_trans (comp_mono_right (inter_lb_left E.E F.E) _)
          (comp_mono_left E.E (inter_lb_left E.E F.E)))
        E.trans
    · exact le_trans
        (le_trans (comp_mono_right (inter_lb_right E.E F.E) _)
          (comp_mono_left F.E (inter_lb_right E.E F.E)))
        F.trans

/-- §2.156: the composition of a COMMUTING pair of equivalence relations is an
    equivalence relation.  Reflexive: `1 ⊑ E ≫ F`; symmetric:
    `(EF)° = F°E° = FE = EF`; transitive (idempotent): `(EF)² = E(FE)F = E²F²`. -/
def compOfCommute (E F : EquivRel x) (hcomm : E.E ≫ F.E = F.E ≫ E.E) :
    EquivRel x where
  E := E.E ≫ F.E
  refl := le_trans F.refl (le_comp_of_reflexive_left E.refl)
  sym := by
    show (E.E ≫ F.E)° ⊑ E.E ≫ F.E
    rw [Allegory.recip_comp, E.recip_eq, F.recip_eq, ← hcomm]
    exact le_refl _
  trans := by
    show (E.E ≫ F.E) ≫ (E.E ≫ F.E) ⊑ E.E ≫ F.E
    apply le_of_eq
    calc (E.E ≫ F.E) ≫ (E.E ≫ F.E)
        = E.E ≫ ((F.E ≫ E.E) ≫ F.E) := by
          rw [Cat.assoc, ← Cat.assoc F.E E.E F.E]
      _ = E.E ≫ ((E.E ≫ F.E) ≫ F.E) := by rw [← hcomm]
      _ = (E.E ≫ E.E) ≫ (F.E ≫ F.E) := by
          rw [Cat.assoc E.E F.E F.E, ← Cat.assoc E.E E.E (F.E ≫ F.E)]
      _ = E.E ≫ F.E := by rw [E.idem, F.idem]

/-- Any equivalence relation `G` containing `E` and `F` contains `E ≫ F`
    (`E ≫ F ⊑ G ≫ G = G`) — the "smallest" half of §2.156's join claim. -/
theorem comp_le (E F G : EquivRel x) (hE : E.E ⊑ G.E) (hF : F.E ⊑ G.E) :
    E.E ≫ F.E ⊑ G.E := by
  have h1 : E.E ≫ F.E ⊑ G.E ≫ G.E :=
    le_trans (comp_mono_right hE F.E) (comp_mono_left G.E hF)
  rwa [G.idem] at h1

end EquivRel

end EquivJoin

/-! ## The headline: partition representations -/

section Partition

variable {ℬ : Type u₂} [Allegory.{v₂} ℬ]
variable {L : Type u} [ModularLattice L]

/-- **§2.156, PARTITION REPRESENTATION / COMBINATORIAL REPRESENTATION.**
    A representation `T` of a modular lattice `𝓛` viewed as an allegory
    (an `AllegoryFunctor` out of `LMonObj 𝓛`, cf. §2.113/§2.154) is a function
    from `𝓛` to a family of commuting equivalence relations (`rep_equivRel`,
    `rep_commute`) that preserves intersection (`rep_meet`) and, viewed as a
    function to the lattice of equivalence relations, preserves ∪: `T(R ⊔ S)`
    (note `R ≫ S = R ⊔ S`, `lmon_comp_eq_join`) is `T(R) ≫ T(S)`, which
    contains `T(R)` and `T(S)` and is contained in every equivalence relation
    containing both — the smallest such, i.e. their join among equivalence
    relations. -/
theorem partition_representation (T : AllegoryFunctor (LMonObj L) ℬ)
    (R S : LMonHom L) :
    T.map (R ≫ S) = T.map R ≫ T.map S ∧
    T.map R ⊑ T.map (R ≫ S) ∧
    T.map S ⊑ T.map (R ≫ S) ∧
    ∀ G : EquivRel (T.obj LMonObj.star),
      T.map R ⊑ G.E → T.map S ⊑ G.E → T.map (R ≫ S) ⊑ G.E := by
  refine ⟨T.map_comp R S, ?_, ?_, ?_⟩
  · rw [T.map_comp]
    exact le_comp_of_reflexive_right (rep_reflexive T S)
  · rw [T.map_comp]
    exact le_comp_of_reflexive_left (rep_reflexive T R)
  · intro G hR hS
    rw [T.map_comp]
    exact EquivRel.comp_le (rep_equivRel T R) (rep_equivRel T S) G hR hS

end Partition

/-! ## Converse: why 𝓛 must be modular

  In ANY allegory, equivalence relations with composition as join satisfy the
  modular law: for equivalence relations `E, G` with `G ⊑ E` and any endo `F`,
  `E ∩ (F ≫ G) = (E ∩ F) ≫ G`.  So a sublattice of commuting equivalence
  relations (meet = ∩, join = composition, by `partition_representation`) is
  always MODULAR — a lattice with a partition representation has no choice. -/

section ConverseModular

variable {𝒜 : Type u} [Allegory 𝒜]

/-- The modular law in the lattice of equivalence relations: if `G ⊑ E` then
    `E ∩ (F ≫ G) = (E ∩ F) ≫ G`.  `⊑` is the allegory modular law
    (`modular_le`) plus `E ≫ G ⊑ E ≫ E = E`; `⊒` is monotonicity. -/
theorem equivRel_modular {x : 𝒜} (E G : EquivRel x) (F : x ⟶ x)
    (hGE : G.E ⊑ E.E) :
    E.E ∩ (F ≫ G.E) = (E.E ∩ F) ≫ G.E := by
  have hEG : E.E ≫ G.E ⊑ E.E := by
    have h1 : E.E ≫ G.E ⊑ E.E ≫ E.E := comp_mono_left E.E hGE
    rwa [E.idem] at h1
  apply le_antisymm
  · -- `E ∩ (F ≫ G) ⊑ (E ∩ F) ≫ G`
    have h1 : (F ≫ G.E) ∩ E.E ⊑ (F ∩ (E.E ≫ G.E°)) ≫ G.E := modular_le F G.E E.E
    rw [G.recip_eq] at h1
    have h2 : F ∩ (E.E ≫ G.E) ⊑ E.E ∩ F :=
      le_inter (le_trans (inter_lb_right _ _) hEG) (inter_lb_left _ _)
    have h4 : (F ≫ G.E) ∩ E.E ⊑ (E.E ∩ F) ≫ G.E :=
      le_trans h1 (comp_mono_right h2 G.E)
    rwa [Allegory.inter_comm] at h4
  · -- `(E ∩ F) ≫ G ⊑ E ∩ (F ≫ G)`
    apply le_inter
    · exact le_trans (comp_mono_right (inter_lb_left E.E F) G.E) hEG
    · exact comp_mono_right (inter_lb_right E.E F) G.E

end ConverseModular

end Freyd.Alg
