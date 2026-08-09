/-
  Freyd & Scedrov, *Categories and Allegories* §1.913 — COVERS = EPICS.

  "In any cartesian category with a subobject classifier, covers coincide with epics."
  (Book §1.913, the statement just before §1.914.)

  The book's argument: every subobject `A' ↪ A` appears as the equalizer of `χ_{A'}` and
  `(A → 1 → Ω)` (the classifier square is a pullback, hence an equalizer once the right leg
  is the universal point).  Consequently:

    * COVER ⟹ EPIC: a cover is right-cancellable (`cover_epi`, S1_52, needs only finite
      products + pullbacks — independent of the classifier).
    * EPIC ⟹ COVER: an epic `f` that factors `g ≫ m = f` through a monic `m` makes `m`
      epic; an epic monic in a category with a subobject classifier is an isomorphism
      (`epi_mono_is_iso` below), so `m` is iso and `f` is a cover.

  The definitions now live in their canonical book-section module, `Freyd.S1_91`. This
  compatibility module keeps older imports working for the §1.933 route to
  `PullbacksTransferCovers`
  ("covers coincide with epics; any functor with a right adjoint preserves epics").  It is
  mathlib-free and adds no second implementation.
-/

module

public import Freyd.S1_91
