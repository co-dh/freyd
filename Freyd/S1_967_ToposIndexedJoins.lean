/-
  Freyd & Scedrov, *Categories, Allegories* §1.967 — arbitrary subobject MEETS/JOINS in a topos
  with arbitrary powers (the engine behind §1.967 "powers ⟹ locally complete").

  ## RELOCATED — the engine now lives in `Freyd/S1_95.lean`

  The §1.967 indexed-joins engine — `familyMeet`/`familyMeet_le`/`familyMeet_greatest`,
  `WellPoweredSub`, `extJoin`/`extJoin_upper`/`extJoin_least`, the §1.84 frame law
  `extJoin_invImage_le`, and the two builders `locallyComplete_of_powers_wellPowered`
  (`LocallyComplete`, S1_70) and `hasIndexedSubobjectJoins_of_powers_wellPowered`
  (`HasIndexedSubobjectJoins`, S1_75 KEYSTONE) — was MOVED UP into `Freyd/S1_95.lean`
  (section `IndexedJoinsEngine`, right after `HasArbitraryPowers`).

  Why the move: `ToposIndexedJoins` imports `S1_95` (it needs `HasArbitraryPowers` /
  `LocallySmallTopos`), so the engine could not be called from inside `S1_95`.  Hosting the
  engine in `S1_95` lets `LocallySmallTopos` carry the `WellPoweredSub` witness as a field and
  lets `topos_powers_implies_locally_complete` feed it into
  `locallyComplete_of_powers_wellPowered` — closing the former `Sorry` with no new axioms.

  All those defs are Sorry-free, axioms `propext, Classical.choice, Quot.sound`.  This file is
  kept as a thin re-export so that any downstream `import Freyd.ToposIndexedJoins` keeps working;
  the names are in `namespace Freyd` and resolve from `S1_95`.
-/

module

public import Freyd.S1_95

open Freyd
