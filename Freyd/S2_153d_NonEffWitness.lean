/-
  Freyd & Scedrov, *Categories, Allegories* §2.153 — the concrete non-effectiveness
  WITNESS over the recursive modulus system `Krec`.

  `Freyd/S2_153c_ConcreteNonEffective.lean` reduces the §2.153 headline
  `¬ CoversSplit (AsmEffReflection Krec)` to ONE construction:

      ∃ (A : Assembly Krec) (E : BinRel (Assembly Krec) A A),
        EquivalenceRelation E ∧ ¬ IsEffective E

  via `asm_not_effective_of_binRel`.  This file supplies the reusable
  categorical HEART of that construction (the "level bridge"), Sorry-free and generic
  over any cover, plus an honest record of the remaining research-level obligation and a
  correctness caveat that rules out the obvious-but-WRONG witness.

  ## The level bridge (this file, hole-free)

  For ANY cover `x : A → Q` of assemblies and ANY relation `E : A → A` dominated by the
  level `graph x ⊚ (graph x)°` (`RelLe E (level x)`, one half of `IsEffective`), the two
  columns of `E` are identified by `x`:

      `E.colA ≫ x = E.colB ≫ x`      (`level_forward`)

  hence, pointwise, every `E`-realized pair `(E.colA t, E.colB t)` is `x`-identified
  (`effective_xIdentifies`).  This is the exact assembly analogue of the `hxeq` step of
  `Freyd.Rcat.ERel_not_effective` (`S1_572b`), lifted to a stand-alone reusable lemma:
  it is the "necessary condition for effectiveness" that the decider-extraction rests on,
  and it holds with NO recursion, NO cover-splitting, purely from `level_legs_comp`
  (§1.594).  In `R` the reverse step used `cover_split` (covers split ⇒ recursive
  representatives); assemblies over `Krec` are NOT AC, so the reverse step is genuinely
  different (see the caveat below).

  ## The remaining obligation (Layers 2–4) — CLOSED in `S2_153f`, and a CORRECTNESS CAVEAT

  Building the concrete `A`/`E` is the genuine hard core.  A tempting but PROVABLY WRONG
  route is: take `A` with SINGLETON caucuses (`A|ₙ = {n}`, cheap point realizers) and put
  the `Kc`-content only in `E`'s TABLE (the caucus over a glued pair `(2e, 2e+1)` carries a
  halting witness for `e`).  That `E` is EFFECTIVE, so it is NOT a witness:

  * Take `Q = A/ESet`, `x a = [a]`, `Q|ₘ = {[m]}` — a `Krec`-cover.
  * The level `graph x ⊚ (graph x)°` over `(2e, 2e+1)` is inhabited (as an assembly) EXACTLY
    when `x(2e) = x(2e+1)`, i.e. exactly when `e ∈ Kc`.  So the "fill" `level x → E` — which
    must produce `E`'s witness-carrying realizer from the level's cheap realizer — need only
    be DEFINED on the glued pairs `(2e, 2e+1)` with `e ∈ Kc`.  A μ-search for a halting
    witness of `e` is a `PartRec` function that halts EXACTLY on `Kc`; it therefore tracks
    the fill.  Both `RelHom`s are tracked, so `E ≅ level x` and `E` IS effective.

  The lesson (`Tracks` only constrains a modulus on INHABITED caucus indices): a semi-decision
  suffices whenever the "hard" caucus is inhabited only on the `Kc`-pairs.  A correct witness
  must therefore use NON-SINGLETON, `Kc`-driven caucuses on `A` itself, arranged so that the
  level's caucus over a glued pair is inhabited for EVERY `e` (halting or not) — forcing the
  fill modulus to be TOTAL, hence a total `Krec`-decider of `Kc`, contradicting
  `Freyd.Rcat.K_not_recursive`.  The caveat's lesson (put the uniformity burden on the
  caucuses, keep the glued point present for EVERY class) is exactly what the parity witness
  of `Freyd/S2_153f_ParityWitness.lean` implements — but no `Kc`-decider is needed at all:
  over `∇ℕ` a single tracked caucus index must contain the whole kernel (uniformity of
  naming), which the class-bounded caucuses refute directly, over `Krec` AND `allPartial`.

  MATHLIB-FREE.  Composition in DIAGRAM ORDER.
-/
module

public import Freyd.S2_153c_ConcreteNonEffective

open Freyd Freyd.Alg

namespace Freyd.Alg

/-! ## The level bridge: a dominated relation's columns are identified by the cover

  Generic over any morphism `x : A → Q` of assemblies (cover-ness is not even needed for
  the identity itself — only `RelLe E (level x)`).  This is the assembly analogue of the
  `hxeq` calc in `Freyd.Rcat.ERel_not_effective`. -/

/-- **Level bridge (§1.594 for assemblies).**  If a relation `E : A → A` is contained in
    the level `graph x ⊚ (graph x)°` of `x : A → Q`, then `x` equalizes the two columns of
    `E`.  Proof: the containment witness `h : E.src → (level x).src` carries `E`'s columns to
    the level's columns, and `level_legs_comp` collapses the level's columns under `x`. -/
theorem level_forward {A Q : Assembly.{u} Krec} (x : A ⟶ Q)
    (E : BinRel (Assembly.{u} Krec) A A)
    (hle : RelLe E (graph x ⊚ (graph x)°)) : E.colA ≫ x = E.colB ≫ x := by
  obtain ⟨⟨h, hA, hB⟩⟩ := hle
  have hll := level_legs_comp x
  calc E.colA ≫ x
      = (h ≫ (graph x ⊚ (graph x)°).colA) ≫ x := by rw [hA]
    _ = h ≫ ((graph x ⊚ (graph x)°).colA ≫ x) := Cat.assoc _ _ _
    _ = h ≫ ((graph x ⊚ (graph x)°).colB ≫ x) := by rw [hll]
    _ = (h ≫ (graph x ⊚ (graph x)°).colB) ≫ x := (Cat.assoc _ _ _).symm
    _ = E.colB ≫ x := by rw [hB]

/-- Pointwise form of the level bridge: every `E`-realized pair is `x`-identified. -/
theorem level_forward_pt {A Q : Assembly.{u} Krec} (x : A ⟶ Q)
    (E : BinRel (Assembly.{u} Krec) A A)
    (hle : RelLe E (graph x ⊚ (graph x)°)) (t : E.src.X) :
    x.toFun (E.colA.toFun t) = x.toFun (E.colB.toFun t) := by
  have h := level_forward x E hle
  have := congrArg (fun m : E.src ⟶ Q => AsmHom.toFun m t) h
  simpa using this

/-- **Necessary condition for effectiveness.**  If `E` is effective, there is a cover `x`
    of assemblies whose two-column identification agrees with `E`: every `E`-realized pair
    is `x`-identified.  (The converse direction — `x`-identified pairs are `E`-realized — is
    where the assembly argument departs from `R`'s cover-splitting proof; see the module
    docstring.)  Extracts the cover and the forward bridge from `IsEffective`. -/
theorem effective_xIdentifies {A : Assembly.{u} Krec} (E : BinRel (Assembly.{u} Krec) A A)
    (heff : IsEffective E) :
    ∃ (Q : Assembly.{u} Krec) (x : A ⟶ Q), Cover x ∧
      ∀ t : E.src.X, x.toFun (E.colA.toFun t) = x.toFun (E.colB.toFun t) := by
  obtain ⟨_, Q, x, hcov, hEle, _⟩ := heff
  exact ⟨Q, x, hcov, fun t => level_forward_pt x E hEle t⟩

end Freyd.Alg
