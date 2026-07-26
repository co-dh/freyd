/-
  The user's §1.39 blackboard proof that ⟨x,y⟩ is monic, in three forms:

    PART 1  — the two directions of the canonical §1.426 theorem
              `monicPair_iff_monic_pair`, exposed under the Q-sequence vocabulary.

    PART 2  — the same statement as a §1.395 Q-SEQUENCE (the §1.41 *second* monic-pair
              diagram, puncture form) with its satisfaction relation `SatMon` written in the
              faithful ∀/∃ shape — a ∀-bar binding a,b with the HYPOTHESIS panel a≫m=b≫m,
              then an ∃-bar imposing the CONCLUSION panel a=b (∃ over the propositional
              witness that the imposed equation holds — exactly §1.395's "∃ a functor into the
              quotient iff the equation holds").  Proved equivalent to `Monic m` and, for the
              pairing, to `MonicPair x y`.

    PART 2' — the SYNTACTIC Q-sequence as pure data (`monicPairQSeq`), the object the generic
              renderer (`QSeq139Render.lean`) consumes; `satMon_pair_iff_monicPair` records
              that its §1.395 satisfaction is `SatMon`.
-/

import Freyd.S1_42   -- Monic, MonicPair (§1.41); pair, fst, snd, fst_pair, snd_pair (§1.42); monicPair_iff_monic_pair (§1.426)

universe v u

namespace Freyd
namespace QSeq139

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## Part 1 — the canonical §1.426 equivalence -/

/-- §1.41/§1.426: a monic pair makes its pairing monic. -/
theorem monic_of_monicPair [HasBinaryProducts 𝒞] {T A B : 𝒞}
    (x : T ⟶ A) (y : T ⟶ B) (hxy : MonicPair x y) : Monic (pair x y) :=
  (monicPair_iff_monic_pair x y).1 hxy

/-- §1.426, conversely: a monic pairing gives a monic pair. -/
theorem monicPair_of_monic [HasBinaryProducts 𝒞] {T A B : 𝒞}
    (x : T ⟶ A) (y : T ⟶ B) (hm : Monic (pair x y)) : MonicPair x y :=
  (monicPair_iff_monic_pair x y).2 hm

/-! ## Part 2 — the §1.395 satisfaction of the monic Q-sequence (∀/∃ puncture form) -/

/-- §1.395 satisfaction of the two-bar MONIC Q-sequence for `m : T ⟶ P` (the §1.41 second
    diagram).  The `∀`-bar ranges over the parallel pair `a, b : W ⇉ T` constrained by the
    HYPOTHESIS panel `a≫m = b≫m`; the `∃`-bar imposes the CONCLUSION panel `a = b` — written
    as `∃ _ : a = b, True`, i.e. "there exists a functor into the `a=b`-quotient", which is
    inhabited exactly when the equation `a = b` holds (§1.395).  No new object is introduced
    by the `∃`-bar, matching the §1.41 remark that an `!` is safe with no vertex after it. -/
def SatMon {T P : 𝒞} (m : T ⟶ P) : Prop :=
  ∀ {W : 𝒞} (a b : W ⟶ T), a ≫ m = b ≫ m → ∃ _ : a = b, True

/-- **The §1.395 monic Q-sequence is satisfied iff `m` is monic.**  The `∃`-bar over the
    propositional witness of `a = b` collapses to the equation, recovering left-cancellation.
    Constructive. -/
theorem satMon_iff_monic {T P : 𝒞} (m : T ⟶ P) : SatMon m ↔ Monic m := by
  constructor
  · intro h W a b hab; obtain ⟨e, _⟩ := h a b hab; exact e
  · intro hm W a b hab; exact ⟨hm a b hab, trivial⟩

/-- **§1.426, Q-sequence form.**  The §1.395 monic Q-sequence for the pairing `⟨x,y⟩` is
    satisfied iff `x, y` is a monic pair — the diagram provably means the property.  Chains
    `satMon_iff_monic` with the §1.426 theorem `monicPair_iff_monic_pair`. -/
theorem satMon_pair_iff_monicPair [HasBinaryProducts 𝒞] {T A B : 𝒞} (x : T ⟶ A) (y : T ⟶ B) :
    SatMon (pair x y) ↔ MonicPair x y := by
  rw [satMon_iff_monic]; exact (monicPair_iff_monic_pair x y).symm

/-! ## Part 2' — the syntactic Q-sequence as data (input to the generic renderer) -/

/-- A §1.395 quantifier bar (the symbol drawn on the vertical bar). -/
inductive Bar | all | ex
  deriving Repr, DecidableEq

/-- A typed arrow `name : src → tgt` of a panel. -/
structure Arr where
  name : String
  src  : String
  tgt  : String
  deriving Repr, DecidableEq

/-- An equation between two composites, each a path of arrow names (diagram order). -/
structure Eqn where
  lhs : List String
  rhs : List String
  deriving Repr, DecidableEq

/-- A §1.392 panel = a finite-presentation increment: new objects, new arrows, the equations
    it IMPOSES (commuting), and the equations it PUNCTURES (drawn `+`, deliberately not
    imposed). `parallel` lists arrow-name groups to be drawn as straight parallel bundles. -/
structure Panel where
  objs     : List String := []
  arrs     : List Arr := []
  impose   : List Eqn := []
  puncture : List Eqn := []
  parallel : List (List String) := []
  deriving Repr

/-- A §1.395 Q-sequence: a root context panel (no bar) followed by quantifier-barred panels. -/
structure QSeq139 where
  title : String
  root  : Panel
  bars  : List (Bar × Panel)
  deriving Repr

/-- The user's proof as a §1.395 Q-sequence: root presents `m = ⟨x,y⟩ : T → A×B` together with
    the product structure (`l = fst`, `r = snd`, the feet `x, y`, and the pairing equations);
    the `∀`-bar introduces the parallel pair `a, b : W ⇉ T` with the hypothesis `a m = b m` and
    punctures `a = b`; the `∃`-bar imposes `a = b`. -/
def monicPairQSeq : QSeq139 :=
  { title := "⟨x,y⟩ monic — §1.41 monic-pair (puncture) Q-sequence"
    root :=
      { objs := ["T", "AxB", "A", "B"]
        arrs := [ ⟨"m", "T", "AxB"⟩, ⟨"l", "AxB", "A"⟩, ⟨"r", "AxB", "B"⟩,
                  ⟨"x", "T", "A"⟩, ⟨"y", "T", "B"⟩ ]
        impose := [ ⟨["m", "l"], ["x"]⟩, ⟨["m", "r"], ["y"]⟩ ] }   -- ⟨x,y⟩;fst = x, ⟨x,y⟩;snd = y
    bars :=
      [ (.all, { objs := ["W"], arrs := [⟨"a", "W", "T"⟩, ⟨"b", "W", "T"⟩],
                 impose := [⟨["a", "m"], ["b", "m"]⟩],     -- a⟨x,y⟩ = b⟨x,y⟩
                 puncture := [⟨["a"], ["b"]⟩],              -- a = b  (the + mark)
                 parallel := [["a", "b"]] }),
        (.ex,  { impose := [⟨["a"], ["b"]⟩] }) ] }          -- impose a = b (puncture removed)

end QSeq139
end Freyd
