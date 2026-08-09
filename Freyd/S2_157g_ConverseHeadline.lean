/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 — the LITERAL converse of Desargues,
  assembled.

  §2.157 shows that in the one-object allegory associated (via §2.156) to the height-4 modular
  lattice `𝓛(P)` of a projective plane `P`, the Desargues *Horn sentence* `DesarguesHorn` is
  EXACTLY the plane's theorem of Desargues.  One direction — `DesarguesHorn ⟹ DesarguesND` — is
  `desarguesHorn_implies_desargues` (§2.157b, needs only Desargues' own nine side conditions).

  This file closes the OTHER direction, the literal converse `DesarguesND ⟹ DesarguesHorn`, i.e.
  every lattice-level Horn instance `HornHyp a₁ a₂ b₁ b₂ c₁ c₂ → HornConc …`.  The proof is the
  `latticeHorn_of_families` case tree (§2.157c) on the shape of `H := (a₁⊔a₂)⊓(b₁⊔b₂)`:
    · `H = ⊥`  — `horn_core_disjoint`             (§2.157c, disjoint modular core);
    · `H = pt z` — `hornCenter_famB` (§2.157e)     — the perspective-centre family, the ONLY one
      consuming `DesarguesND` (via `desarguesND_implies_horn_points`);
    · `H = ln A` — `hornLine_famC`  (§2.157f)      — the line degeneracy (`M_κ` core + ⊤-mixed);
    · `H = ⊤`   — `hornTop_famA`   (§2.157d)       — the top degeneracy.
  Together with the forward direction this gives the full equivalence `desarguesND_iff_desarguesHorn`.
-/
module

public import Freyd.S2_157d_HornTop
public import Freyd.S2_157e_HornCenter
public import Freyd.S2_157f_HornLine

universe u

namespace Freyd.Alg

/-- **§2.157, literal converse**: in a projective plane `P` satisfying the (honest ten-point)
    theorem of Desargues, the allegory Horn sentence `DesarguesHorn` holds on `LMonObj (PElem P)`.
    Assembled from the four `H`-shape families via `latticeHorn_of_families`; only the
    perspective-centre family `hornCenter_famB` uses `DesarguesND`. -/
public theorem desarguesND_implies_desarguesHorn {P : ProjectivePlane.{u}} (hDes : P.DesarguesND) :
    DesarguesHorn (LMonObj (PElem P)) :=
  desarguesHorn_of_latticeHorn (fun a₁ a₂ b₁ b₂ c₁ c₂ h =>
    PElem.latticeHorn_of_families (PElem.hornCenter_famB hDes) PElem.hornLine_famC
      PElem.hornTop_famA a₁ a₂ b₁ b₂ c₁ c₂ h)

/-- **§2.157, in full**: on the allegory associated to `𝓛(P)`, the Desargues Horn sentence is
    EQUIVALENT to the plane's theorem of Desargues.  Forward: `desarguesHorn_implies_desargues`
    (§2.157b).  Converse: `desarguesND_implies_desarguesHorn` (the four-family case tree). -/
public theorem desarguesND_iff_desarguesHorn {P : ProjectivePlane.{u}} :
    P.DesarguesND ↔ DesarguesHorn (LMonObj (PElem P)) :=
  ⟨desarguesND_implies_desarguesHorn, desarguesHorn_implies_desargues⟩

end Freyd.Alg
