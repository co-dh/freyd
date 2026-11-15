import LeetQ.Aop.Calc
import AOP.A7_7_MSS

/-! Stage P0 of `doc/rel-module-design.md` §6: the §6.6 theorem `mss = ⦇k⦈ π₂ est(≥)` with the Rel definitions of
    `Programs/Mss.lean` written by hand as Lean definitions, each one `rel(…)` of its Rel body; P2's `rel_aop` emits
    these, P3's resolver lets `rel(mss)` name them. Binder rule (decision D), one row per thing a body names:

    - an object (`obj N`, a type variable): implicit `{N : RelSet}`;
    - a literal (`zero ≜ {(∗,0)}`) and a def with no AOP reading (`segment`, whose `∋` is on lists): explicit, under
      its Rel name;
    - a builtin: no binder, its `Rel(Set)` reading (`Calc.builtins`: `plus` is `ListRel.plus`), which fixes the
      objects it touches to `⟨A⟩`, `⟨A × A⟩`;
    - a witness `rel(…)` never writes (a `RelProd`, a `Coproduct`; both structures, so no instance search finds
      them): explicit, found by `Calc.fill` from the context by its type; a `let` where a builtin fixes its objects;
    - another def: its definition applied to the same names, here a `let` under the def's own name.

    The book's model is the statement's `let`s: each binder the one RelSet term B&dM means, so the substitution is
    the statement itself and needs no equation. This is a theorem about B&dM's model (`Int`, cons lists, the power
    object), not about the executable `mss.rel.mss`: the evidence between those is still the program's `check`. -/

namespace LeetQ.Rel.Lang.CalcMssTest

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory

/-- `oplus : N×N ⟶ N ≜ Λ(⊤zero ∪ plus)est(≥)`. -/
def oplus {A : Type} [Add A] (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) :
    (⟨A × A⟩ : RelSet.{0}) ⟶ ⟨A⟩ :=
  rel(Λ(⊤zero ∪ plus) est(≥))

/-- `w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus`. -/
def w {A : Type} [Add A] {α : RelSet.{0}} (Nα : RelProd ⟨A⟩ α) (NNα : RelProd ⟨A⟩ Nα.p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) : NNα.p ⟶ ⟨A⟩ :=
  let NN := relProd (⟨A⟩ : RelSet.{0}) ⟨A⟩; let oplus := oplus zero «≥»; rel((𝟙×π₁) oplus)

/-- `mss : [N] ⟶ N ≜ Λ(segment⦇ran(zero),plus⦈)est(≥)`, Rel's own body: the program fold reads as `⦇[zero,plus]⦈`. -/
def mss {A : Type} [Add A] (K : Coproduct ((F Unit A).obj ⟨A⟩) (dL Unit) (relProd (⟨A⟩ : RelSet.{0}) ⟨A⟩).p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) (segment : dCL Unit A ⟶ dCL Unit A) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) :
    dCL Unit A ⟶ ⟨A⟩ :=
  rel(Λ(segment ⦇ran(zero),plus⦈) est(≥))

/-! ### The bridges, each over the book's model: the RelSet term a Rel body names is the one `MSS` states -/

/-- `⊤zero = ⊸ zero`: `⊤` into the one-point object discards its argument. -/
theorem top_zero {X : RelSet.{0}} : (topHom X (dL Unit) ≫ MSS.zero : X ⟶ ⟨Int⟩) = graph fun _ => MSS.zeroVal :=
  hom_ext fun x _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), topMor_eq_topHom X (dL Unit) ▸ topMor_apply x (), h⟩⟩

/-- `oplus` over the book's model is `MSS.oplus`. -/
theorem oplus_eq : oplus MSS.zero MSS.geq = MSS.oplus := by
  unfold oplus; rw [top_zero]; rfl

/-- `w` over the book's model is `MSS.wstep`. -/
theorem w_eq : w (relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩)) (relProd _ _) MSS.zero MSS.geq = MSS.wstep := by
  unfold w; dsimp only; rw [prodMap_eq_rprodMap, oplus_eq]; rfl

/-- **B&dM Ex 7.40 over the book's model**: Rel's `mss` is the scan `⦇k⦈ π₂ est(≥)`, `k` in Rel's spelling. -/
theorem mss_scan :
    let zero := MSS.zero; let «≥» := MSS.geq; let segment := ListRel.segment (A := Int)
    let NN := relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩; let Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩)
    let NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p
    let K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) NN.p := sumCop _ _
    let L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
    let w := w Nα NNα zero «≥»
    mss K zero segment «≥» = rel(⦇[zero ⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]⦈ π₂ est(≥)) := by
  intro zero «≥» segment NN Nα NNα K L w
  calc mss K zero segment «≥»
      = rel(Λ(segment ⦇[zero,plus]⦈) est(≥)) := rfl                      -- ≜ mss
    _ = MSS.mss := congrArg (fun s => rel(Λ(segment s) est(≥))) ListRel.sum_cata.symm   -- sum = ⦇[zero,plus]⦈
    _ = ⦇MSS.k⦈ ≫ (graph (fun p : Int × (Int → Prop) => p.2) : (⟨Int × (Int → Prop)⟩ : RelSet.{0}) ⟶ P ⟨Int⟩)
          ≫ est(MSS.geq) := MSS.mss_eq_scan
    _ = rel(⦇[zero ⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]⦈ π₂ est(≥)) := by
      -- ≜ k in Rel's spelling: `w = wstep`, `⟨R,S⟩ = rpair R S`, and Rel's left-nested juxtaposition
      simp only [zero, «≥», Nα, NNα, w, w_eq, pair_eq_rpair, Cat.assoc]; rfl

#print axioms mss_scan
#print axioms MSS.mss_eq_scan

end LeetQ.Rel.Lang.CalcMssTest
