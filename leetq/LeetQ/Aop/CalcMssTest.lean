import LeetQ.Aop.Calc
import AOP.A7_7_MSS

/-! Stage P0 of `doc/rel-module-design.md` §6: the §6.6 theorem `mss = ⦇k⦈ π₂ est(≥)` with the Rel definitions of
    `Programs/Mss.lean` written by hand as Lean definitions, each one `rel(…)` of its Rel body; P2's `rel_aop` emits
    these, P3's resolver lets `rel(mss)` name them. Binder rule (decision D), one row per thing a body names:

    - an object (`obj N`, a type variable): implicit `{N : RelSet}`;
    - a literal (`zero ≜ {(∗,0)}`) and a def with no AOP reading (`segment`, whose `∋` is on lists): explicit, under
      its Rel name;
    - a builtin with no AOP reading yet (`plus`, P1's table): explicit, under a name the builtin table does not hold;
    - a witness `rel(…)` never writes (a `RelProd`, a `Coproduct`; both structures, so no instance search finds
      them): explicit, found by `Calc.fill` from the context by its type;
    - another def: its definition applied to the same names, here a `let` under the def's own name.

    The book's model is the statement's `let`s: each binder the one RelSet term B&dM means, so the substitution is
    the statement itself and needs no equation. This is a theorem about B&dM's model (`Int`, cons lists, the power
    object), not about the executable `mss.rel.mss`: the evidence between those is still the program's `check`. -/

namespace LeetQ.Rel.Lang.CalcMssTest

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory

/-- `oplus : N×N ⟶ N ≜ Λ(⊤zero ∪ plus)est(≥)`. -/
def oplus {N : RelSet.{0}} (NN : RelProd N N) (zero : dL Unit ⟶ N) (add : NN.p ⟶ N) («≥» : N ⟶ N) : NN.p ⟶ N :=
  rel(Λ(⊤zero ∪ add) est(≥))

/-- `w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus`. -/
def w {N α : RelSet.{0}} (NN : RelProd N N) (Nα : RelProd N α) (NNα : RelProd N Nα.p) (zero : dL Unit ⟶ N)
    (add : NN.p ⟶ N) («≥» : N ⟶ N) : NNα.p ⟶ N :=
  let oplus := oplus NN zero add «≥»; rel((𝟙×π₁) oplus)

/-- `mss : [N] ⟶ N ≜ Λ(segment⦇ran(zero),plus⦈)est(≥)`, the program fold in the book's spelling `⦇[zero,plus]⦈`
    (P1's translation rule). -/
def mss {N : RelSet.{0}} (NN : RelProd N N) (K : Coproduct ((F Unit N.carrier).obj N) (dL Unit) NN.p)
    (zero : dL Unit ⟶ N) (segment : dCL Unit N.carrier ⟶ dCL Unit N.carrier) (add : NN.p ⟶ N) («≥» : N ⟶ N) :
    dCL Unit N.carrier ⟶ N :=
  rel(Λ(segment ⦇[zero,add]⦈) est(≥))

/-! ### The bridges, each over the book's model: the RelSet term a Rel body names is the one `MSS` states -/

/-- `⊤zero = ⊸ zero`: `⊤` into the one-point object discards its argument. -/
theorem top_zero {X : RelSet.{0}} : (topHom X (dL Unit) ≫ MSS.zero : X ⟶ ⟨Int⟩) = graph fun _ => MSS.zeroVal :=
  hom_ext fun x _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), topMor_eq_topHom X (dL Unit) ▸ topMor_apply x (), h⟩⟩

/-- `oplus` over the book's model is `MSS.oplus`. -/
theorem oplus_eq : oplus (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩) MSS.zero MSS.plus MSS.geq = MSS.oplus := by
  unfold oplus; rw [top_zero]; rfl

/-- `w` over the book's model is `MSS.wstep`. -/
theorem w_eq : w (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩) (relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩)) (relProd _ _) MSS.zero MSS.plus MSS.geq
    = MSS.wstep := by
  unfold w; rw [prodMap_eq_rprodMap, oplus_eq]; rfl

/-- **B&dM Ex 7.40 over the book's model**: Rel's `mss` is the scan `⦇k⦈ π₂ est(≥)`, `k` in Rel's spelling. -/
theorem mss_scan :
    let zero := MSS.zero; let add := MSS.plus; let «≥» := MSS.geq; let segment := ListRel.segment (A := Int)
    let NN := relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩; let Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩)
    let NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p
    let K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) NN.p := sumCop _ _
    let L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
    let w := w NN Nα NNα zero add «≥»
    mss NN K zero segment add «≥» = rel(⦇[zero ⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]⦈ π₂ est(≥)) := by
  intro zero add «≥» segment NN Nα NNα K L w
  calc mss NN K zero segment add «≥»
      = rel(Λ(segment ⦇[zero,add]⦈) est(≥)) := rfl                       -- ≜ mss
    _ = MSS.mss := congrArg (fun s => rel(Λ(segment s) est(≥))) ListRel.sum_cata.symm   -- sum = ⦇[zero,plus]⦈
    _ = ⦇MSS.k⦈ ≫ (graph (fun p : Int × (Int → Prop) => p.2) : (⟨Int × (Int → Prop)⟩ : RelSet.{0}) ⟶ P ⟨Int⟩)
          ≫ est(MSS.geq) := MSS.mss_eq_scan
    _ = rel(⦇[zero ⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]⦈ π₂ est(≥)) := by
      -- ≜ k in Rel's spelling: `w = wstep`, `⟨R,S⟩ = rpair R S`, and Rel's left-nested juxtaposition
      simp only [zero, add, «≥», NN, Nα, NNα, w, w_eq, pair_eq_rpair, Cat.assoc]; rfl

#print axioms mss_scan
#print axioms MSS.mss_eq_scan

end LeetQ.Rel.Lang.CalcMssTest
