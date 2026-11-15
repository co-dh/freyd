import LeetQ.Aop.Calc
import AOP.A7_7_MSS

/-! Stage S2 of `doc/rel-mss-proof-design.md`: the versions of `Programs/Mss.lean` (`mss`, `shape`, `fused`, `greedy`,
    `scan`) written by hand as Lean definitions, each one `rel(…)` of its Rel body, and the four theorems between
    them (`toShape`, `toFused`, `toGreedy`, `toScan`) in the shape `rel_aop` will emit; P2's `rel_aop` emits the
    definitions, P3's resolver lets `rel(mss)` name them. Binder rule (decision D), one row per thing a body names:

    - an object (`obj N`, a type variable): implicit `{A : Type}`, `{α : RelSet}`;
    - a literal (`zero ≜ {(∗,0)}`) and a def with no AOP reading (the prelude's `suffix`, `prefix`): explicit, under
      its Rel name;
    - a builtin: no binder, its `Rel(Set)` reading (`Calc.builtins`: `plus` is `ListRel.plus`, `sum` `ListRel.sum`);
    - a witness `rel(…)` never writes (a `RelProd`, a `Coproduct`; both structures, so no instance search finds
      them): explicit, found by `Calc.fill` from the context by its type; a `let` where a builtin fixes its objects;
    - another def: its definition applied to the same names, a `let` under the def's own name.

    The book's model is each statement's `let`s: every binder the one RelSet term B&dM means, so the substitution
    is the statement itself and needs no equation. These are theorems about B&dM's model (`Int`, cons lists, the
    power object), not about the executable `mss.rel.*`: the evidence between those is still the program's `check`. -/

namespace LeetQ.Rel.Lang.CalcMssTest

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory

variable {A : Type} [Add A] [OfNat A 0]

/-- `segment : [α] ⟶ [α] ≜ suffix prefix`. -/
def segment (suffix «prefix» : dCL Unit A ⟶ dCL Unit A) : dCL Unit A ⟶ dCL Unit A := rel(suffix prefix)

/-- `mss : [N] ⟶ N ≜ Λ(segment sum)est(≥)`. -/
def mss (suffix «prefix» : dCL Unit A ⟶ dCL Unit A) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) : dCL Unit A ⟶ ⟨A⟩ :=
  let segment := segment suffix «prefix»; rel(Λ(segment sum)est(≥))

/-- `oplus : N×N ⟶ N ≜ Λ(⊤zero ∪ plus)est(≥)`. -/
def oplus (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) :
    (⟨A × A⟩ : RelSet.{0}) ⟶ ⟨A⟩ :=
  rel(Λ(⊤zero ∪ plus)est(≥))

/-- `g : [N] ⟶ N ≜ ⦇ran(zero), oplus⦈`. -/
def g (K : Coproduct ((F Unit A).obj ⟨A⟩) (dL Unit) (relProd (⟨A⟩ : RelSet.{0}) ⟨A⟩).p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) : dCL Unit A ⟶ ⟨A⟩ :=
  let oplus := oplus zero «≥»; rel(⦇ran(zero), oplus⦈)

/-- `w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus`. -/
def w {α : RelSet.{0}} (Nα : RelProd ⟨A⟩ α) (NNα : RelProd ⟨A⟩ Nα.p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) : NNα.p ⟶ ⟨A⟩ :=
  let NN := relProd (⟨A⟩ : RelSet.{0}) ⟨A⟩; let oplus := oplus zero «≥»; rel((𝟙×π₁)oplus)

/-- `shape : [N] ⟶ N ≜ Λ(suffix)E(Λ(prefix sum)est(≥))est(≥)`. -/
def shape (suffix «prefix» : dCL Unit A ⟶ dCL Unit A) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) : dCL Unit A ⟶ ⟨A⟩ :=
  rel(Λ(suffix)E(Λ(prefix sum)est(≥))est(≥))

/-- `fused : [N] ⟶ N ≜ Λ(suffix)E(Λ(⦇ran(zero), ⊤zero ∪ plus⦈)est(≥))est(≥)`. -/
def fused (K : Coproduct ((F Unit A).obj ⟨A⟩) (dL Unit) (relProd (⟨A⟩ : RelSet.{0}) ⟨A⟩).p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) (suffix : dCL Unit A ⟶ dCL Unit A) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) :
    dCL Unit A ⟶ ⟨A⟩ :=
  rel(Λ(suffix)E(Λ(⦇ran(zero), ⊤zero ∪ plus⦈)est(≥))est(≥))

/-- `greedy : [N] ⟶ N ≜ Λ(suffix)E(g)est(≥)`. -/
def greedy (K : Coproduct ((F Unit A).obj ⟨A⟩) (dL Unit) (relProd (⟨A⟩ : RelSet.{0}) ⟨A⟩).p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) (suffix : dCL Unit A ⟶ dCL Unit A) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) :
    dCL Unit A ⟶ ⟨A⟩ :=
  let g := g K zero «≥»; rel(Λ(suffix)E(g)est(≥))

/-- `scan : [N] ⟶ N ≜ ⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥)`. -/
def scan (Nα : RelProd (⟨A⟩ : RelSet.{0}) (P ⟨A⟩)) (NNα : RelProd ⟨A⟩ Nα.p)
    (L : Coproduct ((F Unit A).obj Nα.p) (dL Unit) NNα.p)
    (zero : dL Unit ⟶ (⟨A⟩ : RelSet.{0})) («≥» : (⟨A⟩ : RelSet.{0}) ⟶ ⟨A⟩) : dCL Unit A ⟶ ⟨A⟩ :=
  let w := w Nα NNα zero «≥»; rel(⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥))

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

/-- `k`, the algebra of `scan`'s fold in Rel's spelling, over the book's model is `MSS.k`: `w = wstep`,
    `⟨R,S⟩ = rpair R S`, and Rel's left-nested juxtaposition. -/
theorem k_eq :
    let zero := MSS.zero; let «≥» := MSS.geq
    let Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩); let NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p
    let L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
    let w := w Nα NNα zero «≥»
    (rel([zero⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]) : (F Unit Int).obj Nα.p ⟶ Nα.p) = MSS.k := by
  intro zero «≥» Nα NNα L w
  simp only [zero, «≥», Nα, NNα, w, w_eq, pair_eq_rpair, Cat.assoc]; rfl

/-! ### The four theorems between the versions, B&dM Ex 7.40 over the book's model -/

/-- `mss = shape` (note `mss-shape`). -/
theorem toShape :
    let «≥» := MSS.geq; let suffix := ListRel.suffix (A := Int); let «prefix» := ListRel.«prefix» (A := Int)
    mss suffix «prefix» «≥» = shape suffix «prefix» «≥» := by
  intro «≥» suffix «prefix»
  calc mss suffix «prefix» «≥»
      = ((suffix ≫ «prefix») ≫ ListRel.sum)%∋ ≫ est(MSS.geq) := rfl                -- ≜ mss, ≜ segment
    _ = MSS.mss := by rw [← ListRel.segment_eq]; rfl                                 -- segment = suffix prefix
    _ = suffix%∋ ≫ existsImage MSS.mssPre ≫ est(MSS.geq) := MSS.mss_shape            -- mss-shape
    _ = (suffix%∋ ≫ existsImage MSS.mssPre) ≫ est(MSS.geq) := (Cat.assoc _ _ _).symm
    _ = shape suffix «prefix» «≥» := rfl                                             -- ≜ mssPre, ≜ shape

/-- `shape = fused` (note `mss-prefix-sum`). -/
theorem toFused :
    let zero := MSS.zero; let «≥» := MSS.geq; let suffix := ListRel.suffix (A := Int)
    let «prefix» := ListRel.«prefix» (A := Int)
    let K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩).p := sumCop _ _
    shape suffix «prefix» «≥» = fused K zero suffix «≥» := by
  intro zero «≥» suffix «prefix» K
  calc shape suffix «prefix» «≥»
      = (suffix%∋ ≫ existsImage ((«prefix» ≫ ListRel.sum)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := rfl   -- ≜ shape
    _ = (suffix%∋ ≫ existsImage ((cataR MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
      rw [MSS.mss_prefix_sum]                                                                         -- prefix sum = ⦇S⦈
    _ = (suffix%∋ ≫ existsImage ((relCata (I := initial Unit Int) MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
      rw [cataR_eq_relCata]                                                                           -- ⦇S⦈ in RelSet
    _ = fused K zero suffix «≥» := by unfold fused; rw [top_zero]; rfl                              -- ⊤zero = ⊸ zero

/-- `fused = greedy` (note `mss-mono`, `mss-step`, the greedy row). -/
theorem toGreedy :
    let zero := MSS.zero; let «≥» := MSS.geq; let suffix := ListRel.suffix (A := Int)
    let K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩).p := sumCop _ _
    fused K zero suffix «≥» = greedy K zero suffix «≥» := by
  intro zero «≥» suffix K
  calc fused K zero suffix «≥»
      = (suffix%∋ ≫ existsImage ((relCata (I := initial Unit Int) MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
        unfold fused; rw [top_zero]; rfl                                                            -- ⊤zero = ⊸ zero
    _ = (suffix%∋ ≫ existsImage ((cataR MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
      rw [cataR_eq_relCata]                                                                           -- ⦇S⦈ in RelSet
    _ = (suffix%∋ ≫ existsImage (cataR (MSS.Salg%∋ ≫ est(MSS.geq)))) ≫ est(MSS.geq) := by
      rw [MSS.mss_greedy_eq]                                                                          -- Λ(⦇S⦈)est(≥) = ⦇Λ(S)est(≥)⦈
    _ = (suffix%∋ ≫ existsImage (cataR (junc (sumCop _ _) MSS.zero MSS.oplus))) ≫ est(MSS.geq) := by
      rw [MSS.mss_step]                                                                               -- Λ(S)est(≥) = [zero,⊕]
    _ = greedy K zero suffix «≥» := by unfold greedy g; rw [oplus_eq, cataR_eq_relCata]               -- ≜ g, oplus

/-- `greedy = scan` (note `mss-scan`). -/
theorem toScan :
    let zero := MSS.zero; let «≥» := MSS.geq; let suffix := ListRel.suffix (A := Int)
    let K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩).p := sumCop _ _
    let Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩); let NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p
    let L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
    greedy K zero suffix «≥» = scan Nα NNα L zero «≥» := by
  intro zero «≥» suffix K Nα NNα L
  calc greedy K zero suffix «≥»
      = (suffix%∋ ≫ existsImage (cataR (junc (sumCop _ _) MSS.zero MSS.oplus))) ≫ est(MSS.geq) := by
        unfold greedy g; rw [oplus_eq, cataR_eq_relCata]                                              -- ≜ g, oplus
    _ = (⦇MSS.k⦈ ≫ (graph (fun p : Int × (Int → Prop) => p.2) : (⟨Int × (Int → Prop)⟩ : RelSet.{0}) ⟶ P ⟨Int⟩))
          ≫ est(MSS.geq) := by rw [MSS.Kalg_snd_eq]                                                  -- ⦇k⦈π₂ = Λ(suffix)E(g)
    _ = scan Nα NNα L zero «≥» := by rw [← k_eq]; rfl                                                -- ≜ k, ≜ scan

/-- **B&dM Ex 7.40 over the book's model**: `mss = scan`, the four theorems in a row. -/
theorem linear :
    let zero := MSS.zero; let «≥» := MSS.geq; let suffix := ListRel.suffix (A := Int)
    let «prefix» := ListRel.«prefix» (A := Int)
    let Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩); let NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p
    let L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
    mss suffix «prefix» «≥» = scan Nα NNα L zero «≥» :=
  calc _ = _ := toShape
    _ = _ := toFused
    _ = _ := toGreedy
    _ = _ := toScan

#print axioms toShape
#print axioms toFused
#print axioms toGreedy
#print axioms toScan
#print axioms k_eq
#print axioms linear
#print axioms MSS.mss_greedy_eq
#print axioms MSS.mss_eq_scan

end LeetQ.Rel.Lang.CalcMssTest
