import LeetQ.Rel.Lang.Embed
import LeetQ.Rel.Lang.Eval

/-! # The 0/1 knapsack

B&dM §8.4, the 0/1 knapsack (diag/aop/08-thinning.typ, "The knapsack problem"): among the subsequences of the items
whose total weight is within the capacity, one of greatest total value. -/

namespace LeetQ.Rel.Programs

rel_program knapsack where
    obj N = 0…60                                  -- values, weights and their totals
    obj K = {a,b,c,d}                             -- the instances, each its own items

    /- The items (value, weight); a is the note's run (08-thinning.typ:750), d has two best packings. Λ lists each
       instance's items ascending, so a holds them in the reverse of the note's order. -/

    X : K ⟶ [N×N] ≜ Λ({(a,(6,5)),(a,(5,4)),(a,(4,6)),(a,(3,3)),(b,(7,4)),(b,(2,2)),(b,(9,8)),(c,(1,9)),(d,(5,5)),(d,(5,6)),(d,(5,4))})
    w : N ⟶ N ≜ {(10,10)}                         -- the capacity

    value : [α×β] ⟶ α ≜ F(π₁)sum                  -- value ≜ sum list(val): the total value of a packing
    weight : [α×β] ⟶ β ≜ F(π₂)sum                 -- weight ≜ sum list(wt): its total weight
    within(w : α ⟶ β) : [γ×α] ⟶ [γ×α] ≜ dom(weight ≤ w)   -- the packing weighs at most w
    ≥ : N ⟶ N ≜ ≤°

    /- The orders on packings (knap-defn); [N×N] has no universe, so est, merge and thinL run them on the pairs they
       compare. -/

    R : [N×α] ⟶ [N×β] ≜ value ≥ value°           -- more valuable
    Q : [N×N] ⟶ [N×N] ≜ R ∩ (weight ≤ weight°)    -- more valuable and lighter

    /- The specification, knap_laws' right side: Λ(subseq within(w)) est(R). -/

    s : K ⟶ [N×N] ≜ Λ(X subseq within(w))est(R)

    /- The specification as a fold, knap_spec: subseq within(w) = ⦇[nil, cons within(w) ∪ π₂]⦈; the seed nil of the base
       case is the fold's coreflexive ran(X nil), the item case its step S. -/

    S : (α×N)×[α×N] ⟶ [α×N] ≜ cons within(w) ∪ π₂   -- at each item, keep it if the packing still fits, or drop it
    p : K ⟶ [N×N] ≜ Λ(X⦇ran(X nil),S⦈)est(R)     -- knap_laws_step2's left side: Λ⦇S⦈ est(R)

    /- The derived program, knap_fold (08-thinning.typ:727):

       ```
         ⦇[nil τ, cpr ⟨list(cons) filter(within w), list(π₂)⟩ merge(R) thinL(Q)]⦈ minL(R)
       ```

       cpr(a,ps) = [(a,p) ∣ p ← ps], the fold over ps that pairs each packing with a; its arguments are families (§e), so
       the step passes the item and the packings as ⟨⊤,π₁⟩, ⟨⊤,π₂⟩ and drops the 1 of the result. -/

    cpr(a : 1 ⟶ N×N, ps : 1 ⟶ [[N×N]]) : 1 ⟶ [(N×N)×[N×N]] ≜ ps⦇ran(nil(1)), ⟨⟨⊤ a, π₁⟩, π₂⟩cons⦈
    step : (N×N)×[[N×N]] ⟶ [[N×N]] ≜ cpr(⟨⊤,π₁⟩,⟨⊤,π₂⟩)π₂⟨F(cons)filter(within(w)), F(π₂)⟩merge(R)thinL(Q)
    knap : K ⟶ [N×N] ≜ X⦇ran(X nil τ), step⦈est(R)   -- minL(R) is est(R) on the thinned array

    check X⦇ran(X nil),S⦈ = X subseq within(w)   -- knap_spec
    check p = s                                   -- knap_laws_step2
    check knap ⊑ s                                -- knap_fold: the derived program refines the specification

    check s = {(a,(5,4) (6,5)),(b,(2,2) (9,8)),(c,[(1,9)]),(d,(5,4) (5,5)),(d,(5,4) (5,6))}
    check p = {(a,(5,4) (6,5)),(b,(2,2) (9,8)),(c,[(1,9)]),(d,(5,4) (5,5)),(d,(5,4) (5,6))}
    check knap = {(a,(5,4) (6,5)),(b,(2,2) (9,8)),(c,[(1,9)]),(d,(5,4) (5,5))}

#guard (Lang.runProgram knapsack).isOk

end LeetQ.Rel.Programs
