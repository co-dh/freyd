import LeetQ.Rel.Programs.Prelude

/-! # The maximum segment sum

B&dM Ex 7.40, the maximum segment sum: the note diag/aop/07-optimisation.typ §mss (line 688), Lean AOP/A7_7_MSS.lean
`mss` (:106) and `mss_eq_scan` (:993). The numbers are signed, so a longer segment can sum to less: `oplus` cuts a
negative running sum back to 0, and an all-negative list has the empty segment's 0. -/

namespace LeetQ.Rel.Programs

open LeetQ.Rel.Programs.prelude in
rel_program mss where
    obj N = -10…20                                -- the elements and the sums

    zero : 1 ⟶ N ≜ {(∗,0)}                        -- the note's `zero`

    /- The specification, Lean `mss ≜ Λ(segment sum) est(≥)`. -/

    segment : [α] ⟶ [α] ≜ suffix prefix           -- the note's `segment = suffix prefix`
    mss : [N] ⟶ N ≜ Λ(segment sum)est(≥)

    /- The versions the note's derivation passes through, Lean `mss_eq_scan : mss = ⦇k⦈ π₂ est(≥)`. The note writes ⊕
       as an operator; ⊕ is the sum of relations here, so it is the ordinary definition `oplus`. The note's
       `S ≜ [zero, ⊤zero ∪ plus]` is the fold `⦇ran(zero), ⊤zero ∪ plus⦈` in `fused`: a fold takes its seed and step
       apart, so `S` has no definition of its own. -/

    oplus : N×N ⟶ N ≜ Λ(⊤zero ∪ plus)est(≥)       -- the larger of 0 and a+b; `⊤zero` is the note's `⊸ zero`
    g : [N] ⟶ N ≜ ⦇ran(zero), oplus⦈              -- the note's `g ≜ ⦇[zero,oplus]⦈`
    w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus                 -- the head oplus the value the tail carries

    shape : [N] ⟶ N ≜ Λ(suffix)E(Λ(prefix sum)est(≥))est(≥)               -- the largest over suffixes of the largest prefix sum
    fused : [N] ⟶ N ≜ Λ(suffix)E(Λ(⦇ran(zero), ⊤zero ∪ plus⦈)est(≥))est(≥)   -- `prefix sum` fused into the fold `⦇S⦈`
    greedy : [N] ⟶ N ≜ Λ(suffix)E(g)est(≥)                                -- each suffix keeps the one value `g`

    /- `k ≜ [zero⟨𝟙,Λ(𝟙)⟩, ⟨w,⟨wΛ(𝟙),π₂π₂⟩ cup⟩]` (note :844) is the fold's seed and step below; the step's set is Lean's
       own `Λ(w ∪ π₂π₂∋)` (`k`, :756), an array: the language has no `cup`. -/

    scan : [N] ⟶ N ≜ ⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥)

    /- The arrays over D = {-2,-1,3} of length at most 3: one fold round per element of D, each adding a head or not. -/

    D : N ⟶ N ≜ {(-2,-2),(-1,-1),(3,3)}
    A : [N] ⟶ [N] ≜ ran(Λ(⊤(1,N)D)⦇ran(⊤(1,1)nil), π₂ ∪ (⟨⊤D,π₂⟩cons)⦈)

    check A shape = A mss
    check A fused = A mss
    check A greedy = A mss
    check A scan = A mss

    /- B&dM Ex 7.40: the spec is the linear `scan`, one theorem per step of the note's derivation. The laws with no
       `calc` are owed to Lean: `rel_aop mss` (LeetQ/Aop/Mss.lean) proves them over the book's model (`Int`, cons
       lists, the power object), so `linear` is a theorem about that model, not about the executable `mss.rel.*`; the evidence
       between those two is the `check`s above. -/

    /- The steps' laws. `absorption` is Λ(S)E(R) = Λ(S R), `Eunion` E(R) = E(Λ(R))E(∋), `Ecomp` E(R S) = E(R)E(S),
       `estMap` Λ(f)est(R) = f for a map f and a reflexive R: laws of any relation, each stated at the one instance
       its step uses, because a Rel theorem takes no parameters under `rel_aop` yet. Each keeps the step's left
       context `Λ(suffix)`, because a step rewrites one subterm and a composite put in place is not re-associated. -/

    theorem absorption : Λ(suffix)E(prefix sum) = Λ(suffix prefix sum)
    theorem Eunion : Λ(suffix)E(prefix sum) = Λ(suffix)E(Λ(prefix sum))E(∋)
    theorem estUnion : Λ(suffix)E(Λ(prefix sum))E(∋)est(≥) = Λ(suffix)E(Λ(prefix sum))E(est(≥))est(≥)  -- no set empty
    theorem Ecomp : Λ(suffix)E(Λ(prefix sum))E(est(≥)) = Λ(suffix)E(Λ(prefix sum)est(≥))
    -- the greedy row Λ(⦇S⦈)est(≥) = ⦇Λ(S)est(≥)⦈, with S's seed and step apart
    theorem greedyFold : Λ(⦇ran(zero), ⊤zero ∪ plus⦈)est(≥) = ⦇ran(Λ(zero)est(≥)), Λ(⊤zero ∪ plus)est(≥)⦈
    theorem estMap : Λ(zero)est(≥) = zero

    theorem toShape : mss = shape := calc         -- note `mss-shape`
      _ = Λ(suffix prefix sum)est(≥) := ≜ segment
      _ = Λ(suffix)E(prefix sum)est(≥) := absorption
      _ = Λ(suffix)E(Λ(prefix sum))E(∋)est(≥) := Eunion
      _ = Λ(suffix)E(Λ(prefix sum))E(est(≥))est(≥) := estUnion
      _ = Λ(suffix)E(Λ(prefix sum)est(≥))est(≥) := Ecomp
      _ = shape := ≜ shape
    theorem toFused : shape = fused               -- note `mss-prefix-sum`
    theorem toGreedy : fused = greedy := calc     -- note `mss-mono`, `mss-step`, the greedy row
      _ = Λ(suffix)E(Λ(⦇ran(zero), ⊤zero ∪ plus⦈)est(≥))est(≥) := ≜ fused
      _ = Λ(suffix)E(⦇ran(Λ(zero)est(≥)), Λ(⊤zero ∪ plus)est(≥)⦈)est(≥) := greedyFold
      _ = Λ(suffix)E(⦇ran(zero), Λ(⊤zero ∪ plus)est(≥)⦈)est(≥) := estMap
      _ = Λ(suffix)E(⦇ran(zero), oplus⦈)est(≥) := ≜ oplus
      _ = Λ(suffix)E(g)est(≥) := ≜ g
      _ = greedy := ≜ greedy
    theorem toScan : greedy = scan                -- note `mss-scan`
    theorem linear : mss = scan := calc
      _ = shape := toShape
      _ = fused := toFused
      _ = greedy := toGreedy
      _ = scan := toScan

    /- Inputs: [3,1,4,1,5], [2,0,7], [], [3,-4,2,-1,2], [-2,-1,-3] keyed by a, b, c, d, e. -/

    obj K = {a,b,c,d,e}
    x : K ⟶ [N] ≜ {(a,3 1 4 1 5),(b,2 0 7),(c,[]),(d,3 -4 2 -1 2),(e,-2 -1 -3)}
    check x mss = {(a,14),(b,9),(c,0),(d,3),(e,0)}
    check x scan = {(a,14),(b,9),(c,0),(d,3),(e,0)}

#guard mss.ok

end LeetQ.Rel.Programs
