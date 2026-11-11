# The maximum segment sum

B&dM Ex 7.40, the maximum segment sum: the note diag/aop/07-optimisation.typ §mss (line 688), Lean AOP/A7_7_MSS.lean
`mss` (:106) and `mss_eq_scan` (:993). The numbers are signed, so a longer segment can sum to less: `oplus` cuts a
negative running sum back to 0, and an all-negative list has the empty segment's 0.

    obj N = -10…20                                -- the elements and the sums

    zero : 1 ⟶ N ≜ {(∗,0)}                        -- the note's `zero`
    ≥ : α ⟶ α ≜ ≤°                                -- the order `est` maximises over

The specification, Lean `mss ≜ Λ(segment sum) est(≥)`.

    segment : [α] ⟶ [α] ≜ tails ∋ inits ∋         -- a prefix of a suffix; the note's `segment = suffix prefix`
    mss : [N] ⟶ N ≜ Λ(segment⦇ran(zero),plus⦈)est(≥)   -- `sum ≜ ⦇[zero,plus]⦈` written in place: `sum` is a builtin's name

The derived program, Lean `mss_eq_scan : mss = ⦇k⦈ π₂ est(≥)`. The note writes ⊕ as an operator; ⊕ is the sum of relations here, so it is the ordinary definition `oplus`.

    oplus : N×N ⟶ N ≜ Λ(⊤zero ∪ plus)est(≥)       -- the larger of 0 and a+b; `⊤zero` is the note's `⊸ zero`
    w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus                 -- the head oplus the value the tail carries

`k ≜ [zero⟨𝟙,Λ(𝟙)⟩, ⟨w,⟨wΛ(𝟙),π₂π₂⟩ cup⟩]` (note :844) is the fold's seed and step below; the step's set is Lean's
own `Λ(w ∪ π₂π₂∋)` (`k`, :756), an array: the language has no `cup`.

The arrays over D = {-2,-1,3} of length at most 3: one fold round per element of D, each adding a head or not.

    D : N ⟶ N ≜ {(-2,-2),(-1,-1),(3,3)}
    A : [N] ⟶ [N] ≜ ran(Λ(⊤(1,N)D)⦇ran(⊤(1,1)nil), π₂ ∪ (⟨⊤D,π₂⟩cons)⦈)

    check A⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥) ⊑ A mss
    check A⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥) = A mss

Inputs: [3,1,4,1,5], [2,0,7], [], [3,-4,2,-1,2], [-2,-1,-3] keyed by a, b, c, d, e.

    obj K = {a,b,c,d,e}
    x : K ⟶ [N] ≜ {(a,3 1 4 1 5),(b,2 0 7),(c,[]),(d,3 -4 2 -1 2),(e,-2 -1 -3)}
    check x mss = {(a,14),(b,9),(c,0),(d,3),(e,0)}
    check x⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥) = {(a,14),(b,9),(c,0),(d,3),(e,0)}
