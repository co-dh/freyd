import LeetQ.Rel.Lang.Embed

/-! # The blocks world -/

namespace LeetQ.Rel.Programs

rel_program blocks where
    obj X = {A,B,C}                               -- the blocks
    obj N = 0…27                                  -- counts: a bound fixed before the search
    obj St = 𝒫(X×X)                               -- a state: the set of its pairs
    S₀ : X ⟶ X ≜ {(C,A),(A,A),(B,B)}              -- C on A, A and B on the table
    G : X ⟶ X ≜ {(A,B),(B,C)}                     -- A on B, B on C

    R(S : X ⟶ X) : X ⟶ X ≜ S ∩ ∼𝟙                 -- b rests on another block
    M(S : X ⟶ X) : X ⟶ X ≜ ∼(R(S)°⊤ ∪ (⊤R(S)))    -- the moves allowed
    S'(S : X ⟶ X, p : X ⟶ X) : X ⟶ X ≜ (S ∩ ∼(p⊤)) ∪ p   -- the state after the move p
    h(S : X ⟶ X) ≜ G ⊑ S                          -- S holds the goal

    c : [X×X] ⟶ [X×X]×(X×X) ≜ ⟨𝟙,M(∋)⟩            -- a state, each move it allows
    ⇝ : [X×X]×(X×X) ⟶ X×X ≜ S'(π₁∋,π₂)            -- the pairs it leads to
    t : [X×X] ⟶ [X×X] ≜ cΛ(⇝)                     -- one move
    s₀ : [X×X] ⟶ [X×X] ≜ ran(Λ(⊤(X,X)⟨𝟙,S₀⟩))     -- the start state
    r : [X×X] ⟶ [N] ≜ Λ(s₀⊤)                      -- the array 0…27, one fold round each
    L(D : α ⟶ β, B : β ⟶ β) : β×N ⟶ β×N ≜ ran(r⦇ran⟨D,D⊤{(0,0)}⟩, π₂ ∪ (π₂⟨π₁B,π₂ succ⟩)⦈)   -- (s,k): s is k steps of B from D
    Q : [X×X] ⟶ [X×X] ≜ ran(L(s₀,t)π₁)            -- the reachable states
    H : [X×X] ⟶ [X×X] ≜ Qh(∋)                     -- the reachable states holding G
    C : [X×X]×N ⟶ [X×X]×N ≜ L(H,(Qt)°)            -- each state with each walk length to H
    W : [X×X] ⟶ N ≜ (Cπ₁)°(Cπ₂)
    δ : [X×X] ⟶ N ≜ Λ(W)est(≤)                    -- the distance to the goal
    K : [X×X] ⟶ [X×X]×(X×X) ≜ Qc dom(Λ(⇝)δ succ ∩ (π₁δ))   -- the moves that take the distance down by one
    ≼ : α×β ⟶ α×β ≜ π₁ < π₁° ∪ (π₁π₁° ∩ (π₂ ≤ π₂°))   -- moves in lexicographic order
    σ : [X×X] ⟶ X×X ≜ Λ(Kπ₂)est(≼)                -- the move chosen in each state
    ν : [X×X] ⟶ [X×X] ≜ ⟨dom(σ),σ⟩Λ(⇝)            -- the state it leads to
    Z : [X×X]×N ⟶ [X×X]×N ≜ L(s₀,ν)               -- the chosen path, with each state's step
    ζ : N ⟶ [X×X] ≜ (Zπ₂)°(Zπ₁)                   -- the k-th state
    plan : N ⟶ X×X ≜ ζσ                           -- the k-th move

    check plan = {(0,(C,C)),(1,(B,C)),(2,(A,B))}  -- C to the table, B onto C, A onto B

#guard (Lang.runProgram blocks).isOk

end LeetQ.Rel.Programs
