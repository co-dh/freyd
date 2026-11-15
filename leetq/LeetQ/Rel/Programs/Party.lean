import LeetQ.Rel.Programs.Prelude

/-! # Planning a company party

B&dM §7.3 (diag/aop/07-optimisation.typ, "Planning a company party"): a party is a set of employees with none beside
his boss; `party ≜ fold choose` and `best` picks one of greatest total rating. The efficient version carries the cost
as the relation `c` and recovers the guests with `win` and `guests`. Design: doc/rel-party-design.md. -/

namespace LeetQ.Rel.Programs

open LeetQ.Rel.Programs.prelude in
rel_program partyPlan where
    obj E = {a,b,c,d,e,f,g,h,i,k,l,m}             -- one forest: exStaff a…f, a chain g h i, a tie k l, one employee m
    obj N = 0…40                                  -- ratings and their totals, non-negative

    /- An employee stands for the subtree under him, so every employee is one instance of the check. -/

    boss : E ⟶ E ≜ {(b,a),(c,a),(d,b),(e,b),(f,c),(h,g),(i,h),(l,k)}
    rating : E ⟶ N ≜ {(a,3),(b,7),(c,2),(d,5),(e,1),(f,8),(g,4),(h,5),(i,4),(k,2),(l,2),(m,0)}

    under : E ⟶ E ≜ μX : 𝟙 ∪ (boss° X)           -- e and everyone below e
    leaf : E ⟶ E ≜ 𝟙 − ran(boss)
    kids : E ⟶ [E] ≜ Λ(boss°) ∪ (leaf nil)        -- Λ has no row at a leaf, so [] is added there
    cost(r : α ⟶ β) : [α] ⟶ β ≜ F(r)sum
    R(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≥ cost(r)°

    /- The book's fold ⦇S⦈ (p. 177), written as μ over the array objects [E]. -/

    choose : [E]×[E] ⟶ [E] ≜ π₁ ∪ π₂
    include : E×[[E]×[E]] ⟶ [E] ≜ ⟨π₁τ τ, π₂F(π₂)⟩cat union
    exclude : E×[[E]×[E]] ⟶ [E] ≜ π₂F(choose)union
    S : E×[[E]×[E]] ⟶ [E]×[E] ≜ ⟨include, exclude⟩
    fold : E ⟶ [E]×[E] ≜ μX : ⟨𝟙, kids F(X)⟩S
    party : E ⟶ [E] ≜ fold choose
    best : E ⟶ [E] ≜ Λ(party)est(R(rating))

    -- the sets with no employee beside his boss
    check party = Λ(under)subseq(𝟙 − dom(∋ ∩ (∋ boss)))

    /- The greedy form (p. 178): exclude keeps only the best party of each child. -/

    exclude₁ : E×[[E]×[E]] ⟶ [E] ≜ π₂F(Λ(choose)est(R(rating)))union
    gfold : E ⟶ [E]×[E] ≜ μX : ⟨𝟙, kids F(X)⟩⟨include, exclude₁⟩
    check gfold Λ(choose)est(R(rating)) ⊑ best

    /- The efficient form: c is (cost with e, cost without e), win the employees whose best party holds them, ties
       to include, and guests the party as a relation into E. -/

    c : E ⟶ N×N ≜ μX : ⟨rating + (kids F(X π₂)sum), kids F(X max)sum⟩
    win : E ⟶ E ≜ dom((c π₁ ≥) ∩ (c π₂))
    guests : E ⟶ E ≜ μX : win(𝟙 ∪ (boss° boss° X)) ∪ ((𝟙 − win)boss° X)
    check Λ(guests) ⊑ best
    check c max = best cost(rating)
    root : E ⟶ E ≜ {(a,a)}
    check root best = {(a,a d e f)}
    check root c max = {(a,17)}

#guard partyPlan.ok

end LeetQ.Rel.Programs
