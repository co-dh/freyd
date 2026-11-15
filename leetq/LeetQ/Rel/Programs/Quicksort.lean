import LeetQ.Rel.Programs.Prelude

/-! # Quicksort

B&dM §6.6 "Quicksort" (p.154–156): the specification `perm ordered(≤)` of sorting by selection, derived through the
type `tree A ::= null | fork(tree A, A, tree A)` to `flatten ⦇[nil, split°]⦈°`, an unfold then a fold. The tree is
never built: the program is the least `X` with `X = c (𝟙 + X×𝟙×X) [nil, join]`, on arrays. -/

namespace LeetQ.Rel.Programs

open LeetQ.Rel.Programs.prelude in
rel_program quicksort where
    obj N = 0…9                                   -- the elements

    /- The inputs of sorting by selection, each an array `1 ⟶ [N]` written as a literal. -/

    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    y : 1 ⟶ [N] ≜ {(∗,2 1 2)}                     -- a repeated element
    z : 1 ⟶ [N] ≜ {(∗,5 4 3 2 1)}
    e : 1 ⟶ [N] ≜ nil                             -- the empty array

    join : ([α]×α)×[α] ⟶ [α] ≜ (snoc×𝟙)cat        -- p.154 join(x,a,y) = x ⧺ [a] ⧺ y
    -- p.155 check': (x,a,y) with b ≤ a for every b in x and a ≤ b for every b in y
    check' : ([α]×α)×[α] ⟶ ([α]×α)×[α] ≜ dom(π₁⟨π₂,π₁⟩cor(≥/∋)) ∩ dom(⟨π₁π₂,π₂⟩cor(≤/∋))
    -- p.155 split ⊆ check' join° perm
    split : [α] ⟶ ([α]×α)×[α] ≜ perm join° check'

    /- The coalgebra sends [] to the leaf and a non-empty array to (smaller ones, pivot, the rest). -/

    c : [N] ⟶ 1+(([N]×N)×[N]) ≜ (ran(nil)⊤ inl) ∪ (split inr)
    sort' : [N] ⟶ [N] ≜ refold(c, [nil, join])    -- p.155 X = (nil nil°) ∪ (join (X×id×X) split°)

    /- The arrays sorted in the check: every rearrangement of an input. -/

    C : [N] ⟶ [N] ≜ ran((x ∪ y ∪ z ∪ e)perm)

    check x sort' = {(∗,1 2 3)}
    check y sort' = {(∗,1 2 2)}
    check z sort' = {(∗,1 2 3 4 5)}
    check e sort' = {(∗,[])}
    check C sort' ⊑ C perm ordered(≤)             -- p.154 flatten ⦇[nil, split°]⦈° ⊆ ordered · perm
    check C sort' = C perm ordered(≤)

#guard quicksort.ok

end LeetQ.Rel.Programs
