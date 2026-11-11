# Sorting by selection

B&dM §6.6 "Sorting by selection" (diag/aop/06-recursive.typ:286-344): the specification `perm ordered(≤)` and the
derived program `X ≜ ⦇[nil, select°]⦈°`, on arrays; B&dM's preorder `R`, fixed for the whole of §6.6, is `≤`.

    obj N = 0…9                                   -- the elements

The inputs, each an array `1 ⟶ [N]` written as a literal.

    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    y : 1 ⟶ [N] ≜ {(∗,2 1 2)}                     -- a repeated element
    z : 1 ⟶ [N] ≜ {(∗,5 4 3 2 1)}
    e : 1 ⟶ [N] ≜ nil                             -- the empty array

    ok : α×[α] ⟶ α×[α] ≜ cor(≤/∋)                 -- (a, xs) with a ≤ every element of xs (Lean `ok`)
    select : [α] ⟶ α×[α] ≜ perm cons° ok          -- Lean `selectC`: a::y a permutation of x, a ≤ every element of y

The converse of a fold needs the arrays it folds: `C`, every rearrangement of an input.

    C : [N] ⟶ [N] ≜ ran((x ∪ y ∪ z ∪ e)perm)
    X : [N] ⟶ [N] ≜ (C⦇ran(nil), select°⦈)°       -- 06:316 ⦇[nil, select°]⦈°

    check x perm ordered(≤) = {(∗,1 2 3)}
    check y perm ordered(≤) = {(∗,1 2 2)}
    check z perm ordered(≤) = {(∗,1 2 3 4 5)}
    check e perm ordered(≤) = {(∗,[])}
    check x X = {(∗,1 2 3)}
    check y X = {(∗,1 2 2)}
    check z X = {(∗,1 2 3 4 5)}
    check e X = {(∗,[])}
    check C X ⊑ C perm ordered(≤)                 -- selection_sort, 06:316
    check C X = C perm ordered(≤)
