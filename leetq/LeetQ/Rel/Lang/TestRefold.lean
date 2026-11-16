import LeetQ.Rel.Programs.Prelude

/-! `refold(c, S)`, an unfold by `c` then a fold by `S`, is `μX : c G(X) S` with `G` read off the types of `c` and
    `S`, run bottom-up over the nodes `c` reaches: Party-shaped data (a tree, a chain, a single node, no node), a
    cyclic `c` failing with the fold named, and B&dM's quicksort (p.154–156), whose `c` targets a sum and whose
    source `[N]` has no universe. -/

namespace LeetQ.Rel.Lang.TestRefold

open LeetQ.Rel.Programs.prelude in
rel_program refolds where
    obj E = {a,b,c,d,e,f,g,h,i,m}                 -- a tree under a, a chain g h i, one employee m
    obj N = 0…40
    boss : E ⟶ E ≜ {(b,a),(c,a),(d,b),(e,b),(f,c),(h,g),(i,h)}
    rating : E ⟶ N ≜ {(a,3),(b,7),(c,2),(d,5),(e,1),(f,8),(g,4),(h,5),(i,4),(m,0)}
    kids : E ⟶ [E] ≜ Λ(boss°)
    S : E×[N] ⟶ N ≜ ⟨π₁ rating, π₂ sum⟩ plus      -- the ratings of a subtree, summed
    total : E ⟶ N ≜ refold(⟨𝟙, kids⟩, S)
    totalμ : E ⟶ N ≜ μX : ⟨𝟙, kids F(X)⟩S
    check total = totalμ
    print {(a,a)} total
    print {(g,g)} total
    print {(m,m)} total
    print 𝟘(E,E) total

#guard refolds.ok && refolds.prints == [
  "{(a, a)} total = {(a, 26)}",
  "{(g, g)} total = {(g, 13)}",
  "{(m, m)} total = {(m, 0)}",
  "𝟘(E, E) total = {}"]

open LeetQ.Rel.Programs.prelude in
rel_program refoldCycle where
    obj E = {a,b,m}
    obj N = 0…40
    next : E ⟶ E ≜ {(a,b),(b,a)}                  -- a and b each other's child: c is not well-founded
    S : E×[N] ⟶ N ≜ π₂ sum
    bad : E ⟶ N ≜ refold(⟨𝟙, Λ(next)⟩, S)

#guard refoldCycle.failures.map (·.msg) == ["an op ran out of capacity (its twin's ok bit is false); in bad, or the " ++
  s!"coalgebra c at line {decl_line% refoldCycle + 5}, col 26 reaches a node from itself, so it is not well-founded there"]

open LeetQ.Rel.Programs.prelude in
rel_program quicksort where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    y : 1 ⟶ [N] ≜ {(∗,2 1 2)}
    e : 1 ⟶ [N] ≜ nil
    join : ([α]×α)×[α] ⟶ [α] ≜ (snoc×𝟙)cat
    check' : ([α]×α)×[α] ⟶ ([α]×α)×[α] ≜ dom(π₁⟨π₂,π₁⟩cor(≥/∋)) ∩ dom(⟨π₁π₂,π₂⟩cor(≤/∋))
    split : [α] ⟶ ([α]×α)×[α] ≜ perm cat°(snoc°×𝟙) check'
    c : [N] ⟶ 1+(([N]×N)×[N]) ≜ (ran(nil)⊤ inl) ∪ (split inr)
    sort : [N] ⟶ [N] ≜ refold(c, [nil, join])
    print x sort
    print y sort
    print e sort

#guard quicksort.ok && quicksort.prints == ["x sort = {(∗, 1 2 3)}", "y sort = {(∗, 1 2 2)}", "e sort = {(∗, [])}"]

end LeetQ.Rel.Lang.TestRefold
