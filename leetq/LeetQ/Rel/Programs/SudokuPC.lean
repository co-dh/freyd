import LeetQ.Rel.Programs.CSP

/-! # Sudoku path consistency (AIMA §6.2.3), 4×4

`K : Cell×D ⟶ Cell×D` relates two assignments that can hold together; its diagonal is what is left of each
cell's domain. A pair survives when every cell holds a point between them. Column 0 of `4............1.4`,
after AC: cell 4 ∈ {1,2,3}, cells 8 and 12 ∈ {2,3}:

```
(4,2) {K} (12,z) {K} (8,3)     needs     z ≠ 2  and  z ≠ 3,  z ∈ {2,3}  — no z
```

so `(4,2) {K} (8,3)` goes, `(4,2)` then has no partner at cell 8, and cell 4 loses 2; likewise 3, so cell 4 = 1.
AC keeps 2 there: cells 8 and 12 each support it on their own.

## Montanari's form: one relation per pair of cells

`Rᵢⱼ : D ⟶ D` relates the digits cells `i` and `j` can take together: `x {Rᵢⱼ} y` is `(i,x) {K} (j,y)`, so `K`
packs every `Rᵢⱼ` into one relation. It starts as `cor(Dᵢ) ≠ cor(Dⱼ)` for peers, `Dᵢ × Dⱼ` for other cells, and
`𝟙` on `Dᵢ` for `i = j`; PC shrinks it, after which it is no longer `≠`. One step is
`Rᵢⱼ := Rᵢⱼ ∩ Rᵢₘ Rₘⱼ`, for every `m`. Cells a, b, c of one row, `a, b ∈ {1,2}`, `c ∈ {1,2,3}`:

```
R_ca = {(1,2),(2,1),(3,1),(3,2)}       R_cb = {(1,2),(2,1),(3,1),(3,2)}       R_ba = {(1,2),(2,1)}

1 {R_cb} 2 {R_ba} 1  → (1,1)           2 {R_cb} 1 {R_ba} 2  → (2,2)
3 {R_cb} 1 {R_ba} 2  → (3,2)           3 {R_cb} 2 {R_ba} 1  → (3,1)

R_ca ∩ R_cb R_ba = {(3,1),(3,2)}                    -- m = b: (1,2), (2,1) have no path through b
R_cc ∩ R_ca R_ac = {(1,1),(2,2),(3,3)} ∩ {(3,3)}    -- m = a, R_ac = R_ca° = {(1,3),(2,3)}: c's domain is {3}
```

Montanari loops over `m` outside the formula; `pc` puts `m` in the key, `(u,m) {sup(X) X} v`, and `π₁\` meets
over every `m` at once. -/

namespace LeetQ.Rel.Programs

rel_program sudokupc after csp where
    obj Cell = 0…15                               -- the cell in row r, column k is 4r+k
    obj Unit = 0…11                               -- rows 0…3, columns 4…7, boxes 8…11
    obj D = 1…4

    unit : Cell ⟶ Unit ≜ {(0,0),(0,4),(0,8),(1,0),(1,5),(1,8),(2,0),(2,6),(2,9),(3,0),(3,7),(3,9),(4,1),(4,4),(4,8),(5,1),(5,5),(5,8),(6,1),(6,6),(6,9),(7,1),(7,7),(7,9),(8,2),(8,4),(8,10),(9,2),(9,5),(9,10),(10,2),(10,6),(10,11),(11,2),(11,7),(11,11),(12,3),(12,4),(12,10),(13,3),(13,5),(13,10),(14,3),(14,6),(14,11),(15,3),(15,7),(15,11)}
    g : Cell ⟶ D ≜ {(0,4),(13,1),(15,4)}          -- "4............1.4"

    peer : Cell ⟶ Cell ≜ (unit unit°) ∩ ≠
    s₀ : Cell ⟶ D ≜ g°\𝟙(D)
    s : Cell ⟶ D ≜ AC3(peer, ≠, s₀)

    K₀ : Cell×D ⟶ Cell×D ≜ cor(s₀) ∼((peer×𝟙) ∪ (𝟙×≠)) cor(s₀)       -- live points, not (a peer with the same digit, or the same cell with another digit)
    sup(X : α×β ⟶ α×β) : (α×β)×α ⟶ α×β ≜ π₁X ∩ (π₂π₁°)             -- (u,m) ↦ w: u X w and w lies in cell m
    pc(X : α×β ⟶ α×β) : α×β ⟶ α×β ≜ π₁\(sup(X) X)                  -- u ↦ v: for every m some w in m with u X w X v
    K : Cell×D ⟶ Cell×D ≜ νX : K₀ ∩ pc(X)                           -- the largest X ⊑ K₀ with every pair witnessed at every cell
    s' : Cell ⟶ D ≜ π₁°(K ∩ 𝟙)π₂                                    -- the digits left: the diagonal of K

    check s' ⊑ s                                  -- PC keeps no digit AC drops
    check s = {(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3),(5,2),(5,3),(6,1),(6,2),(6,3),(6,4),(7,1),(7,2),(7,3),(8,2),(8,3),(9,2),(9,3),(9,4),(10,1),(10,2),(10,3),(11,1),(11,2),(11,3),(12,2),(12,3),(13,1),(14,2),(14,3),(15,4)}
    check s' = {(0,4),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(5,2),(5,3),(6,4),(7,2),(7,3),(8,2),(8,3),(9,4),(10,1),(10,2),(10,3),(11,1),(11,2),(11,3),(12,2),(12,3),(13,1),(14,2),(14,3),(15,4)}

#guard sudokupc.ok

end LeetQ.Rel.Programs
