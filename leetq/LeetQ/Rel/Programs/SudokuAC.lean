import LeetQ.Rel.Lang.Embed
import LeetQ.Rel.Lang.Eval

/-! # Sudoku arc consistency (AIMA §6.2.2)

A state is `s : Cell ⟶ D`, each cell related to the digits still possible for it. A cell's peers are the 20
other cells in its row, column and box.

## The start: `s₀ ≜ g°\𝟙`

`s₀` is the largest `s` with `g° s ⊑ 𝟙`. Cell 0 is given 5:

```
5 {g°} 0 {s} d     must imply     5 {𝟙} d,  i.e.  d = 5
```

Cell 2 is given nothing, so no path starts with `{g°} 2` and `s₀` holds all of 1…9 there, with no complement
needed to name the empty cells.

## One round of AC-3: `rev(s) ≜ s ∩ (peer\(s ≠))`

`peer\(s ≠)` is the largest `X` with `peer X ⊑ s ≠`. Take cell 2 and its peer cell 0 under `s₀`:

```
0 {peer} 2 {X} d     must imply     0 {s₀} 5 {≠} d,  i.e.  d ∈ {1,2,3,4,6,7,8,9}
```

so `X` may not hold 5 at cell 2. Each peer of cell 2 adds such a bound:

| peer c′ | `s₀` at c′ | bound on `X` at cell 2 |
|---------|------------|------------------------|
| 0       | {5}        | ≠ 5                    |
| 1       | {3}        | ≠ 3                    |
| 4       | {7}        | ≠ 7                    |
| 9       | {6}        | ≠ 6                    |
| 19      | {9}        | ≠ 9                    |
| 20      | {8}        | ≠ 8                    |
| empty   | 1…9        | none                   |

The largest `X` holds {1,2,4} at cell 2, and `s₁ = rev(s₀)` keeps those digits of `s₀`. A second round
`s₂ = rev(s₁)` sees cells newly forced by `s₁`: cell 62 is forced to 4, so its column peer cell 8 loses 4. -/

namespace LeetQ.Rel.Programs

rel_program sudokuac after prelude where
    obj Cell = 0…80                               -- the cell in row r, column k is 9r+k
    obj Unit = 0…26                               -- rows 0…8, columns 9…17, boxes 18…26
    obj D = 1…9

    /- The data: which units each cell lies in, and the givens. -/

    unit : Cell ⟶ Unit ≜ {(0,0),(0,9),(0,18),(1,0),(1,10),(1,18),(2,0),(2,11),(2,18),(3,0),(3,12),(3,19),(4,0),(4,13),(4,19),(5,0),(5,14),(5,19),(6,0),(6,15),(6,20),(7,0),(7,16),(7,20),(8,0),(8,17),(8,20),(9,1),(9,9),(9,18),(10,1),(10,10),(10,18),(11,1),(11,11),(11,18),(12,1),(12,12),(12,19),(13,1),(13,13),(13,19),(14,1),(14,14),(14,19),(15,1),(15,15),(15,20),(16,1),(16,16),(16,20),(17,1),(17,17),(17,20),(18,2),(18,9),(18,18),(19,2),(19,10),(19,18),(20,2),(20,11),(20,18),(21,2),(21,12),(21,19),(22,2),(22,13),(22,19),(23,2),(23,14),(23,19),(24,2),(24,15),(24,20),(25,2),(25,16),(25,20),(26,2),(26,17),(26,20),(27,3),(27,9),(27,21),(28,3),(28,10),(28,21),(29,3),(29,11),(29,21),(30,3),(30,12),(30,22),(31,3),(31,13),(31,22),(32,3),(32,14),(32,22),(33,3),(33,15),(33,23),(34,3),(34,16),(34,23),(35,3),(35,17),(35,23),(36,4),(36,9),(36,21),(37,4),(37,10),(37,21),(38,4),(38,11),(38,21),(39,4),(39,12),(39,22),(40,4),(40,13),(40,22),(41,4),(41,14),(41,22),(42,4),(42,15),(42,23),(43,4),(43,16),(43,23),(44,4),(44,17),(44,23),(45,5),(45,9),(45,21),(46,5),(46,10),(46,21),(47,5),(47,11),(47,21),(48,5),(48,12),(48,22),(49,5),(49,13),(49,22),(50,5),(50,14),(50,22),(51,5),(51,15),(51,23),(52,5),(52,16),(52,23),(53,5),(53,17),(53,23),(54,6),(54,9),(54,24),(55,6),(55,10),(55,24),(56,6),(56,11),(56,24),(57,6),(57,12),(57,25),(58,6),(58,13),(58,25),(59,6),(59,14),(59,25),(60,6),(60,15),(60,26),(61,6),(61,16),(61,26),(62,6),(62,17),(62,26),(63,7),(63,9),(63,24),(64,7),(64,10),(64,24),(65,7),(65,11),(65,24),(66,7),(66,12),(66,25),(67,7),(67,13),(67,25),(68,7),(68,14),(68,25),(69,7),(69,15),(69,26),(70,7),(70,16),(70,26),(71,7),(71,17),(71,26),(72,8),(72,9),(72,24),(73,8),(73,10),(73,24),(74,8),(74,11),(74,24),(75,8),(75,12),(75,25),(76,8),(76,13),(76,25),(77,8),(77,14),(77,25),(78,8),(78,15),(78,26),(79,8),(79,16),(79,26),(80,8),(80,17),(80,26)}
    g : Cell ⟶ D ≜ {(0,5),(1,3),(4,7),(9,6),(12,1),(13,9),(14,5),(19,9),(20,8),(25,6),(27,8),(31,6),(35,3),(36,4),(39,8),(41,3),(44,1),(45,7),(49,2),(53,6),(55,6),(60,2),(61,8),(66,4),(67,1),(68,9),(71,5),(76,8),(79,7),(80,9)}

    /- The constraint: peers take different digits. -/

    peer : Cell ⟶ Cell ≜ (unit unit°) ∩ ≠     -- 1701 pairs sharing a unit, less the 81 (c,c): 1620; ≠ itself is 81·80 = 6480
    rev(s : Cell ⟶ D) : Cell ⟶ D ≜ s ∩ (peer\(s ≠))   -- one round of AC-3; see the module doc

    s₀ : Cell ⟶ D ≜ g°\𝟙(D)                       -- the givens, 1…9 elsewhere; see the module doc
    s₁ : Cell ⟶ D ≜ rev(s₀)
    s₂ : Cell ⟶ D ≜ rev(s₁)

    c2 : Cell ⟶ Cell ≜ {(2,2)}
    c8 : Cell ⟶ Cell ≜ {(8,8)}
    c40 : Cell ⟶ Cell ≜ {(40,40)}
    c62 : Cell ⟶ Cell ≜ {(62,62)}
    e2 : Cell ⟶ D ≜ {(2,1),(2,2),(2,4)}
    e40 : Cell ⟶ D ≜ {(40,5)}
    e62 : Cell ⟶ D ≜ {(62,4)}
    e8₁ : Cell ⟶ D ≜ {(8,2),(8,4),(8,8)}
    e8₂ : Cell ⟶ D ≜ {(8,2),(8,8)}
    check c2 s₁ = e2                              -- row 0, column 2 and box 0 rule out all but 1, 2, 4
    check c40 s₁ = e40                            -- the centre is forced to 5
    check c62 s₁ = e62
    check c8 s₁ = e8₁
    check c8 s₂ = e8₂                             -- round 2: cell 62 is now 4, so its column peer 8 loses 4

#guard (Lang.runProgram sudokuac).isOk

end LeetQ.Rel.Programs
