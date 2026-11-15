import LeetQ.Rel.Programs.Prelude

/-! # Constraint propagation (AIMA §6.2), the definitions the Sudoku programs share

`AC3` is elaborated here once, as the constant `csp.AC3`; a program read after `csp` calls it (`Tm.call`) instead
of expanding its body. `SudokuAC` traces one arc of it on a board. -/

namespace LeetQ.Rel.Programs

rel_program csp after prelude where
    -- AIMA REVISE on every arc of A at once, iterated: AC-3 (arc consistency, Mackworth's algorithm 3): the largest
    -- X ⊑ s with every arc supported
    AC3(A : α ⟶ α, C : β ⟶ β, s : α ⟶ β) : α ⟶ β ≜ νX : s ∩ (A\(X C))

end LeetQ.Rel.Programs
