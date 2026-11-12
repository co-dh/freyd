import LeetQ.Rel.Lang.Embed

/-! # A full adder

AIMA §8.4.2's one-bit full adder C1. Its three inputs are one array of three bits: the first, second and third
input are the elements at positions `0`, `1`, `2`. -/

namespace LeetQ.Rel.Programs

rel_program circuit where
    obj B = 0…1                                   -- a bit

    /- The note writes ⊕ for xor; ⊕ is the sum of relations here, so xor is an ordinary definition. -/

    xor : B×B ⟶ B ≜ {((0,0),0),((0,1),1),((1,0),1),((1,1),0)}   -- xor: 1 where the inputs differ
    ∧ : B×B ⟶ B ≜ {((0,0),0),((0,1),0),((1,0),0),((1,1),1)}   -- and: 1 where both are 1
    ∨ : B×B ⟶ B ≜ {((0,0),0),((0,1),1),((1,0),1),((1,1),1)}   -- or: 1 where one is 1

    /- An array has no universe, so the adder's inputs are built: every bit put in front of each array, three times
       from the empty one, gives the eight arrays of three bits. -/

    ins : [α] ⟶ [α] ≜ ⟨⊤,𝟙⟩cons                    -- each element of α put in front
    I : [B] ⟶ [B] ≜ ran(nil ins ins ins)           -- the adder's inputs: the arrays of three bits

    q : [α] ⟶ α×α ≜ ⟨at(0),at(1)⟩                  -- the first two inputs
    x₂ : [B] ⟶ B×B ≜ ⟨q xor,at(2)⟩                 -- their xor, and the third input
    add : [B] ⟶ B×B ≜ I⟨x₂ xor,⟨q∧,x₂∧⟩∨⟩         -- (sum, carry)
    p : B ⟶ B×B ≜ ⟨{(0,0)},{(0,1)}⟩               -- the point (0,1) at the bit 0
    answer : [B] ⟶ B ≜ add p°                     -- the inputs giving sum 0, carry 1

    check answer = {(0 1 1,0),(1 0 1,0),(1 1 0,0)}

#guard (Lang.runProgram circuit).isOk

end LeetQ.Rel.Programs
