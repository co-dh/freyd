import LeetQ.Rel.Lang.Embed
import LeetQ.Rel.Lang.Test

/-! The Rel language written inside Lean (`Embed`): `circuit.rel.md` and `blocks.rel.md`, their code blocks pasted as
    they are, read to the AST the text parser reads from the files and run by the same evaluator; and the grammar's
    closedness: a Lean term in a body is a parse error. -/

namespace LeetQ.Rel.Lang.EmbedTest

open Lean LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test

rel_program circuitR where
    obj B = 0…1                                   -- a bit

    xor : B×B ⟶ B ≜ {((0,0),0),((0,1),1),((1,0),1),((1,1),0)}   -- xor: 1 where the inputs differ
    ∧ : B×B ⟶ B ≜ {((0,0),0),((0,1),0),((1,0),0),((1,1),1)}   -- and: 1 where both are 1
    ∨ : B×B ⟶ B ≜ {((0,0),0),((0,1),1),((1,0),1),((1,1),1)}   -- or: 1 where one is 1

    ins : [α] ⟶ [α] ≜ ⟨⊤,𝟙⟩cons                    -- each element of α put in front
    I : [B] ⟶ [B] ≜ ran(nil ins ins ins)           -- the adder's inputs: the arrays of three bits

    q : [α] ⟶ α×α ≜ ⟨at(0),at(1)⟩                  -- the first two inputs
    x₂ : [B] ⟶ B×B ≜ ⟨q xor,at(2)⟩                 -- their xor, and the third input
    add : [B] ⟶ B×B ≜ I⟨x₂ xor,⟨q∧,x₂∧⟩∨⟩         -- (sum, carry)
    p : B ⟶ B×B ≜ ⟨{(0,0)},{(0,1)}⟩               -- the point (0,1) at the bit 0
    answer : [B] ⟶ B ≜ add p°                     -- the inputs giving sum 0, carry 1

    check answer = {(0 1 1,0),(1 0 1,0),(1 1 0,0)}

rel_program blocksR where
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

/-! The two front ends agree: the AST read here is the AST `Parse` reads from the file, positions aside (they are
    places in two different files). -/

local instance (priority := high) : BEq Lang.Pos := ⟨fun _ _ => true⟩
deriving instance BEq for OExp
deriving instance BEq for Tup
deriving instance BEq for Lang.Expr
deriving instance BEq for Body
deriving instance BEq for Param
deriving instance BEq for ObjDef
deriving instance BEq for Decl

def circuitText : String := program_file "../../../programs/circuit.rel.md"

#guard match Parse.parse circuitText with | .ok p => p == circuitR | .error _ => false
#guard match Parse.parse blocks with | .ok p => p == blocksR | .error _ => false

-- every `check` holds (a failed one is an error) and nothing is printed
#guard (runProgram circuitR).isOk && (ok (runProgram circuitR)).prints == []
#guard (runProgram blocksR).isOk && (ok (runProgram blocksR)).prints == []
#guard (ok (runProgram (blocksR ++ [.print {} (.name {} "plan")]))).prints ==
  ["plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}"]

/-! Closedness: a Lean term in a body is a parse error of the grammar, never a term elaborated. -/

elab "#rel_parse " s:str : command => do
  match Parser.runParserCategory (← getEnv) `relStmt s.getString with
  | .ok t => logInfo m!"parsed {t}"
  | .error e => logInfo e

/-- info: parsed f:A⟶A≜R∩∼S° -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R ∩ ∼S°"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ fun x => x"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ let x := R; x"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ do R"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ if R then S else T"
/-- info: <input>:1:14: expected ')' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ (R, S)"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ 1 + 1"
/-- info: <input>:1:15: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R (1 + 1)"
/-- info: <input>:1:14: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R(fun x => x)"
/-- info: <input>:1:22: expected '≜' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R where x := 1"

-- Lean gives every category the antiquotation `$x`, `$(…)` at any quotation depth, so these parse; reading the
-- program refuses them
/-- info: parsed f:A⟶A≜$x -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $x"
/-- info: parsed f:A⟶A≜$(fun x => x) -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $(fun x => x)"
/-- error: line 123, col 19: `$` is no term of the Rel language: an antiquotation has no place in a program -/
#guard_msgs in
rel_program antiquot where
    f : 1 ⟶ 1 ≜ 𝟙 $(fun x => x)

/-! Every program file read by both front ends: the literate text after `rel_program p where`, parsed as a Lean
    command and read to the AST, against `Parse.parse` of the same text. -/

open Elab Command in
elab "#rel_agree " p:str : command => do
  let some dir := (System.FilePath.mk (← getFileName)).parent | throwError "no directory for `{← getFileName}`"
  let lit ← match Parse.programText p.getString (← IO.FS.readFile (dir / p.getString)) with
    | .ok s => pure s
    | .error e => throwError "{p.getString}: {e}"
  let text := "rel_program p where\n" ++ lit
  match Parser.runParserCategory (← getEnv) `command text with
  | .error e => logInfo m!"parse: {e}"
  | .ok stx => match Embed.program (FileMap.ofString text) stx[3].getArgs, Parse.parse lit with
    | .ok a, .ok b => logInfo m!"{if a == b then "agree" else "differ"}: {a.length} declarations"
    | .error e, _ => logInfo m!"embedding: {e}"
    | _, .error e => logInfo m!"text: {e}"

/-- info: agree: 12 declarations -/
#guard_msgs in #rel_agree "../../../programs/circuit.rel.md"
/-- info: agree: 28 declarations -/
#guard_msgs in #rel_agree "../../../programs/blocks.rel.md"
/-- info: agree: 46 declarations -/
#guard_msgs in #rel_agree "../../../programs/chess.rel.md"
/-- info: agree: 28 declarations -/
#guard_msgs in #rel_agree "../../../programs/edit.rel.md"
/-- info: agree: 28 declarations -/
#guard_msgs in #rel_agree "../../../programs/wumpus.rel.md"
/-- info: agree: 19 declarations -/
#guard_msgs in #rel_agree "../../../programs/selsort.rel.md"
/-- info: agree: 15 declarations -/
#guard_msgs in #rel_agree "../../../programs/mss.rel.md"
/-- info: agree: 22 declarations -/
#guard_msgs in #rel_agree "../../../programs/knapsack.rel.md"
/-- info: agree: 38 declarations -/
#guard_msgs in #rel_agree "../../../programs/detab.rel.md"

end LeetQ.Rel.Lang.EmbedTest
