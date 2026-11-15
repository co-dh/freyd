import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Chess
/- Turned off: it re-runs `Programs.chess` on many boards at every build (about 15 s). Remove this comment
   wrapper to turn it back on.

/-! Mate in one in the Rel language, the program `Programs.chess`: each check on its position, the program's board
    `on` replaced (`rel_program v from Programs.chess`), each variant expanded once; and the program's tables and
    the relations `W`, `P` of its own board, as sets. -/

namespace LeetQ.Rel.Lang.TestChess

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg QLean

abbrev SS : Obj := .prod .long .long
abbrev Bd : Obj := .arr SS

/-- `Ω` is the board when it is mate, else empty. -/
def mated (gs : List (String × Gen.Gv)) : Option Bool := (Test.get gs "Ω" Bd Bd).map fun R => !(R ⊑ zero)

/-- `m`'s mating moves as `[p, s, t]`, sorted. -/
def moves (gs : List (String × Gen.Gv)) : Option (List (List Int64)) :=
  (Test.get gs "m" SS .long).map fun R =>
    (R.nub.toList.map fun ((s, t), p) => [p, s, t]).mergeSort fun a b => decide (a ≤ b)

/-! The tables, and the relations of the program's own board `on`. -/

rel_program one from Programs.chess upto Ω where

def tbl (n : String) : Option (Rel .long .long) := Test.get one.expanded n .long .long
/-- A one-board family `Bd ⟶ Sq×Sq` as the relation its fibre is. -/
def fibre (n : String) : Option (Rel .long .long) :=
  (Test.get one.expanded n Bd SS).map fun R => ofPairs (R.toList.map (·.2))

-- `S₀`, `S₁`: the second and the seventh rank; `W'`: the squares White attacks on `on`; no pin
#guard one.ok && tbl "S₀" == some (ofPairs ((List.range 8).map fun i => (8 + Int64.ofNat i, 8 + Int64.ofNat i))) &&
  tbl "S₁" == some (ofPairs ((List.range 8).map fun i => (48 + Int64.ofNat i, 48 + Int64.ofNat i))) &&
  fibre "W'" == some (ofPairs [(48, 49), (48, 50), (48, 51), (48, 52), (48, 53), (48, 54), (48, 55), (1, 2), (1, 3),
    (1, 4), (1, 5), (1, 6), (1, 0), (48, 56), (1, 9), (1, 17), (1, 25), (1, 33), (1, 41), (1, 49), (1, 57), (48, 40),
    (48, 32), (48, 24), (48, 16), (48, 8), (48, 0), (6, 7), (6, 5), (6, 14), (6, 15), (6, 13)]) &&
  fibre "Pin'" == some (ofPairs [])

/-! Mate in one, each against the value its check states. -/

rel_program printM after Programs.chess where
    print m

-- W Kg1 Ra7 Rb1, B Ke8: Rb1-b8 mates; the program's own board, run as written: its `check m = …` holds and it
-- prints nothing, and `m` printed here is the one move
#guard Programs.chess.ok && moves Programs.chess.expanded == some [[3, 1, 57]] && Programs.chess.prints == [] &&
  printM.prints == ["m = {((1, 57), R)}"]

-- B Kc8: Rb8+ fails to Kxb8, Ra8+ leaves c7
rel_program noMate from Programs.chess where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(1,R),(58,k)}
#guard noMate.ok && moves noMate.expanded == some []
-- a third rook, no new code: Rb1-b8 and Rh2-h8
rel_program twoMates from Programs.chess where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(1,R),(15,R),(60,k)}
#guard twoMates.ok && moves twoMates.expanded == some [[3, 1, 57], [3, 15, 63]]

-- W Kg1 Ra7 Rb8, B Ke8 mated; with B Kc8, Kxb8 takes the undefended rook
rel_program b₀ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(60,k)}
#guard b₀.ok && mated b₀.expanded == some true
rel_program b₀' from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(58,k)}
#guard b₀'.ok && mated b₀'.expanded == some false
-- 1. B Rc6 interposes on c8
rel_program b₁ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(60,k),(42,r)}
#guard b₁.ok && mated b₁.expanded == some false
-- 2. B Nc6 takes b8 (or interposes on d8)
rel_program b₂ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(60,k),(42,n)}
#guard b₂.ok && mated b₂.expanded == some false
-- 3. as 2, W Bb5 pins the knight to e8
rel_program b₃ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(60,k),(42,n),(33,B)}
#guard b₃.ok && mated b₃.expanded == some true
-- 4. as 1, W Bb5 pins the rook to e8
rel_program b₄ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(60,k),(42,r),(33,B)}
#guard b₄.ok && mated b₄.expanded == some true
-- W Ka1 Ra5 Rg1 Nf3 Nf7, B Kh5: mated along rank 5
rel_program r₅ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(0,K),(32,R),(6,R),(21,N),(53,N),(39,k)}
#guard r₅.ok && mated r₅.expanded == some true
-- 5. B pd6 steps to d5
rel_program b₅ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(0,K),(32,R),(6,R),(21,N),(53,N),(39,k),(43,p)}
#guard b₅.ok && mated b₅.expanded == some false
-- 6. B ph6 reaches the empty g5 only diagonally, and h5 holds its king
rel_program b₆ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(0,K),(32,R),(6,R),(21,N),(53,N),(39,k),(47,p)}
#guard b₆.ok && mated b₆.expanded == some true
-- W Kg1 Ra7 Rd8 Rd1, B Ke8: Kxd8 fails, d8 is defended by Rd1
rel_program d₈ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(59,R),(3,R),(60,k)}
#guard d₈.ok && mated d₈.expanded == some true
-- 7. as above, B Nc6 takes d8
rel_program b₇ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(59,R),(3,R),(60,k),(42,n)}
#guard b₇.ok && mated b₇.expanded == some false
-- 8. W Kg1 Ra7 Rb8, B Kd8: Ke8 steps back along the checking line, still attacked
rel_program b₈ from Programs.chess upto Ω where
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(57,R),(59,k)}
#guard b₈.ok && mated b₈.expanded == some true

/-! Each line rewritten with `where` (§c) reads as the line it replaced, its items put in place. -/

def before : List String := [
  "W(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(R,R),(Q,Q)}), dom(on{(B,B),(Q,Q)}), e(on) ∪ k(on)) ∪ (dom(on{(N,N)})N) ∪ (dom(on{(P,P)})X₀) ∪ (dom(on{(K,K)})K)",
  "B(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(r,r),(q,q)}), dom(on{(b,b),(q,q)}), e(on)) ∪ (dom(on{(n,n)})N) f(on) ∪ (dom(on{(p,p)})p(↓,S₁,X₁,e(on),dom(on{(P,P),(N,N),(B,B),(R,R),(Q,Q),(K,K)})))",
  "Pin(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ q(dom(on{(R,R),(Q,Q)}),→,e(on),k(on)) ∪ q(dom(on{(R,R),(Q,Q)}),←,e(on),k(on)) ∪ q(dom(on{(R,R),(Q,Q)}),↑,e(on),k(on)) ∪ q(dom(on{(R,R),(Q,Q)}),↓,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↗,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↖,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↘,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↙,e(on),k(on))",
  "M(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(R,R),(Q,Q)}), dom(on{(B,B),(Q,Q)}), e(on)) ∪ (dom(on{(N,N)})N) ∪ (dom(on{(K,K)})K) (𝟙 − dom(on{(P,P),(N,N),(B,B),(R,R),(Q,Q),(K,K),(k,k)})) ∪ (dom(on{(P,P)})p(↑,S₀,X₀,e(on),dom(on{(p,p),(n,n),(b,b),(r,r),(q,q)})))"]

def rewritten (p : Program) : List (String × String) :=
  (p.filterMap Test.reading).filter fun r => ["W", "B", "Pin", "M"].contains r.1

-- the program up to the line of `W`, the lines `W B Pin M` refer to, is the same before and after
#guard match Test.extend (Programs.chess.takeWhile fun | .defn _ "W" _ _ _ => false | _ => true)
    ("\n".intercalate before) with
  | .ok q => (rewritten Programs.chess).length == 4 && rewritten Programs.chess == rewritten q
  | .error _ => false

end LeetQ.Rel.Lang.TestChess
-/
