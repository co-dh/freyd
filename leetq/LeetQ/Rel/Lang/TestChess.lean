import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Chess

/-! Mate in one in the Rel language, read from `programs/chess.rel`, against `Chess.lean`: each of its `#guard`s
    on the same position, the program's board `on` replaced at the AST, each guard running the program once; and
    the program's tables and the relations `W`, `P` of its own board compared with `Chess`'s, as sets. -/

namespace LeetQ.Rel.Lang.TestChess

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg QLean

def chess : String := program_file "../../../programs/chess.rel"

abbrev SS : Obj := .prod .long .long
abbrev Bd : Obj := .arr SS

/-- The pieces as `obj Pc` names them, in `Chess`'s codes `colour*6 + kind`. -/
def pcs : List String := ["P", "N", "B", "R", "Q", "K", "p", "n", "b", "r", "q", "k"]

/-- The board `ps` as a literal of the program. -/
def lit (ps : List (Nat × Int64)) : String :=
  "{" ++ ",".intercalate (ps.map fun (s, p) => s!"({s},{pcs.getD p.toInt.toNat "?"})") ++ "}"

/-- The program, its board `on` replaced by `ps` when given; `one` keeps the declarations up to `Ω`, the mate
    test of one board. -/
def board (ps : Option (List (Nat × Int64))) (one : Bool) : Except Err Out := do
  let prog ← Parse.parse chess
  let prog ← match ps with
    | none => pure prog
    | some ps => do
      let b ← Parse.parseExpr (lit ps)
      pure (prog.map fun | .defn p "on" [] _ ty => .defn p "on" [] (.rel b) ty | d => d)
  let k := prog.findIdx fun | .defn _ "Ω" _ _ _ => true | _ => false
  runProgram (if one then prog.take (k + 1) else prog)

/-- `Ω` is the board when it is mate, else empty. -/
def mated (ps : List (Nat × Int64)) : Option Bool :=
  (Test.get (Test.ok (board ps true)) "Ω" Bd Bd).map fun R => !(R ⊑ zero)

/-- `m`'s mating moves as `[p, s, t]`, sorted as `Chess`'s checks sort them. -/
def moves (o : Out) : Option (List (List Int64)) :=
  (Test.get o "m" SS .long).map fun R =>
    (R.nub.toList.map fun ((s, t), p) => [p, s, t]).mergeSort fun a b => decide (a ≤ b)

def answer (ps : List (Nat × Int64)) : Option (List (List Int64)) := moves (Test.ok (board ps false))

def leanAnswer (ps : List (Nat × Int64)) : List (List Int64) :=
  ((Chess.mateIn1 (Chess.pos ps)).map fun (p, s, t) => [p, s, t]).mergeSort fun a b => decide (a ≤ b)

def leanMate (ps : List (Nat × Int64)) : Bool := Chess.isMate (Chess.pos ps)

/-! The tables, and the relations of the program's own board `on`, against `Chess`. -/

def one : Out := Test.ok (board none true)
def tbl (n : String) : Option (Rel .long .long) := Test.get one n .long .long
/-- A one-board family `Bd ⟶ Sq×Sq` as the relation its fibre is. -/
def fibre (n : String) : Option (Rel .long .long) := (Test.get one n Bd SS).map fun R => ofPairs (R.toList.map (·.2))
def on₀ : Chess.Board := Chess.pos [(6, 5), (48, 3), (1, 3), (60, 11)]

#guard [("→", (1, 0)), ("←", (-1, 0)), ("↑", (0, 1)), ("↓", (0, -1)), ("↗", (1, 1)), ("↖", (-1, 1)),
  ("↘", (1, -1)), ("↙", (-1, -1))].all (fun (n, d) => tbl n == some (Chess.D d)) &&
  tbl "K" == some Chess.K && tbl "N" == some Chess.N && tbl "X₀" == some (Chess.X 0) &&
  tbl "X₁" == some (Chess.X 1) && tbl "S₀" == some (Chess.S 0) && tbl "S₁" == some (Chess.S 1) &&
  fibre "W'" == some (Chess.W on₀) && fibre "Pin'" == some (Chess.P on₀)

/-! `Chess.lean`'s checks, each against `Chess` and against the value it states. -/

-- W Kg1 Ra7 Rb1, B Ke8: Rb1-b8 mates; the program's own board, run as written, `print m` included
#guard let o := Test.ok (runText chess); let a := moves o
  a == some (leanAnswer [(6, 5), (48, 3), (1, 3), (60, 11)]) && a == some [[3, 1, 57]] &&
    o.prints == ["m = {((1, 57), R)}"]
-- B Kc8: Rb8+ fails to Kxb8, Ra8+ leaves c7
#guard let a := answer [(6, 5), (48, 3), (1, 3), (58, 11)]
  a == some (leanAnswer [(6, 5), (48, 3), (1, 3), (58, 11)]) && a == some []
-- a third rook, no new code: Rb1-b8 and Rh2-h8
#guard let a := answer [(6, 5), (48, 3), (1, 3), (15, 3), (60, 11)]
  a == some (leanAnswer [(6, 5), (48, 3), (1, 3), (15, 3), (60, 11)]) && a == some [[3, 1, 57], [3, 15, 63]]

/-- `Ω` on `ps` agrees with `Chess.isMate` and with the verdict `v` the check states. -/
def mate (ps : List (Nat × Int64)) (v : Bool) : Bool := let m := mated ps; m == some (leanMate ps) && m == some v

-- W Kg1 Ra7 Rb8, B Ke8 mated; with B Kc8, Kxb8 takes the undefended rook
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11)] true
#guard mate [(6, 5), (48, 3), (57, 3), (58, 11)] false
-- 1. B Rc6 interposes on c8
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 9)] false
-- 2. B Nc6 takes b8 (or interposes on d8)
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 7)] false
-- 3. as 2, W Bb5 pins the knight to e8
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 7), (33, 2)] true
-- 4. as 1, W Bb5 pins the rook to e8
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 9), (33, 2)] true
-- W Ka1 Ra5 Rg1 Nf3 Nf7, B Kh5: mated along rank 5
#guard mate [(0, 5), (32, 3), (6, 3), (21, 1), (53, 1), (39, 11)] true
-- 5. B pd6 steps to d5
#guard mate [(0, 5), (32, 3), (6, 3), (21, 1), (53, 1), (39, 11), (43, 6)] false
-- 6. B ph6 reaches the empty g5 only diagonally, and h5 holds its king
#guard mate [(0, 5), (32, 3), (6, 3), (21, 1), (53, 1), (39, 11), (47, 6)] true
-- W Kg1 Ra7 Rd8 Rd1, B Ke8: Kxd8 fails, d8 is defended by Rd1
#guard mate [(6, 5), (48, 3), (59, 3), (3, 3), (60, 11)] true
-- 7. as above, B Nc6 takes d8
#guard mate [(6, 5), (48, 3), (59, 3), (3, 3), (60, 11), (42, 7)] false
-- 8. W Kg1 Ra7 Rb8, B Kd8: Ke8 steps back along the checking line, still attacked
#guard mate [(6, 5), (48, 3), (57, 3), (59, 11)] true

/-! Each line rewritten with `where` (§c) reads as the line it replaced, its items put in place. -/

def before : List String := [
  "W(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(R,R),(Q,Q)}), dom(on{(B,B),(Q,Q)}), e(on) ∪ k(on)) ∪ (dom(on{(N,N)})N) ∪ (dom(on{(P,P)})X₀) ∪ (dom(on{(K,K)})K)",
  "B(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(r,r),(q,q)}), dom(on{(b,b),(q,q)}), e(on)) ∪ (dom(on{(n,n)})N) f(on) ∪ (dom(on{(p,p)})p(↓,S₁,X₁,e(on),dom(on{(P,P),(N,N),(B,B),(R,R),(Q,Q),(K,K)})))",
  "Pin(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ q(dom(on{(R,R),(Q,Q)}),→,e(on),k(on)) ∪ q(dom(on{(R,R),(Q,Q)}),←,e(on),k(on)) ∪ q(dom(on{(R,R),(Q,Q)}),↑,e(on),k(on)) ∪ q(dom(on{(R,R),(Q,Q)}),↓,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↗,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↖,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↘,e(on),k(on)) ∪ q(dom(on{(B,B),(Q,Q)}),↙,e(on),k(on))",
  "M(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(R,R),(Q,Q)}), dom(on{(B,B),(Q,Q)}), e(on)) ∪ (dom(on{(N,N)})N) ∪ (dom(on{(K,K)})K) (𝟙 − dom(on{(P,P),(N,N),(B,B),(R,R),(Q,Q),(K,K),(k,k)})) ∪ (dom(on{(P,P)})p(↑,S₀,X₀,e(on),dom(on{(p,p),(n,n),(b,b),(r,r),(q,q)})))"]

def rewritten (p : Program) : List (String × String) :=
  (p.filterMap Test.reading).filter fun r => ["W", "B", "Pin", "M"].contains r.1

-- the program up to line 31, the lines `W B Pin M` refer to, is the same before and after
#guard match Parse.parse chess, Parse.parse ("\n".intercalate ((chess.splitOn "\n").take 31 ++ before)) with
  | .ok p, .ok q => (rewritten p).length == 4 && rewritten p == rewritten q
  | _, _ => false

end LeetQ.Rel.Lang.TestChess
