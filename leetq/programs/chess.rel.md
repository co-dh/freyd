# Mate in one

    obj Sq = 0…63                                 -- the squares, a1 = 0, b1 = 1, …, h8 = 63
    obj Pc = {P,N,B,R,Q,K,p,n,b,r,q,k}            -- the pieces, white then black: colour*6 + kind
    obj Bd = 𝒫(Sq×Pc)                             -- a board: the set of its (square, piece) rows
    on : Sq ⟶ Pc ≜ {(6,K),(48,R),(1,R),(60,k)}    -- W Kg1 Ra7 Rb1, B Ke8

    h : Sq ⟶ Sq ≜ {(7,7),(15,15),(23,23),(31,31),(39,39),(47,47),(55,55),(63,63)}   -- the h-file
    → : Sq ⟶ Sq ≜ (𝟙 − h)succ                     -- one file right
    ← : Sq ⟶ Sq ≜ →°                              -- one file left
    ↑ : Sq ⟶ Sq ≜ succ succ succ succ succ succ succ succ   -- one rank up
    ↓ : Sq ⟶ Sq ≜ ↑°                              -- one rank down
    ↗ : Sq ⟶ Sq ≜ ↑→
    ↖ : Sq ⟶ Sq ≜ ↑←
    ↘ : Sq ⟶ Sq ≜ ↓→
    ↙ : Sq ⟶ Sq ≜ ↓←
    K : Sq ⟶ Sq ≜ → ∪ ← ∪ ↑ ∪ ↓ ∪ ↗ ∪ ↖ ∪ ↘ ∪ ↙   -- king steps
    N : Sq ⟶ Sq ≜ ↑↑→ ∪ (↑→→) ∪ (↑↑←) ∪ (↑←←) ∪ (↓↓→) ∪ (↓→→) ∪ (↓↓←) ∪ (↓←←)   -- knight steps
    X₀ : Sq ⟶ Sq ≜ ↗ ∪ ↖                          -- a white pawn's forward diagonals
    X₁ : Sq ⟶ Sq ≜ ↘ ∪ ↙                          -- a black pawn's forward diagonals
    S₀ : Sq ⟶ Sq ≜ {(8,8),(9,9),(10,10),(11,11),(12,12),(13,13),(14,14),(15,15)}         -- white's pawn rank
    S₁ : Sq ⟶ Sq ≜ {(48,48),(49,49),(50,50),(51,51),(52,52),(53,53),(54,54),(55,55)}     -- black's pawn rank

    L(R : Sq ⟶ Sq) : Sq ⟶ Sq ≜ 𝟙 ∪ R ∪ (RR) ∪ (RRR) ∪ (RRRR) ∪ (RRRRR) ∪ (RRRRRR) ∪ (RRRRRRR)   -- a line: R⁰ ∪ … ∪ R⁷
    e(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ 𝟙 − dom(on)       -- the empty squares
    k(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ dom(on{(k,k)})    -- the black king's square
    f(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ 𝟙 − dom(on{(p,p),(n,n),(b,b),(r,r),(q,q),(k,k)})   -- the squares with no black piece

    r(s : Sq ⟶ Sq, D : Sq ⟶ Sq, V : Sq ⟶ Sq) : Sq ⟶ Sq ≜ sDL(VD)   -- s's ray along D, on through V to the first square off V
    ρ(s : Sq ⟶ Sq, d : Sq ⟶ Sq, V : Sq ⟶ Sq) : Sq ⟶ Sq ≜ r(s,→,V) ∪ r(s,←,V) ∪ r(s,↑,V) ∪ r(s,↓,V) ∪ r(d,↗,V) ∪ r(d,↖,V) ∪ r(d,↘,V) ∪ r(d,↙,V)   -- the rays of the orthogonal sliders s and the diagonal d
    p(t : Sq ⟶ Sq, S : Sq ⟶ Sq, X : Sq ⟶ Sq, e : Sq ⟶ Sq, c : Sq ⟶ Sq) : Sq ⟶ Sq ≜ te ∪ (Stete) ∪ (Xc)   -- pawn moves: forward onto e, two from S across e, diagonally onto c
    q(s : Sq ⟶ Sq, D : Sq ⟶ Sq, e : Sq ⟶ Sq, k : Sq ⟶ Sq) : Sq ⟶ Sq ≜ sL(De)D dom(L(De)Dk)   -- a slider of s to each square between it and k along D

    W(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(s, d, e(on) ∪ k(on)) ∪ (dom(on{(N,N)})N) ∪ (dom(on{(P,P)})X₀) ∪ (dom(on{(K,K)})K) where s ≜ dom(on{(R,R),(Q,Q)}), d ≜ dom(on{(B,B),(Q,Q)})   -- the squares white attacks
    B(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(dom(on{(r,r),(q,q)}), dom(on{(b,b),(q,q)}), ε) ∪ (dom(on{(n,n)})N) f(on) ∪ (dom(on{(p,p)})p(↓,S₁,X₁,ε,dom(on{(P,P),(N,N),(B,B),(R,R),(Q,Q),(K,K)}))) where ε ≜ e(on)   -- black's moves but the king's
    Pin(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ q(s,→,ε,κ) ∪ q(s,←,ε,κ) ∪ q(s,↑,ε,κ) ∪ q(s,↓,ε,κ) ∪ q(d,↗,ε,κ) ∪ q(d,↖,ε,κ) ∪ q(d,↘,ε,κ) ∪ q(d,↙,ε,κ) where s ≜ dom(on{(R,R),(Q,Q)}), d ≜ dom(on{(B,B),(Q,Q)}), ε ≜ e(on), κ ≜ k(on)   -- the pinned squares
    M(on : Sq ⟶ Pc) : Sq ⟶ Sq ≜ ρ(s, d, ε) ∪ (dom(on{(N,N)})N) ∪ (dom(on{(K,K)})K) (𝟙 − dom(on{(P,P),(N,N),(B,B),(R,R),(Q,Q),(K,K),(k,k)})) ∪ (dom(on{(P,P)})p(↑,S₀,X₀,ε,dom(on{(p,p),(n,n),(b,b),(r,r),(q,q)}))) where s ≜ dom(on{(R,R),(Q,Q)}), d ≜ dom(on{(B,B),(Q,Q)}), ε ≜ e(on)   -- white's moves

    a(k : Sq ⟶ Sq, f : Sq ⟶ Sq, W : Sq ⟶ Sq) ≜ k(𝟙 ∪ (Kf)) ⊑ ⊤W   -- the king and each of its steps attacked
    i(B : Sq ⟶ Sq, Pin : Sq ⟶ Sq, W : Sq ⟶ Sq, k : Sq ⟶ Sq) ≜ B(𝟙 ∪ Pin°)Wk ⊑ Pin°⊤   -- each capture or interposition pinned

    b : [Sq×Pc] ⟶ [Sq×Pc] ≜ ran(Λ(⊤(Sq,Sq)⟨𝟙,on⟩))   -- the board on
    W' : [Sq×Pc] ⟶ Sq×Sq ≜ bW(∋)
    Pin' : [Sq×Pc] ⟶ Sq×Sq ≜ bPin(∋)
    Ω : [Sq×Pc] ⟶ [Sq×Pc] ≜ b a(k(∋),f(∋),W') i(B(∋),Pin',W',k(∋))   -- the board, when it is mate: the end

    c : [Sq×Pc] ⟶ [Sq×Pc]×(Sq×Sq) ≜ ⟨𝟙,M(∋)⟩       -- a board, each white move on it
    A(on : Sq ⟶ Pc, m : Sq ⟶ Sq) : Sq ⟶ Pc ≜ 𝟙 − dom(m) − ran(m)on ∪ (m°on)   -- on after the move m
    ⇝ : [Sq×Pc]×(Sq×Sq) ⟶ Sq×Pc ≜ A(π₁∋,π₂)       -- the board after the move
    j : [Sq×Pc]×(Sq×Sq) ⟶ [Sq×Pc]×(Sq×Sq) ≜ ran(bc)   -- the moves on b
    W₁ : [Sq×Pc]×(Sq×Sq) ⟶ Sq×Sq ≜ jW(⇝)
    Pin₁ : [Sq×Pc]×(Sq×Sq) ⟶ Sq×Sq ≜ jPin(⇝)
    ν : [Sq×Pc]×(Sq×Sq) ⟶ [Sq×Pc]×(Sq×Sq) ≜ j a(k(⇝),f(⇝),W₁) i(B(⇝),Pin₁,W₁,k(⇝))   -- the moves that mate
    m : Sq×Sq ⟶ Pc ≜ ran(νπ₂)π₁ on                -- each mating move, the piece it moves

    check m = {((1,57),R)}                        -- Rb1-b8 mates
