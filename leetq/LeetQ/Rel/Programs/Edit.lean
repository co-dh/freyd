import LeetQ.Rel.Lang.Embed

/-! # String edit -/

namespace LeetQ.Rel.Programs

rel_program edit where
    obj A = {a,b}                                 -- the alphabet
    obj Op = A+(A+A)                              -- Op ::= cpy A ∣ del A ∣ ins A
    obj N = 0…6                                   -- lengths, and the fold rounds

    cpy : A ⟶ A+(A+A) ≜ inl
    del : A ⟶ A+(A+A) ≜ inl inr
    ins : A ⟶ A+(A+A) ≜ inr inr

    /- The universe: the strings of length ≤ 2, and every edit sequence of length ≤ 4, which holds all the edit sequences
       of a pair of them (each operation consumes a character of one string). -/

    r₂ : 1 ⟶ [N] ≜ Λ(⊤{(0,0),(1,1)})              -- the array 0…1, one fold round each
    r₄ : 1 ⟶ [N] ≜ Λ(⊤{(0,0),(1,1),(2,2),(3,3)})  -- the array 0…3
    Ss : [A] ⟶ [A] ≜ ran(r₂⦇ran(nil(1)), π₂ ∪ (⟨π₂⊤,π₂⟩cons)⦈)    -- the strings
    Es : [A+(A+A)] ⟶ [A+(A+A)] ≜ ran(r₄⦇ran(nil(1)), π₂ ∪ (⟨π₂⊤,π₂⟩cons)⦈)   -- the edit sequences
    D : [A]×[A] ⟶ [A]×[A] ≜ Ss×Ss                 -- the pairs of strings

    /- The specification (09:485, edit-defn). -/

    base : 1 ⟶ [A]×[A] ≜ ⟨nil,nil⟩                -- ([],[])
    step : (A+(A+A))×([A]×[A]) ⟶ [A]×[A] ≜ ⟨⟨π₁cpy°,π₂π₁⟩cons,⟨π₁cpy°,π₂π₂⟩cons⟩ ∪ ⟨⟨π₁del°,π₂π₁⟩cons,π₂π₂⟩ ∪ ⟨π₂π₁,⟨π₁ins°,π₂π₂⟩cons⟩
    edit : [A+(A+A)] ⟶ [A]×[A] ≜ Es⦇ran(base), step⦈   -- edit ≜ ⦇[base,step]⦈, on the sequences Es
    R : [α] ⟶ [β] ≜ length ≤(N,N) length°         -- R ≜ length ≤ length°, run on the pairs est compares
    spec : [A]×[A] ⟶ [A+(A+A)] ≜ DΛ(edit°)est(R)  -- Λ(edit°) est(R): a shortest sequence of each pair

    /- The tabulation (09:596-610), each definition with the book page it is on (`mle (x,y)` is `head (column x y)`, so one
       column of `column` per character of `x`, p.227). A `'` marks a name the book also uses for the specification.

       `fstcol` is the first column, the edit sequences that delete a suffix of `x`: `fstcol = tails · list del` (p.228). -/

    fstcol(x : 1 ⟶ [A]) : 1 ⟶ [[A+(A+A)]] ≜ x F(del) tails          -- fstcol = list(del) tails

    /- `base'(b,u)` is the one-element array holding the insertion of `b` before `u` (p.229). -/

    base'(b : 1 ⟶ A, u : 1 ⟶ [Op]) : 1 ⟶ [[A+(A+A)]] ≜ ⟨b ins,u⟩cons τ   -- base(b,u) = [[ins(b)]⧺u]

    /- `bmin(R)(p,q)` is `p` when `p` is shorter than or equal to `q`, else `q`; `R` is `length ≤ length°` (p.267,
       `bmin r = cond r (outl, outr)`). -/

    bmin : [α]×[α] ⟶ [α] ≜ q π₁ ∪ (π₂ − (q π₂)) where q ≜ dom(⟨π₁length,π₂length⟩(𝟙(N×N) ∩ (π₁ ≤ π₂°)))   -- bmin(R)(p,q): p if p R q, else q

    /- `ne` is the test "otherwise" of `step` (p.229, `a ≠ b`); the book has no name for it. -/

    ne : A×A ⟶ A×A ≜ 𝟙 − dom(π₁ ∩ π₂)

    /- `step'(b)` takes `((a,(u,v)),ws)`: copy `a` onto `v` when `a = b`, else the shorter of `del a` before the head of `ws`
       and `ins b` before `u` (p.229). Here `π₁π₁` is `a`, `π₁π₂π₁` is `u`, `π₁π₂π₂` is `v`, `π₂` is `ws`, `⊤b` is `b`. -/

    step'(b : 1 ⟶ A) : (A×([Op]×[Op]))×[[Op]] ⟶ [[Op]] ≜ dom(π₁π₁ ∩ (⊤b))⟨⟨π₁π₁cpy,π₁π₂π₂⟩cons,π₂⟩cons ∪ (dom(⟨π₁π₁,⊤b⟩ne)⟨⟨⟨π₁π₁del,π₂head⟩cons,⟨⊤b ins,π₁π₂π₁⟩cons⟩bmin,π₂⟩cons)

    /- `nextcol(x,b,us)` is the next column, a fold over `xus` from `base'(b,last(us))` by `step'(b)` (p.228,
       `nextcol x (b, us) = ([base (b, last us), step b]) xus`); its seed depends on `(b,us)`, a family over the key of
       the fold's own left (§e). `xus` pairs each character of `x` with the entries of `us` for the string before it and
       after it (p.229, `xus = zip (x, zip (init us, tail us))`). -/

    nextcol(x : 1 ⟶ [A], b : 1 ⟶ A, us : 1 ⟶ [[Op]]) : 1 ⟶ [[Op]] ≜ xus⦇ran(base'(b,us last)), step'(b)⦈ where xus ≜ ⟨x,⟨us init,us tail⟩zip⟩zip

    /- `column(x,y)` is the fold over `y` from `fstcol(x)` by `nextcol x` (p.228, `column x = ([fstcol x, nextcol x])`):
       the step takes `(b,us)` to `nextcol(x,b,us)`, applied to the closed families of `(x,(b,us))`. -/

    column(x : 1 ⟶ [A], y : 1 ⟶ [A]) : 1 ⟶ [[Op]] ≜ y⦇ran(fstcol(x)), ⟨⊤x,⟨π₁,π₂⟩⟩(nextcol(⟨⊤,π₁⟩,⟨⊤,π₂π₁⟩,⟨⊤,π₂π₂⟩)π₂)⦈

    /- `mle` is the first entry of the column, a minimal edit sequence (p.229, `mle (x,y) = outl (head (column x y))`). -/

    mle : [A]×[A] ⟶ [Op] ≜ column(⟨⊤,π₁⟩,⟨⊤,π₂⟩)π₂ head

    /- The tabulation gives a shortest edit sequence of every pair of `D`, of the specification's length. -/

    check D mle ⊑ spec
    check D mle length 𝟙(N) = (spec length 𝟙(N))

    /- The specification's own values are not written out, being too many rows; `TestEdit.lean` checks the first print. -/

    print spec length 𝟙(N)
    print Ddom(⟨π₁length,π₂length⟩{((2,2),(2,2))})spec

#guard (Lang.runProgram edit).isOk

end LeetQ.Rel.Programs
