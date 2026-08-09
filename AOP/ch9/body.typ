// Bird & de Moor, "Algebra of Programming", chapter 9 "Dynamic Programming" (book pp. 219-243),
// mirrored item by item into Freyd's conventions: composition by juxtaposition in DIAGRAM order.
//
// AUDIT — every numbered item of chapter 9, kept or dropped.
//   §9.1  (9.1)-(9.4) kept.  Theorem 9.1 kept WITH its proof — it is the one thing the chapter
//         proves, and both halves are short.  Theorem 9.2 kept (statement); its proof is the
//         book's own Ex 9.3, and the book does not give it.
//         Proposition 9.1 kept (statement).  Proposition 9.2 kept with its chain.  Proposition
//         9.3 kept, its chain DROPPED — it is 9.2's chain with `⟨cost, H°⟩` for `cost`
//         throughout, and repeating it says nothing new.  Proposition 9.4 kept with its chain.
//         Ex 9.1, 9.2, 9.4, 9.5 kept.  Ex 9.3 DROPPED (asks for Theorem 9.2's proof).
//   §9.2  specification, both conditions, the spine, the tabulation and the two arrays kept.
//         Ex 9.6 kept (the monotonicity law the section turns on).  Ex 9.7 DROPPED (supplies a
//         proof the book leaves out).
//   §9.3  specification, (9.5)-(9.10), the spine and the array kept.  Ex 9.12, 9.13 kept (both
//         state reusable laws; 9.13 is what justifies (9.9)).  Ex 9.8-9.11 DROPPED (they ask for
//         `cost` and `size` of one particular product; the scheme they instantiate is above).
//         Ex 9.14, 9.15 DROPPED (research problems).
//   §9.4  specification, the choice of `Q`, the spine kept.  Ex 9.16, 9.17 DROPPED (missing
//         proofs), 9.18, 9.19 DROPPED (questions the book does not answer), 9.20 DROPPED
//         (research problem).
//   Figures: chapter 9 prints no captioned figure.  Its three displayed arrays are here as two —
//         the `mle` grid (p. 227) and the `mct` triangle (p. 233); the p. 228 picture is the
//         same grid again, and what it adds is one sentence, printed as one sentence.
//   The Gofer programs are dropped throughout, as in chapters 7 and 8; what each computes and
//         what it costs is one row.
//   Nothing is dropped for being false in Rel.
#import "/AOP/bdm.typ": *

= 9 Dynamic Programming

== 9.1 Theory

An optimal solution is composed of optimal solutions to subproblems — the #emph[principle of
optimality]. Decompose in every possible way, solve recursively, and assemble: that is Theorem 9.1.
Discard the decompositions that can never contribute: that is Theorem 9.2. Discard all but one:
that is chapter 10.

#dt(
  ("9.1", [Throughout, $H = ⦇T⦈^degree ⦇h⦈$ and $M = Lambda(H)(min R)$ — the problem being solved.
    $h$ is a #emph[map]: the chapter never needs the assembling algebra relational.]),
  ("T 9.1 ✓", [#Th[$h$ monotonic on $R$ #sym.dash.em that is, $(F R) h subset h R$ #sym.dash.em and
    $R$ transitive. Then
    $ (mu X : Lambda(T^degree) thin P((F X) h) thin (min R)) subset M. $]]),
  ("", [Unfold $T$ every way at once, solve each part, rebuild with $h$, keep a best. By
    Knaster–Tarski it is enough to make $M$ a prefixed point:]),
  ("(9.1) ✓", [$Lambda(T^degree) thin P((F M) h) thin (min R) subset M$.]),
  ("", [which the universal property of $min$ splits into a refinement and a bound:]),
  ("(9.2) ✓", [$Lambda(T^degree) thin P((F M) h) thin (min R) subset H$.]),
  ("(9.3) ✓", [$H^degree Lambda(T^degree) thin P((F M) h) thin (min R) subset R$.]),
  ("(9.4) ✓", [Both use $(P X)(min R) subset (eps X) inter (eps^degree backslash (X R))$ #sym.dash.em
    which is (7.10), the two halves of fusion with the power functor.]),
)

#deriv(
  $Lambda(T^degree) thin P((F M) h) thin (min R)$,
  ("⊂", [(9.4), member half]), $Lambda(T^degree) eps (F M) h$,
  ("=", [$Lambda$ cancellation]), $T^degree (F M) h$,
  ("⊂", [$M subset H$, universal property of $min$]), $T^degree (F H) h$,
  ("=", [$H$ and the hylomorphism theorem]), $H$,
)

#deriv(
  $H^degree Lambda(T^degree) thin P((F M) h) thin (min R)$,
  ("⊂", [(9.4), lower-bound half]), $H^degree Lambda(T^degree) (eps^degree backslash ((F M) h thin R))$,
  ("=", [$H^degree = h^degree (F H^degree) T$, hylomorphism]),
    $h^degree (F H^degree) T thin Lambda(T^degree) (eps^degree backslash ((F M) h thin R))$,
  ("⊂", [$X Lambda(X^degree) subset eps^degree$; division; functors]), $h^degree F(H^degree M) h thin R$,
  ("⊂", [$M subset H$, universal property of $min$]), $h^degree (F R) h thin R$,
  ("⊂", [$h$ monotonic, shunted]), $R R$,
  ("⊂", [$R$ transitive]), $R$,
)

#dt(
  ("T 9.2 ✓", [#Th[#D("thinning") $h$ monotonic on $R$ and $Q$ a preorder with
    $Q^degree (F H) h subset (F H) h thin R^degree$. Then
    $ (mu X : Lambda(T^degree) ("thin" Q) thin P((F X) h) thin (min R)) subset M. $]]),
  ("", [The proviso says: throwing away the $Q$-worse decompositions throws away no optimum. The
    two conditions of dynamic programming are therefore
    $ (F R) h subset h R quad "and" quad Q^degree (F H) h subset (F H) h thin R^degree. $]),
  ("", [Both theorems say the optimum is a #emph[least] fixed point. Theorem 6.3 makes it the
    #emph[only] one when $"mem"(F) T^degree$ is inductive; and if $Lambda(T^degree)$ returns
    finite non-empty sets and $R$ is a connected preorder, that solution is entire. Refining
    $min R$ and $Lambda(T^degree)("thin" Q)$ then gives a recursive function.]),
  ("P 9.1", [$F alpha$ is usually a coproduct, so the recursion usually splits. If $V_1, V_2$ have
    disjoint ranges, $V_1 V_2^degree = nothing$, then
    $ Lambda([V_1,V_2]^degree)("thin"(Q_1 + Q_2)) thin P([U_1,U_2]) thin (min R) \
      ("ran" V_1 -> W_1, W_2), $
    where $W_i = Lambda(V_i^degree)("thin" Q_i) thin (P U_i)(min R)$. Every case study below
    uses it to peel off the base case.]),
)

#sub[Checking monotonicity]

#dt(
  ("P 9.2", [A cost function discharges it. If $R = "cost" "leq" "cost"^degree$,
    $h thin "cost" = (F "cost") k$ and $(F "leq") k subset k thin "leq"$, then
    $(F R) h subset h R$.]),
)

#deriv(
  $(F R) h subset h R$,
  ("≡", [$R$; shunting]), $(F R) h thin "cost" subset h thin "cost" thin "leq"$,
  ("≡", [assumption on $"cost"$]), $F(R thin "cost") k subset (F "cost") k thin "leq"$,
  ("⇐", [$R thin "cost" subset "cost" thin "leq"$]),
    $F("cost" thin "leq") k subset (F "cost") k thin "leq"$,
  ("⇐", [functors]), $(F "leq") k subset k thin "leq"$,
  ("⇐", [$k$ monotonic on $"leq"$]), $"true"$,
)

#dt(
  ("P 9.3", [#D("monotonicity in context") the same with the answer carried alongside the cost: if
    $R = "cost" "leq" "cost"^degree$, $h thin "cost" = F chevron.l "cost", H^degree chevron.r thin k$,
    $F("leq" times 1) k subset k thin "leq"$ and $H^degree$ is simple, then
    $F(R inter (H^degree H)) h subset h R$. Same chain as 9.2 with
    $chevron.l "cost", H^degree chevron.r$ for $"cost"$; simplicity of $H^degree$ is what lets the
    pair be cancelled.]),
  ("P 9.4", [#D("both conditions at once") take $F$ a bifunctor, written $F(1, X)$. If $U, V$ are
    preorders with $F(U, R) h subset h R$ and $V^degree H subset H R^degree$, then Theorem 9.2
    holds with $Q = F(U,V)$. Monotonicity is $U$ reflexive; the rest:]),
)

#deriv(
  $Q^degree F(1, H) h$,
  ("=", [$Q = F(U,V)$; converse; bifunctors]), $F(U^degree, V^degree H) h$,
  ("⊂", [assumption on $V$]), $F(U^degree, H R^degree) h$,
  ("⊂", [bifunctors]), $F(1, H) F(U^degree, R^degree) h$,
  ("⊂", [assumption on $h$, converted and shunted]), $F(1,H) h thin R^degree$,
)

#dt(
  ("Ex 9.1 ✓", [Theorem 9.1 is Theorem 9.2 at $Q = 1$.]),
  ("Ex 9.2 ✓", [#D("context") both conditions weaken to
    $F(R inter (H^degree H)) h subset h R$ and
    $(Q inter (T T^degree))^degree (F H) h subset (F H) h thin R^degree$ #sym.dash.em only
    decompositions of one and the same input need comparing.]),
  ("Ex 9.4 ✓", [$Q = F(M R M^degree)$ always satisfies the thinning condition, and is useless: it
    presupposes the optimum $M$.]),
  ("Ex 9.5 ✓", [The three facts Proposition 9.1 rests on. Disjoint ranges is
    $"ran" V_2 = tld("ran" V_1) thin "ran" V_2$; then
    $Lambda([V_1,V_2]^degree) = ("ran" V_1 -> Lambda(V_1^degree iota), Lambda(V_2^degree iota'))$
    and $(E iota)("thin"(Q_1+Q_2)) = ("thin" Q_1)(E iota)$, likewise for $iota'$.]),
)

== 9.2 The string edit problem

#dt(
  ("9.2 ✓", [Turn one string into another by copying, deleting and inserting characters, in as few
    operations as possible. $"Op" ::= "cpy" "Char" | "del" "Char" | "ins" "Char"$, and
    $"edit" = ⦇"base", "step"⦈ : "list" "Op" -> "list" "Char" times "list" "Char"$ replays a
    sequence onto the two strings:
    $ "base" = ([], []), $
    $ "step"("cpy" a, (x,y)) = ([a] cc x, [a] cc y), $
    $ "step"("del" a, (x,y)) = ([a] cc x, y), $
    $ "step"("ins" a, (x,y)) = (x, [a] cc y). $]),
  ("", [Spec: a map $"mle" subset Lambda("edit"^degree)(min R)$ with
    $R = "length" "leq" "length"^degree$.]),
  ("", [#emph[Monotonic]: $sans("in") = ["nil", "cons"]$ is monotonic under $R$, by Proposition 9.2
    with $"length" = ⦇"zero", pi' "succ"⦈$ and $"succ"$ monotonic on $"leq"$.]),
  ("", [#emph[Thinning]: a copy, when available, beats a delete or an insert. With
    $F(A,B) = 1 + (A times B)$ the condition is
    $Q^degree F(1, "edit"^degree) sans("in") subset F(1,"edit"^degree) sans("in") thin R^degree$,
    and Proposition 9.4 reduces it to two:
    $ F(Pi, R) sans("in") subset sans("in") R quad "and" quad "edit" V subset R thin "edit". $]),
  ("Ex 9.6 ✓", [The first always holds, so $U = Pi$: $(Pi times R)"cons" subset "cons" R$.]),
  ("", [For the second take $V = "suffix" times "suffix"$. Since $"suffix" = "tail"^*$ and
    $A B subset C B$ gives $A^* B subset C^* B$, it is enough to have
    $"edit"(1 times "tail") subset R thin "edit"$ and $"edit"("tail" times 1) subset R thin "edit"$.
    In words: if $"edit" e s = (x, "cons"(b,y))$, find the operation producing $b$ and either
    demote $"cpy" b$ to $"del" b$ or delete $"ins" b$ #sym.dash.em no longer, same result.]),
  ("", [The recursion, with $Q = 1 + (U times V)$:
    $ X = Lambda(["base","step"]^degree)("thin" Q) \
      thin P(["nil", (1 times X)"cons"]) thin (min R). $]),
  ("", [$"base"$ and $"step"$ have disjoint ranges, so Proposition 9.1 peels the base case:
    $ X = ("empty" -> "nil", thin Lambda("step"^degree)("thin"(U times V)) \
      thin P((1 times X)"cons")(min R)), $
    $"empty"(x,y)$ holding when both are $[]$.]),
  ("", [$Lambda("step"^degree)("thin"(U times V))$ is the list-valued $"unstep"$, and $min R$ is
    $"minlist" R$:
    $ "unstep"([a] cc x, []) = [("del" a, (x,[]))], $
    $ "unstep"([], [b] cc y) = [("ins" b, ([],y))], $
    $ "unstep"([a] cc x, [a] cc y) = [("cpy" a, (x,y))], $
    $ "unstep"([a] cc x, [b] cc y) = $
    $ quad [("del" a, (x, [b] cc y)), ("ins" b, ([a] cc x, y))] quad (a != b). $
    $ "mle" = ("empty" -> "nil", thin "unstep" thin "list"((1 times "mle")"cons")("minlist" R)). $]),
  ("", [It terminates #sym.dash.em $"unstep"$ shortens the combined length #sym.dash.em and runs in
    exponential time, because the same subproblem is met again and again.]),
)

#sub[Tabulation]

#dt(
  ("9.2", [$"mle"(x,y)$ needs $"mle"(u,v)$ for every tail $u$ of $x$ and $v$ of $y$: a grid, one
    column per tail of $y$, one row per tail of $x$. For $x = a_1 a_2 a_3$ and $y = b_1 b_2$:]),
)

#align(center, block(inset: (y: 3pt), table(
  columns: 3, stroke: none, inset: (x: 4pt, y: 1.2pt), align: left,
  $"mle"(a_1 a_2 a_3, b_1 b_2)$, $"mle"(a_1 a_2 a_3, b_2)$, $"mle"(a_1 a_2 a_3, [])$,
  $"mle"(a_2 a_3, b_1 b_2)$, $"mle"(a_2 a_3, b_2)$, $"mle"(a_2 a_3, [])$,
  $"mle"(a_3, b_1 b_2)$, $"mle"(a_3, b_2)$, $"mle"(a_3, [])$,
  $"mle"([], b_1 b_2)$, $"mle"([], b_2)$, $"mle"([], [])$,
)))

#dt(
  ("", [The leftmost column is $"column" x thin y$, the rightmost $"column" x thin []$, and the
    answer is the top of the leftmost. Each entry depends on the one below it (a delete), the one
    to its right (an insert), and the one below that (a copy) #sym.dash.em so the columns can be
    built right to left, each from its neighbour:
    $ "column" x = ⦇"fstcol" x, "nextcol" x⦈, $
    $ "fstcol" = ("list" "del")"tails". $]),
  ("", [Written out, with $m, n$ the lengths of $"mle"(u, [b] cc y)$ and $"mle"([a] cc u, y)$:
    $ "mle"([a] cc u, [b] cc y) = cases(
        ["cpy" a] cc "mle"(u,y) & a = b,
        ["del" a] cc "mle"(u, [b] cc y) & m <= n,
        ["ins" b] cc "mle"([a] cc u, y) & "else.") $]),
  ("", [$"nextcol" x thin (b, "us") = ⦇"base"(b, "last" "us"), "step" b⦈ thin x "us"$ over
    $x "us" = "zip"(x, "zip"("init" "us", "tail" "us"))$, with
    $"base"(b,u) = [["ins" b] cc u]$ (a #emph[different] $"base"$) and
    $ "step" b thin ((a,(u,v)), w s) = $
    $ quad cases(
        [["cpy" a] cc v] cc w s & a = b,
        ["bmin" R(["del" a] cc w, ["ins" b] cc u)] cc w s & "else,") $
    $ quad w = "head" w s. $]),
  ("", [The program carries each sequence as a pair $(v, "length" v)$; $"column" x thin y$ costs $q$
    calls of $"nextcol"$ at $O(p)$ each, so $O(p q)$ #sym.dash.em quadratic.]),
)

== 9.3 Optimal bracketing

#dt(
  ("9.3 ✓", [Bracket $a_1 plus.o dots.c plus.o a_n$ as cheaply as possible.
    $"tree" A ::= "tip" A | "bin"("tree" A, "tree" A)$ and
    $"flatten" = ⦇"wrap", "cat"⦈ : "tree" A -> "list"^+ A$ reads off the tips left to right. Spec: a
    map $"mct" subset Lambda(⦇"wrap","cat"⦈^degree)(min R)$ with
    $R = "cost" "leq" "cost"^degree$.]),
  ("", [The cost of a tip is zero; the cost of a node is a function $"cb"$ of the #emph[sizes] of
    its two subtrees, plus their costs. $"size"$ is not the number of elements:
    $ "cost"("bin"(x,y)) = "cb"("size" x, "size" y) + "cost" x + "cost" y, $
    $ "size"("bin"(x,y)) = "sb"("size" x, "size" y), $
    $ chevron.l "cost", "size" chevron.r = ⦇"opt", "opb"⦈, $
    $ "opt" = chevron.l "zero", "st" chevron.r, $
    $ "opb"((c_x,s_x),(c_y,s_y)) = ("cb"(s_x,s_y) + c_x + c_y, thin "sb"(s_x,s_y)). $]),
  ("", [#rel[$x_1 cc dots.c cc x_n$ on cons-lists: $"cb"(m,n) = m$, $"sb"(m,n) = m+n$,
    $"st" = "length"$. Bracketing to the right is always optimal #sym.dash.em which is why
    $"concat"$ is a cons-list catamorphism.]]),
  ("", [No decomposition is obviously better than another, so there is no thinning step and
    Theorem 9.1 is the target. The one assumption: #emph[size depends only on the atoms, not on
    the bracketing] #sym.dash.em true when $"sb"$ is associative, and then
    $"size" = "flatten" "sz"$ for a map $"sz"$.]),
  ("", [Monotonicity comes from Proposition 9.3 with
    $g = ["zero", (1 times "sz")^2 "opb" thin pi]$:]),
  ("(9.5)", [$F(1 + chevron.l "cost", "flatten" chevron.r^2) g = ["tip","bin"] "cost"$ #sym.dash.em
    $g$ is Proposition 9.3's $k$. Unfold $g$, use $"flatten" "sz" = "size"$, then
    $chevron.l "cost","size" chevron.r = ⦇"opt","opb"⦈$ and $"tip" "cost" = "zero"$.]),
  ("(9.6)", [$(1 + ("leq" times 1)^2) g subset g thin "leq"$ #sym.dash.em from the shape of
    $"opb"$, monotonicity of $+$, and reflexivity of $"leq"$.]),
  ("", [Theorem 9.1 and then Proposition 9.1, $"wrap"$ and $"cat"$ having disjoint ranges:
    $ X = Lambda(["wrap","cat"]^degree) thin P(["tip", (X times X)"bin"]) thin (min R), $
    $ X = ("single" -> "wrap"^degree "tip", \
      thin Lambda("cat"^degree) thin P((X times X)"bin")(min R)). $]),
  ("", [$Lambda("cat"^degree)$ is $"splits" = chevron.l "inits"^+, "tails"^+ chevron.r "zip"$, the
    proper prefixes against the proper suffixes, giving
    $ "mct" = ("single" -> "head" "tip", \
      thin "splits" thin "list"(("mct" times "mct")"bin") thin ("minlist" R)). $
    Both halves of a split are shorter, so it terminates; and it is exponential.]),
)

#sub[Tabulation]

#dt(
  ("9.3", [$"mct" x$ needs $"mct" y$ for every non-empty segment $y$ of $x$: a triangle, held as a
    list of rows. $"array" = "inits" thin "list" "row"$, $"row" = "tails" thin "list" "mct"$,
    $"col" = "inits" thin "list" "mct"$. For $x = a_1 a_2 a_3 a_4$:]),
)

#align(center, block(inset: (y: 3pt), table(
  columns: 4, stroke: none, inset: (x: 4pt, y: 1.2pt), align: left,
  $"mct"(a_1)$, [], [], [],
  $"mct"(a_1 a_2)$, $"mct"(a_2)$, [], [],
  $"mct"(a_1 a_2 a_3)$, $"mct"(a_2 a_3)$, $"mct"(a_3)$, [],
  $"mct"(a_1 a_2 a_3 a_4)$, $"mct"(a_2 a_3 a_4)$, $"mct"(a_3 a_4)$, $"mct"(a_4)$,
)))

#dt(
  ("", [The answer is the bottom of the leftmost column. Three mutual recursions, each got by
    pushing $"list" "mct"$ through the definition of $"inits"$ or $"tails"$:]),
  ("(9.7)", [$"mct" = ("single" -> "head" "tip", chevron.l "init" "col", "tail" "row" chevron.r "mix")$
    with $"mix" = "zip" thin "list" "bin" thin ("minlist" R)$.]),
  ("(9.8)", [$"col" = ("single" -> "head" "tip" "wrap", chevron.l "init" "col", "tail" "row" chevron.r "next")$
    with $"next" = chevron.l pi, "mix" chevron.r "snoc"$, so a column is a loop.]),
  ("(9.9)", [$"cons" "col" = (1 times "array")"process"$ with
    $"process" = (("tip" "wrap") times 1)("loop" "next")$ #sym.dash.em the column of
    $"cons"(a,x)$ by looping $"next"$ over the array of $x$.]),
  ("(9.10)", [$"row" = ("single" -> "head" "tip" "wrap", chevron.l "mct", "tail" "row" chevron.r "cons")$.]),
  ("", [Hence $"array" = ⦇"fstcol", "addcol"⦈$ with $"fstcol" = "tip" "wrap" "wrap"$ and
    $ "addcol" = chevron.l pi thin "tip" "wrap", "step" chevron.r "cons", $
    $ "step" = chevron.l "process" "tail", pi' chevron.r "zip" thin "list" "cons". $]),
  ("", [$"mct" x = ("array" thin "last" thin "head") x$, each node labelled with its cost and size.
    $"addcol"$ runs $n-1$ times and $"step"$ costs $O(m^2)$ on an $m times m$ array, so
    $O(n^3)$.]),
  ("Ex 9.12", [$h$ associative $==> ⦇"wrap","cat"⦈ ⦇g,h⦈ = ⦇g,h⦈$, the left one over trees and the
    right over non-empty lists.]),
  ("Ex 9.13", [$k = (g times "inits" thin "list" h)("loop" f)$ exactly when
    $(1 times "nil")k = pi g$ and
    $(1 times "snoc")k = chevron.l (1 times pi)k, thin pi' thin "snoc" thin h chevron.r f$. This is
    what proves (9.9).]),
)

== 9.4 Data compression

#dt(
  ("9.4 ✓", [Compress by textual substitution: a code element is a character or a pointer back into
    the part already decoded, $"Code" ::= "sym" "Char" | "ptr"("String", "String"^+)$. Snoc-lists
    here. $"decode" = ⦇"nil", "extend"⦈$ is a #emph[partial] map:
    $ "extend"(x, "sym" a) = x cc [a], $
    $ "extend"(x, "ptr"(y,z)) = x cc z, quad (y cc z) "init"^+ (x cc z). $]),
  ("", [$y cc z$ need not be a prefix of $x$, so a pointer may overlap what it produces:
    $"extend"("aba", "ptr"("a","bab")) = "ababab"$. A leading pointer is undefined, since nothing
    precedes it; but $"decode"$ is surjective, so everything can be coded. Compactly, a pointer is
    a pair of lengths: $x times.o (m,0) = x$ and
    $x times.o (m,n+1) = (x cc [x_m]) times.o (m+1,n)$.]),
  ("", [#rel[$"decode"['a', (0,9)] = "aaaaaaaaaa"$ and
    $"decode"['a','a','b',(1,3),'c',(1,2)] = "aababacab"$.]]),
  ("", [$"size" = ⦇"zero", "distr" thin [1 times c, 1 times p] thin "plus"⦈$ counts bytes, $c$ and
    $p$ constants set by the machine. Spec: a map
    $"encode" subset Lambda("decode"^degree)(min R)$ with $R = "size" "leq" "size"^degree$.]),
  ("", [Monotonicity is routine; the thinning is the work. Symbol against pointer cannot be decided
    for general $c, p$, but pointer against pointer can: a pointer consuming more input is better.
    If $w = "extend"(x, "ptr"(y,z)) = "extend"(x', "ptr"(y',z'))$ then $z$ is longer than $z'$
    exactly when $x$ is a prefix of $x'$. So take
    $ Q = F(Pi + Pi, "prefix"), $
    $ F("Code", "String") = 1 + ("String" times "Code"), $
    and Proposition 9.4 asks for $F(Pi+Pi, R) sans("in") subset sans("in") R$ (routine: symbol and
    pointer sizes are constants, so $(Pi + Pi)[c,p] = [c,p]$ — the book prints $d$ for $p$ here)
    and
    $"decode" thin "prefix" subset R thin "decode"$, which follows from
    $"decode" thin "init" subset R thin "decode"$: drop a trailing $"sym" a$, or shorten a trailing
    $"ptr"(y, z cc [a])$ to $"ptr"(y,z)$, or drop it when $z = []$.]),
  ("", [The recursion, with $U = "prefix"$ and $V = Pi + Pi$, then Proposition 9.1 on the disjoint
    ranges of $"nil"$ and $"extend"$:
    $ X = Lambda(["nil","extend"]^degree)("thin"(1 + (U times V))) \
      thin P(["nil", (X times 1)"snoc"])(min R), $
    $ X = ("null" -> "nil", thin Lambda("extend"^degree)("thin"(U times V)) \
      thin P((X times 1)"snoc")(min R)). $]),
  ("", [$Lambda("extend"^degree)("thin"(U times V))$ is $"reduce"$, built on the #emph[longest
    repeated tail]
    $ "lrt" w = min (U times V) \
      {(x,(y,z)) | x cc z = w and (y cc z) "init"^+ w}, $
    $ "reduce"(w cc [a]) = cases([(w, "sym" a), (x, "ptr"(y,z))] & z != [],
        [(w, "sym" a)] & "else,") $
    $ quad (x,(y,z)) = "lrt"(w cc [a]). $]),
  ("", [$"encode" = ("null" -> "nil", thin "reduce" thin "list"(("encode" times 1)"snoc") thin ("minlist" R))$.
    The same subproblem recurs, so a tabulation over the initial segments is called for; the book
    leaves the details, calling them messy.]),
)
