// Bird & de Moor, "Algebra of Programming", chapter 6 "Recursive Programs" (book pp. 137-163),
// mirrored item by item into Freyd's conventions: composition by juxtaposition in DIAGRAM order.
// The dictionary that does the mirroring is printed on the sheet, in Conventions.
//
// A row tagged ✓ has its mirrored statement machine-checked in this repo, under AOP/A6_*.lean;
// the rest are hand-mirrored from the page.  Chapter 6 is the most heavily formalised of the
// book: A6_FixedPoint, A6_GenHylo, A6_WellFound, A6_PolyMembership, A6_ConvFun and the section
// files A6_1_Digits … A6_7 carry most of what is below.
//
// AUDIT — every numbered item of chapter 6, kept or dropped.
//   §6.1  (6.1) kept, with the derivation of `val°` and both programs.
//         Ex 6.1 DROPPED (asks for a justification of a program already printed).
//   §6.2  Theorem 6.1 kept.  (6.2)-(6.5) kept.
//         Ex 6.2 DROPPED (asks where a hypothesis was used).  6.3, 6.4, 6.5 kept.
//         6.6 DROPPED (proof of (6.4)/(6.5)).  6.7, 6.8 kept.
//   §6.3  Theorem 6.2 and Corollary 6.1 kept, with the divide/conquer reading.
//         Ex 6.9 DROPPED (asks for one more example).  6.10 kept.
//   §6.4  both derivations kept, with their fusion conditions and both programs.
//         Ex 6.11 DROPPED (asks why they terminate).
//   §6.5  the non-unique hylomorphism, inductive and well-founded relations, the membership
//         table, Theorem 6.3, Corollaries 6.2 and 6.3, Theorem 6.4 — all kept.
//         Ex 6.12, 6.13, 6.15, 6.16, 6.17, 6.18, 6.19, 6.20, 6.21 kept.
//         6.14 DROPPED (a question with no stated answer).
//   §6.6  (6.6), `ordered`, `ok`, both derivations and both programs kept.
//         Ex 6.22, 6.24, 6.25, 6.30 kept.  6.23 DROPPED (why does it terminate).
//         6.26-6.29 DROPPED (four "repeat the exercise with another `join`" variants).
//   §6.7  the universal property, (6.7), (6.8), the `suffix`/`tails` derivation, subtraction,
//         the rolling rule, (6.9) and both closure algorithms kept.
//         Ex 6.31 DROPPED (justify (6.8)).  6.32-6.37 kept.
//   Nothing is dropped for being false in Rel.
#import "/AOP/bdm.typ": *

= 6 Recursive Programs

== 6.1 Digits of a number

Convert a positive natural to its decimal digits.  The pattern of the whole chapter in one
example: specify a function as a refinement of some relation, discover that the relation solves a
recursion equation, then read the recursion off as a program.

#dt(
  ("6.1", [$"Decimal" ::= "wrap" "Digit"^+ | "snoc"("Decimal", "Digit")$, so
    $(["wrap", "snoc"], "Decimal")$ is the initial algebra of
    $F A = "Digit"^+ + (A times "Digit")$.]),
  ("", [$"val" = ⦇"embed", "op"⦈ : "Decimal" -> "Nat"^+$, with $"embed"$ the inclusion of digits
    and $"op"(n,d) = 10 n + d$.]),
  ("(6.1)", [$"digits" subset "val"^degree$ — a #emph[functional refinement] of $"val"^degree$,
    which is not yet known to be a map.  This is the specification.]),
)

#deriv(
  $"val"^degree$,
  ("=", [definition]),
  $⦇"embed", "op"⦈^degree$,
  ("=", [catamorphisms]),
  $(["wrap", "snoc"]^degree (F "val") ["embed", "op"])^degree$,
  ("=", [converse]),
  $["embed", "op"]^degree (F "val"^degree) ["wrap", "snoc"]$,
  ("=", [definition of $F$]),
  $["embed", "op"]^degree (1 + ("val"^degree times 1)) ["wrap", "snoc"]$,
  ("=", [coproduct]),
  $["embed", "op"]^degree ["wrap", thin ("val"^degree times 1) "snoc"]$,
  ("=", [coproduct]),
  $("embed"^degree "wrap") union ("op"^degree ("val"^degree times 1) "snoc")$,
)

#dt(
  ("6.1 ✓", [So $"val"^degree = ("embed"^degree "wrap") union
    ("op"^degree ("val"^degree times 1) "snoc")$.]),
  ("", [$"op"(n,d) = m <==> n = m "div" 10 and d = m "mod" 10$, so $"op"^degree$ is defined exactly
    for $m >= 10$ and $"embed"^degree$ exactly for $m < 10$: the two branches have disjoint
    domains, and the join becomes a conditional.]),
  ("", [$"val"^degree m = "wrap" m$ if $m < 10$, else $"snoc"("val"^degree (m "div" 10),
    m "mod" 10)$.  The recursion terminates because $m >= 10 ==> m "div" 10 < m$, so
    $"val"^degree$ is a total function and $"digits" = "val"^degree$.]),
  ("", [$"digits" m = [m]$ if $m < 10$, else $"digits"(m "div" 10) cc [m "mod" 10]$ — quadratic,
    because $"snoc"$ on lists is linear.]),
  ("", [With an accumulator, $"digits" m = f(m, [])$ where $f(m,x) = [m] cc x$ if $m < 10$, else
    $f(m "div" 10, [m "mod" 10] cc x)$ — linear, and correct at $0$.]),
)

== 6.2 Least fixed points

#dt(
  ("T 6.1 ✓", [#D("Knaster–Tarski") #Th[$phi$ a monotonic mapping on the arrows $alpha -> beta$
    of a locally complete allegory.  Then $phi X subset X$ and $phi X = X$ have the same least
    solution, written $(mu X : phi X)$; dually $X subset phi X$ and $X = phi X$ have the same
    greatest solution.]]),
  ("", [Proof: $(mu X : phi X) = inter.big {X : phi X subset X}$.  Local completeness is what
    makes that meet exist.]),
  ("", [$sans("in")$ is an isomorphism, so $⦇R⦈$ is the unique — hence both least and greatest —
    solution of $X = sans("in")^degree (F X) R$, and $phi X = sans("in")^degree (F X) R$ is
    monotonic.  Knaster–Tarski then gives:]),
  ("(6.2) ✓", [$⦇R⦈ subset X ⟸ sans("in")^degree (F X) R subset X$.]),
  ("(6.3) ✓", [$X subset ⦇R⦈ ⟸ X subset sans("in")^degree (F X) R$.]),
  ("(6.4) ✓", [#D("fusion, ⊂") $⦇T⦈ subset ⦇R⦈ S ⟸ (F S) T subset R S$.]),
  ("(6.5) ✓", [#D("fusion, ⊃") $⦇R⦈ S subset ⦇T⦈ ⟸ R S subset (F S) T$.  Equality of the two
    hypotheses gives back the catamorphism fusion law of ch. 3.]),
  ("Ex 6.3 ✓", [#D("Kleene") $phi$ #emph[continuous] — it preserves joins of ascending chains —
    then $(mu X : phi X) = union.big {phi^n nothing : 0 <= n}$.]),
  ("Ex 6.4 ✓", [#D("fixed point induction") $(mu X : phi X) subset A ⟸ phi A subset A$; by
    Kleene, $(forall X. thin X subset A ==> phi X subset A)$ suffices too.]),
  ("Ex 6.5", [The least solution of $phi X subset X$ satisfies $phi X = X$ — Lambek's lemma, for
    the containment order read as a category and $phi$ as a functor on it.]),
  ("Ex 6.7 ✓", [$⦇R⦈ subset ⦇S⦈ ⟸ (F ⦇S⦈) R subset (F ⦇S⦈) S$.  It does #emph[not] need
    $R subset S$.]),
  ("Ex 6.8 ✓", [$R$ #D("difunctional") $eq.delta R = R R^degree R$; the difunctional closure of
    $R$ is a least fixed point.]),
)

== 6.3 Hylomorphisms

#dt(
  ("6.3", [A #D("hylomorphism") is a catamorphism after the converse of one, $⦇S⦈^degree ⦇R⦈$ for
    $R : F alpha -> alpha$ and $S : F beta -> beta$.  The initial type $mu F$ is the
    #emph[intermediate data structure]: it is built by $⦇S⦈^degree$ and consumed by $⦇R⦈$, and
    never appears in the answer.]),
  ("T 6.2 ✓", [#D("hylomorphism theorem")
    $ ⦇S⦈^degree ⦇R⦈ = (mu X : S^degree (F X) R). $
    $S^degree$ divides, $F X$ conquers, $R$ combines.]),
  ("", [Proof in two halves: $⦇S⦈^degree ⦇R⦈$ is a fixed point (functors and the two
    catamorphism laws), and it is below every prefixed point — that half goes through division,
    $⦇S⦈^degree ⦇R⦈ subset X <==> ⦇R⦈ subset X slash ⦇S⦈^degree$, which is the standard move for
    least fixed points.]),
  ("C 6.1 ✓", [$F X = G X + H X$, so an $F$-algebra is a pair:
    $⦇S_1,S_2⦈^degree ⦇R_1,R_2⦈ = (mu X : (S_1^degree (G X) R_1) union (S_2^degree (H X) R_2))$.]),
  ("", [$sans("in")$ is an isomorphism and $⦇sans("in")⦈ = 1$, so every catamorphism and every
    converse of one is already a hylomorphism.]),
  ("Ex 6.10 ✓", [Hylomorphisms preserve simplicity: $R$ and $S$ simple $==> ⦇S⦈^degree ⦇R⦈$
    simple.]),
)

== 6.4 Fast exponentiation and modulus

#dt(
  ("6.4", [$"exp" a = ⦇"one", "mult" a⦈ : "Nat" -> "Nat"$ encodes $a^0 = 1$ and
    $a^(b+1) = a times a^b$ — $O(b)$ steps.  Divide and conquer brings it to $O(log b)$.]),
  ("", [$"Bin" = "listl" "Bit"$, $"Bit" = {0,1}$; $"convert" = ⦇"zero", "shift"⦈ : "Bin" ->
    "Nat"$ with $"shift"(n,d) = 2 n + d$ reads a bit sequence as a number.  It is simple.]),
)

#deriv(
  $"exp" a$,
  ("⊇", [$"convert"$ simple, so $"convert"^degree "convert" subset 1$]),
  $"convert"^degree "convert" ("exp" a)$,
  ("=", [fusion, with $"op" a (n,d) = (d = 0 -> n^2, thin a times n^2)$]),
  $"convert"^degree ⦇"one", "op" a⦈$,
  ("=", [Corollary 6.1]),
  $(mu X : ("zero"^degree "one") union ("shift"^degree (X times 1)("op" a)))$,
)

#dt(
  ("6.4 ✓", [The fusion step needs $"zero" ("exp" a) = "one"$ and
    $"shift" ("exp" a) = ("exp" a times 1)("op" a)$.  $"zero"$ and $"shift"$ have disjoint ranges,
    so the join is again a conditional:]),
  ("", [$"exp" a thin b = 1$ if $b = 0$, else $"op" a ("exp" a (b "div" 2), b "mod" 2)$.]),
  ("6.4 ✓", [Same idea for $a "mod" b$: $"mod" b = ⦇"zero", "succ" b⦈$ with
    $"succ" b thin a = (a = b-1 -> 0, thin a+1)$ costs $O(a)$; fusing through $"convert"$ gives
    $ "mod" b supset (mu X : ("zero"^degree "zero") union ("shift"^degree (X times 1)("op" b))) $
    with $"op" b (r,d) = (n >= b -> n - b, thin n)$ and $n = 2r + d$.]),
  ("", [Conditions: $"zero" ("mod" b) = "zero"$ and
    $"shift" ("mod" b) = ("mod" b times 1)("op" b)$.  The program is
    $"mod" b thin a = 0$ if $a = 0$; $"op" b ("mod" b (a "div" 2), 0)$ if $a$ even;
    $"op" b ("mod" b (a "div" 2), 1)$ if $a$ odd — $O(log a)$.]),
)

== 6.5 Unique fixed points

A hylomorphism is the #emph[least] fixed point of its recursion, not necessarily the only one.

#dt(
  ("6.5", [On $"Nat"$ take $X = ⦇"zero", "positive"⦈^degree ⦇"zero", 1⦈$ with $"positive" =
    "succ"^degree "succ"$ the coreflexive on positives.  Both catamorphisms describe the
    coreflexive on $0$, so $X$ is that.  But its recursion
    $X = ("zero"^degree "zero") union ("positive" X)$ also has $X = 1$ as a solution.]),
  ("", [$["zero", "positive"]^degree$ and $["zero", 1]$ are both maps, yet the least solution is
    not even entire.  Simplicity does carry over (Ex 6.10); entireness is what needs a hypothesis,
    and the hypothesis is that a membership relation be #emph[inductive].]),
)

#sub[Inductive and well-founded relations]

#dt(
  ("6.5 ✓", [$R : alpha -> alpha$ is #D("inductive") $eq.delta$ for all $X$,
    $ X slash R subset X ==> Pi subset X. $
    Pointwise: if $(forall c. thin c R a ==> c X b) ==> a X b$ holds for all $a, b$, then $X$
    holds everywhere — exactly a proof by induction over $R$.]),
  ("", [$<$ on $"Nat"$ gives ordinary mathematical induction; $"tail" = "cons"^degree pi'$ gives
    induction over lists.]),
  ("Ex 6.13 ✓", [$S$ inductive and $R R subset S R$ $==>$ $R$ inductive.  Hence $R subset S$ with
    $S$ inductive $==> R$ inductive, and $S$ inductive $<==> S^+$ inductive, where
    $S^+ = (mu X : S union (S X))$.]),
  ("Ex 6.15 ✓", [The meet of two inductive relations is inductive; the join need not be.]),
  ("6.5 ✓", [$R$ is #D("well-founded") $eq.delta$ for all $X$, $X subset R X ==> X = nothing$ —
    no infinite chain $a_0 R a_1 R dots$  Inductive $==>$ well-founded, and the converse holds in
    a Boolean allegory.]),
  ("Ex 6.16 ✓", [$R$ well-founded $==> f R f^degree$ well-founded, for any map $f$.]),
)

#sub[Membership]

#dt(
  ("6.5", [A relator $F$ may carry a #D("membership") arrow $"mem"(F)_alpha : F alpha -> alpha$
    with $a thin "mem" thin x$ exactly when $a$ is an element of $x$.  For the polynomial
    relators, the power relator and the type relators it exists:]),
  ("", [$"mem"("Id") = 1$, #h(0.5em) $"mem"(K_beta) = nothing$, #h(0.5em)
    $"mem"(F + G) = ["mem"(F), "mem"(G)]$.]),
  ("", [$"mem"(F times G) = (pi thin "mem"(F)) union (pi' thin "mem"(G))$, #h(0.5em)
    $"mem"(F compose G) = "mem"(F) thin "mem"(G)$, #h(0.5em) $"mem"([dot]) = eps$.]),
  ("", [Type relators, via sets: $"mem"(T) = "setify"(T) eps$ with
    $"setify"(T) = Lambda("mem"(T))$ — Ex 6.17 gives a set-free alternative.]),
  ("", [$"mem"$ is a lax natural transformation $1 arrow.hook F$, that is
    $(F R) "mem" subset "mem" R$, and it is the #emph[largest] one of that type — so a membership
    relation, if it exists, is unique.]),
  ("6.5 ✓", [The result the section is for: $sans("in")^degree "mem"(F)$ is inductive.  It is the
    immediate-subterm relation.]),
  ("", [$"Nat"$, $F X = 1 + X$: $"mem" = [nothing, 1]$ and
    $["zero","succ"]^degree [nothing, 1] = "succ"^degree$ is inductive; $< thin = "pred"^+$ with
    $"pred" = "succ"^degree$, which is what made §6.1's recursion terminate.]),
  ("", [Lists: $"mem" = [nothing, pi']$ and $["nil","cons"]^degree [nothing, pi'] = "cons"^degree
    pi' = "tail"$ is inductive, so proper suffix $"tail"^+$ is; on snoc-lists $"init"$ and proper
    prefix are.]),
)

#sub[Unique solutions]

#dt(
  ("T 6.3 ✓", [#Th[$S thin "mem"(F)$ inductive $==>$ $X = S (F X) R$ has a unique solution
    $phi(R,S)$, and $phi(R,S)$ is entire if $R$ and $S$ are.]  With $S := S^degree$ this is the
    hylomorphism of §6.3, now pinned down as the #emph[only] fixed point.]),
  ("C 6.2 ✓", [$g thin "mem"(F)$ inductive $==>$ the unique solution of $X = g (F X) f$ is a map
    ($X = ⦇g^degree⦈^degree ⦇f⦈$ is entire by the theorem and simple by Ex 6.10).]),
  ("C 6.3 ✓", [$R^degree "mem"(F)$ inductive $==>$ $⦇R⦈$ is surjective when $R$ is
    ($R$ surjective $eq.delta 1 subset R^degree R$, i.e. $"ran" R = 1$).]),
  ("T 6.4 ✓", [#Th[$R$ surjective and $R f subset (F f) sans("in")$ $==>$ $f^degree = ⦇R⦈$.]
    This is the theorem §5.6 borrowed to show $"partition" = "concat"^degree$ is a
    catamorphism.]),
  ("Ex 6.12 ✓", [$R$ inductive $<==>$ $X = X slash R$ has a unique solution.]),
  ("Ex 6.17", [$"inlist" : "list"^+ alpha -> alpha$ is a catamorphism, but $"inlist"$ on
    $"list" alpha$ is not; instead $"inlist" = "tail"^* "head"$.  The same trick defines
    $"intree"$.]),
  ("Ex 6.18", [The formal definition: $"mem"$ is a membership relation for $F$ if
    $(1 slash "mem")(F R) = R slash "mem"$ for all $R$; equivalently
    $(S slash "mem")(F R) = (S R) slash "mem"$ for all $R, S$.]),
  ("Ex 6.20", [$"mem"(G) slash "mem"(F)$ is the largest lax natural transformation
    $F arrow.hook G$.]),
  ("Ex 6.21", [In a Boolean allegory, $"mem"(F)$ is entire $<==> F nothing = nothing$.]),
)

== 6.6 Sorting by selection

#dt(
  ("(6.6) ✓", [$"sort" subset "perm" ("ordered")$, for $R$ a #emph[connected] preorder
    ($R union R^degree = Pi$).  A connected preorder need not be anti-symmetric, so $"sort"$ is
    genuinely a refinement, not an equality.]),
  ("", [$"ordered" = ⦇"nil", "ok" thin "cons"⦈$, where the coreflexive $"ok"$ holds at $(a,x)$
    when $(forall b : b thin "inlist" thin x : a R b)$ — rebuild the list, checking at each step
    that only $R$-smaller elements go in front.  ($"ok"(a,x) = (x = [] or a R ("head" x))$ also
    works but is less useful here.)]),
)

#sub[Selection sort]

#deriv(
  $"perm" ("ordered")$,
  ("=", [$"perm" = "perm"^degree$ and $"ordered" = "ordered"^degree$]),
  $("ordered" thin "perm")^degree$,
  ("=", [$"ordered" = ⦇"nil", "ok" thin "cons"⦈$]),
  $(⦇"nil", "ok" thin "cons"⦈ "perm")^degree$,
  ("⊇", [fusion, for a suitable $"select"$]),
  $⦇"nil", "select"^degree⦈^degree$,
)

#dt(
  ("6.6", [The fusion proviso is $"ok" thin "cons" thin "perm" supset (1 times "perm")
    "select"^degree$, and $"select"$ is found by calculating:]),
)

#deriv(
  $"ok" thin "cons" thin "perm"$,
  ("=", [$"perm" = ⦇"nil", "cons" thin "perm"⦈$ (§5.6)]),
  $"ok" (1 times "perm") "cons" thin "perm"$,
  ("=", [$(1 times "perm")"ok" = "ok"(1 times "perm")$, Ex 6.22]),
  $(1 times "perm") "ok" thin "cons" thin "perm"$,
  ("⊇", [specifying $"select" subset "perm" thin "cons"^degree "ok"$]),
  $(1 times "perm") "select"^degree$,
)

#dt(
  ("6.6", [In words: $(a,y) = "select" x$ means $[a] cc y$ is a permutation of $x$ with $a R b$
    for every $b$ in $y$.  It is undefined on $[]$, so take
    $"select" = "embed" ⦇"base", "step"⦈$ with
    $"embed" : "list" alpha -> "list"^+ alpha$.]),
  ("", [Fusion conditions: $"base" subset "wrap" thin "perm" thin "cons"^degree "ok"$ and
    $(1 times ("cons"^degree "ok")) "step" subset "cons" thin "perm" thin "cons"^degree "ok"$,
    satisfied by
    $"base" a = (a, [])$ and $"step"(a,(b,x)) = (a, [b] cc x)$ if $a R b$, else $(b, [a] cc x)$.]),
  ("6.6 ✓", [The hylomorphism theorem then makes $X = ⦇"nil", "select"^degree⦈^degree$ the unique
    solution of $X = ("nil"^degree "nil") union ("select" (1 times X) "cons")$, i.e.
    $"sort" x = []$ if $x = []$, else $[a] cc "sort" y$ where $(a,y) = "select" x$.]),
)

#sub[Quicksort]

#dt(
  ("6.6", [Same shape, with a tree as the intermediate datatype:
    $"tree" alpha ::= "null" | "fork"("tree" alpha, alpha, "tree" alpha)$ and
    $"flatten" = ⦇"nil", "join"⦈$, $"join"(x,a,y) = x cc [a] cc y$.]),
)

#deriv(
  $"perm" ("ordered")$,
  ("⊇", [$"flatten"$ a map, so $"flatten"^degree "flatten" subset 1$]),
  $"perm" thin "flatten"^degree "flatten" thin "ordered"$,
  ("=", [claim: $"flatten" thin "ordered" = "inordered" thin "flatten"$]),
  $"perm" thin "flatten"^degree "inordered" thin "flatten"$,
  ("=", [converses]),
  $("inordered" thin "flatten" thin "perm")^degree "flatten"$,
  ("⊇", [fusion, for a suitable $"split"$]),
  $⦇"nil", "split"^degree⦈^degree "flatten"$,
)

#dt(
  ("6.6", [$"inordered" = ⦇"null", "check" thin "fork"⦈$, with $"check"$ holding at $(x,a,y)$ when
    $(forall b : b thin "intree" thin x ==> b R a)$ and
    $(forall b : b thin "intree" thin y ==> a R b)$; $"check"'$ is the same with $"inlist"$ for
    $"intree"$.  Writing $F f = f times 1 times f$, the proviso is
    $F("flatten" thin "perm") "split"^degree subset "check" thin "fork" thin "flatten" thin "perm"$.]),
  ("", [Discharged by taking $"split" subset "perm" thin "join"^degree "check"'$, i.e.
    $(y,a,z) = "split" x$ means $y cc [a] cc z$ is a permutation of $x$ with $b R a$ throughout
    $y$ and $a R b$ throughout $z$.]),
  ("", [$"split" = "embed" ⦇"base", "step"⦈$ with
    $"base" subset "wrap" thin "perm" thin "join"^degree "check"'$ and
    $(1 times ("join"^degree "check"')) "step" subset "cons" thin "perm" thin "join"^degree
    "check"'$ #text(size: 0.9em)[(the book prints $"split"$ for $"step"$ here, and drops the
    $degree$ on $"join"$)], satisfied by $"base" a = ([], a, [])$ and
    $"step"(a,(x,b,y)) = ([a] cc x, b, y)$ if $a R b$, else $(x, b, [a] cc y)$.]),
  ("6.6", [$X = ⦇"nil", "split"^degree⦈^degree "flatten"$ is the least solution of
    $X = ("nil"^degree "nil") union ("split"(X times 1 times X)"join")$, i.e.
    $"sort" x = []$ if $x = []$, else $"sort" y cc [a] cc "sort" z$ where
    $(y,a,z) = "split" x$.]),
  ("Ex 6.22", [$"inlist" = "perm" thin "inlist"$; hence a point-free $"ok"$ and
    $(1 times "perm")"ok" = "ok"(1 times "perm")$.]),
  ("Ex 6.24", [$"ordered"(R) thin "ordered"(S) = "ordered"(R inter S)$.]),
  ("Ex 6.25", [Sorting a #emph[set]: $"sort" subset "setify"^degree "ordered"(R)$ is the wrong
    specification, $"sort" subset "setify"^degree "ordered"(R inter "neq")$ the right one, where
    $a thin "neq" thin b$ iff $a eq.not b$.]),
  ("Ex 6.30", [From $"perm" = ⦇"nil", "add"⦈$ instead, fusion gives
    $"perm"("ordered") = ⦇"nil", "add" thin "ordered"⦈ supset ⦇"nil", "insert"⦈$ for a suitable
    map $"insert"$ with $(1 times "ordered")"insert" subset "add" thin "ordered"$ — insertion
    sort.]),
)

== 6.7 Closure

#dt(
  ("6.7 ✓", [$R^*$, the #D("reflexive transitive closure"), is the smallest preorder containing
    $R$: $ R subset X <==> R^* subset X quad "for every preorder" X. $]),
  ("(6.7) ✓", [$R^* = (mu X : 1 union (R X))$.]),
  ("(6.8) ✓", [$R^* = (mu X : 1 union (X R))$.  That $S = (mu X : 1 union (R X))$ is reflexive and
    contains $R$ is immediate; transitivity goes through division, the same move as
    Theorem 6.2.]),
  ("Ex 6.32 ✓", [$S R^* = (mu X : S union (X R))$, #h(0.5em) $R S^* = (mu X : R union (X S))$,
    #h(0.5em) $S^* R = (mu X : R union (S X))$.]),
  ("Ex 6.33", [$R^* = ⦇[1,1]⦈^degree ⦇[1,R]⦈$, the intermediate datatype being
    $"iterate" alpha ::= "once" alpha | "again"("iterate" alpha)$.]),
  ("Ex 6.34", [$R^* = "chainR"^degree "head"$ for a catamorphism $"chainR"$ on non-empty lists.]),
  ("Ex 6.36", [$(R union S)^* = (R^* S)^* R^*$, by the diagonal rule.]),
  ("Ex 6.37", [$C R = C ==> R^* = (tld C thin R)^*$, for $C$ coreflexive.]),
)

#sub[When the recursion has a unique solution]

#dt(
  ("6.7", [$X = 1 union (R X)$ has a unique solution — necessarily $R^*$ — exactly when $R$ is
    inductive.  $"tail"$ is inductive, so $"suffix" = 1 union ("tail" thin "suffix")$ pins
    $"suffix"$ down, and transposing gives
    $Lambda "suffix" = chevron.l tau, Lambda("tail" thin "suffix") chevron.r "cup"$.]),
  ("", [$"tail"$ is undefined on $[]$, so a case analysis splits it:
    $(Lambda "suffix")[] = {[]}$ and
    $(Lambda "suffix")([a] cc x) = {[a] cc x} union (Lambda "suffix") x$ — sets as lists, and this
    is §5.6's $"tails" [] = [[]]$, $"tails"([a] cc x) = [[a] cc x] cc "tails" x$.]),
)

#sub[Computing a closure that is not a unique fixed point]

#dt(
  ("6.7", [#D("subtraction") (Ex 4.30) $R minus S subset T <==> R subset S union T$; hence
    $R minus nothing = R$, $R union S = R union (S minus R)$,
    $R minus (S union T) = R minus S minus T$ and
    $(R union S) minus T = (R minus T) union (S minus T)$.]),
  ("Ex 6.35 ✓", [#D("μ-calculus") the two defining rules are $phi(mu X : phi X) = (mu X : phi X)$
    and $phi Y subset Y ==> (mu X : phi X) subset Y$.  From them:
    #h(0.5em) #emph[rolling] $(mu X : phi(psi X)) = phi(mu X : psi(phi X))$,
    #h(0.5em) #emph[diagonal] $(mu X : mu Y : phi(X,Y)) = (mu X : phi(X,X))$,
    #h(0.5em) #emph[substitution] $(mu X : phi(mu Y : psi(X,Y))) = (mu X : psi(phi X, X))$.]),
  ("(6.9)", [$theta(P,Q) eq.delta P union (mu X : Q union ((X R) minus P))$, which satisfies
    $ theta(nothing, S) = S R^*, quad theta(P, nothing) = P, $
    $ theta(P,Q) = theta(P union Q, thin (Q R) minus P minus Q). $
    The third comes out of the rolling rule and the subtraction laws.]),
  ("", [Read as a program: compute $theta(nothing, S)$, where
    $theta(P,Q) = P$ if $Q = nothing$, else $theta(P union Q, (Q R) minus P minus Q)$.  It
    terminates only if $S R^*$ is finite; then $P$ grows at every step.]),
  ("", [Relations as data are awkward, so apply $Lambda$ throughout: with $p = Lambda P$,
    $q = Lambda Q$, $s = Lambda S$ and $Lambda(S R^*) = (Lambda S)(E R^*)$,
    $ "close"(p, nothing) = p, $
    $ "close"(p,q) = "close"(p union q, thin (E R) q minus p minus q), $
    now with set union and set difference.  This is how $E(R^*)$ is computed whenever the answer
    is known to be finite — reachability in a graph.]),
)
