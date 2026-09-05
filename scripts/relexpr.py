"""relexpr — the note's relation notation, parsed and printed.  Neither convention's, so neither
convention owns it.

`diag/allegory-axioms.typ` writes one relation language — diagram order, juxtaposition for
composition, `°`, `F(R)`, `𝟙`, `[x,y]`, `⟨x,y⟩`, `x∪y` — and BOTH generators read it: `scripts/
circuit` to lay out a circuit (a wire is an object, a box a morphism), `scripts/diagram` and
`scripts/scanline` to lay out and sweep a Hinze–Marsden panel (a wire is a functor, a bead an
arrow).  The two pictures share nothing else, so this file is the one place the language lives:
`scripts/circuit` used to load the whole 1100-line panel sweep to get `parse`.

    ('atom', s) | ('comp', [e…]) | ('prod', [e…]) | ('hc', [e…]) | ('conv', e) | ('app', name, e[, s])
    ('union', [e…], s) | ('case', [e…], s) | ('fork', [e…], s)

`spell` is the inverse of `parse` in the note's own spelling; `norm` is the normal form two
spellings of one arrow are compared in.  `opt`/`help_if` are here for the same reason: every
script that reads this language has the same two flags.
"""
import json, os, re, sys

# A unit's source is `Id`: it contains no object wire, so the bead may not sit on one.
UNIT = "𝟙"
# The terminal object, which is the summand a non-recursive branch — `nil`, `zero` — collapses `F` to.
TERM = "𝟏"

# ---------------------------------------------------------------- expressions
# ('atom', s) | ('comp', [e…]) | ('prod', [e…]) | ('hc', [e…]) | ('conv', e) | ('app', name, e[, s])
# ('union', [e…], s) | ('case', [e…], s) | ('fork', [e…], s) — `x∪y`, `[x,y]`, `⟨x,y⟩`; the
# trailing `s` is the note's own spelling, kept because one bracket spaces `(𝟙×list(p))π₂` and
# `(p×list(p)) cons` differently.
# `hc` is the ACROSS composite `s∘t`, leftmost outermost: a factor beside the wires that pass it.
OPENERS, CLOSERS = "([⟨⦇{", ")]⟩⦈}"
BREAK = OPENERS + CLOSERS + "×° \t"
# `[0,2¹⁶)` is an OBJECT NAME (§16's machine words), one token whose `[` closes with a `)`: the
# bracket walk would pair that `)` with the wrong opener, so the name is matched before it runs.
INTERVAL = re.compile(r"\[[^\[\]()]*\)")
# A projection ends its own token: the note writes the guard of a conditional `π₁p`, with nothing
# between the two arrows, and one bead reading `π₁p` is a composite drawn as though it were an atom.
PROJ = ("π₁", "π₂")
# An index is written as a SMALL CAPITAL — the subscript block has no `b` and no `c`, so one family
# (`αᴀ`, `αʙ`, `αᴄ`) cannot be spelled with real subscripts at all.
SMALLCAP = dict(zip("ᴀʙᴄᴅᴇꜰɢʜɪᴊᴋʟᴍɴᴏᴘꞯʀꜱᴛᴜᴠᴡʏᴢ", "ABCDEFGHIJKLMNOPQRSTUVWYZ"))
# A fold that writes its carrier: `⦇αᴀ⦈`.  The body is bracket-free, so the index is the small-capital
# run just inside the closing banana.
CARRIER = re.compile("⦇([^⦇⦈]*?)([" + "".join(SMALLCAP) + "]+)⦈")


def deindex(s):
    """`s` with every fold's carrier index stripped, and a map from the stripped label to what it
    dropped: `⦇αᴀ⦈` is drawn `⦇α⦈` at carrier `A`.  A bead's index IS the object wire under it, so a
    carrier written in the label as well spells one object twice and the two are free to drift."""
    idx = {}

    def one(m):
        lab = f"⦇{m.group(1)}⦈"
        idx[lab] = "".join(SMALLCAP[c] for c in m.group(2))
        return lab
    return CARRIER.sub(one, s), idx


def matching(s, i):
    c, d, j = CLOSERS[OPENERS.index(s[i])], 0, i
    while j < len(s):
        m = j > i and INTERVAL.match(s, j)
        if m:
            j = m.end(); continue
        d += (s[j] == s[i]) - (s[j] == c)
        if d == 0:
            return j
        j += 1
    raise ValueError(f"unbalanced {s[i]} in {s!r}")


def split_top(s, sep):
    """`s` cut at the `sep`s no bracket encloses."""
    out, last, i = [], 0, 0
    while i < len(s):
        m = INTERVAL.match(s, i)
        if m:
            i = m.end() - 1
        elif s[i] in OPENERS:
            i = matching(s, i)
        elif s[i] == sep:
            out.append(s[last:i]); last = i + 1
        i += 1
    return out + [s[last:]]


def squeeze(s):
    """A source slice as the note spells it: runs of whitespace collapsed, single spaces kept."""
    return ' '.join(s.split())


def parse(s, obj=False):
    """Juxtaposition, `×`, `∘`, `∪`, `∩`, postfix `°`, `N(e)`, `[x,y]`, `⦇x⦈`, `(g→x,y)`; anything
    else bracketed rides through as one atom.  `∘` binds loosest — `η∘M μ` is `η` beside the `M`
    wire, then `μ` — so the note brackets it — then `∪`, then `∩`, then juxtaposition: `a b ∪ c∩d`
    is `(a b)∪(c∩d)`, which is the lattice's own precedence."""
    hs = split_top(s, '∘')
    if len(hs) > 1:
        return ('hc', [parse(h, obj) for h in hs])
    us = split_top(s, '∪')
    if len(us) > 1:
        # The `∪` always gets a space on each side; the operands keep the source's own spacing,
        # which `spell` would renormalise (`(p×𝟙) cons` → `(p×𝟙)cons`).
        return ('union', [parse(u, obj) for u in us], ' ∪ '.join(squeeze(u) for u in us))
    ms = split_top(s, '∩')
    if len(ms) > 1:
        return ('cap', [parse(m, obj) for m in ms], squeeze(s))
    xs, i = [], 0
    while i < len(s):
        if s[i] in " \t":
            i += 1; continue
        x, i = p_prod(s, i, obj)
        xs.append(x)
    if not xs:
        raise ValueError(f"empty expression {s!r}")
    return xs[0] if len(xs) == 1 else ('comp', xs)


def p_prod(s, i, obj=False):
    xs = []
    while True:
        x, i = p_prim(s, i, obj)
        while i < len(s) and s[i] == '°':
            x, i = ('conv', x), i + 1
        xs.append(x)
        if i >= len(s) or s[i] != '×':
            return (xs[0] if len(xs) == 1 else ('prod', xs)), i
        i += 1


def p_prim(s, i, obj=False):
    while i < len(s) and s[i] in " \t":
        i += 1
    if i >= len(s):
        raise ValueError(f"expected a term at the end of {s!r}")
    m = INTERVAL.match(s, i)
    if m:
        return ('atom', m.group()), m.end()
    if s[i] in OPENERS:
        j = matching(s, i)
        # A division is ONE token, `x%∋`, whether or not `x` is bracketed: that is how the note's
        # `plain` spells `frac(x, ∋)`, so `⦇S⦈%∋` must not read as `⦇S⦈` beside a stray `%∋`.
        # Checked before the `(` case, or a composite numerator `(prefix list(p))%∋` loses its `%∋`.
        if s[j + 1:j + 3] == '%∋':
            return ('atom', squeeze(s[i:j + 3])), j + 3
        if s[i] == '(':
            # `(g→x,y)`: guarded branches, then an optional default.  The operands stay FLAT in
            # source order — guard, body, …, default — so a walk maps over them like any other list.
            bs = split_top(s[i + 1:j], ',')
            gs = [x for b in bs for x in split_top(b, '→')]
            if len(gs) > len(bs):
                return ('cond', [parse(g, obj) for g in gs], squeeze(s[i:j + 1])), j + 1
            return parse(s[i + 1:j], obj), j + 1
        if s[i] == '⦇':
            return ('cata', [parse(s[i + 1:j], obj)], squeeze(s[i:j + 1])), j + 1
        bs = split_top(s[i + 1:j], ',')
        if s[i] == '[' and len(bs) > 1:
            return ('case', [parse(b, obj) for b in bs], squeeze(s[i:j + 1])), j + 1
        if s[i] == '⟨' and len(bs) > 1:
            # A fork of FUNCTORS is itself a functor and can be APPLIED: `⟨𝟙,T⟩(A)` is the object
            # `(A,TA)` of `𝒜×𝒜`, which is ONE wire, and §11.5.1's `F(A,TA)` is `F` over it.  So a
            # bracket followed by `(` is the lane's NAME, not a fork of arrows.
            if j + 1 < len(s) and s[j + 1] == '(':
                k = matching(s, j + 1)
                return ('app', s[i:j + 1], parse(s[j + 2:k], obj), s[i:j + 1] + '(−)'), k + 1
            return ('fork', [parse(b, obj) for b in bs], squeeze(s[i:j + 1])), j + 1
        return ('atom', squeeze(s[i:j + 1])), j + 1
    for q in PROJ:
        if s.startswith(q, i):
            # A projection is the one token that returns early, so it must take a trailing `%∋`
            # with it just as the bracket branch does; otherwise `π₂%∋` orphans an empty numerator.
            if s[i + len(q):i + len(q) + 2] == '%∋':
                return ('atom', q + '%∋'), i + len(q) + 2
            return ('atom', q), i + len(q)
    j = i
    while j < len(s) and s[j] not in BREAK:
        j += 1
    if j == i:
        raise ValueError(f"stray {s[i]!r} in {s!r}")
    if j < len(s) and s[j] == '(':
        k = matching(s, j)
        # `F(X)` abbreviates `F(𝟙,X)` (the note's own `== Type relator` definition), so ONE live slot
        # parses as an application with a context saying which; `F(∋,∋)` stays one opaque bead.
        # In an OBJECT every slot is an object, so `𝟙` cannot mark the live one: there the LAST
        # slot is the wire and the rest is context, which makes `F(A,E B)` the lane `F(A,−)`.
        bs = [b.strip() for b in split_top(s[j + 1:k], ',')]
        hs = [len(bs) - 1] if obj else [n for n, b in enumerate(bs) if b != UNIT]
        if len(bs) > 1 and len(hs) == 1:
            ctx = s[i:j] + '(' + ','.join('−' if n == hs[0] else b for n, b in enumerate(bs)) + ')'
            return ('app', s[i:j], parse(bs[hs[0]], obj), ctx), k + 1
        return ('app', s[i:j], parse(s[j + 1:k], obj)), k + 1
    if j < len(s) and s[j] == '[':
        # `[A]` is a name, so `E[A]` is an application spelled without parentheses; the argument
        # keeps its brackets so the AST is exactly the one `E([A])` builds.
        k = matching(s, j)
        return ('app', s[i:j], parse(s[j:k + 1], obj), s[i:j] + '−'), k + 1
    return ('atom', s[i:j]), j


def hole_last(ctx):
    """Whether an `app` context acts in its LAST argument slot: `F(𝟙,−)`, `E−` and `thin −` do,
    `F(−,𝟙)` does not.  A lane passes the last slot, so only that one reads as a wire."""
    return ctx.rstrip(')').endswith('−')


def unit_ctx(ctx):
    """A context whose non-hole slots are all `𝟙`, so it says nothing the bare application does
    not: `F(𝟙,−)` and `E−` do, `F(A,−)` does not — that one names the object its lane carries."""
    if '(' not in ctx:
        return True
    return all(b.strip() in ('−', UNIT)
               for b in split_top(ctx[ctx.index('(') + 1:ctx.rindex(')')], ','))


def hole_slot(ctx):
    """Which argument slot of an `app` context the hole sits in, and how many slots there are."""
    bs = [b.strip() for b in split_top(ctx[ctx.index('(') + 1:ctx.rindex(')')], ',')]
    return bs.index('−') + 1, len(bs)


def require_hole_last(e):
    """Every consumer reads an `app`'s `e[2]` as the LAST slot's argument, so a hole anywhere else
    is drawn in the wrong slot: refused here once, for all of them, rather than in each."""
    if e[0] == 'app' and len(e) > 3 and not hole_last(e[3]):
        i, n = hole_slot(e[3])
        raise Unhandled(f"{spell(e)} acts in slot {i} of {n} of {e[1]}; a lane passes only the last"
                        f" slot, so write {e[1]} with {spell(e[2])} in slot {n}")


def spell(e):
    """The note's own spelling.  A juxtaposition needs no space where a bracket already separates."""
    k = e[0]
    if k == 'atom':
        return e[1]
    if k in ('union', 'case', 'cap', 'cond', 'cata', 'fork'):
        return e[2]
    if k == 'app':      # a context — `E−`, `thin −`, `F(𝟙,−)` — spells by filling its own hole, so
        # the spelling cannot go stale when `rec` rewrites what is inside it (`F(𝟙,R)°` → `F(𝟙,R°)`).
        return e[3].replace('−', spell(e[2])) if len(e) > 3 else f"{e[1]}({spell(e[2])})"
    if k == 'conv':
        return (f"({spell(e[1])})" if e[1][0] in ('comp', 'prod', 'union', 'cap')
                else spell(e[1])) + '°'
    if k == 'prod':
        # A sum reaches here as one atom, its parentheses eaten by the parser; × binds tighter, so
        # re-parenthesise it or `prefix°×(⊤+⊤)` writes back as `prefix°×⊤+⊤`, which is a different relation.
        return '×'.join(f"({spell(x)})" if x[0] in ('comp', 'hc', 'union', 'cap')
                        or (x[0] == 'atom' and '+' in x[1]) else spell(x)
                        for x in e[1])
    if k == 'hc':
        return '∘'.join(f"({spell(x)})" if x[0] in ('comp', 'prod') else spell(x) for x in e[1])
    # A cap or union reaches here as one atom, its parentheses eaten by the parser; juxtaposition
    # binds tighter, so re-bracket it or `old (R∩H)` writes back as `old R∩H` = `(old R)∩H`.
    ps = [f"({spell(x)})" if x[0] in ('prod', 'hc', 'union', 'cap')
          or (x[0] == 'atom' and any(len(split_top(x[1], o)) > 1 for o in '∩∪'))
          else spell(x) for x in e[1]]
    out = ps[0]
    for p in ps[1:]:
        # A factor opening with `(` keeps its space: `pick (schedule×𝟙)snoc` closed up reads as an
        # application of `pick`.  The other openers (`⦇`, `[`, `⟨`) cannot, so they still close up.
        out += ('' if out[-1] in CLOSERS or (p[0] in OPENERS and p[0] != '(') else ' ') + p
    return out


def tidy(e):
    """`R°×R°` is printed `(R×R)°`: one converse the reader undoes once, not twice."""
    e = rec(e, tidy)
    if e[0] == 'prod' and all(x[0] == 'conv' for x in e[1]):
        return ('conv', ('prod', [x[1] for x in e[1]]))
    return e


def rec(e, f):
    if e[0] in ('comp', 'prod', 'hc'):
        return (e[0], [f(x) for x in e[1]])
    if e[0] == 'conv':
        return ('conv', f(e[1]))
    # The context tail travels with the node: `f` rewrites what sits in the hole, and only a context
    # — never a finished spelling — survives that.
    return ('app', e[1], f(e[2])) + e[3:] if e[0] == 'app' else e


def listable(e):
    """Whether `[X]` reads back as `list(X)`.  A `,` inside the bracket opens a case and a `∪` a
    union, so those nodes — and an atom whose own text carries either — swallow the bracket.  It is
    the TOP-LEVEL separator that swallows it: the `,` of the object name `[0,2¹⁶)` is inside the
    name's own brackets, so `[[0,2¹⁶)]` is still a list."""
    if e[0] == 'atom':
        return len(split_top(e[1], ',')) == 1 and len(split_top(e[1], '∪')) == 1
    if e[0] in ('comp', 'prod', 'hc'):
        return all(listable(x) for x in e[1])
    if e[0] == 'conv':
        return listable(e[1])
    return listable(e[2]) if e[0] == 'app' else False


def dun(e):
    """`R%∋=𝟙%∋ E(R)`, the note's own `DUN` (`Λ R = singletonMap ≫ existsImage R`, `AOP/A4_6.lean`):
    ONE fraction the display writes, TWO beads the picture draws — the unit opens `E` outside `R`.
    Guarded at `𝟙`, the rewrite's own fixed point, which would otherwise regress for ever."""
    if e[0] != 'atom' or not e[1].endswith('%∋') or e[1][:-2] == UNIT:
        return None
    return ('comp', [('atom', UNIT + '%∋'), ('app', 'E', parse(e[1][:-2]))])


def norm(e):
    """The confluent rewrite comparison runs on: `°` pushed to the atoms, `Δ(R)=R×R`, `𝟙` dropped,
    `[A]=list(A)`, juxtaposition and `×` flat.  `F(R°)=F(R)°`, `F(R)F(S)=F(RS)` and `dun`'s
    `R%∋=𝟙%∋ E(R)` are laws applied on trust.  `P` keeps its own head here — `quot` is what
    identifies it with `E`, and only where two readings are COMPARED."""
    # One bead on the sweep side, so the comparison form stays the atom these were before the parser
    # could read them — `cond` alone gains its brackets, and no certified string carries a `→`.
    if e[0] in ('cap', 'cond', 'cata', 'fork'):
        return ('atom', e[2])
    e = rec(e, norm)
    # A hole-LAST context is only a spelling — `F(𝟙,R)` is the picture `F(R)` — so it goes and every
    # `F(`-bearing certificate compares equal; a hole-first one stays, so `F(∋,𝟙)F(𝟙,∋)` cannot fuse.
    if e[0] == 'app' and len(e) > 3 and hole_last(e[3]) and unit_ctx(e[3]):
        e = ('app', e[1], e[2])
    d = dun(e)
    if d is not None:
        return norm(d)
    if e[0] == 'conv':
        b = e[1]
        if b[0] == 'comp':
            return norm(('comp', [('conv', x) for x in reversed(b[1])]))
        if b[0] == 'prod':
            return norm(('prod', [('conv', x) for x in b[1]]))
        if b[0] == 'app':
            return norm(('app', b[1], ('conv', b[2])) + b[3:])
        if b[0] == 'conv':
            return b[1]
    if e[0] == 'app' and e[1] == 'Δ':
        return ('prod', [e[2], e[2]])
    if e[0] == 'atom' and e[1].startswith('[') and e[1].endswith(']'):
        inner = parse(e[1][1:-1])
        if listable(inner):
            return ('app', 'list', norm(inner))
    if e[0] in ('comp', 'prod', 'hc'):
        xs = [y for x in e[1] for y in (x[1] if x[0] == e[0] else [x])]
        if e[0] == 'comp':
            xs = [x for x in xs if x != ('atom', UNIT)] or [('atom', UNIT)]
            xs = fuse(interchange(xs))
        return xs[0] if len(xs) == 1 else (e[0], xs)
    return e


# The relators one wire draws: `P A = E A`, so a lane labelled either carries the same object and a
# panel may name it either way.  They differ as RELATIONS — B&dM p.119 symmetrises `P`'s second
# conjunct, and only on maps do they agree (p.202) — so the panel keeps the letter it was drawn with
# and the quotient is taken at the comparison alone.
# Declared in `diag/hm-sigs.json`, beside the signatures, because which two letters draw one lane is
# a fact about the NOTE, not about the sweep.
SIGS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "diag",
                    "hm-sigs.json")
_ALIAS = None


def alias():
    global _ALIAS
    if _ALIAS is None:
        _ALIAS = json.load(open(SIGS, encoding="utf-8")).get("alias", {})
    return _ALIAS


def canon(e):
    """One head for every wire that draws the same lane, `P(R)` read as `E(R)`.  Runs BEFORE `norm`,
    whose `fuse` merges two applications only when their heads already agree."""
    a = alias()
    return rec(('app', a[e[1]], e[2]) + e[3:], canon) if e[0] == 'app' and e[1] in a \
        else rec(e, canon)


def quot(e):
    """The form two readings are held against: normalised, with the aliased relators identified."""
    return norm(canon(e))


def interchange(xs):
    """`(a×b)(c×d)=(ac)×(bd)`: the picture reads two products at two heights, the display writes
    them at one, so both sides normalise to the merged form."""
    out = []
    for x in xs:
        if out and out[-1][0] == 'prod' and x[0] == 'prod' and len(out[-1][1]) == len(x[1]):
            out[-1] = norm(('prod', [('comp', [a, b]) for a, b in zip(out[-1][1], x[1])]))
        else:
            out.append(x)
    return out


def fuse(xs):
    """`F(R)F(S)=F(RS)`: the picture draws one bead per arrow under an unbroken relator wire, the
    display writes one application of the relator to the composite they make."""
    out = []
    for x in xs:
        # The context is part of the wire's identity: `F(∋,𝟙)F(𝟙,∋)` acts in two different slots
        # and is not `F(∋∋)`, so two applications merge only when their contexts agree.
        if out and out[-1][0] == 'app' and x[0] == 'app' and out[-1][1] == x[1] \
                and out[-1][3:] == x[3:]:
            out[-1] = norm(('app', x[1], ('comp', [out[-1][2], x[2]])) + x[3:])
        else:
            out.append(x)
    return out


def act(label, e, obj=False):
    """How a wire acts on what passes it.  A label with a hole is a context — the named slots go to
    `𝟙` for an arrow and keep their names for an object; `Δ` is the AOP relator `X↦X×X`."""
    if '−' in label and '(' in label and label.endswith(')'):
        head = label[:label.index('(')]
        bs = [b.strip() for b in split_top(label[label.index('(') + 1:-1], ',')]
        return ('app', head, e,
                head + '(' + ','.join('−' if b == '−' else (b if obj else UNIT) for b in bs) + ')')
    if '−' in label:
        return ('prod', [e if p == '−' else ('atom', p if obj else UNIT) for p in label.split('×')])
    if label == 'Δ':
        return ('prod', [e, e])
    return ('app', label, e)


def fill(wire, bead, inner):
    """A bead ON a context wire, at the same height as the one inside it (13.3.5b's `p×𝟙` beside
    `p`): the wire's hole takes the inner factor and the bead supplies the other slots."""
    ps, bs = wire.split('×'), bead.split('×')
    if '−' not in ps or len(ps) != len(bs) or bs[ps.index('−')] != UNIT:
        raise Unhandled(f"the bead {bead} does not fit the wire {wire}")
    return ('prod', [inner if p == '−' else parse(b) for p, b in zip(ps, bs)])


class Unhandled(Exception):
    """A panel shape the sweep has no rule for — reported, never skipped."""


def opt(argv, name):
    return argv[argv.index(name) + 1] if name in argv else None


def help_if(argv, doc, body):
    """`-h` prints the module docstring and the caller's own flag/example block."""
    if "-h" in argv or "--help" in argv:
        print(doc.strip() + "\n\n" + body.strip()); sys.exit(0)
