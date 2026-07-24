#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["numpy", "scipy"]
# ///
"""Duplicate-lemma detector for the Freyd dependency graph, in two passes.

Pass 1 (exact): group by the `key` column of decls.tsv — the alpha/universe-normalised statement hash
ExtractGraph computes from the elaborated `Expr`. Equal keys ARE duplicates, no threshold, no ranking.
This is the pass the dependency similarity below structurally cannot do: two independent proofs of one
statement have disjoint dependency rows, so they score ~0 there and were silently dropped.

Pass 2 (fuzzy): nearest neighbours in the SVD embedding of the hub-removed dependency matrix.
Each declaration's row (what it uses) is compressed to a K-D fingerprint; duplicates have near-identical
fingerprints. This catches duplicates that share only *mid-frequency* dependencies — a rare-dep inverted
index (the earlier approach) misses those, and SVD-NN found a strict superset of its results.

Then filter: cross-file (kills same-file symmetric siblings like left/right, Preserves/Reflects),
same kind, high row-Jaccard on the hub-removed rows; corroborate & rank by name and type agreement.

Hubs (deps used by > HUB_INDEG decls, e.g. Cat.Hom) are dropped everywhere: they're in almost every
row so they carry no duplicate signal.

Run:  uv run scripts/dep_dup.py     (regen data first: lake env lean --run scripts/ExtractGraph.lean)
"""
import numpy as np, csv, re, collections
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import svds

HUB_INDEG = 100    # dep used by more than this many decls = hub, dropped from every row
K         = 32     # SVD embedding dimension
COS       = 0.90   # nearest-neighbour cosine threshold for a candidate pair
MIN_SHARED= 3      # shared non-hub deps required (unless name/type corroborates)
MIN_J     = 0.80   # row-Jaccard (hub-removed) threshold
TOP       = 50     # how many ranked candidates to print
ALIAS_SZ  = 12     # value-DAG nodes at or below which a shared def body is a naming, not a copy
DECLS, DEPS = 'graph/decls.tsv', 'graph/deps.tsv'
IMPORTS = 'graph/imports.tsv'

# --- load ---
info={}; idx={}; names=[]; key={}; size={}
for r in csv.reader(open(DECLS), delimiter='\t'):
    if len(r) < 4 or r[0] in idx: continue
    idx[r[0]] = len(names); names.append(r[0])
    info[r[0]] = (r[1], r[2], r[3], r[4] if len(r) > 4 else '')     # kind, file, line, type
    if len(r) > 6 and r[6]: key[r[0]] = r[6]                        # statement hash (ExtractGraph)
    if len(r) > 7 and r[7].isdigit(): size[r[0]] = int(r[7])        # value-term DAG nodes

# module -> modules it transitively imports, so a group can say which member every other member can
# already see (the canonical home must be upstream of its uses, else forwarding needs a cycle).
mod = lambda f: f[:-5].replace('/', '.')
direct = collections.defaultdict(set)
try:
    for r in csv.reader(open(IMPORTS), delimiter='\t'):
        if len(r) == 2: direct[r[0]].add(r[1])
except FileNotFoundError: direct = {}
upstream = {}
def imports_of(m, seen=None):
    if m in upstream: return upstream[m]
    seen = (seen or set()) | {m}
    out = set()
    for i in direct.get(m, ()):
        if i not in seen: out |= {i} | imports_of(i, seen)
    upstream[m] = out
    return out
n=len(names); rows=[]; cols=[]
for r in csv.reader(open(DEPS), delimiter='\t'):
    if len(r) < 2: continue
    a,b = idx.get(r[0]), idx.get(r[1])
    if a is not None and b is not None: rows.append(a); cols.append(b)
A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(n,n)).tocsr()
indeg = np.asarray(A.sum(0)).ravel()                       # dep in-degree (also a decl's own in-degree)
dout_all = [A.indices[A.indptr[i]:A.indptr[i+1]] for i in range(n)]   # full dep rows (hubs kept)

# --- pass 1: exact statement collisions --------------------------------------------------------
# Equal `key` = identical elaborated statement up to binder/universe renaming. For a theorem that is
# proof-irrelevantly the same fact, so the group is a duplicate outright; for a def it means type AND
# body agree, i.e. copy-paste. Two groups are NOT actionable and are split off below: an `abbrev`, and
# a def/instance whose shared body is a handful of nodes — naming an existing term is legitimate, and
# `OppCat (C : Type u) := C` exists precisely to carry a second `Cat` instance, so merging it breaks
# instance resolution.
where = lambda nm: f"{info[nm][1]}:{info[nm][2]}"
modof = lambda nm: mod(info[nm][1])
visible = lambda a, b: modof(a) == modof(b) or modof(a) in imports_of(modof(b))

def canonical(g):
    """The member every other one can already import, most-used first — the collapse target."""
    ok = [a for a in g if all(visible(a, b) for b in g)]
    return max(ok, key=lambda nm: indeg[idx[nm]]) if ok else None

def suggested_home(g):
    """Where a group with no canonical member has to move to. Candidates are the modules EVERY member
    already imports. Among those, prefer the ones that define something the declaration is stated in
    terms of — a `Cover` fact belongs where `Cover` is defined, not merely in the nearest file that
    can see it. Of those, the most downstream (importing the most of the other candidates)."""
    common = set.intersection(*(imports_of(modof(nm)) for nm in g))
    hosts = {modof(names[d]) for nm in g for d in dout_all[idx[nm]] if names[d] in info} & common
    return max(hosts or common, key=lambda m: len(imports_of(m) & common), default=None)

def blocker(can, nm):
    if modof(can) != modof(nm): return ''                  # `canonical` already proved it upstream
    return '  [reorder: canonical is below]' if int(info[can][2]) > int(info[nm][2]) else ''

groups = collections.defaultdict(list)
for nm in names:
    if nm in key: groups[key[nm]].append(nm)
alias = lambda g: info[g[0]][0] == 'abbrev' or (info[g[0]][0] in ('def', 'instance')
                                                and max(size.get(nm, 0) for nm in g) <= ALIAS_SZ)
exact = sorted((g for g in groups.values() if len(g) > 1),
               key=lambda g: (info[g[0]][0] != 'thm', -len(g), g[0]))
real = [g for g in exact if not alias(g)]
exact_pairs = {frozenset((g[i], g[j])) for g in exact for i in range(len(g)) for j in range(i+1, len(g))}

print(f"=== exact duplicates ({len(real)} groups, {sum(len(g) for g in real)} declarations) ===")
for g in real:
    can = canonical(g)
    print(f"[{len(g)}x {info[g[0]][0]}] {info[g[0]][3][:140]}")
    for nm in sorted(g, key=lambda nm: (nm != can, -indeg[idx[nm]])):
        tag = 'canon' if nm == can else ('dup  ' if can else 'split')
        print(f"      {tag} {nm}  ({where(nm)})  used={int(indeg[idx[nm]])}"
              f"{blocker(can, nm) if can and nm != can else ''}")
    if can is None:
        home = suggested_home(g)
        print(f"      no member is importable from all the others — move to {home or '(no common import)'}")

print(f"\n=== aliases / pins ({len(exact)-len(real)} groups, informational: naming a term is not "
      f"duplication) ===")
for g in exact:
    if alias(g): print(f"  [{len(g)}x {info[g[0]][0]}] " + ", ".join(f"{nm} ({where(nm)})" for nm in g))
print()
keep  = (indeg <= HUB_INDEG).astype(float)
Ah    = (A @ diags(keep)).tocsr(); Ah.eliminate_zeros()    # hub columns zeroed
dout  = [set(Ah.indices[Ah.indptr[i]:Ah.indptr[i+1]]) for i in range(n)]

# --- SVD embedding + nearest-neighbour candidate generation ---
U,S,_ = svds(Ah.astype(float), k=K); E = U*S
nz = np.linalg.norm(E, axis=1); good = nz > 1e-9
En = E.copy(); En[good] /= nz[good][:,None]
cand=set(); gi=np.where(good)[0]
for s in range(0, len(gi), 1000):
    blk = gi[s:s+1000]; C = En[blk] @ En.T
    for r,i in enumerate(blk):
        for j in np.where(C[r] >= COS)[0]:
            if j > i and good[j]: cand.add((int(i), int(j)))

# --- name / type tokenisation ---
def toks(s):
    ts=[]
    for p in re.split(r'[^A-Za-z0-9]+', s):
        ts += re.findall(r'[A-Z]+(?![a-z])|[A-Z]?[a-z0-9]+', p)
    return set(t.lower() for t in ts if t)
def jac(a,b): return len(a&b)/len(a|b) if (a or b) else 0.0
def name_sim(a,b):
    tail=lambda x: toks('.'.join(x.split('.')[-2:])); return jac(tail(a), tail(b))

# --- score & filter ---
rows_out=[]
for a,b in cand:
    ia,ib = info[names[a]], info[names[b]]
    if ia[0] != ib[0] or ia[1] == ib[1]: continue         # same kind, cross-file
    da,db = dout[a], dout[b]
    if not da or not db: continue
    sh = len(da&db); j = jac(da,db)
    if j < MIN_J: continue
    ns = name_sim(names[a], names[b]); ts = jac(toks(ia[3]), toks(ib[3]))
    if sh < MIN_SHARED and not (ts >= 0.9 or ns >= 0.5): continue
    unused = indeg[a]==0 or indeg[b]==0
    score = 0.45*ns + 0.35*ts + 0.20*j
    rows_out.append((score, j, unused, ns, ts, sh, names[a], names[b], ia, ib))
rows_out.sort(key=lambda x:(x[0], x[2]), reverse=True)

# --- report ---
def verdict(k, ts):                                        # cheap real/verify guess
    if k=='thm' and ts>=0.999: return 'DUP  '              # same statement, proof-irrelevant
    if k=='thm' and ts>=0.85:  return 'likely'
    return 'verify'
print(f"hubs removed (in-degree > {HUB_INDEG}): {int((~(keep>0)).sum())}; SVD k={K}, cos>={COS}")
print(f"candidate pairs {len(cand)} -> {len(rows_out)} pass (cross-file, same-kind, Jaccard>={MIN_J})\n")

# Regression seeds. Either pass may claim a pair; the exact pass is authoritative when it does, and
# these are the shapes it was added for (two proofs of one statement score ~0 on dependency overlap).
TESTS=[('Alg.AllegoryFunctor.mono','Alg.AllegoryFunctor.map_mono'),
       ('eqMap_monic',"eqMap_mono'"),
       ('FibreDensityProof.fibrePinEqualizers','UniformCap.uniformPinEqualizers'),
       ('inter_mono','Subobject.inter_mono')]
rank={frozenset((r[6],r[7])):i for i,r in enumerate(rows_out)}
print("=== known duplicates (test) ===")
for a,b in TESTS:
    if not (a in info and b in info): v = 'STALE   '                # decl gone: prune the seed
    elif frozenset((a,b)) in exact_pairs: v = 'exact   '
    else:
        i = rank.get(frozenset((a,b)))
        v = 'rank #%-3d'%(i+1) if i is not None else 'MISSED  '
    print(f"  {v}  {a} ~ {b}")

print(f"\n=== top {min(TOP,len(rows_out))} candidates ===")
for i,(_,j,un,ns,ts,sh,a,b,ia,ib) in enumerate(rows_out[:TOP]):
    print(f"#{i+1:<3} {verdict(ia[0],ts)} name={ns:.2f} type={ts:.2f} J={j:.2f} sh={sh}{' U' if un else '  '} [{ia[0]}]")
    print(f"      {a} ({ia[1].split('/')[-1]}:{ia[2]})  ~  {b} ({ib[1].split('/')[-1]}:{ib[2]})")

hc=[r for r in rows_out if r[3]>=0.6 and r[4]>=0.9]
print(f"\nhigh-confidence (name>=0.6 & type>=0.9): {len(hc)} pairs")
