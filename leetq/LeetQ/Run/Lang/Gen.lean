import LeetQ.Run.AC3Def
import LeetQ.Run.CRelDef
import LeetQ.Run.CRelArithDef
import LeetQ.Run.CRelRelDef
import LeetQ.Run.CRelListDef
import LeetQ.Run.CRelFoldDef
import LeetQ.Run.CRelPowerDef
import LeetQ.Run.CRelLoopDef
import LeetQ.Run.CRelEstDef
import LeetQ.Run.Lang.Bits

/-! The code a `rel_program` definition expands into (`Expand`): one function per core-term constructor, each
    a composition of `CRel` ops, so a definition is an ordinary Lean term over `CRel` and its ok bit is the `&&`
    of the ops it ran. A term that runs on demand (§a) is a function of its keys, `Dem true A`; a closed one of
    `Dem false A = Unit`. A closed term over `≫`/`∩`/`−`/`\` runs as a bit-matrix plan (`Bits.runC`), each node of
    the plan built by the `p*` functions below on the demand its parent gives it. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

/-- The keys a term reads: a coreflexive when it runs on demand, nothing when it is closed. -/
@[reducible] def Dem : Bool → Obj → Type
  | true, A => Rel A A
  | false, _ => Unit

def Dem.of {A : Obj} : (d : Bool) → Rel A A → Dem d A
  | true, D => D
  | false, _ => ()

def Dem.l {A : Obj} : (d e : Bool) → Dem (d || e) A → Dem d A
  | true, _, D => D
  | false, _, _ => ()

def Dem.r {A : Obj} : (d e : Bool) → Dem (d || e) A → Dem e A
  | _, false, _ => ()
  | true, true, D => D
  | false, true, D => D

namespace Gen

open QLean QLean.Dep QLean.Kernel

/-- A term's code: its relation and ok bit on the keys it is given. -/
abbrev Fn (d : Bool) (A B : Obj) := Dem d A → CRel A B

/-- A term's bit-matrix plan on the keys it is given, and the ok bit of the tables at its leaves. -/
abbrev Pl (d : Bool) (A B : Obj) := Dem d A → Bits.Route A B × Bool

/-- A definition's value with its objects: what `rel_program n` lists as `n.expanded`. -/
abbrev Gv := (A : Obj) × (B : Obj) × CRel A B

def entry (n : String) (A B : Obj) (c : CRel A B) : String × Gv := (n, ⟨A, B, c⟩)

/-- A twin's answer as a `CRel`. -/
def ofC {A B : Obj} (r : Rel A B × Bool) : CRel A B := ⟨r.1, r.2⟩

/-- `r` with the bits `b` of the ops that computed its inputs outside it. -/
def also {A B : Obj} (b : Bool) (r : CRel A B) : CRel A B := ⟨r.rel, b && r.ok⟩

/-! ### Leaves: the values `build` put in the term, rebuilt from their payloads -/

/-- The bytes of the hex text `s` (two lowercase digits a byte, as `Expand.hex` writes them). One string
    literal per column, so a column of any size is one node of the generated term. -/
def unhex (s : String) : ByteArray := Id.run do
  let u := s.toUTF8; let d (c : UInt8) : UInt8 := if c ≤ 57 then c - 48 else c - 87
  let mut b := ByteArray.emptyWithCapacity (u.size / 2)
  for h : i in [0:u.size / 2] do
    have := h.upper; b := b.push (d u[2 * i] * 16 + d u[2 * i + 1])
  pure b

/-- The column of `t` whose payload is the hex text `s`, `bits` a boolean's (`Enc.bits`), else `Enc.bytes`, and
    its fit as its ok bit: `Enc.WF` is decided, so a payload that does not fit `n` is a blank column with bit
    false, never a wrong column read as right. -/
def atom (t : QAtomicType) (n : USize) (bits : Bool) (s : String) : Arr t n × Bool :=
  let e := if bits then Enc.bits (unhex s) else Enc.bytes (unhex s)
  if h : Enc.WF t n e then (Arr.mk e h, true) else (Arr.mk (Enc.blank t n) (Enc.blank_WF t n), false)

/-- A rebuilt column from its rebuilt parts, its bit the `&&` of theirs. -/
def pairV (A B : Obj) (n : USize) (x : Vals A n × Bool) (y : Vals B n × Bool) : Vals (.prod A B) n × Bool :=
  ((x.1, y.1), x.2 && y.2)
def arrV (B : Obj) (n m : USize) (lo hi : Arr .long n × Bool) (p : Vals B m × Bool) : Vals (.arr B) n × Bool :=
  (⟨m, lo.1, hi.1, p.1⟩, lo.2 && hi.2 && p.2)
def sumV (A B : Obj) (n l r : USize) (tag : Arr .boolean n × Bool) (idx : Arr .long n × Bool) (x : Vals A l × Bool)
    (y : Vals B r × Bool) : Vals (.sum A B) n × Bool :=
  (⟨l, r, tag.1, idx.1, x.1, y.1⟩, tag.2 && idx.2 && x.2 && y.2)
def relV (A B : Obj) (n : USize) (k : Vals A n × Bool) (v : Vals B n × Bool) : Rel A B × Bool :=
  (⟨n, k.1, v.1⟩, k.2 && v.2)

/-! ### Code -/

def const (A B : Obj) (c : CRel A B) : Fn false A B := fun _ => c
def val (A B : Obj) (R : Rel A B × Bool) : Fn false A B := fun _ => ofC R
def uni (A : Obj) (m : USize) (U : Vals A m × Bool) : Fn false A A := fun _ => ⟨idU U.1, U.2⟩
def zero (A B : Obj) : Fn false A B := fun _ => ⟨Alg.zero, true⟩
def id (A : Obj) : Fn true A A := fun D => ⟨D, true⟩
def top (A B : Obj) (V : Fn false B B) : Fn true A B := fun D => let v := V (); also v.ok (ofC (topC D.val v.rel.val))
def mem (B : Obj) : Fn true (.arr B) B := fun D => CRel.mem D.val
def outl (A B : Obj) : Fn true (.prod A B) A := fun D => ⟨Alg.outl D, true⟩
def outr (A B : Obj) : Fn true (.prod A B) B := fun D => ⟨Alg.outr D, true⟩
def inl (A B : Obj) : Fn true A (.sum A B) := fun D => CRel.inl D.val
def inr (A B : Obj) : Fn true B (.sum A B) := fun D => CRel.inr D.val

/-- The demand of `S` in `R S`: `ran(R)` where `S` takes one, `R`'s plan run for it, `ranC`'s bit kept so the
    demand is proved a coreflexive on `R`'s range (`GenSpec.demP_spec`). -/
def demP {A B : Obj} : (e : Bool) → Bits.Route A B → Dem e B × Bool
  | false, _ => ((), true)
  | true, r => let x := Bits.runC r; let k := ranC x.1; (k.1, x.2 && k.2)

/-- `R S` on demand: `S` runs on `ran(R)`, and not at all where `R` has no row. -/
def comp (A B C : Obj) (e : Bool) (R : Fn true A B) (S : Fn e B C) : Fn true A C := fun D =>
  let r := R D
  if r.rel.n == 0 then ⟨Alg.zero, r.ok⟩ else
  let k := CRel.ran r; also k.ok (CRel.comp r (S (Dem.of e k.rel)))

/-- A closed `R S`, `R ∩ S`, `R − S`, `R\S` as bit matrices where its plan's objects are small (`Bits.runC`). -/
def compB (A B C : Obj) (e : Bool) (R : Pl false A B) (S : Pl e B C) : Fn false A C := fun _ =>
  let r := R (); let k := demP e r.1; let s := S k.1; also (r.2 && k.2 && s.2) (ofC (Bits.runC (.comp r.1 s.1)))
def meetB (A B : Obj) (R S : Pl false A B) : Fn false A B := fun _ =>
  let r := R (); let s := S (); also (r.2 && s.2) (ofC (Bits.runC (.meet r.1 s.1)))
def diffB (A B : Obj) (R S : Pl false A B) : Fn false A B := fun _ =>
  let r := R (); let s := S (); also (r.2 && s.2) (ofC (Bits.runC (.diff r.1 s.1)))
def ldivB (A B C : Obj) (R : Pl false A B) (S : Pl false A C) (UB : Fn false B B) (UC : Fn false C C) :
    Fn false B C := fun _ =>
  let r := R (); let s := S (); let ub := UB (); let uc := UC ()
  also (r.2 && s.2 && ub.ok && uc.ok) (ofC (Bits.runC (.ldiv r.1 s.1 ub.rel uc.rel)))

def conv (A B : Obj) (R : Fn false A B) : Fn false B A := fun _ => let r := R (); ⟨r.rel°, r.ok⟩
def meet (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B := fun D =>
  CRel.inter (R (Dem.l d e D)) (S (Dem.r d e D))
def join (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B := fun D =>
  CRel.union (R (Dem.l d e D)) (S (Dem.r d e D))
def diff (A B : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A B) : Fn (d || e) A B := fun D =>
  CRel.diff (R (Dem.l d e D)) (S (Dem.r d e D))
def dom (A B : Obj) (d : Bool) (R : Fn d A B) : Fn d A A := fun D => CRel.dom (R D)
def ran (A B : Obj) (R : Fn false A B) : Fn false B B := fun _ => CRel.ran (R ())
def rdiv (A B C : Obj) (R : Fn false A C) (S : Fn false B C) (UA : Fn false A A) (UB : Fn false B B) :
    Fn false A B := fun _ =>
  let ua := UA (); let ub := UB (); also (ua.ok && ub.ok) (CRel.rightDiv (R ()) (S ()) ua.rel.val ub.rel.val)
def pair (A B C : Obj) (d e : Bool) (R : Fn d A B) (S : Fn e A C) : Fn (d || e) A (.prod B C) := fun D =>
  CRel.pair (R (Dem.l d e D)) (S (Dem.r d e D))
def prod (A B C D : Obj) (R : Fn false A B) (S : Fn false C D) : Fn false (.prod A C) (.prod B D) := fun _ =>
  CRel.prod (R ()) (S ())
def junc (A B C : Obj) (R : Fn false A C) (S : Fn false B C) : Fn false (.sum A B) C := fun _ =>
  CRel.junc (R ()) (S ())
/-- `Λ(R)` total on the keys `D`: `[]` at a key `R` relates to nothing (`CRel.lamOn`, `rep_lamOn`). -/
def lam (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true A (.arr B) := fun D => CRel.lamOn (R (Dem.of d D)) D.val
def E (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true (.arr A) (.arr B) := fun D =>
  let k := CRel.ran (CRel.mem D.val); also k.ok (CRel.E (R (Dem.of d k.rel)) D.val)
def filter (B : Obj) (d : Bool) (R : Fn d B B) : Fn true (.arr B) (.arr B) := fun D =>
  let k := CRel.ran (CRel.mem D.val); also k.ok (CRel.filter (R (Dem.of d k.rel)) D.val)
def takewhile (B : Obj) (d : Bool) (R : Fn d B B) : Fn true (.arr B) (.arr B) := fun D =>
  let k := CRel.ran (CRel.mem D.val); also k.ok (CRel.takewhile (R (Dem.of d k.rel)) D.val)
def map (A B : Obj) (d : Bool) (R : Fn d A B) : Fn true (.arr A) (.arr B) := fun D =>
  let k := CRel.ran (CRel.mem D.val); also k.ok (CRel.map (R (Dem.of d k.rel)) D.val)

/-- An order held as its pair test, run on the pairs the operator compares. -/
def est (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) B := fun D =>
  CRel.estOn (fun P => Q P.rel) (CRel.mem D.val)
def thin (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) (.arr B) := fun D =>
  let T := CRel.thinOn (fun P => Q P.rel) (CRel.mem D.val)
  let df := CRel.diff ⟨D, true⟩ (CRel.dom T)
  CRel.union (CRel.transpose T) (also df.ok (ofC (topC df.rel.key (nilVal _))))
def tau (A : Obj) : Fn true A (.arr A) := fun D => CRel.τ D.val
def nil (A B : Obj) : Fn true A (.arr B) := fun D => ofC (topC D.val (nilVal _))
def cons (B : Obj) : Fn true (.prod B (.arr B)) (.arr B) := fun D => CRel.cons ⟨D, true⟩
def uncons (B : Obj) : Fn true (.arr B) (.prod B (.arr B)) := fun D => CRel.uncons D.val
def length (B : Obj) : Fn true (.arr B) .long := fun D => CRel.length D.val
def total : Fn true (.arr .long) .long := fun D => CRel.Arr.sum D.val
def inits (B : Obj) : Fn true (.arr B) (.arr (.arr B)) := fun D => CRel.inits D.val
def tails (B : Obj) : Fn true (.arr B) (.arr (.arr B)) := fun D => CRel.tails D.val
def «prefix» (B : Obj) : Fn true (.arr B) (.arr B) := fun D => CRel.prefix D.val
def suffix (B : Obj) : Fn true (.arr B) (.arr B) := fun D => CRel.suffix D.val
def concat (B : Obj) : Fn true (.arr (.arr B)) (.arr B) := fun D => CRel.concat D.val
def cat (B : Obj) : Fn true (.prod (.arr B) (.arr B)) (.arr B) := fun D => CRel.cat ⟨D, true⟩
def uncat (B : Obj) : Fn true (.arr B) (.prod (.arr B) (.arr B)) := fun D => CRel.uncat D.val
def zip (A B : Obj) : Fn true (.prod (.arr A) (.arr B)) (.arr (.prod A B)) := fun D => CRel.zip ⟨D, true⟩
def snoc (B : Obj) : Fn true (.prod (.arr B) B) (.arr B) := fun D => CRel.snoc ⟨D, true⟩
def unsnoc (B : Obj) : Fn true (.arr B) (.prod (.arr B) B) := fun D => CRel.unsnoc D.val
def atPos (B : Obj) (k : Nat) : Fn true (.arr B) B := fun D => CRel.atPos k D.val
def setify (B : Obj) : Fn true (.arr B) (.arr B) := fun D => CRel.setify D.val
def bagify (B : Obj) : Fn true (.arr B) (.arr B) := fun D => CRel.bagify D.val
def tic (B : Obj) : Fn true (.prod B (.arr B)) (.arr (.arr B)) := fun D => CRel.tic ⟨D, true⟩
def thinL (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.arr B) (.arr B) := fun D =>
  CRel.thinLOn (fun P => Q P.rel) D.val
def merge (B : Obj) (Q : Fn true (.prod B B) (.prod B B)) : Fn true (.prod (.arr B) (.arr B)) (.arr B) := fun D =>
  CRel.mergeOn (fun P => Q P.rel) ⟨D, true⟩

/-- A step run on a round's pairs `P`, where its value is read only composed after rows into `P`: with no key,
    nothing reads it, so it is not run — the last round of a fold or loop meets no pair. -/
def onKeys {A B : Obj} (d : Bool) (F : Fn d A B) (P : CRel A A) : CRel A B :=
  if P.rel.n == 0 then ⟨Alg.zero, true⟩ else F (Dem.of d P.rel)

def loop (X Y : Obj) (d : Bool) (F : Fn d (.prod X Y) X) : Fn true (.prod X (.arr Y)) X := fun D =>
  CRel.loopOn (onKeys d F) ⟨D, true⟩
def succ (m : USize) (U : Arr .long m × Bool) : Fn true .long .long := fun D =>
  also U.2 (CRel.comp ⟨D, true⟩ (CRel.succ U.1))
/-- A result outside the declared object has no row, as `succ` at its top. -/
def arith (k : UInt8) (m : USize) (U : Arr .long m × Bool) : Fn true (.prod .long .long) .long := fun D =>
  CRel.comp ⟨Alg.arith k D.val, true⟩ ⟨idU U.1, U.2⟩
def leq (m : USize) (U : Arr .long m × Bool) : Fn false .long .long := fun _ => also U.2 (CRel.leq U.1)
def lt (m : USize) (U : Arr .long m × Bool) : Fn false .long .long := fun _ => also U.2 (CRel.lt U.1)
/-- `succ`, a value verb, `≤`, `<` on the universe `U` a constant is given for an object variable: its keys. -/
def succF (U : Fn false .long .long) : Fn true .long .long := fun D =>
  let u := U (); also u.ok (CRel.comp ⟨D, true⟩ (CRel.succ u.rel.key))
def arithF (k : UInt8) (U : Fn false .long .long) : Fn true (.prod .long .long) .long := fun D =>
  CRel.comp ⟨Alg.arith k D.val, true⟩ (U ())
def leqF (U : Fn false .long .long) : Fn false .long .long := fun _ => let u := U (); also u.ok (CRel.leq u.rel.key)
def ltF (U : Fn false .long .long) : Fn false .long .long := fun _ => let u := U (); also u.ok (CRel.lt u.rel.key)
def fold (E V : Obj) (d : Bool) (e : Fn false V V) (S : Fn d (.prod E V) V) : Fn true (.arr E) V := fun D =>
  let v := e (); also v.ok (CRel.foldOn v.rel.val (onKeys d S) D.val)

/-- The pairs `(i, xs)` in demand, one fold row each, starting from its own key's seeds `(i,v)` from `e`. -/
def foldI (I E V : Obj) (d d' : Bool) (e : Fn d I (.prod V V)) (S : Fn d' (.prod E (.prod I V)) (.prod I V)) :
    Fn true (.prod I (.arr E)) V := fun D =>
  let ro := ofC (ranC (Alg.outl D)); let es := e (Dem.of d ro.rel)
  let res := CRel.ran es
  let iv := CRel.pair (CRel.dom es) (CRel.comp es ⟨Alg.outl res.rel, res.ok⟩)
  let r := CRel.num ⟨D, true⟩ 0
  let ci := CRel.comp ⟨Alg.outl r.rel, r.ok⟩ iv
  let G := ofC (foldRowsC (Alg.outr r.rel) ci.rel
    (demandStepC fun A => let s := onKeys d' S ⟨A, true⟩; (s.rel, s.ok)))
  let rg := CRel.ran G
  also (ro.ok && ci.ok) (CRel.comp ⟨r.rel°, r.ok⟩ (CRel.comp G ⟨Alg.outr rg.rel, rg.ok⟩))

/-- `R` at the keys of the pairs, its rows `(i,(a,b))` re-keyed as `((i,a),b)`, a join with the pairs. -/
def flat (I A B : Obj) (d : Bool) (R : Fn d I (.prod A B)) : Fn true (.prod I A) B := fun D =>
  let ro := ofC (ranC (Alg.outl D)); let r := R (Dem.of d ro.rel); let u := CRel.ran r
  let p := CRel.pair ⟨r.rel°, r.ok⟩ ⟨Alg.outl u.rel, u.ok⟩
  also ro.ok (CRel.comp ⟨D, true⟩ (CRel.comp ⟨p.rel°, p.ok⟩ ⟨Alg.outr u.rel, u.ok⟩))

/-- `νX : φ`: rounds of `φ` from `S` down to the greatest fixed point. -/
def nu (A B : Obj) (S : Fn false A B) (φ : CRel A B → Fn false A B) : Fn false A B := fun _ =>
  let s := S (); (CRel.fixOn (s.rel.n.toNat + 1) (fun X => φ X ()) s).1

/-- One arc `A\(X C)` of an AC-3 body: `A`, `C`, `𝟙(V)`, `𝟙(D)`. -/
abbrev Arc (V D : Obj) := Fn false V V × Fn false D D × Fn false V V × Fn false D D

/-- `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` by AC-3's delta rounds (`acFixC`), its arcs `a :: as`. -/
def nuAC (V D : Obj) (S : Fn false V D) (a : Arc V D) (as : List (Arc V D)) : Fn false V D := fun _ =>
  let s := S ()
  let rs := (a :: as).map fun (x, c, uv, ud) => (x (), c (), uv (), ud ())
  let ok := rs.all fun (x, c, uv, ud) => x.ok && c.ok && uv.ok && ud.ok
  let rv := rs.map fun (x, c, uv, ud) => (⟨x.rel, c.rel, uv.rel, ud.rel⟩ : Revise V D)
  let r := acFixC s.rel rv (a.2.2.1 ()).rel
  ⟨r.1.1, s.ok && ok && r.2⟩

/-- `μX : φ`: rounds of `φ` from `𝟘` up to the least fixed point, at most `cap`. Fewer than `cap` rounds run means a
    round left the row count, so the chain reached its fixed point; `cap` rounds run is not ok, never a truncated
    chain passed off as the answer. -/
def mu (A B : Obj) (cap : Nat) (φ : CRel A B → Fn false A B) : Fn false A B := fun _ =>
  let r := CRel.fixOn cap (fun X => φ X ()) ⟨Alg.zero, true⟩
  also (decide (r.2 < cap)) r.1

/-- `F` read only at the nodes `P`: run on their keys, or closed and composed after `P`; not run on none. -/
def onNodes {A B : Obj} : (d : Bool) → Fn d A B → CRel A A → CRel A B
  | true, F, P => if P.rel.n == 0 then ⟨Alg.zero, P.ok⟩ else also P.ok (F P.rel)
  | false, F, P => if P.rel.n == 0 then ⟨Alg.zero, P.ok⟩ else CRel.comp P (F ())

/-- `[R,S]` on the sum values in demand: `R` on the left values they hold, `S` on the right, joined with them. -/
def juncD (A B C : Obj) (d e : Bool) (R : Fn d A C) (S : Fn e B C) : Fn true (.sum A B) C := fun D =>
  let ⟨_, _, _, _, x, y⟩ := D.val
  CRel.comp ⟨D, true⟩ (CRel.junc (onNodes d R ⟨idU x, true⟩) (onNodes e S ⟨idU y, true⟩))

/-- `refold`'s rounds, at most `f`, from the nodes `pend` not yet valued and the values `X` so far: the nodes
    of `pend` with no child in `pend` (`chN`, each node's children) are ready, valued by `φ X` there and leave
    `pend`. The bit: `pend` emptied; none ready while some pend is a cycle of `chN`. -/
def refoldRounds {A B : Obj} (chN : CRel A A) (φ : CRel A B → CRel A A → CRel A B) :
    Nat → CRel A A → CRel A B → CRel A B × Bool
  | 0, _, X => (X, false)
  | f + 1, pend, X =>
    if pend.rel.n == 0 then (X, true) else
    let ready := CRel.diff pend (CRel.dom (CRel.comp (CRel.comp pend chN) pend))
    if ready.rel.n == 0 then (X, false) else
    refoldRounds chN φ f (CRel.diff pend ready) (CRel.union X (φ X ready))

/-- `refold(c, S)` = `μX : c G(X) S` on the keys `D`, bottom-up: the nodes `N` the children `ch` reach from `D`
    (no universe read), then `refoldRounds` over them, each node valued once by `φ` after its children, so no
    intermediate structure of `G` is built. Not ok where the reach did not settle or `ch` has a cycle on `N`. -/
def refold (A B : Obj) (d e : Bool) (ch : Fn d A A) (φ : CRel A B → Fn e A B) : Fn true A B := fun D =>
  let N := CRel.fixOn USize.size (fun N => CRel.union N (CRel.ran (onNodes d ch N))) ⟨D, true⟩
  let r := refoldRounds (onNodes d ch N.1) (fun X P => onNodes e (φ X) P) (N.1.rel.n.toNat + 1) N.1 ⟨Alg.zero, true⟩
  also (decide (N.2 < USize.size) && r.2) (CRel.comp ⟨D, true⟩ r.1)

/-! ### Plans: the bit-rule nodes kept, every other sub-term its table -/

def pleaf (A B : Obj) (d : Bool) (f : Fn d A B) : Pl d A B := fun D => let r := f D; (.leaf r.rel, r.ok)
/-- The plan `P` run to its relation: a constant's result or argument read where a table is wanted. -/
def ofPl (A B : Obj) (d : Bool) (P : Pl d A B) : Fn d A B := fun D => let r := P D; also r.2 (ofC (Bits.runC r.1))
def pcomp (A B C : Obj) (d e : Bool) (R : Pl d A B) (S : Pl e B C) : Pl d A C := fun D =>
  let r := R D; let k := demP e r.1; let s := S k.1; (.comp r.1 s.1, r.2 && k.2 && s.2)
def pconv (A B : Obj) (R : Pl false A B) : Pl false B A := fun _ => let r := R (); (.conv r.1, r.2)
def pmeet (A B : Obj) (d e : Bool) (R : Pl d A B) (S : Pl e A B) : Pl (d || e) A B := fun D =>
  let r := R (Dem.l d e D); let s := S (Dem.r d e D); (.meet r.1 s.1, r.2 && s.2)
def pjoin (A B : Obj) (d e : Bool) (R : Pl d A B) (S : Pl e A B) : Pl (d || e) A B := fun D =>
  let r := R (Dem.l d e D); let s := S (Dem.r d e D); (.join r.1 s.1, r.2 && s.2)
def pdiff (A B : Obj) (d e : Bool) (R : Pl d A B) (S : Pl e A B) : Pl (d || e) A B := fun D =>
  let r := R (Dem.l d e D); let s := S (Dem.r d e D); (.diff r.1 s.1, r.2 && s.2)
def pldiv (A B C : Obj) (R : Pl false A B) (S : Pl false A C) (UB : Fn false B B) (UC : Fn false C C) :
    Pl false B C := fun _ =>
  let r := R (); let s := S (); let ub := UB (); let uc := UC ()
  (.ldiv r.1 s.1 ub.rel uc.rel, r.2 && s.2 && ub.ok && uc.ok)

end Gen

end LeetQ.Rel.Lang
