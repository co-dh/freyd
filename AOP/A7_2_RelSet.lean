/-
  Bird & de Moor §7.2 in the set model: `+` distributes over `≤`.

  `AOP.A7_2` states `Distributes` abstractly and proves Theorem 7.1 from it.  The INSTANCE the
  book reads the definition by — the minimum of a sum is the sum of the minima — is a concrete
  construction, so it needs a concrete allegory and lives here rather than dragging the §6.1 set
  model into the abstract §7.2 module.  The pointwise `est`/`Λ` lemmas it is proved from were
  built for §7.4's Horner rule, which is the only place in the repo that has them.
-/
module

public import AOP.A6_1_OrdRelSet
public import AOP.A7_2
public import AOP.A7_4_Horner

namespace Freyd.Alg.RelSet

/-- Addition as an arrow `Nat×Nat ⟶ Nat` of `Rel(Set)`, the algebra of the relator `Δ`. -/
@[expose] public def plusRel : (Δ RelSet.{0}).obj (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  -- `Nat.add`/`Nat.le` and not `+`/`≤`: the `binop%` elaborator reads the OPERANDS' types, and a
  -- component of the relator's object is one only up to unfolding, where the instance search stops.
  fun p n => Nat.add p.1 p.2 = n

/-- The order `≤` on `Nat` as an endorelation, the `R` of `est R`. -/
@[expose] public def leRel : (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) := fun x y => Nat.le x y

/-- `{x+y ∣ x ∈ xs ∧ y ∈ ys}` — the set the square's top edge carries `(xs,ys)` to.  Named rather
    than written out at the corner it labels: the picture sets a corner's value in one line. -/
@[expose] public def sums (xs ys : (pow (⟨Nat⟩ : RelSet.{0})).carrier) :
    (pow (⟨Nat⟩ : RelSet.{0})).carrier := fun n => ∃ x y, xs x ∧ ys y ∧ Nat.add x y = n

/-- `min(xs)` — the least member of `xs`, the point `est(≤)` sends `xs` to; `xs` stays explicit
    because it is what the printed corner shows.  The witness is a binder, not `Classical.choose`:
    a set of naturals is `Nat → Prop`, nothing computes its least member, and the statement is about
    sets that have one. -/
@[expose] public def minOf (xs : (pow (⟨Nat⟩ : RelSet.{0})).carrier)
    (m : {a // est leRel xs a}) : Nat := m.val

/-- **`+` distributes over `≤`** — `Distributes` (§7.2) at `Rel(Set)`'s `+` and `est(≤)`: the
    smallest sum of a member of `xs` and a member of `ys` is the sum of the smallest of each.

    The four points are the square's corners read at `(xs,ys)`: they say what the picture writes
    under each object, and they are hypotheses because the terms are of this statement's own
    context — `(xs,ys)` names binders of it — where an attribute is elaborated outside it. -/
public theorem plus_distributes_le
    {xs ys : (pow (⟨Nat⟩ : RelSet.{0})).carrier}
    (mx : {a // est leRel xs a}) (my : {a // est leRel ys a})
    {fea : ((Δ RelSet.{0}).obj (pow (⟨Nat⟩ : RelSet.{0}))).carrier} (_hfea : fea = (xs, ys))
    {ea : (pow (⟨Nat⟩ : RelSet.{0})).carrier}
    (_hea : ea = sums xs ys)
    {fa : ((Δ RelSet.{0}).obj (⟨Nat⟩ : RelSet.{0})).carrier}
    (_hfa : fa = (minOf xs mx, minOf ys my))
    {c : Nat} (_hc : c = minOf xs mx + minOf ys my) :
    Distributes (F := Δ RelSet.{0}) plusRel leRel := by
  refine RelSet.le_iff.mpr ?_
  rintro p w ⟨q, hq, hw⟩
  obtain ⟨hq1, hq2⟩ := (delta_map_apply (est leRel) p q).mp hq
  obtain ⟨hm1, hd1⟩ := (est_apply leRel p.1 q.1).mp hq1
  obtain ⟨hm2, hd2⟩ := (est_apply leRel p.2 q.2).mp hq2
  refine (Λ_comp_est_apply _ leRel p w).mpr
    ⟨⟨q, (delta_map_apply (∋ (⟨Nat⟩ : RelSet.{0})) p q).mpr ⟨hm1, hm2⟩, hw⟩, ?_⟩
  rintro z ⟨r, hr, hz⟩
  obtain ⟨hr1, hr2⟩ := (delta_map_apply (∋ (⟨Nat⟩ : RelSet.{0})) p r).mp hr
  have hw' : Nat.add q.1 q.2 = w := hw
  have hz' : Nat.add r.1 r.2 = z := hz
  have h1 : Nat.le q.1 r.1 := hd1 r.1 hr1
  have h2 : Nat.le q.2 r.2 := hd2 r.2 hr2
  show Nat.le w z
  exact hw' ▸ hz' ▸ Nat.add_le_add h1 h2

end Freyd.Alg.RelSet
