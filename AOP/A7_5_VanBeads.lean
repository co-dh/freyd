/-
  The §7.5 security-van beads, decided as natural families.

  A bead the note draws OFF the object wire claims a naturality square — `G(S) φ ⊑ φ F(S)` for
  EVERY relation `S`, not only for the maps.  `Sched` is `list∘list` and `Seg` is `list` as
  functors of the transaction type `Tx`, so each of the six families of `AOP.A7_5_Van` gets its
  square at an arbitrary `S : dE A ⟶ dE B`.  The verdicts:

  * `new` is STRICTLY natural (`new_natural`).  It is `(wrap×𝟙) cons`, and both factors are
    strictly natural already (`ListRel.wrap_natural`, `ListRel.cons_natural`), so the square is
    those two squares stacked — nothing is proved pointwise here.
  * `head` is LAX only (`head_lax_natural`, `head_not_strict`).  A `list(list S)`-image of a
    schedule has the schedule's shape, so its first segment is the image of the first segment;
    the converse asks the DISCARDED tail to have an image too, and a relation that is not
    entire leaves a tail with none.
  * `R`, `H`, `R;H` and `|R|` are NOT EVEN LAX (`R_not_lax_natural`, `H_not_lax_natural`,
    `RH_not_lax_natural`, `strict_not_lax_natural`).  Each of the four compares two schedules
    without relating their elements, so the left side of the square constrains only the SOURCE
    schedule while the right side demands a `list(list S)`-preimage of the TARGET — and a
    relation that is not surjective leaves the target without one.  This is what a relator
    demands and a length-only or converse-built comparison cannot give.

  * `glue` is STRICTLY natural (`glue_natural`) and so is `nil` (`nil_natural`).  `glue` moves
    the transaction onto the front of the first segment and passes every other element along
    untouched, and `nil` looks at no element at all, so both squares are equalities.
  * `R∩H` and `⊤` are NOT EVEN LAX (`RH_inter_not_lax_natural`, `top_not_lax_natural`), for the
    same reason `R` and `H` are not: the left side of the square constrains only the SOURCE
    schedule while the right side demands a `list(list S)`-preimage of the TARGET.

  The witness is `ListRel.trueOnly`, the coreflexive `{(true,true)} : Bool ⟶ Bool`, on the
  schedules `[[false]]`, `[[]]` and `[[],[false]]`: `false` has neither a `trueOnly`-image nor a
  `trueOnly`-preimage, so a segment holding it has neither, and so does a schedule holding that
  segment.  Composition is diagram order (`≫`).
-/
module

public import AOP.A7_5_Van
public import AOP.A5_7_ListBeads
public import AOP.A7_4_Horner

namespace Freyd.Alg.RelSet.Van

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A B : Type}

/-! ## `new` is strictly natural -/

/-- **`new` is STRICTLY natural**: `(S × list(list S)) new = new list(list S)`.  `new` is
    `(wrap×𝟙) cons` (`new_eq`), so the square is `wrap_natural` in the first component followed
    by `cons_natural` at the segment type. -/
public theorem new_natural (S : dE A ⟶ dE B) :
    rprodMap S (list (list S)) ≫ newR B = newR A ≫ list (list S) := by
  rw [new_eq, new_eq, ← Cat.assoc, rprodMap_comp, Cat.comp_id, ← wrap_natural S, Cat.assoc,
    ← cons_natural (list S), ← Cat.assoc, rprodMap_comp, Cat.id_comp]

/-- **`wrap×𝟙` is STRICTLY natural**: `(S×list(list S))(wrap×𝟙) = (wrap×𝟙)(list S×list(list S))`.
    The bead the note draws between `new`'s two factors, and it is `strictNatural_prod` at `wrap`
    and the identity family — `×` closes in the strict theory, so nothing is computed here.  The
    four `prodMap_eq_rprodMap` rewrites are the concrete model's product read as the allegory's. -/
public theorem wrapProd_natural (S : dE A ⟶ dE B) :
    rprodMap S (list (list S)) ≫ rprodMap (singleR () : dE B ⟶ dList B) (𝟙 (dE (Sched B)))
      = rprodMap (singleR () : dE A ⟶ dList A) (𝟙 (dE (Sched A)))
        ≫ rprodMap (list S) (list (list S)) := by
  rw [← RelSet.prodMap_eq_rprodMap S (list (list S)),
    ← RelSet.prodMap_eq_rprodMap (singleR () : dE B ⟶ dList B) (𝟙 (dE (Sched B))),
    ← RelSet.prodMap_eq_rprodMap (singleR () : dE A ⟶ dList A) (𝟙 (dE (Sched A))),
    ← RelSet.prodMap_eq_rprodMap (list S) (list (list S))]
  exact strictNatural_prod (F := listRelator) (F' := Relator.comp listRelator listRelator)
    (G := Relator.idRelator RelSet.{0}) (G' := Relator.comp listRelator listRelator)
    (φ := fun a => (singleR () : dE a.carrier ⟶ dList a.carrier))
    (ψ := fun a => 𝟙 ((Relator.comp listRelator listRelator).obj a))
    (fun {_ _} R => (wrap_natural R).symm)
    (fun {_ _} _ => by rw [Cat.comp_id, Cat.id_comp]) S

/-! ## `head` is lax only -/

/-- **`head` is lax natural**: `list(list S) head ⊑ head list(S)`.  A `list(list S)`-image of a
    non-empty schedule is a `cons`, and its first segment is the `list(S)`-image of the first
    segment of the schedule. -/
public theorem head_lax_natural (S : dE A ⟶ dE B) :
    list (list S) ≫ headR B ⊑ headR A ≫ list S :=
  le_iff.mpr fun p s' h => by
    obtain ⟨q, hpq, t, rfl⟩ := h
    cases p with
    | wrap _ => exact hpq.elim
    | cons s x => exact ⟨s, ⟨x, rfl⟩, hpq.1⟩

/-! ### The witnesses

  `ListRel.falseOne` is the segment `[false]` and `ListRel.trueOnly` the coreflexive
  `{(true,true)}`; `ListRel.trueOnly_no_image` says `[false]` has no `list(trueOnly)`-image. -/

/-- The schedule `[[false]]` — one segment holding the one transaction `false`. -/
@[expose] public def schedFalse : Sched Bool := ConsList.cons falseOne (ConsList.wrap ())

/-- The schedule `[[]]` — one empty segment.  It is `list(list(trueOnly))`-related to itself. -/
@[expose] public def schedNil : Sched Bool :=
  ConsList.cons (ConsList.wrap ()) (ConsList.wrap ())

/-- The schedule `[[], [false]]` — an empty first segment, so `head` reaches `[]`, over a tail
    that has no image. -/
@[expose] public def schedNilFalse : Sched Bool := ConsList.cons (ConsList.wrap ()) schedFalse

/-- `[[false]]` has no `list(list(trueOnly))`-IMAGE: its one segment has none. -/
public theorem trueOnly_no_image_sched : ∀ q : Sched Bool, ¬ listP (list trueOnly) schedFalse q
  | ConsList.wrap _, h => h.elim
  | ConsList.cons u _, h => trueOnly_no_image u h.1

/-- `[[false]]` has no `list(list(trueOnly))`-PREIMAGE: a preimage's first segment would have to
    hold a `trueOnly`-preimage of `false`, and `trueOnly` relates nothing to `false`. -/
public theorem trueOnly_no_preimage : ∀ r : Sched Bool, ¬ listP (list trueOnly) r schedFalse
  | ConsList.wrap _, h => h.elim
  | ConsList.cons (ConsList.wrap _) _, h => h.1.elim
  | ConsList.cons (ConsList.cons _ _) _, h => Bool.noConfusion h.1.1.2

/-- `[[]]` is `list(list(trueOnly))`-related to itself: no element is looked at. -/
public theorem schedNil_related : listP (list trueOnly) schedNil schedNil := ⟨trivial, trivial⟩

/-- **`head` is not strictly natural**: `head list(S) ⋢ list(list S) head`.  Out of `[[],[false]]`
    the right side reaches `[]` — the first segment is empty and `list(trueOnly)` relates `[]` to
    `[]` — while the left side must first map the WHOLE schedule, and the tail `[[false]]` has no
    image. -/
public theorem head_not_strict :
    ∃ S : dE Bool ⟶ dE Bool, ¬ (headR Bool ≫ list S ⊑ list (list S) ≫ headR Bool) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨q, hq, -⟩ :=
    le_iff.mp h schedNilFalse (ConsList.wrap ()) ⟨ConsList.wrap (), ⟨schedFalse, rfl⟩, trivial⟩
  cases q with
  | wrap _ => exact hq.elim
  | cons _ v => exact trueOnly_no_image_sched v hq.2

/-! ## `R`, `H`, `R;H` and `|R|` are not even lax

  One shape of witness settles all four: the empty schedule on the left, `[[false]]` on the
  right.  The left side of each square maps the empty schedule to itself and then compares
  lengths (or, for `H`, prefixes of first segments); the right side compares first and must then
  reach `[[false]]` by `list(list(trueOnly))`, which has no preimage. -/

/-- **`R` is not even lax natural**: `list(list S) R ⊑ R list(list S)` fails.  The left side
    relates `[]` to `[[false]]` — `[]` is its own image and `0 ≤ 1` — while the right side would
    need a `list(list(trueOnly))`-preimage of `[[false]]`. -/
public theorem R_not_lax_natural :
    ∃ S : dE Bool ⟶ dE Bool, ¬ (list (list S) ≫ R Bool ⊑ R Bool ≫ list (list S)) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨r, -, hr⟩ :=
    le_iff.mp h (ConsList.wrap ()) schedFalse ⟨ConsList.wrap (), trivial, Nat.zero_le _⟩
  exact trueOnly_no_preimage r hr

/-- **`|R|` is not even lax natural**: `list(list S) |R| ⊑ |R| list(list S)` fails on the same
    witness, `0 < 1` in place of `0 ≤ 1`. -/
public theorem strict_not_lax_natural :
    ∃ S : dE Bool ⟶ dE Bool, ¬ (list (list S) ≫ strictR Bool ⊑ strictR Bool ≫ list (list S)) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨r, -, hr⟩ :=
    le_iff.mp h (ConsList.wrap ()) schedFalse ⟨ConsList.wrap (), trivial, Nat.zero_lt_succ _⟩
  exact trueOnly_no_preimage r hr

/-- **`R;H` is not even lax natural**: same witness again — `[]` is strictly shorter than
    `[[false]]`, so the `H` half of `R∩(R°⇒H)` is vacuous. -/
public theorem RH_not_lax_natural :
    ∃ S : dE Bool ⟶ dE Bool, ¬ (list (list S) ≫ RH Bool ⊑ RH Bool ≫ list (list S)) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨r, -, hr⟩ :=
    le_iff.mp h (ConsList.wrap ()) schedFalse
      ⟨ConsList.wrap (), trivial, Nat.zero_le _, fun hle => absurd hle (by decide)⟩
  exact trueOnly_no_preimage r hr

/-- **`H` is not even lax natural**: `list(list S) H ⊑ H list(list S)` fails out of `[[]]`, whose
    first segment `[]` is a prefix of `[false]`, so the left side reaches `[[false]]`; the right
    side would again need a `list(list(trueOnly))`-preimage of `[[false]]`. -/
public theorem H_not_lax_natural :
    ∃ S : dE Bool ⟶ dE Bool, ¬ (list (list S) ≫ Hrel Bool ⊑ Hrel Bool ≫ list (list S)) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨r, -, hr⟩ :=
    le_iff.mp h schedNil schedFalse
      ⟨schedNil, schedNil_related,
        Or.inl ⟨ConsList.wrap (), ConsList.wrap (), falseOne, ConsList.wrap (), rfl, rfl,
          prefixP.nil falseOne⟩⟩
  exact trueOnly_no_preimage r hr

/-! ## `glue` is strictly natural -/

/-- **`glue` is STRICTLY natural**: `(S × list(list S)) glue = glue list(list S)`.  `glue` splits
    the schedule with `cons°`, puts the transaction on the front of the first segment and conses
    the lengthened segment back on — every element is passed along and none is discarded, so the
    square is the two `cons` squares (`cons_natural`, and its converse for `cons°`) stacked. -/
public theorem glue_natural (S : dE A ⟶ dE B) :
    rprodMap S (list (list S)) ≫ glueR B = glueR A ≫ list (list S) := by
  apply hom_ext; rintro ⟨a, x⟩ w
  constructor
  · rintro ⟨⟨b, y⟩, ⟨hab, hxy⟩, s', t', hy, hw⟩
    obtain rfl : y = ConsList.cons s' t' := hy
    obtain rfl : w = ConsList.cons (ConsList.cons b s') t' := hw
    cases x with
    | wrap _ => exact hxy.elim
    | cons s t =>
        exact ⟨ConsList.cons (ConsList.cons a s) t, ⟨s, t, rfl, rfl⟩, ⟨hab, hxy.1⟩, hxy.2⟩
  · rintro ⟨r, ⟨s, t, hx, hr⟩, hrw⟩
    obtain rfl : x = ConsList.cons s t := hx
    obtain rfl : r = ConsList.cons (ConsList.cons a s) t := hr
    cases w with
    | wrap _ => exact hrw.elim
    | cons u v =>
        cases u with
        | wrap _ => exact hrw.1.elim
        | cons b s' =>
            exact ⟨(b, ConsList.cons s' v), ⟨hrw.1.1, hrw.1.2, hrw.2⟩, s', v, rfl, rfl⟩

/-! ## `R∩H` and `⊤` are not even lax

  The same witness as `R` and `H`: `[[]]` on the left, `[[false]]` on the right. -/

/-- **`R∩H` is not even lax natural**: `list(list S) (R∩H) ⊑ (R∩H) list(list S)` fails.  The left
    side relates `[[]]` to `[[false]]` — `[[]]` is its own `list(list(trueOnly))`-image, the two
    schedules have the same length, and `[]` is a prefix of `[false]` — while the right side
    would need a `list(list(trueOnly))`-preimage of `[[false]]`, and `false` has none. -/
public theorem RH_inter_not_lax_natural :
    ∃ S : dE Bool ⟶ dE Bool,
      ¬ (list (list S) ≫ (R Bool ∩ Hrel Bool) ⊑ (R Bool ∩ Hrel Bool) ≫ list (list S)) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨r, -, hr⟩ :=
    le_iff.mp h schedNil schedFalse
      ⟨schedNil, schedNil_related, Nat.le_refl _,
        Or.inl ⟨ConsList.wrap (), ConsList.wrap (), falseOne, ConsList.wrap (), rfl, rfl,
          prefixP.nil falseOne⟩⟩
  exact trueOnly_no_preimage r hr

/-- **`⊤` is not even lax natural**: `list(list S) ⊤ ⊑ ⊤ list(list S)` fails.  The left side
    relates a schedule that HAS an image to everything, the right side relates everything to a
    schedule that HAS a preimage — so the empty schedule, whose image is itself, reaches
    `[[false]]` on the left and nothing on the right. -/
public theorem top_not_lax_natural :
    ∃ S : dE Bool ⟶ dE Bool,
      ¬ (list (list S) ≫ relTop (dSched Bool) (dSched Bool)
          ⊑ relTop (dSched Bool) (dSched Bool) ≫ list (list S)) := by
  refine ⟨trueOnly, fun h => ?_⟩
  obtain ⟨r, -, hr⟩ :=
    le_iff.mp h (ConsList.wrap ()) schedFalse ⟨ConsList.wrap (), trivial, trivial⟩
  exact trueOnly_no_preimage r hr

/-! ## `nil` is strictly natural

  The note's `nil : 𝟏 ⟶ [[Tx]]` is `AOP.A6_ConsList`'s `wrapR` read at `dL Unit ⟶ dSched Tx` —
  the same relation `H_eq` already writes there — so no new definition is made for it. -/

/-- **`nil` is STRICTLY natural**: `𝟙 nil = nil list(list S)`.  `nil` produces the empty schedule
    out of the one point and looks at no transaction, and `list(list S)` relates the empty
    schedule to itself and to nothing else, so both sides are the single pair `((), [])`. -/
public theorem nil_natural (S : dE A ⟶ dE B) :
    𝟙 (dL Unit) ≫ (wrapR : dL Unit ⟶ dSched B)
      = (wrapR : dL Unit ⟶ dSched A) ≫ list (list S) := by
  rw [Cat.id_comp]
  apply hom_ext; rintro ⟨⟩ w
  constructor
  · rintro rfl
    exact ⟨ConsList.wrap (), rfl, trivial⟩
  · rintro ⟨r, rfl, hrw⟩
    cases w with
    | wrap u => cases u; rfl
    | cons _ _ => exact hrw.elim

/-! ## The greedy fold is not even lax natural -/

variable {Tx : Type} {amount : Tx → Int} {N : Int}

/-- The fold `⦇S%∋ est(R;H)⦈` read one transaction at a time: the empty stretch has only the
    empty schedule to answer with. -/
public theorem greedyFold_wrap (r : Sched Tx) :
    greedyFold amount N (ConsList.wrap ()) r ↔ r = ConsList.wrap () := by
  rw [greedyFold, ← cataR_eq_relCata]
  refine Iff.trans (Λ_comp_est_apply (Salg amount N) (RH Tx) (Sum.inl ()) r) ?_
  constructor
  · rintro ⟨hmem, -⟩
    rw [Salg, junc_sum_inl] at hmem
    exact hmem
  · rintro rfl
    refine ⟨?_, fun z hz => ?_⟩
    · rw [Salg, junc_sum_inl]; rfl
    · rw [Salg, junc_sum_inl] at hz
      obtain rfl : z = ConsList.wrap () := hz
      exact le_iff.mp RH_refl _ _ rfl

/-- The fold `⦇S%∋ est(R;H)⦈` at a `cons`: the tail's answer `y` is extended by `new∪old`, and
    the answer kept is one of those extensions that is `R;H`-below every one of them. -/
public theorem greedyFold_cons (a : Tx) (x : Seg Tx) (r : Sched Tx) :
    greedyFold amount N (ConsList.cons a x) r
      ↔ ∃ y, greedyFold amount N x y ∧ (newR Tx ∪ oldR amount N) (a, y) r
          ∧ ∀ z, (newR Tx ∪ oldR amount N) (a, y) z → RH Tx r z := by
  rw [greedyFold, ← cataR_eq_relCata]
  refine (Iff.rfl : cataR (Λ (Salg amount N) ≫ est (RH Tx)) (ConsList.cons a x) r
      ↔ ∃ y, cataR (Λ (Salg amount N) ≫ est (RH Tx)) x y
          ∧ (Λ (Salg amount N) ≫ est (RH Tx)) (Sum.inr (a, y)) r).trans ?_
  constructor
  · rintro ⟨y, hy, hmem⟩
    rw [Λ_comp_est_apply] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [Salg, junc_sum_inr] at h1
    refine ⟨y, hy, h1, fun z hz => h2 z ?_⟩
    rw [Salg, junc_sum_inr]
    exact hz
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨y, hy, ?_⟩
    rw [Λ_comp_est_apply]
    refine ⟨?_, fun z hz => h2 z ?_⟩
    · rw [Salg, junc_sum_inr]; exact h1
    · rw [Salg, junc_sum_inr] at hz; exact hz

/-- Two kinds of transaction, priced so that one of each fits a van visit and two of the dear
    kind do not: `false` costs 1 and `true` costs 6, against the note's `N = 10`. -/
@[expose] public def vanAmount : Bool → Int := fun b => if b then 6 else 1

/-- The greedy fold on a one-transaction stretch: `new` is the only extension of the empty
    schedule, so the least of them is `[[a]]`. -/
public theorem greedyFold_single (a : Bool) :
    greedyFold vanAmount 10 (ConsList.cons a (ConsList.wrap ()))
      (ConsList.cons (ConsList.cons a (ConsList.wrap ())) (ConsList.wrap ())) := by
  refine (greedyFold_cons _ _ _).mpr ⟨ConsList.wrap (), (greedyFold_wrap _).mpr rfl, Or.inl rfl, ?_⟩
  rintro z (rfl | ⟨s, t, hst, -, -⟩)
  · exact le_iff.mp RH_refl _ _ rfl
  · simp at hst

/-- **The greedy fold `⦇S%∋ est(R;H)⦈` is not even lax natural**: `list(S) ⦇S%∋ est(R;H)⦈ ⊑
    ⦇S%∋ est(R;H)⦈ list(list(S))` fails at `S = not` on the stretch `[false,false]`.  Two cheap
    transactions are one secure segment, so the greedy schedule of `[false,false]` is
    `[[false,false]]` — one van visit; negating them first makes the pair too dear, `old` is
    barred and the greedy schedule of `[true,true]` is `[[true],[true]]` — two visits, and no
    `list(list(not))`-image of a one-visit schedule.  The fold's algebra names its own carrier
    and its own `amount`, so it is an arrow at one object and not a family over it. -/
public theorem greedyFold_not_lax_natural :
    ¬ (list (graph not) ≫ greedyFold vanAmount 10
        ⊑ greedyFold vanAmount 10 ≫ list (list (graph not))) := by
  intro h
  have hmap : list (graph not)
      (ConsList.cons false (ConsList.cons false (ConsList.wrap ())))
      (ConsList.cons true (ConsList.cons true (ConsList.wrap ()))) := by
    rw [list_graph]; rfl
  -- `[true,true]` is too dear to glue, so the greedy answer there is two segments
  have htt : greedyFold vanAmount 10 (ConsList.cons true (ConsList.cons true (ConsList.wrap ())))
      (ConsList.cons (ConsList.cons true (ConsList.wrap ()))
        (ConsList.cons (ConsList.cons true (ConsList.wrap ())) (ConsList.wrap ()))) := by
    refine (greedyFold_cons _ _ _).mpr ⟨_, greedyFold_single true, Or.inl rfl, ?_⟩
    rintro z (rfl | ⟨s, t, hst, -, hsec⟩)
    · exact le_iff.mp RH_refl _ _ rfl
    · injection hst with hs _
      subst hs
      exact absurd hsec (by decide)
  obtain ⟨w, hw, hfw⟩ := le_iff.mp h _ _ ⟨_, hmap, htt⟩
  -- `[false,false]` IS secure, so `old` is on offer and every greedy answer has one segment
  obtain ⟨y, hy, -, hest⟩ := (greedyFold_cons _ _ _).mp hw
  obtain ⟨y', hy', hmem', -⟩ := (greedyFold_cons _ _ _).mp hy
  obtain rfl : y' = ConsList.wrap () := (greedyFold_wrap _).mp hy'
  obtain rfl : y = ConsList.cons (ConsList.cons false (ConsList.wrap ())) (ConsList.wrap ()) := by
    rcases hmem' with rfl | ⟨s, t, hst, -, -⟩
    · rfl
    · simp at hst
  have hlen : clen w ≤ 1 :=
    (hest (ConsList.cons (ConsList.cons false (ConsList.cons false (ConsList.wrap ())))
        (ConsList.wrap ()))
      (Or.inr ⟨ConsList.cons false (ConsList.wrap ()), ConsList.wrap (), rfl, rfl,
        by decide⟩)).1
  simp only [list_graph] at hfw
  have hfw' : ConsList.cons (ConsList.cons true (ConsList.wrap ()))
      (ConsList.cons (ConsList.cons true (ConsList.wrap ())) (ConsList.wrap ()))
      = cmap (cmap not) w := hfw
  cases w with
  | wrap u => simp [cmap] at hfw'
  | cons s t =>
    cases t with
    | wrap u => simp [cmap] at hfw'
    | cons s' t' =>
      have h2 : clen t' + 1 + 1 ≤ 1 := hlen
      omega

end Freyd.Alg.RelSet.Van
