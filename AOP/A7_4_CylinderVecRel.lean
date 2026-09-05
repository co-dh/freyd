/-
  B&dM §7.4's cylinder on `Vec` (the note's §13.5) as RELATIONS in `Rel(Set)`: every bead is the
  `graph` of the function `AOP.A7_4_CylinderVec` already defines, so nothing is redefined here,
  and on top of them sit the greedy algebra `Q`, its fold, and the three laws the derivation
  `paths est(R) ⊒ ⦇Q⦈ est(R)` runs on.

  Composition is diagram order (`≫`): B&dM `X·Y` = Freyd `Y ≫ X`.
-/
module

public import AOP.A7_4_CylinderVec
public import AOP.A7_4_CylinderPaths

namespace Freyd.Alg.Vec.Rel

open Freyd RelSet
open Freyd.Alg.RelSet.Tuple (dTuple tupleP)

variable {a b c d : RelSet.{0}} {n m k j p : Nat}

/-! ## The beads as relations

  A bead whose index map is a BIJECTION is strictly natural: the right-hand side's image can be
  pulled back index by index.  `moves` reads each entry three times and `cp` copies the square
  into every entry, so for those the right-hand side may choose a different image per copy and
  only the inclusion holds. -/

/-- **`moves` is lax natural**: `Vec(n)(S) moves ⊑ moves Vec(3)(Vec(n)(S))`.  Not an equality:
    the three rows of the right-hand side may take unrelated `S`-images of one entry. -/
public theorem moves_lax_natural (S : a ⟶ b) :
    tupleP n S ≫ RelSet.graph moves ⊑ RelSet.graph moves ≫ tupleP 3 (tupleP n S) := by
  refine le_iff.mpr fun t V h => ?_
  obtain ⟨u, hu, hV⟩ := h
  have hVeq : V = moves u := hV
  subst hVeq
  exact ⟨moves t, rfl, fun _ _ => hu _⟩

/-- **`trans` is natural**: transposing is a bijection on indices, so the transpose of an image is
    the image of the transpose — read backwards by transposing again. -/
public theorem trans_natural (S : a ⟶ b) :
    tupleP 3 (tupleP n S) ≫ RelSet.graph trans = RelSet.graph trans ≫ tupleP n (tupleP 3 S) := by
  apply hom_ext; intro v W
  constructor
  · rintro ⟨u, hu, hW⟩
    have hWeq : W = trans u := hW
    subst hWeq
    exact ⟨trans v, rfl, fun i k => hu k i⟩
  · rintro ⟨z, hz, hW⟩
    have hzeq : z = trans v := hz
    subst hzeq
    exact ⟨fun k i => W i k, fun k i => hW i k, rfl⟩

/-- **`concat` is natural**: flattening is a bijection on indices, entry `r·p+i` of the row laid
    out being entry `i` of row `r`, so an image of the flattening is the flattening of an image. -/
public theorem concat_natural (S : a ⟶ b) :
    tupleP j (tupleP p S) ≫ RelSet.graph concat = RelSet.graph concat ≫ tupleP (j * p) S := by
  apply hom_ext; intro v W
  constructor
  · rintro ⟨u, hu, hW⟩
    have hWeq : W = concat u := hW
    subst hWeq
    exact ⟨concat v, rfl, fun _ => hu _ _⟩
  · rintro ⟨z, hz, hW⟩
    have hzeq : z = concat v := hz
    subst hzeq
    refine ⟨fun r i => W ⟨r.val * p + i.val, concat_lt r i⟩, fun r i => ?_, ?_⟩
    · have hl := hW ⟨r.val * p + i.val, concat_lt r i⟩
      rwa [concat_mk] at hl
    · funext l
      exact congrArg W (Fin.eq_of_val_eq (Nat.div_add_mod' l.val p)).symm

/-- **`zip` is natural**: `F(Vec(n)(S),Vec(n)(T)) zip = zip Vec(n)(F(S,T))`.  `graph zip` IS
    `AOP.A7_4_CylinderBeads`'s `zipT`, so this is that square, restated for the `Vec` bead. -/
public theorem zip_natural (S : a ⟶ b) (T : c ⟶ d) :
    rprodMap (tupleP n S) (tupleP n T) ≫ RelSet.graph zip
      = RelSet.graph zip ≫ tupleP n (rprodMap S T) :=
  Tuple.zip_natural S T

/-- **`cp` is lax natural**: `F(S,Vec(k)(T)) cp ⊑ cp Vec(k)(F(S,T))`.  Not an equality: the copied
    square is one point on the left and may take a different `S`-image in each entry on the
    right. -/
public theorem cp_lax_natural (S : a ⟶ b) (T : c ⟶ d) :
    rprodMap S (tupleP k T) ≫ RelSet.graph cp ⊑ RelSet.graph cp ≫ tupleP k (rprodMap S T) := by
  refine le_iff.mpr fun q r h => ?_
  obtain ⟨w, ⟨h1, h2⟩, hr⟩ := h
  have hreq : r = cp w := hr
  subst hreq
  exact ⟨cp q, rfl, fun i => ⟨h1, h2 i⟩⟩

/-- **`cons` is natural**: `F(S,Vec(m)(S)) cons = cons Vec(m+1)(S)`.  A head and a tail is a
    bijection with a tuple one longer, `uncons` reading it backwards. -/
public theorem cons_natural (S : a ⟶ b) :
    rprodMap S (tupleP m S) ≫ RelSet.graph cons = RelSet.graph cons ≫ tupleP (m + 1) S := by
  apply hom_ext; intro q W
  constructor
  · rintro ⟨r, ⟨h1, h2⟩, hW⟩
    have hWeq : W = cons r := hW
    subst hWeq
    refine ⟨cons q, rfl, fun l => ?_⟩
    induction l using Fin.cases with
    | zero => exact h1
    | succ i => exact h2 i
  · rintro ⟨z, hz, hW⟩
    have hzeq : z = cons q := hz
    subst hzeq
    exact ⟨uncons W, ⟨hW 0, fun i => hW i.succ⟩, (congrFun uncons_cons W).symm⟩

/-! ## `tupleP`'s laws

  The relator laws of `Vec(n)` on relations.  They live here rather than beside `tupleP` because
  only the derivation below composes with them. -/

/-- `Vec(n)(𝟙) = 𝟙`: agreeing entry by entry is being the same tuple. -/
public theorem tupleP_id : tupleP n (𝟙 a) = 𝟙 (dTuple n a) := by
  apply hom_ext; intro t u
  exact ⟨fun h => funext fun i => h i, fun h i => congrFun h i⟩

/-- `Vec(n)(S) Vec(n)(T) = Vec(n)(ST)`: the intermediate tuple is chosen entry by entry. -/
public theorem tupleP_comp (S : a ⟶ b) (T : b ⟶ c) :
    tupleP n (S ≫ T) = tupleP n S ≫ tupleP n T := by
  apply hom_ext; intro t w
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Tuple.tuple_of_forall_exists (fun i => h i)
    exact ⟨u, fun i => (hu i).1, fun i => (hu i).2⟩
  · rintro ⟨u, h1, h2⟩ i
    exact ⟨u i, h1 i, h2 i⟩

/-- `Vec(n)` is monotonic. -/
public theorem tupleP_mono {S T : a ⟶ b} (h : S ⊑ T) : tupleP n S ⊑ tupleP n T :=
  le_iff.mpr fun _ _ hS i => le_iff.mp h _ _ (hS i)

/-- `Vec(n)` of a function's graph is the graph of `Vec(n)`'s action on it. -/
public theorem tupleP_graph (f : a.carrier → b.carrier) :
    tupleP n (RelSet.graph f) = (RelSet.graph ((Vec n).map f) : dTuple n a ⟶ dTuple n b) := by
  apply hom_ext; intro t u
  constructor
  · intro h
    show u = _
    funext i
    exact h i
  · intro h i
    show u i = f (t i)
    exact congrFun h i

/-! ## `∋` and `est` on a vector -/

/-- **`∋ : X[k]⟶X`** — a component of the vector, the note's membership on a row. -/
@[expose] public def mem {k : Nat} : dTuple k a ⟶ a := fun v x => ∃ i, v i = x

/-- **`est(S) ≜ ∋∩(∈\S°)`** on a vector: a component that is `S`-below every component. -/
@[expose] public def est (S : a ⟶ a) {k : Nat} : dTuple k a ⟶ a :=
  fun v x => (∃ i, v i = x) ∧ ∀ i, S x (v i)

/-- **`est(S) = ∋∩(∈\S°)`** — the pointwise definition above is B&dM's operator, `∈ = ∋°`. -/
public theorem est_eq (S : a ⟶ a) : (est S : dTuple k a ⟶ a) = mem ∩ (mem° \ S°) := by
  apply hom_ext; intro v x
  constructor
  · rintro ⟨hx, hall⟩
    exact ⟨hx, fun z hz => by obtain ⟨i, hi⟩ := hz; exact hi ▸ hall i⟩
  · rintro ⟨hx, hall⟩
    exact ⟨hx, fun i => hall (v i) ⟨i, rfl⟩⟩

/-! ## The greedy algebra and its fold -/

/-- **`Q(S) ≜ F(𝟙,moves trans Vec(n)(est(S))) zip Vec(n)(cons)`** — `gen` with the choice made:
    each square keeps ONE cheapest of the three paths offered by its neighbours, and the square
    goes in front of it. -/
@[expose] public def Q {n m : Nat} (S : dTuple m a ⟶ dTuple m a) :
    (⟨(dTuple n a).carrier × (dTuple n (dTuple m a)).carrier⟩ : RelSet.{0})
      ⟶ dTuple n (dTuple (m + 1) a) :=
  rprodMap (𝟙 (dTuple n a)) (RelSet.graph moves ≫ RelSet.graph trans ≫ tupleP n (est S))
    ≫ RelSet.graph zip ≫ tupleP n (RelSet.graph cons)

/-- **`⦇Q⦈`** — the greedy fold: one cheapest path per square, extended a column at a time.  The
    order compared at stage `m` is `R (m+1)`, the length the fold has already built. -/
@[expose] public def Qfold {n : Nat} (R : (i : Nat) → dTuple i a ⟶ dTuple i a) :
    (m : Nat) → dTuple (m + 1) (dTuple n a) ⟶ dTuple n (dTuple (m + 1) a)
  | 0 => RelSet.graph fun v i _ => v 0 i
  | m + 1 => RelSet.graph uncons ≫ rprodMap (𝟙 (dTuple n a)) (Qfold R m) ≫ Q (R (m + 1))

/-- **`α⦇Q⦈ = F(𝟙,⦇Q⦈)Q`** at `α = cons` — the greedy fold's defining equation. -/
public theorem cons_Qfold (R : (i : Nat) → dTuple i a ⟶ dTuple i a) {n m : Nat} :
    (RelSet.graph cons : (⟨(dTuple n a).carrier × (dTuple (m + 1) (dTuple n a)).carrier⟩ : RelSet.{0})
        ⟶ dTuple (m + 2) (dTuple n a)) ≫ Qfold R (m + 1)
      = rprodMap (𝟙 (dTuple n a)) (Qfold R m) ≫ Q (R (m + 1)) := by
  have h : (RelSet.graph cons : (⟨(dTuple n a).carrier × (dTuple (m + 1) (dTuple n a)).carrier⟩
        : RelSet.{0}) ⟶ dTuple (m + 2) (dTuple n a)) ≫ RelSet.graph uncons = 𝟙 _ := by
    rw [RelSet.graph_comp]
    exact hom_ext fun _ _ => ⟨Eq.symm, Eq.symm⟩
  show RelSet.graph cons ≫ RelSet.graph uncons ≫ _ = _
  rw [← Cat.assoc, h]
  exact Cat.id_comp _

/-! ## The laws of the derivation -/

/-- **`Vec(j)(est(S)) est(S) ⊑ concat est(S)`** — a cheapest of each of the `j` rows and then a
    cheapest of those is a cheapest of all `j·k` entries.  Needs `S` transitive. -/
public theorem est_concat {S : a ⟶ a} (htrans : S ≫ S ⊑ S) :
    (tupleP j (est S) ≫ est S : dTuple j (dTuple k a) ⟶ a) ⊑ RelSet.graph concat ≫ est S := by
  refine le_iff.mpr fun v x h => ?_
  obtain ⟨u, hu, ⟨r₀, hr₀⟩, hxu⟩ := h
  obtain ⟨i₀, hi₀⟩ := (hu r₀).1
  refine ⟨concat v, rfl, ⟨⟨r₀.val * k + i₀.val, concat_lt r₀ i₀⟩, ?_⟩, fun l => ?_⟩
  · rw [concat_mk]; exact hi₀.trans hr₀
  · exact le_iff.mp htrans x _ ⟨u _, hxu _, (hu _).2 _⟩

/-- **(7.13)** `F(𝟙,est(R)) cons ⊑ cp Vec(k)(cons) est(R)` — choose the cheapest path and put the
    square in front of it, or put the square in front of all `k` and choose.  Needs `hmono`:
    putting the same square in front keeps the cost order. -/
public theorem cyl_7_13 {R : (i : Nat) → dTuple i a ⟶ dTuple i a} {m k : Nat}
    (hmono : rprodMap (𝟙 a) (R m) ≫ RelSet.graph cons ⊑ RelSet.graph cons ≫ R (m + 1)) :
    rprodMap (𝟙 a) (est (R m) (k := k)) ≫ RelSet.graph cons
      ⊑ RelSet.graph cp ≫ tupleP k (RelSet.graph cons) ≫ est (R (m + 1)) := by
  refine le_iff.mpr fun q y h => ?_
  obtain ⟨q₁, q₂⟩ := q
  obtain ⟨⟨r₁, r₂⟩, ⟨hx, ⟨⟨i₀, hi₀⟩, hall⟩⟩, hy⟩ := h
  have hxeq : q₁ = r₁ := hx
  have hyeq : y = cons (r₁, r₂) := hy
  subst hxeq; subst hyeq
  refine ⟨cp (q₁, q₂), rfl, fun i => cons (q₁, q₂ i), fun _ => rfl, ⟨⟨i₀, ?_⟩, fun i => ?_⟩⟩
  · exact congrArg (fun w => cons (q₁, w)) hi₀
  · obtain ⟨w, hw, hR⟩ := le_iff.mp hmono (q₁, r₂) (cons (q₁, q₂ i))
      ⟨(q₁, q₂ i), ⟨rfl, hall i⟩, rfl⟩
    have hweq : w = cons (q₁, r₂) := hw
    subst hweq
    exact hR

/-- **The fusion condition** `F(𝟙,Vec(n)(est(R))) Q ⊑ gen Vec(n)(est(R))` — choosing a cheapest
    path per square before extending the column is no better than extending and choosing after.
    The left `est` is over the `p` paths of a square, the right over the `3p` of the next
    column. -/
public theorem cyl_fusion {R : (i : Nat) → dTuple i a ⟶ dTuple i a} {n m p : Nat}
    (htrans : R m ≫ R m ⊑ R m)
    (hmono : rprodMap (𝟙 a) (R m) ≫ RelSet.graph cons ⊑ RelSet.graph cons ≫ R (m + 1)) :
    rprodMap (𝟙 (dTuple n a)) (tupleP n (est (R m) (k := p))) ≫ Q (R m)
      ⊑ RelSet.graph gen ≫ tupleP n (est (R (m + 1))) := by
  refine le_iff.mpr fun q z h => ?_
  obtain ⟨q₁, q₂⟩ := q
  obtain ⟨⟨y₁, y₂⟩, ⟨hu, hw⟩, ⟨y₁', y₂'⟩, ⟨hu', s, hs, t, ht, hbest⟩, cs, hcs, hz⟩ := h
  have hueq : q₁ = y₁ := hu
  have hu'eq : y₁ = y₁' := hu'
  have hseq : s = moves y₂ := hs
  have hteq : t = trans s := ht
  subst hueq; subst hu'eq; subst hseq; subst hteq
  have hcseq : cs = zip (q₁, y₂') := hcs
  subst hcseq
  refine ⟨gen (q₁, q₂), rfl, fun i => ?_⟩
  -- a cheapest of the three neighbours' cheapests is a cheapest of all `3p` candidates …
  obtain ⟨_, hcat0, hcat⟩ := le_iff.mp (est_concat htrans) (trans (moves q₂) i) (y₂' i)
    ⟨trans (moves y₂) i, fun _ => hw _, hbest i⟩
  have hcat0eq : _ = concat (trans (moves q₂) i) := hcat0
  subst hcat0eq
  -- … and putting the square in front of that cheapest is (7.13).
  obtain ⟨v₁, hv₁, v₂, hv₂, hest⟩ := le_iff.mp (cyl_7_13 hmono)
    (q₁ i, concat (trans (moves q₂) i)) (z i) ⟨(q₁ i, y₂' i), ⟨rfl, hcat⟩, hz i⟩
  have hv₁eq : v₁ = cp (q₁ i, concat (trans (moves q₂) i)) := hv₁
  subst hv₁eq
  have hv : v₂ = gen (q₁, q₂) i := funext fun k' => hv₂ k'
  exact hv ▸ hest

/-- **`⦇Q⦈ ⊑ ⦇gen⦈ Vec(n)(est(R))`** — the greedy fold picks one of the paths `⦇gen⦈` generates,
    and a cheapest one.  By induction on the columns, from the fusion condition. -/
public theorem Qfold_le_genFold {R : (i : Nat) → dTuple i a ⟶ dTuple i a} {n : Nat}
    (hrefl : ∀ i, 𝟙 (dTuple i a) ⊑ R i) (htrans : ∀ i, R i ≫ R i ⊑ R i)
    (hmono : ∀ i, rprodMap (𝟙 a) (R i) ≫ RelSet.graph cons ⊑ RelSet.graph cons ≫ R (i + 1)) : ∀ m : Nat,
    (Qfold R m : dTuple (m + 1) (dTuple n a) ⟶ dTuple n (dTuple (m + 1) a))
      ⊑ RelSet.graph (genFold m) ≫ tupleP n (est (R (m + 1)))
  | 0 => by
      refine le_iff.mpr fun v z h => ?_
      have hzeq : z = fun i (_ : Fin 1) => v 0 i := h
      subst hzeq
      exact ⟨genFold 0 v, rfl, fun i => ⟨⟨⟨0, by decide⟩, rfl⟩, fun l =>
        le_iff.mp (hrefl 1) _ _ rfl⟩⟩
  | m + 1 => by
      have h1 : rprodMap (𝟙 (dTuple n a)) (Qfold R m)
          ⊑ rprodMap (𝟙 (dTuple n a)) (RelSet.graph (genFold m))
              ≫ rprodMap (𝟙 (dTuple n a)) (tupleP n (est (R (m + 1)))) := by
        rw [rprodMap_comp, Cat.id_comp]
        exact rprodMap_mono (le_refl _) (Qfold_le_genFold hrefl htrans hmono m)
      have key : rprodMap (𝟙 (dTuple n a)) (Qfold R m) ≫ Q (R (m + 1))
          ⊑ rprodMap (𝟙 (dTuple n a)) (RelSet.graph (genFold m))
              ≫ RelSet.graph gen ≫ tupleP n (est (R (m + 1 + 1))) := by
        refine le_trans (comp_mono_right h1 _) ?_
        rw [Cat.assoc]
        exact comp_mono_left _ (cyl_fusion (htrans (m + 1)) (hmono (m + 1)))
      -- `graph_id` and `rprodMap_graph` are module-private in `AOP.A6_1_RelSet`, so the pair's
      -- graph is re-derived here rather than cited.
      have hpair : rprodMap (𝟙 (dTuple n a)) (RelSet.graph (genFold (n := n) (A := a.carrier) m))
          = RelSet.graph (Prod.map id (genFold (n := n) (A := a.carrier) m)) := by
        apply hom_ext; intro q r
        obtain ⟨r₁, r₂⟩ := r
        constructor
        · rintro ⟨h1, h2⟩
          have h1' : q.1 = r₁ := h1
          subst h1'; subst h2; rfl
        · intro h
          injection h with h1 h2
          exact ⟨h1.symm, h2⟩
      have hgraph : (RelSet.graph uncons ≫ rprodMap (𝟙 (dTuple n a)) (RelSet.graph (genFold m)))
          ≫ RelSet.graph gen = RelSet.graph (genFold (m + 1)) := by
        rw [hpair, RelSet.graph_comp, RelSet.graph_comp]
        rfl
      show RelSet.graph uncons ≫ rprodMap (𝟙 (dTuple n a)) (Qfold R m) ≫ Q (R (m + 1)) ⊑ _
      refine le_trans (comp_mono_left _ key) ?_
      rw [← Cat.assoc, ← Cat.assoc, hgraph]
      exact le_refl _

/-- **`⦇Q⦈ est(R) ⊑ paths est(R)`** — the note's `paths est(R) ⊒ ⦇Q⦈ est(R)`: the greedy fold
    followed by a cheapest of the `n` column answers is a cheapest of all `n·3^m` paths. -/
public theorem cyl_laws {R : (i : Nat) → dTuple i a ⟶ dTuple i a} {n m : Nat}
    (hrefl : ∀ i, 𝟙 (dTuple i a) ⊑ R i) (htrans : ∀ i, R i ≫ R i ⊑ R i)
    (hmono : ∀ i, rprodMap (𝟙 a) (R i) ≫ RelSet.graph cons ⊑ RelSet.graph cons ≫ R (i + 1)) :
    (Qfold R m : dTuple (m + 1) (dTuple n a) ⟶ _) ≫ est (R (m + 1))
      ⊑ RelSet.graph paths ≫ est (R (m + 1)) := by
  refine le_trans (comp_mono_right (Qfold_le_genFold hrefl htrans hmono m) _) ?_
  rw [Cat.assoc]
  refine le_trans (comp_mono_left _ (est_concat (htrans (m + 1)))) ?_
  rw [← Cat.assoc, RelSet.graph_comp]
  exact le_refl _

end Freyd.Alg.Vec.Rel
