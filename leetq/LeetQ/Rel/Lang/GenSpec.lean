import LeetQ.Run.Lang.Gen
import LeetQ.Rel.Lang.BitsSpecRun
import LeetQ.Rel.CRelRel
import LeetQ.Run.CRelRelDef
import LeetQ.Rel.CRelArith
import LeetQ.Run.CRelArithDef
import LeetQ.Rel.CRelFold
import LeetQ.Run.CRelFoldDef
import LeetQ.Rel.CRelPower
import LeetQ.Rel.CRelLoop
import LeetQ.Rel.CRelEst

/-! The code of `Gen` read back: one lemma per combinator, saying that where its ok bit is set its relation is
    the allegory's operation on its parts' relations, so `Expand` assembles the correctness of a definition from
    these lemmas structurally over its term. A term that runs on demand is read only at the keys it is given
    (§a), so `Sound f T` says that `f` and `T` agree on those keys: `D ≫ rep(f D) = D ≫ T`, pointwise. A closed
    term has no keys, and there it is the equation `rep(f ()) = T` (`Sound.eq`). -/

namespace LeetQ.Rel.Lang.Gen

open LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep Freyd Freyd.Alg Freyd.Alg.RelSet QLean.Kernel

/-- An arrow `A ⟶ B` of `Rel(Set)` between the elements of two objects. -/
abbrev Den (A B : Obj) := (⟨A.El⟩ : RelSet.{0}) ⟶ ⟨B.El⟩

/-- The keys `D` as a relation: the coreflexive itself on demand, `𝟙` for a closed term. -/
def keys : {d : Bool} → {A : Obj} → Dem d A → Den A A
  | true, _, D => rep D
  | false, _, _ => 𝟙 _

/-- The keys a term is given form a coreflexive. -/
def Cor : {d : Bool} → {A : Obj} → Dem d A → Prop
  | true, _, D => ∀ x y, rep D x y → x = y
  | false, _, _ => True

/-- `f` computes `T` on its keys: given a coreflexive `D` and its ok bit, `x {rep(f D)} y ↔ x {T} y` at each key
    `x` of `D`. -/
def Sound {d : Bool} {A B : Obj} (f : Fn d A B) (T : Den A B) : Prop :=
  ∀ D : Dem d A, Cor D → (f D).ok = true → ∀ x y, keys D x x → (rep (f D).rel x y ↔ T x y)

/-- A closed term's `Sound` is the equation of its relation. -/
theorem Sound.eq {A B : Obj} {f : Fn false A B} {T : Den A B} (h : Sound f T) (hb : (f ()).ok = true) :
    rep (f ()).rel = T :=
  hom_ext fun x y => h () trivial hb x y rfl

/-- A plan computes `T` on its keys, read by `TP.den`, the relation it denotes. -/
def PSound {d : Bool} {A B : Obj} (p : Pl d A B) (T : Den A B) : Prop :=
  ∀ D : Dem d A, Cor D → (p D).2 = true → ∀ x y, keys D x x → ((p D).1.den x y ↔ T x y)

/-! ### Keys -/

theorem demL {A : Obj} : ∀ (d e : Bool) (D : Dem (d || e) A) (x : A.El), Cor D → keys D x x →
    Cor (Dem.l d e D) ∧ keys (Dem.l d e D) x x
  | true, _, _, _, h, k => ⟨h, k⟩
  | false, _, _, _, _, _ => ⟨trivial, rfl⟩

theorem demR {A : Obj} : ∀ (d e : Bool) (D : Dem (d || e) A) (x : A.El), Cor D → keys D x x →
    Cor (Dem.r d e D) ∧ keys (Dem.r d e D) x x
  | true, true, _, _, h, k => ⟨h, k⟩
  | false, true, _, _, h, k => ⟨h, k⟩
  | _, false, _, _, _, _ => ⟨trivial, rfl⟩

/-- A coreflexive `K` given as the keys of `S`: `S` agrees with `T` at every key of `K`. -/
theorem atKeys {B C : Obj} {e : Bool} {S : Fn e B C} {T : Den B C} (hS : Sound S T) (K : Rel B B)
    (hc : ∀ x y, rep K x y → x = y) (hb : (S (Dem.of e K)).ok = true) :
    ∀ b c, rep K b b → (rep (S (Dem.of e K)).rel b c ↔ T b c) := by
  cases e
  · exact fun b c _ => hS () trivial hb b c rfl
  · exact fun b c hk => hS K hc hb b c hk

/-- A coreflexive's row values: on the keys of `D`, every key is one of `D.val`'s rows. -/
theorem keyRow {A : Obj} {D : Rel A A} {x : A.El} (h : rep D x x) : ∃ i, D.val.row i = x :=
  let ⟨i, _, e⟩ := h; ⟨i, e⟩

theorem rowKey {A : Obj} {D : Rel A A} (hD : ∀ x y, rep D x y → x = y) {x : A.El} :
    (∃ i, D.val.row i = x) → rep D x x := by
  rintro ⟨i, rfl⟩
  have h : rep D (D.key.row i) (D.val.row i) := ⟨i, rfl, rfl⟩
  rw [hD _ _ h] at h; exact h

/-- `ranC`'s and `CRel.ran`'s relation: the coreflexive on `R`'s values. -/
theorem ran_iff {A B : Obj} (R : Den A B) (y y' : B.El) :
    (𝟙 _ ∩ R° ≫ R°° : Den B B) y y' ↔ y = y' ∧ ∃ x, R x y ∧ R x y' := Iff.rfl

theorem ok_and {A B : Obj} {b : Bool} {k : Unit → CRel A B} (h : (CRel.guard b k).ok = true) : b = true := by
  rw [CRel.guard_ok, Bool.and_eq_true] at h; exact h.1

/-! ### Leaves -/

theorem const_sound {A B : Obj} {c : CRel A B} {T : Den A B} (h : c.ok = true → rep c.rel = T) :
    Sound (const A B c) T := fun ⟨⟩ _ hb x y _ => by rw [show (const A B c ()) = c from rfl, h hb] at *

theorem val_sound {A B : Obj} (R : Rel A B × Bool) : Sound (val A B R) (rep R.1) :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem uni_sound {A : Obj} {m : USize} (U : Vals A m × Bool) : Sound (uni A m U) (rep (idU U.1)) :=
  fun _ _ _ _ _ _ => Iff.rfl

/-- `succ`, `arith`, `≤`, `<` on a declared object's universe `uni` read its literal `U` directly: the one
    definition of each is also the literal form, so no second copy can drift from it. -/
theorem uni_lits {m : USize} (U : Vals .long m × Bool) (k : UInt8) :
    succ (uni .long m U) = (fun D => also U.2 (CRel.comp ⟨D, true⟩ (CRel.succ U.1))) ∧
    arith k (uni .long m U) = (fun D => CRel.comp ⟨Alg.arith k D.val, true⟩ ⟨idU U.1, U.2⟩) ∧
    leq (uni .long m U) = (fun _ => also U.2 (CRel.leq U.1)) ∧
    lt (uni .long m U) = (fun _ => also U.2 (CRel.lt U.1)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem zero_sound {A B : Obj} : Sound (zero A B) 𝟘 := fun _ _ _ x y _ => by
  show rep (Alg.zero : Rel A B) x y ↔ _; rw [rep_zero]

theorem id_sound {A : Obj} : Sound (id A) (𝟙 _) := fun D hD _ x y hx =>
  ⟨fun h => hD x y h, fun e => e ▸ hx⟩

theorem outl_sound {A B : Obj} : Sound (outl A B) (graph Prod.fst) := fun D hD _ x y hx => by
  show rep (Alg.outl D) x y ↔ _; rw [rep_outl]
  exact ⟨fun ⟨z, h, e⟩ => (hD x z h) ▸ e, fun e => ⟨x, hx, e⟩⟩

theorem outr_sound {A B : Obj} : Sound (outr A B) (graph Prod.snd) := fun D hD _ x y hx => by
  show rep (Alg.outr D) x y ↔ _; rw [rep_outr]
  exact ⟨fun ⟨z, h, e⟩ => (hD x z h) ▸ e, fun e => ⟨x, hx, e⟩⟩

theorem inl_sound {A B : Obj} : Sound (ofVals A (.sum A B) CRel.inl) (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ := fun D _ hb x y hx => by
  show rep (CRel.inl (B := B) D.val).rel x y ↔ _; rw [CRel.rep_inl _ hb]
  exact ⟨fun ⟨z, ⟨e, _⟩, h⟩ => e ▸ h, fun h => ⟨x, ⟨rfl, keyRow hx⟩, h⟩⟩

theorem inr_sound {A B : Obj} : Sound (ofVals B (.sum A B) CRel.inr) (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ := fun D _ hb x y hx => by
  show rep (CRel.inr (A := A) D.val).rel x y ↔ _; rw [CRel.rep_inr _ hb]
  exact ⟨fun ⟨z, ⟨e, _⟩, h⟩ => e ▸ h, fun h => ⟨x, ⟨rfl, keyRow hx⟩, h⟩⟩

theorem mem_sound {B : Obj} : Sound (ofVals (.arr B) B CRel.mem) (fun xs x => x ∈ xs) := fun D _ hb xs x hx => by
  show rep (CRel.mem D.val).rel xs x ↔ _; rw [CRel.rep_mem _ hb]
  exact ⟨fun h => h.2, fun h => ⟨keyRow hx, h⟩⟩

/-! ### The rows of `prims` -/

/-- A row read on its keys' values computes `T` where its kernel relates each listed value by `T`. -/
theorem ofVals_sound {A B : Obj} {f : {n : USize} → Vals A n → CRel A B} {T : Den A B}
    (h : ∀ {n : USize} (X : Vals A n), (f X).ok = true → ∀ x y, rep (f X).rel x y ↔ (∃ j, X.row j = x) ∧ T x y) :
    Sound (ofVals A B f) T := fun D _ hb x y hx => (h D.val hb x y).trans ⟨And.right, fun t => ⟨keyRow hx, t⟩⟩

/-- A row composed after its keys computes `T` where its kernel is `P` then `T`. -/
theorem after_sound {A B : Obj} {f : {K : Obj} → CRel K A → CRel K B} {T : Den A B}
    (h : ∀ {K : Obj} (P : CRel K A), (f P).ok = true → ∀ k y, rep (f P).rel k y ↔ ∃ a, rep P.rel k a ∧ T a y) :
    Sound (after A B f) T := fun D hD hb x y hx =>
  (h ⟨D, true⟩ hb x y).trans ⟨fun ⟨_, hk, t⟩ => hD x _ hk ▸ t, fun t => ⟨x, hx, t⟩⟩

theorem τ_sound {A : Obj} : Sound (ofVals A (.arr A) fun X => CRel.τ X) (fun a Y => Y = [a]) :=
  ofVals_sound fun X hb => by
    obtain ⟨hX, -, hx, -, hWk, hW, h63⟩ := transposeC_ok (idU X) hb
    exact rep_tau_list X hX hx hWk hW h63

theorem uncons_sound {B : Obj} :
    Sound (ofVals (.arr B) (.prod B (.arr B)) fun X => CRel.uncons X) (fun xs p => xs = p.1 :: p.2) :=
  ofVals_sound fun X hb xs _ => CRel.rep_uncons X hb xs _ _

theorem unsnoc_sound {B : Obj} :
    Sound (ofVals (.arr B) (.prod (.arr B) B) fun X => CRel.unsnoc X) (fun xs p => xs = p.1 ++ [p.2]) :=
  ofVals_sound fun X hb xs _ => CRel.rep_unsnoc X hb xs _ _

theorem uncat_sound {B : Obj} :
    Sound (ofVals (.arr B) (.prod (.arr B) (.arr B)) fun X => CRel.uncat X) (fun xs p => xs = p.1 ++ p.2) :=
  ofVals_sound fun X hb xs _ => CRel.rep_uncat X hb xs _ _

theorem length_sound {B : Obj} :
    Sound (ofVals (.arr B) .long fun X => CRel.length X) (fun xs w => w = Int64.ofNat xs.length) :=
  ofVals_sound fun X hb => CRel.rep_length X hb

/-- `sum` adds in `Int64`: its kernel has no row at an array holding `nul` or one whose partial sums leave the
    `Int64` range, so this is its relation, not `foldr (+) 0` on every array. -/
theorem sum_sound : Sound (ofVals (.arr .long) .long fun X => CRel.Arr.sum X) (fun xs w =>
    (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
      List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ nul) ∧
      w = xs.foldr (· + ·) 0) :=
  ofVals_sound fun X hb => CRel.Arr.rep_sum X hb

theorem inits_sound {B : Obj} : Sound (ofVals (.arr B) (.arr (.arr B)) fun X => CRel.inits X)
    (fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.take k) :=
  ofVals_sound fun X hb => CRel.rep_inits X hb

theorem tails_sound {B : Obj} : Sound (ofVals (.arr B) (.arr (.arr B)) fun X => CRel.tails X)
    (fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k) :=
  ofVals_sound fun X hb => CRel.rep_tails X hb

theorem prefix_sound {B : Obj} : Sound (ofVals (.arr B) (.arr B) fun X => CRel.«prefix» X) (fun xs ys => ys <+: xs) :=
  ofVals_sound fun X hb => CRel.rep_prefix X hb

theorem suffix_sound {B : Obj} : Sound (ofVals (.arr B) (.arr B) fun X => CRel.suffix X) (fun xs ys => ys <:+ xs) :=
  ofVals_sound fun X hb => CRel.rep_suffix X hb

theorem concat_sound {B : Obj} :
    Sound (ofVals (.arr (.arr B)) (.arr B) fun X => CRel.concat X) (fun xss ys => ys = xss.flatten) :=
  ofVals_sound fun X hb => CRel.rep_concat X hb

open Classical in
theorem distinct_sound {B : Obj} :
    Sound (ofVals (.arr B) (.arr B) fun X => CRel.distinct X) (fun xs ys => ys = xs.eraseDups) :=
  ofVals_sound fun X hb xs ys => by
    obtain ⟨h1, h2⟩ := CRel.rep_distinct X hb
    refine ⟨h1 xs ys, fun ⟨hx, e⟩ => ?_⟩
    obtain ⟨Y, hY⟩ := (h2 xs).2 hx
    rwa [e, ← (h1 xs Y hY).2]

open Classical in
/-- `elems`' relation run on the elements of the arrays in demand: at every element of a key `xs`, its test (some
    `y` related) is `TR`'s. -/
theorem elems_test {B C : Obj} {d : Bool} {R : Fn d B C} {TR : Den B C} (hR : Sound R TR) (D : Rel (.arr B) (.arr B))
    (hk : (CRel.ran (CRel.mem D.val)).ok = true) (hr : (R (Dem.of d (CRel.ran (CRel.mem D.val)).rel)).ok = true)
    {xs : (Obj.arr B).El} (hx : rep D xs xs) : ∀ x ∈ xs,
      decide (∃ y, rep (R (Dem.of d (CRel.ran (CRel.mem D.val)).rel)).rel x y) = decide (∃ y, TR x y) :=
  fun x hin => by
    have hK := CRel.rep_ran _ hk
    have h1 : rep (CRel.mem D.val).rel xs x := (CRel.rep_mem _ (ok_and hk) xs x).2 ⟨keyRow hx, hin⟩
    have hs := atKeys hR _ (fun a b h => ((ran_iff _ a b).1 (hK ▸ h)).1) hr
    exact decide_eq_decide.2 (exists_congr fun y => hs x y (hK ▸ (ran_iff _ x x).2 ⟨rfl, xs, h1, h1⟩))

open Classical in
/-- `filter(R)` keeps the elements `TR` relates to something. -/
theorem filter_sound {B : Obj} {d : Bool} {R : Fn d B B} {TR : Den B B} (hR : Sound R TR) :
    Sound (elems B B (.arr B) d R CRel.filter) (fun xs ys => ys = xs.filter fun x => decide (∃ y, TR x y)) :=
  fun D _ hb xs ys hx => by
    simp only [elems, also] at hb ⊢; have hb' := Bool.and_eq_true_iff.1 hb
    rw [CRel.rep_filter _ _ hb'.2, List.filter_congr (elems_test hR D hb'.1 (ok_and hb'.2) hx)]
    exact ⟨And.right, fun t => ⟨keyRow hx, t⟩⟩

open Classical in
/-- `takewhile(R)` keeps the longest prefix of elements `TR` relates to something. -/
theorem takewhile_sound {B : Obj} {d : Bool} {R : Fn d B B} {TR : Den B B} (hR : Sound R TR) :
    Sound (elems B B (.arr B) d R CRel.takewhile) (fun xs ys => ys = xs.takeWhile fun x => decide (∃ y, TR x y)) :=
  fun D _ hb xs ys hx => by
    simp only [elems, also] at hb ⊢; have hb' := Bool.and_eq_true_iff.1 hb
    have hc := elems_test hR D hb'.1 (ok_and hb'.2) hx
    rw [CRel.rep_takewhile _ _ hb'.2]
    suffices e : ∀ {p q : B.El → Bool} (l : List B.El), (∀ x ∈ l, p x = q x) → l.takeWhile p = l.takeWhile q by
      rw [e xs hc]; exact ⟨And.right, fun t => ⟨keyRow hx, t⟩⟩
    intro p q l; induction l with
    | nil => intro _; rfl
    | cons a l ih => intro h; simp only [List.takeWhile_cons, h a List.mem_cons_self,
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem cons_sound {B : Obj} :
    Sound (after (.prod B (.arr B)) (.arr B) fun P => CRel.cons P) (fun p ys => ys = p.1 :: p.2) :=
  after_sound fun P hb k ys => (CRel.rep_cons P hb k ys).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem snoc_sound {B : Obj} :
    Sound (after (.prod (.arr B) B) (.arr B) fun P => CRel.snoc P) (fun p ys => ys = p.1 ++ [p.2]) :=
  after_sound fun P hb k ys => (CRel.rep_snoc P hb k ys).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem cat_sound {B : Obj} :
    Sound (after (.prod (.arr B) (.arr B)) (.arr B) fun P => CRel.cat P) (fun p zs => zs = p.1 ++ p.2) :=
  after_sound fun P hb k zs => (CRel.rep_cat P hb k zs).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem zip_sound {A B : Obj} :
    Sound (after (.prod (.arr A) (.arr B)) (.arr (.prod A B)) fun P => CRel.zip P) (fun p zs => zs = p.1.zip p.2) :=
  after_sound fun P hb k zs => (CRel.rep_zip P hb k zs).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem tic_sound {B : Obj} : Sound (after (.prod B (.arr B)) (.arr (.arr B)) fun P => CRel.tic P)
    (fun p zss => zss = (List.range (p.2.length + 1)).map fun j => (p.1 :: p.2).take (j + 1)) :=
  after_sound fun P hb k zss => (CRel.rep_tic P hb k zss).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

open Classical in
/-- A test `Q` read as an order on the coreflexives a kernel runs it on: `a` before `b` where `Q` relates `(a, b)` to
    something. -/
theorem test_le {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)} (hQ : Sound Q TQ) :
    ∀ (E : Rel (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep E = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) S → (Q E).ok = true →
      ∀ a b, S (a, b) → ((∃ c, rep (Q E).rel (a, b) c) ↔ decide (∃ c, TQ (a, b) c) = true) := fun E S hE hb a b hS => by
  have hC : Cor (d := true) E := fun u v h => (show corefl S u v by rw [← hE]; exact h).1
  have hk : rep E (a, b) (a, b) := by rw [hE]; exact ⟨rfl, hS⟩
  rw [decide_eq_true_iff]; exact exists_congr fun c => hQ E hC hb _ c hk

open Classical in
/-- `merge(Q)` merges by the test `Q` read as an order (`test_le`). -/
theorem merge_sound {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : Sound Q TQ) : Sound (testAfter B (.prod (.arr B) (.arr B)) (.arr B) Q fun q P => CRel.mergeOn q P)
      (fun p zs => zs = List.merge p.1 p.2 fun a b => decide (∃ c, TQ (a, b) c)) := fun D hD hb x zs hx => by
  have hb' : (CRel.mergeOn (fun P => Q P.rel) ⟨D, true⟩).ok = true := hb
  exact (CRel.rep_mergeOn (fun P => Q P.rel) ⟨D, true⟩ (fun a b => decide (∃ c, TQ (a, b) c)) (test_le hQ) hb' x
    zs).trans ⟨fun ⟨_, _, h, e⟩ => hD x _ h ▸ e, fun e => ⟨x.1, x.2, hx, e⟩⟩

open Classical in
/-- `thinL(Q)` bumps each element into the thinned rest by the test `Q` read as an order (`test_le`). -/
theorem thinL_sound {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : Sound Q TQ) : Sound (testVals B (.arr B) (.arr B) Q fun q X => CRel.thinLOn q X)
      (thinLDen fun a b => decide (∃ c, TQ (a, b) c)) :=
  ofVals_sound (f := @fun _ X => CRel.thinLOn (fun P => Q P.rel) X) fun X hb =>
    CRel.rep_thinLOn _ _ X (test_le hQ) hb

/-- A step run on a round's coreflexive `D` of the pairs `S` (`onKeys`) computes `T` at those pairs: `D` has a
    row, so the step ran. -/
theorem onKeys_sound {A B : Obj} {d : Bool} {F : Fn d A B} {T : Den A B} (hF : Sound F T) (D : Rel A A)
    (S : A.El → Prop) (hD : rep D = corefl (A := (⟨A.El⟩ : RelSet.{0})) S) (hb : (onKeys d F ⟨D, true⟩).ok = true) :
    ∀ x y, S x → (rep (onKeys d F ⟨D, true⟩).rel x y ↔ T x y) := fun x y hx => by
  have hk : rep D x x := by rw [hD]; exact ⟨rfl, hx⟩
  unfold onKeys at hb ⊢; dsimp only at hb ⊢
  split
  · rename_i h0
    obtain ⟨i, -⟩ := keyRow hk
    have : D.n.toNat = 0 := by simp [beq_iff_eq.1 h0]
    exact absurd i.2 (by omega)
  · rename_i h0; rw [if_neg h0] at hb
    exact atKeys hF D (fun a b h => (show corefl S a b by rw [← hD]; exact h).1) hb x y hk

/-- `loop(F)` folds the step `F` along each array from the left, from the seed. -/
theorem loop_sound {X Y : Obj} {d : Bool} {F : Fn d (.prod X Y) X} {TF : Den (.prod X Y) X} (hF : Sound F TF) :
    Sound (stepAfter (.prod X Y) X (.prod X (.arr Y)) X d F fun G P => CRel.loopOn G P)
      (fun p c => ∃ g : Nat → X.El, g 0 = p.1 ∧ (∀ t (ht : t < p.2.length), TF (g t, p.2[t]'ht) (g (t + 1))) ∧
        c = g p.2.length) :=
  after_sound (f := @fun _ P => CRel.loopOn (onKeys d F) P) fun P hb k c =>
    (CRel.rep_loopOn _ P hb TF (fun D S hD hb' cy c' hS => (onKeys_sound hF D S hD hb' cy c' hS).symm) k c).trans
      ⟨fun ⟨c₀, xs, h, g⟩ => ⟨(c₀, xs), h, g⟩, fun ⟨⟨c₀, xs⟩, h, g⟩ => ⟨c₀, xs, h, g⟩⟩

/-! ### The allegory's operations -/

theorem comp_sound {A B C : Obj} {e : Bool} {R : Fn true A B} {S : Fn e B C} {TR : Den A B} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (comp A B C e R S) (TR ≫ TS) := by
  intro D hD hb x z hx
  have hr := hR D hD
  unfold comp at hb ⊢
  by_cases h0 : ((R D).rel.n == 0) = true
  · rw [if_pos h0] at hb ⊢
    show rep (Alg.zero : Rel A C) x z ↔ _
    rw [rep_zero]
    refine ⟨False.elim, fun ⟨y, hy, _⟩ => ?_⟩
    obtain ⟨i, -⟩ := (hr hb x y hx).2 hy
    have : (R D).rel.n.toNat = 0 := by simp [beq_iff_eq.1 h0]
    exact absurd i.2 (by omega)
  · rw [if_neg h0] at hb ⊢
    simp only [also, Bool.and_eq_true] at hb ⊢
    obtain ⟨hk, hc⟩ := hb
    have hc2 := ok_and hc; rw [Bool.and_eq_true] at hc2
    have hro : (R D).ok = true := hc2.1
    rw [CRel.rep_comp _ _ hc]
    have hK := CRel.rep_ran (R D) hk
    have hs := atKeys hS (CRel.ran (R D)).rel (fun a b h => ((ran_iff _ a b).1 (hK ▸ h)).1) hc2.2
    refine ⟨fun ⟨y, h1, h2⟩ => ⟨y, (hr hro x y hx).1 h1, ?_⟩, fun ⟨y, h1, h2⟩ => ?_⟩
    · exact (hs y z (hK ▸ (ran_iff _ y y).2 ⟨rfl, x, h1, h1⟩)).1 h2
    · have h1' := (hr hro x y hx).2 h1
      exact ⟨y, h1', (hs y z (hK ▸ (ran_iff _ y y).2 ⟨rfl, x, h1', h1'⟩)).2 h2⟩

theorem conv_sound {A B : Obj} {R : Fn false A B} {T : Den A B} (hR : Sound R T) : Sound (conv A B R) T° :=
  fun ⟨⟩ _ hb y x _ => by
    show rep ((R ()).rel°) y x ↔ _; rw [rep_conv]; exact hR () trivial hb x y rfl

theorem meet_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (meet A B d e R S) (TR ∩ TS) := fun D hD hb x y hx => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.inter _ _).rel x y ↔ _; rw [CRel.rep_inter _ _ hb]
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact and_congr (hR _ cl hc.1 x y kl) (hS _ cr hc.2 x y kr)

theorem join_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (join A B d e R S) (TR ∪ TS) := fun D hD hb x y hx => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.union _ _).rel x y ↔ _; rw [CRel.rep_union _ _ hb]
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact or_congr (hR _ cl hc.1 x y kl) (hS _ cr hc.2 x y kr)

theorem diff_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (diff A B d e R S) (fun x y => TR x y ∧ ¬ TS x y) :=
  fun D hD hb x y hx => by
    have hc := ok_and hb; rw [Bool.and_eq_true] at hc
    show rep (CRel.diff _ _).rel x y ↔ _; rw [CRel.rep_diff _ _ hb]
    obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
    exact and_congr (hR _ cl hc.1 x y kl) (not_congr (hS _ cr hc.2 x y kr))

theorem dom_sound {A B : Obj} {d : Bool} {R : Fn d A B} {T : Den A B} (hR : Sound R T) :
    Sound (dom A B d R) (𝟙 _ ∩ T ≫ T°) := fun D hD hb x x' hx => by
  have hro : (R D).ok = true := ok_and hb
  show rep (CRel.dom (R D)).rel x x' ↔ _; rw [CRel.rep_dom _ hb]
  exact ⟨fun ⟨e, y, h, _⟩ => ⟨e, y, (hR D hD hro x y hx).1 h, e ▸ (hR D hD hro x y hx).1 h⟩,
    fun ⟨e, y, h, _⟩ => ⟨e, y, (hR D hD hro x y hx).2 h, e ▸ (hR D hD hro x y hx).2 h⟩⟩

theorem ran_sound {A B : Obj} {R : Fn false A B} {T : Den A B} (hR : Sound R T) :
    Sound (ran A B R) (𝟙 _ ∩ T° ≫ T°°) := fun ⟨⟩ _ hb y y' _ => by
  show rep (CRel.ran (R ())).rel y y' ↔ _; rw [CRel.rep_ran _ hb, (hR.eq (ok_and hb))]

theorem pair_sound {A B C : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A C} {TR : Den A B} {TS : Den A C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (pair A B C d e R S) (rpair TR TS) := fun D hD hb x p hx => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.pair _ _).rel x p ↔ _; rw [CRel.rep_pair _ _ hb]
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact and_congr (hR _ cl hc.1 x p.1 kl) (hS _ cr hc.2 x p.2 kr)

/-- `⟨X,Y⟩ = Xπ₁° ∩ Yπ₂°`: the converse `convTm` gives two sides each read through one projection
    (`Proj.meet`), which is how `(P×Q)° = P°×Q°` runs on demand. -/
theorem rpair_eq_meet_proj {A B C : Obj} (X : Den C A) (Y : Den C B) :
    (X ≫ (graph Prod.fst : Den (.prod A B) A)° ∩ Y ≫ (graph Prod.snd : Den (.prod A B) B)°) = rpair X Y :=
  funext fun _ => funext fun _ => propext
    ⟨fun ⟨⟨_, ha, ea⟩, ⟨_, hb, eb⟩⟩ => ⟨ea ▸ ha, eb ▸ hb⟩, fun ⟨ha, hb⟩ => ⟨⟨_, ha, rfl⟩, ⟨_, hb, rfl⟩⟩⟩

/-- `Xf° ∩ Yf° = (X∩Y)f°` for a map `f`: two sides read through one projection stay so (`Proj.meet`). -/
theorem meet_comp_conv_graph {A B C : Obj} (f : A.El → B.El) (X Y : Den C B) :
    (X ≫ (graph f : Den A B)° ∩ Y ≫ (graph f : Den A B)°) = (X ∩ Y) ≫ (graph f : Den A B)° :=
  funext fun _ => funext fun a => propext
    ⟨fun ⟨⟨w, hx, ex⟩, ⟨w', hy, ey⟩⟩ =>
      ⟨w, ⟨hx, ((show w' = f a from ey).trans (show w = f a from ex).symm) ▸ hy⟩, ex⟩,
      fun ⟨_, ⟨hx, hy⟩, e⟩ => ⟨⟨_, hx, e⟩, ⟨_, hy, e⟩⟩⟩

theorem prod_sound {A B C D : Obj} {R : Fn false A B} {S : Fn false C D} {TR : Den A B} {TS : Den C D}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (prod A B C D R S) (rprodMap TR TS) := fun ⟨⟩ _ hb x y _ => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.prod _ _).rel x y ↔ _; rw [CRel.rep_prod _ _ hb, hR.eq hc.1, hS.eq hc.2]

theorem junc_sound {A B C : Obj} {R : Fn false A C} {S : Fn false B C} {TR : Den A C} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) :
    Sound (junc A B C R S) (Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) TR TS) := fun ⟨⟩ _ hb x y _ => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.junc _ _).rel x y ↔ _; rw [CRel.rep_junc _ _ hb, hR.eq hc.1, hS.eq hc.2]

/-- A relation's value rows are the values its `rep` reaches. -/
theorem valRow {A B : Obj} (U : Rel A B) (b : B.El) : (∃ p, U.val.row p = b) ↔ ∃ a, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.key.row p, p, rfl, e⟩, fun ⟨_, p, _, e⟩ => ⟨p, e⟩⟩

/-- A relation's key rows are the keys its `rep` relates. -/
theorem keyRowRep {A B : Obj} (U : Rel A B) (a : A.El) : (∃ p, U.key.row p = a) ↔ ∃ b, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.val.row p, p, e, rfl⟩, fun ⟨_, p, e, _⟩ => ⟨p, e⟩⟩

theorem nil_sound {A B : Obj} : Sound (nil A B) (fun _ Y => Y = []) := fun D _ hb x Y hx => by
  show rep (topC D.val (nilVal B)).1 x Y ↔ _
  rw [rep_topC _ _ hb]
  refine ⟨fun ⟨_, _, _, _, e, j, hj⟩ => by subst e; rw [← hj, nilVal_row], fun e => ?_⟩
  exact ⟨x, ⟨rfl, keyRow hx⟩, Y, trivial, rfl, ⟨0, by simp⟩, by rw [e, nilVal_row]⟩

theorem atPos_sound {B : Obj} (k : Nat) : Sound (atPos B k) (fun xs x => ∃ h : k < xs.length, x = xs[k]'h) :=
  ofVals_sound (f := fun X => CRel.atPos k X) fun X hb => CRel.rep_atPos k X hb

/-- `succ` on the universe `U`: `u` and its successor both in `U`. -/
theorem succ_sound {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (succ U) (fun u w => (∃ v, TU u v) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ v, TU w v) :=
  fun D hD hb u w hu => by
    simp only [succ, also, Bool.and_eq_true] at hb ⊢
    obtain ⟨hu0, hc⟩ := hb
    have h2 := ok_and hc; rw [Bool.and_eq_true] at h2
    rw [CRel.rep_comp _ _ hc, Freyd.Alg.RelSet.comp_apply]
    have e : ∀ u', rep (CRel.succ (U ()).rel.key).rel u' w ↔ (∃ v, TU u' v) ∧ w = Ew.intStep Ew.add nul u' 1 ∧
        ∃ v, TU w v := fun u' => by
      rw [CRel.rep_succ _ h2.2, keyRowRep, keyRowRep, hU.eq hu0]
    exact ⟨fun ⟨u', hd, h⟩ => hD u u' hd ▸ (e u').1 h, fun h => ⟨u, hu, (e u).2 h⟩⟩

theorem leq_sound {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (leq U) (fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ a ≤ b) := fun ⟨⟩ _ hb a b _ => by
  simp only [leq, also, Bool.and_eq_true] at hb ⊢
  rw [CRel.rep_leq _ _ hb.2, keyRowRep, keyRowRep, hU.eq hb.1]

theorem lt_sound {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (lt U) (fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ a < b) := fun ⟨⟩ _ hb a b _ => by
  simp only [lt, also, Bool.and_eq_true] at hb ⊢
  rw [CRel.rep_lt _ _ hb.2, keyRowRep, keyRowRep, hU.eq hb.1]

/-- A value verb `k` on the universe `U`: `Int64`'s step, not the null and, for `+ - *`, not wrapped, then
    within `U` (`rep_arith`). -/
theorem arith_sound (k : UInt8) {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (arith k U) ((fun (p : (Obj.prod .long .long).El) (w : Obj.long.El) => w = Ew.intStep k nul p.1 p.2 ∧ w ≠ nul ∧
      (if k == Ew.add then (0 ≤ p.2 ↔ p.1 ≤ w) else if k == Ew.sub then (0 ≤ p.2 ↔ w ≤ p.1)
       else if k == Ew.mul then (Ew.intStep Ew.idiv nul w p.1 = p.2 ∨ p.1 = 0) else True) : Den (.prod .long .long) .long) ≫ TU) :=
  fun D _ hb p w hp => by
    have hc := ok_and hb; rw [Bool.and_eq_true] at hc
    show rep (CRel.comp _ _).rel p w ↔ _
    rw [CRel.rep_comp _ _ hb, hU.eq hc.2, Freyd.Alg.RelSet.comp_apply, Freyd.Alg.RelSet.comp_apply]
    obtain ⟨a, b⟩ := p
    exact exists_congr fun v => and_congr_left fun _ => (rep_arith k D.val a b v).trans (and_iff_right (keyRow hp))

/-- `fold(e, S)`: a chain of values `ys`, its last from `e`, each the step `S` of the element and the next value
    (`rep_foldOn`, `S` run on each round's pairs by `onKeys`). -/
theorem fold_sound {E V : Obj} {d : Bool} {e : Fn false V V} {S : Fn d (.prod E V) V} {Te : Den V V}
    {TS : Den (.prod E V) V} (he : Sound e Te) (hS : Sound S TS) :
    Sound (fold E V d e S) (fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ a, Te a (ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm))) ∧
        (∀ t (ht : t < xs.length), TS (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm)) := fun D _ hb xs w hx => by
  simp only [fold, also, Bool.and_eq_true] at hb ⊢
  -- a round's pairs have a row, so `onKeys` runs `S` on them
  have hon : ∀ (K : Rel (.prod E V) (.prod E V)) p w, (∃ a, rep K a p) → (∀ a b, rep K a b → a = b) →
      (onKeys d S ⟨K, true⟩).ok = true → (rep (onKeys d S ⟨K, true⟩).rel p w ↔ TS p w) := by
    intro K p w ⟨a, ha⟩ hc hok
    have h0 : (K.n == 0) = false := by
      obtain ⟨j, -⟩ := ha
      cases h : K.n == 0
      · rfl
      · have : K.n.toNat = 0 := by simp [beq_iff_eq.1 h]
        exact absurd j.2 (by omega)
    simp only [onKeys, h0, Bool.false_eq_true, if_false] at hok ⊢
    exact atKeys hS K hc hok p w (hc a p ha ▸ ha)
  refine (CRel.rep_foldOn _ _ _ hb.2 _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) _
    (fun _ => rfl) (fun _ => TS) ?_ xs w).trans ?_
  · intro i _ _ hbi p w hp hc
    simp only [demandStepC, Bool.and_eq_true] at hbi
    exact hon _ p w hp hc hbi.1.2
  · rw [and_iff_right (keyRow hx)]
    exact exists_congr fun ys => exists_congr fun hy => and_congr_left fun _ =>
      (valRow _ _).trans (by rw [he.eq hb.1])

open LeetQ.Rel.KernelWF LeetQ.Rel.Rep.FoldN LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.Prim in
/-- `est(Q)` keeps `b` of `xs` unless some other `c` of `xs` fails `Q` at `(b, c)`; `Q` runs on the pairs of
    values of one array (`estOnC_ok`'s `pair` and `ran` bits read them back). -/
theorem est_sound {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : Sound Q TQ) :
    Sound (est B Q) (fun xs b => b ∈ xs ∧ ¬ ∃ c, c ∈ xs ∧ c ≠ b ∧ ¬ TQ (b, c) (b, c)) := fun D _ hb xs b hx => by
  have hb' : (CRel.estOn (fun P => Q P.rel) (CRel.mem D.val)).ok = true := hb
  have hG : (CRel.mem D.val).ok = true := ok_and hb'
  obtain ⟨hq, h⟩ := CRel.rep_estOn _ _ hb'
  have e : CRel.estOn (fun P => Q P.rel) (CRel.mem D.val) = _ := CRel.guard_eq CRel.ok hb'
  rw [e] at hb'
  obtain ⟨-, ⟨hPf, hP'⟩, ⟨hDf, hDp⟩, -⟩ := estOnC_ok _ _ hb' _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  obtain ⟨p1, p2, p3, p4, p5⟩ := hP' _ rfl
  have eD : ∀ x x', rep (Alg.ran (Alg.pair (CRel.mem D.val).rel (CRel.mem D.val).rel)) x x' ↔
      x = x' ∧ ∃ a, rep (CRel.mem D.val).rel a x.1 ∧ rep (CRel.mem D.val).rel a x.2 := fun x x' => by
    rw [rep_ran_corefl _ (one_ok _ hDf) hDp, rep_pair _ _ (codes_faithful_wf _ _ hPf).1 p1 p2 p3 p4 p5]; exact Iff.rfl
  have hC : Cor (d := true) (Alg.ran (Alg.pair (CRel.mem D.val).rel (CRel.mem D.val).rel)) :=
    fun x x' h => ((eD x x').1 h).1
  have hr := keyRow hx
  show rep (CRel.estOn (fun P => Q P.rel) (CRel.mem D.val)).rel xs b ↔ _
  rw [h xs b, CRel.rep_mem _ hG, and_iff_right hr]
  refine and_congr_right fun hbx => not_congr (exists_congr fun c => ?_)
  rw [CRel.rep_mem _ hG]
  have hk c (hc : c ∈ xs) : rep (Alg.ran (Alg.pair (CRel.mem D.val).rel (CRel.mem D.val).rel)) (b, c) (b, c) :=
    (eD _ _).2 ⟨rfl, xs, (CRel.rep_mem _ hG xs b).2 ⟨hr, hbx⟩, (CRel.rep_mem _ hG xs c).2 ⟨hr, hc⟩⟩
  exact ⟨fun ⟨⟨_, hc⟩, hne, hn⟩ => ⟨hc, hne, fun t => hn ((hQ _ hC hq _ _ (hk c hc)).2 t)⟩,
    fun ⟨hc, hne, hn⟩ => ⟨⟨hr, hc⟩, hne, fun t => hn ((hQ _ hC hq _ _ (hk c hc)).1 t)⟩⟩

theorem top_sound {A B : Obj} {V : Fn false B B} {TV : Den B B} (hV : Sound V TV) :
    Sound (top A B V) (relTop ≫ TV) := fun D _ hb x y hx => by
  simp only [top, also, ofC, Bool.and_eq_true] at hb ⊢
  rw [rep_topC _ _ hb.2, ← hV.eq hb.1]
  exact ⟨fun ⟨_, _, _, _, e, hq⟩ => let ⟨a, h⟩ := (valRow _ _).1 hq; ⟨a, trivial, e ▸ h⟩,
    fun ⟨a, _, hy⟩ => ⟨x, ⟨rfl, keyRow hx⟩, y, trivial, rfl, (valRow _ _).2 ⟨a, hy⟩⟩⟩

theorem rdiv_sound {A B C : Obj} {R : Fn false A C} {S : Fn false B C} {UA : Fn false A A} {UB : Fn false B B}
    {TR : Den A C} {TS : Den B C} {TA : Den A A} {TB : Den B B} (hR : Sound R TR) (hS : Sound S TS)
    (hA : Sound UA TA) (hB : Sound UB TB) :
    Sound (rdiv A B C R S UA UB)
      (fun x y => (∀ c, TS y c → TR x c) ∧ ((∃ c, TS y c) ∨ ((∃ a, TA a x) ∧ ∃ b, TB b y))) :=
  fun ⟨⟩ _ hb x y _ => by
    simp only [rdiv, also, Bool.and_eq_true] at hb ⊢
    have hc := ok_and hb.2; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_rightDiv _ _ _ _ hb.2, hR.eq hc.1, hS.eq hc.2, valRow, valRow, hA.eq hb.1.1, hB.eq hb.1.2]

/-! ### The bit-matrix plans -/

/-- **`runC`'s answer is the plan's relation** under its bit, on either path, in check mode too (`die` is its
    argument). -/
theorem rep_runC {A B : Obj} {d : Bool} (p : Tm A B d) (hb : (Bits.runC p).2 = true) (a : A.El) (b : B.El) :
    rep (Bits.runC p).1 a b ↔ p.den a b := by
  by_cases hv : p.isVal = true
  · simp only [Bits.runC, hv, if_true] at hb ⊢; exact Bits.rep_tableC p hb a b
  · simp only [Bits.runC, hv, Bool.false_eq_true, if_false] at hb ⊢
    revert hb; split
    · rename_i R h; simp only [dbgTrace, Bits.die, ite_self]; exact fun _ => Bits.bits_table h a b
    · by_cases hc : (Bits.checkOn == 0) = true
      · rw [if_pos hc]; exact fun hb => Bits.rep_tableC _ hb a b
      · rw [if_neg hc]; simp only [dbgTrace]; exact fun hb => Bits.rep_table _ hb a b

/-- The demand `demP` hands `S` in `R S`: a coreflexive holding every value of `R`'s plan. -/
theorem demP_spec {A B : Obj} (e : Bool) (r : Tm A B false) (hb : (demP e r).2 = true) :
    Cor (demP e r).1 ∧ ∀ a b, r.den a b → keys (demP e r).1 b b := by
  cases e
  · exact ⟨trivial, fun _ _ _ => rfl⟩
  · simp only [demP, Bool.and_eq_true] at hb
    have hK := rep_ranC _ hb.2
    have hR := rep_runC r hb.1
    refine ⟨fun a b h => ?_, fun a b h => ?_⟩
    · have h' : rep (ranC (Bits.runC r).1).1 a b := h
      rw [hK] at h'; exact h'.1
    · show rep (ranC (Bits.runC r).1).1 b b
      rw [hK]; exact ⟨rfl, a, (hR a b).2 h, (hR a b).2 h⟩

theorem pleaf_sound {A B : Obj} {d : Bool} {f : Fn d A B} {T : Den A B} (hf : Sound f T) :
    PSound (pleaf A B d f) T := fun D hD hb x y hx => hf D hD hb x y hx

theorem pcomp_sound {A B C : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e B C} {TR : Den A B} {TS : Den B C}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pcomp A B C d e R S) (TR ≫ TS) := by
  intro D hD hb x z hx
  simp only [pcomp, Bool.and_eq_true] at hb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb
  obtain ⟨kc, kk⟩ := demP_spec e _ h2
  have hr := hR D hD h1
  have hs := hS _ kc h3
  exact ⟨fun ⟨b, p1, p2⟩ => ⟨b, (hr x b hx).1 p1, (hs b z (kk x b p1)).1 p2⟩,
    fun ⟨b, p1, p2⟩ => have p1' := (hr x b hx).2 p1; ⟨b, p1', (hs b z (kk x b p1')).2 p2⟩⟩

theorem pconv_sound {A B : Obj} {R : Pl false A B} {T : Den A B} (hR : PSound R T) : PSound (pconv A B R) T° :=
  fun ⟨⟩ _ hb y x _ => hR () trivial hb x y rfl

theorem pmeet_sound {A B : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e A B} {TR TS : Den A B}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pmeet A B d e R S) (TR ∩ TS) := fun D hD hb x y hx => by
  simp only [pmeet, Bool.and_eq_true] at hb
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact and_congr (hR _ cl hb.1 x y kl) (hS _ cr hb.2 x y kr)

theorem pjoin_sound {A B : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e A B} {TR TS : Den A B}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pjoin A B d e R S) (TR ∪ TS) := fun D hD hb x y hx => by
  simp only [pjoin, Bool.and_eq_true] at hb
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact or_congr (hR _ cl hb.1 x y kl) (hS _ cr hb.2 x y kr)

theorem pdiff_sound {A B : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e A B} {TR TS : Den A B}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pdiff A B d e R S) (fun x y => TR x y ∧ ¬ TS x y) :=
  fun D hD hb x y hx => by
    simp only [pdiff, Bool.and_eq_true] at hb
    obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
    exact and_congr (hR _ cl hb.1 x y kl) (not_congr (hS _ cr hb.2 x y kr))

/-- `R\S` within the universes `UB`, `UC`: the book's left division where `R` has a column, every pair of the
    universes where it has none. -/
abbrev ldivDen {A B C : Obj} (TR : Den A B) (TS : Den A C) (TB : Den B B) (TC : Den C C) : Den B C :=
  fun b c => (∀ a, TR a b → TS a c) ∧ ((∃ a, TR a b) ∨ ((∃ b', TB b' b) ∧ ∃ c', TC c' c))

theorem pldiv_sound {A B C : Obj} {R : Pl false A B} {S : Pl false A C} {UB : Fn false B B} {UC : Fn false C C}
    {TR : Den A B} {TS : Den A C} {TB : Den B B} {TC : Den C C} (hR : PSound R TR) (hS : PSound S TS)
    (hB : Sound UB TB) (hC : Sound UC TC) : PSound (pldiv A B C R S UB UC) (ldivDen TR TS TB TC) :=
  fun ⟨⟩ _ hb b c _ => by
    simp only [pldiv, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
    have r a b := hR () trivial h1 a b rfl
    have s a c := hS () trivial h2 a c rfl
    show ((∀ a, _ → _) ∧ ((∃ a, _) ∨ ((∃ p, _) ∧ ∃ j, _))) ↔ _
    rw [Tm.tab, Tm.tab, valRow, valRow, hB.eq h3, hC.eq h4]
    simp only [r, s]

/-- A closed plan run as bits (`Bits.runC`), its leaves' bits kept: the plan's relation. -/
theorem runP_sound {A B : Obj} {p : Pl false A B} {T : Den A B} (hp : PSound p T) :
    Sound (fun _ => also (p ()).2 (ofC (Bits.runC (p ()).1)) : Fn false A B) T := fun ⟨⟩ _ hb x y _ => by
  simp only [also, ofC, Bool.and_eq_true] at hb ⊢
  exact (rep_runC _ hb.2 x y).trans (hp () trivial hb.1 x y rfl)

theorem compB_sound {A B C : Obj} {e : Bool} {R : Pl false A B} {S : Pl e B C} {TR : Den A B} {TS : Den B C}
    (hR : PSound R TR) (hS : PSound S TS) : Sound (compB A B C e R S) (TR ≫ TS) :=
  runP_sound (pcomp_sound hR hS)

theorem meetB_sound {A B : Obj} {R S : Pl false A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    Sound (meetB A B R S) (TR ∩ TS) :=
  runP_sound (pmeet_sound (d := false) (e := false) hR hS)

theorem diffB_sound {A B : Obj} {R S : Pl false A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    Sound (diffB A B R S) (fun x y => TR x y ∧ ¬ TS x y) :=
  runP_sound (pdiff_sound (d := false) (e := false) hR hS)

theorem ldivB_sound {A B C : Obj} {R : Pl false A B} {S : Pl false A C} {UB : Fn false B B} {UC : Fn false C C}
    {TR : Den A B} {TS : Den A C} {TB : Den B B} {TC : Den C C} (hR : PSound R TR) (hS : PSound S TS)
    (hB : Sound UB TB) (hC : Sound UC TC) : Sound (ldivB A B C R S UB UC) (ldivDen TR TS TB TC) :=
  runP_sound (pldiv_sound hR hS hB hC)

end LeetQ.Rel.Lang.Gen
