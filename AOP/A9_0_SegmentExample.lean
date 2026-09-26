/-
  Bird & de Moor §9.1's `H≜⦇T⦈°⦇h⦈` at one worked instance: segmenting a list.

  The base functor is the list functor `F(X) = 𝟏 + [a]×X` (`CL.F Unit (ConsList Unit A)`), and
  `T = [nil, cat]` with `cat` at B&dM's restricted type `list⁺ A × list A` (p.128, `catNE`), so
  `T°` cuts a non-empty prefix off a list every way and `⦇T⦈` is `concat` (`concatNE`).
  WIP: the algebra `h` is still to be chosen; only the `T` side is here.
-/
module

public import AOP.A9_1

namespace Freyd.Alg.RelSet.Segment

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-- **`T = [nil, cat] : FA⟶A`**, `A = [a]`: `inl(()) ↦ []`, `inr(xs,ys) ↦ xs⧺ys` with `xs`
    non-empty, so `T°` cuts off a non-empty prefix every way. -/
@[expose] public def T : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A :=
  junc (sumCop (dL Unit) ⟨ConsList Unit A × ConsList Unit A⟩) wrapR catNE

/-- **`⦇T⦈ = concat`**: folding with `T` flattens a list of non-empty segments. -/
public theorem fold_T :
    (⦇(T : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A)⦈
      : (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) ⟶ dList A) = concatNE := rfl

/-- **`⦇T⦈° = partition`**: unfolding with `T°` segments a list every way. -/
public theorem fold_T_recip :
    (⦇(T : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A)⦈)°
      = (partition : dList A ⟶ (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0})) := by
  rw [fold_T, partition_concat]

/-! ## The algebra `h = [nil, cons(sum×𝟙)]`: each segment replaced by its sum -/

/-- **`h = [nil, cons(sum×𝟙)] : FB⟶B`**, `B = [ℕ]`: `inl(()) ↦ []`, `inr(xs,ys) ↦ sum(xs):ys`. -/
@[expose] public def h : (F Unit (ConsList Unit Nat)).obj (dList Nat) ⟶ dList Nat :=
  junc (sumCop (dL Unit) ⟨ConsList Unit Nat × ConsList Unit Nat⟩) wrapR
    (rprodMap sumR (𝟙 (dList Nat)) ≫ consR)

/-- **`⦇h⦈ = list(sum)`**: folding with `h` sends a list of segments to the list of their sums. -/
public theorem fold_h :
    (⦇h⦈ : (⟨ConsList Unit (ConsList Unit Nat)⟩ : RelSet.{0}) ⟶ dList Nat) = list sumR := by
  rw [sumR, list_graph]
  refine ((relCata_UP (initial Unit (ConsList Unit Nat)) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun D r => ?_, fun seg rest r => ?_⟩)).symm
  · exact Iff.rfl
  · show r = ConsList.cons (csum seg) (cmap csum rest)
        ↔ ∃ y, y = cmap csum rest ∧ ∃ q : Nat × ConsList Unit Nat,
            (q.1 = csum seg ∧ y = q.2) ∧ r = ConsList.cons q.1 q.2
    exact ⟨fun hr => ⟨_, rfl, (csum seg, cmap csum rest), ⟨rfl, rfl⟩, hr⟩,
      fun ⟨y, hy, q, ⟨h1, h2⟩, h3⟩ => by rw [h3, h1, ← h2, hy]⟩

/-- **`H = ⦇T⦈°⦇h⦈ = partition list(sum)`**: segment the list every way, then sum each segment. -/
public theorem H_eq : H T h = partition ≫ list sumR := by
  show (⦇(T : (F Unit (ConsList Unit Nat)).obj (dList Nat) ⟶ dList Nat)⦈)° ≫ ⦇h⦈ = _
  rw [fold_T_recip, fold_h]

/-- **`H = T°F(H)h`**: cut once, solve the rest, put the pieces back together — the fixed-point
    equation `hylo_fixed` at this `T` and `h`. -/
public theorem H_fix :
    T° ≫ (F Unit (ConsList Unit Nat)).map (H T h) ≫ h = H T h :=
  hylo_fixed (F_preservesRecip _ _) _ h T

/-! ## The table: `h` at four inputs, and `H` at `[a,b,c]` -/

public theorem h_nil : h (Sum.inl ()) (ConsList.wrap ()) := (junc_sum_inl _ _ _ _).mpr rfl

public theorem h_c (c : Nat) :
    h (Sum.inr (.cons c (.wrap ()), .wrap ())) (.cons c (.wrap ())) :=
  (junc_sum_inr _ _ _ _).mpr ⟨(c, .wrap ()), ⟨rfl, rfl⟩, rfl⟩

public theorem h_ab_c (a b c : Nat) :
    h (Sum.inr (.cons a (.cons b (.wrap ())), .cons c (.wrap ()))) (.cons (a + b) (.cons c (.wrap ()))) :=
  (junc_sum_inr _ _ _ _).mpr ⟨(a + b, .cons c (.wrap ())), ⟨rfl, rfl⟩, rfl⟩

public theorem h_a_bc (a b c : Nat) :
    h (Sum.inr (.cons a (.wrap ()), .cons (b + c) (.wrap ()))) (.cons a (.cons (b + c) (.wrap ()))) :=
  (junc_sum_inr _ _ _ _).mpr ⟨(a, .cons (b + c) (.wrap ())), ⟨rfl, rfl⟩, rfl⟩

theorem cappend_eq_nil {s y : ConsList Unit A} :
    cappend s y = .wrap () ↔ s = .wrap () ∧ y = .wrap () := by
  cases s with
  | wrap u => cases u; simp [cappend]
  | cons a x => simp [cappend]

theorem cappend_eq_cons {s y x : ConsList Unit A} {b : A} :
    cappend s y = .cons b x ↔ (s = .wrap () ∧ y = .cons b x) ∨ ∃ s', s = .cons b s' ∧ cappend s' y = x := by
  cases s with
  | wrap u => cases u; simp [cappend]
  | cons a s => simp [cappend, and_assoc]

theorem partition_nil {ps : ConsList Unit (ConsList Unit A)} :
    partition (.wrap ()) ps ↔ ps = .wrap () := by
  cases ps with
  | wrap u => cases u; simp [partition, cconcat, allNonempty]
  | cons seg rest => cases seg with
    | wrap u => simp [partition, allNonempty, isNonempty]
    | cons a s => simp [partition, cconcat, cappend]

theorem partition_cons {a : A} {x : ConsList Unit A} {ps : ConsList Unit (ConsList Unit A)} :
    partition (.cons a x) ps
      ↔ ∃ s rest, ps = .cons (.cons a s) rest ∧ ∃ y, cappend s y = x ∧ partition y rest := by
  cases ps with
  | wrap u => simp [partition, cconcat]
  | cons seg rest => cases seg with
    | wrap u => simp [partition, allNonempty, isNonempty]
    | cons a' s =>
      simp only [partition, cconcat, cappend, allNonempty, isNonempty, ConsList.cons.injEq]
      exact ⟨fun ⟨⟨h1, h2⟩, _, h3⟩ => ⟨s, rest, by rw [h1]; exact ⟨⟨rfl, rfl⟩, rfl⟩, _, h2, rfl, h3⟩,
        fun ⟨_, _, hp, y, h1, h2, h3⟩ => by
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
          exact ⟨⟨rfl, by rw [h2]; exact h1⟩, trivial, h3⟩⟩

/-- **`H` at `[a,b,c]`**: exactly the four ways of summing the segments of a three-element list. -/
public theorem H_abc (a b c : Nat) (ys : ConsList Unit Nat) :
    H T h (.cons a (.cons b (.cons c (.wrap ())))) ys
      ↔ ys = .cons (a + b + c) (.wrap ()) ∨ ys = .cons a (.cons (b + c) (.wrap ()))
        ∨ ys = .cons (a + b) (.cons c (.wrap ())) ∨ ys = .cons a (.cons b (.cons c (.wrap ()))) := by
  rw [H_eq, sumR, list_graph]
  show (∃ ps, partition _ ps ∧ ys = cmap csum ps) ↔ _
  have hp : ∀ ps : ConsList Unit (ConsList Unit Nat), cconcat ps = .cons a (.cons b (.cons c (.wrap ())))
      → allNonempty ps → partition (.cons a (.cons b (.cons c (.wrap ())))) ps := fun _ h1 h2 => ⟨h1, h2⟩
  constructor
  · rintro ⟨ps, hps, rfl⟩
    obtain ⟨s, rest, rfl, y, hs, hr⟩ := partition_cons.mp hps
    rcases cappend_eq_cons.mp hs with ⟨rfl, rfl⟩ | ⟨s1, rfl, hs1⟩
    · obtain ⟨s2, rest2, rfl, y2, hs2, hr2⟩ := partition_cons.mp hr
      rcases cappend_eq_cons.mp hs2 with ⟨rfl, rfl⟩ | ⟨s3, rfl, hs3⟩
      · obtain ⟨s4, rest3, rfl, y3, hs4, hr3⟩ := partition_cons.mp hr2
        obtain ⟨rfl, rfl⟩ := cappend_eq_nil.mp hs4
        obtain rfl := partition_nil.mp hr3
        exact Or.inr (Or.inr (Or.inr rfl))
      · obtain ⟨rfl, rfl⟩ := cappend_eq_nil.mp hs3
        obtain rfl := partition_nil.mp hr2
        exact Or.inr (Or.inl rfl)
    · rcases cappend_eq_cons.mp hs1 with ⟨rfl, rfl⟩ | ⟨s2, rfl, hs2⟩
      · obtain ⟨s4, rest3, rfl, y3, hs4, hr3⟩ := partition_cons.mp hr
        obtain ⟨rfl, rfl⟩ := cappend_eq_nil.mp hs4
        obtain rfl := partition_nil.mp hr3
        exact Or.inr (Or.inr (Or.inl rfl))
      · obtain ⟨rfl, rfl⟩ := cappend_eq_nil.mp hs2
        obtain rfl := partition_nil.mp hr
        exact Or.inl (by rw [Nat.add_assoc]; rfl)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨.cons (.cons a (.cons b (.cons c (.wrap ())))) (.wrap ()),
        hp _ rfl ⟨trivial, trivial⟩, by rw [Nat.add_assoc]; rfl⟩
    · exact ⟨.cons (.cons a (.wrap ())) (.cons (.cons b (.cons c (.wrap ()))) (.wrap ())),
        hp _ rfl ⟨trivial, trivial, trivial⟩, rfl⟩
    · exact ⟨.cons (.cons a (.cons b (.wrap ()))) (.cons (.cons c (.wrap ())) (.wrap ())),
        hp _ rfl ⟨trivial, trivial, trivial⟩, rfl⟩
    · exact ⟨.cons (.cons a (.wrap ())) (.cons (.cons b (.wrap ())) (.cons (.cons c (.wrap ())) (.wrap ()))),
        hp _ rfl ⟨trivial, trivial, trivial, trivial⟩, rfl⟩

end Freyd.Alg.RelSet.Segment
