/-
  `thinLOn` read back: `foldBy` at a `demandStep` whose body bumps each element `a` into the thinned rest `y` —
  `[a]` when `y` is empty, else with `b` its head `a` replaces `b` when `(a, b)` passes the test, `y` stays when
  `(b, a)` passes, and `a :: y` when neither does. The test is `q` at the pairs the round meets, read as `le`.
-/
import LeetQ.Rel.RepMerge

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN OpsN Prim

-- the state of `thinLOn`'s step: an element and the thinned rest
set_option hygiene false in
local notation "SP" => Obj.prod B (.arr B)

section Body

open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **`thinLOn`'s body on a coreflexive `D`, read back from its primitives' read-backs**: `(a, y)` in `D` goes to
    `[a]` when `y` is empty; with `y = b :: bs`, to `a :: bs` when `le a b`, to `y` when `le b a`, and to `a :: y`
    when neither. Each hypothesis is one primitive's read-back at the body's values (`rep_uncons`, `rep_comp`,
    `rep_pair`, `rep_ran`, `rep_dom`, `rep_diff`, `rep_union_full`, `rep_cons`); `ht1`, `ht2` read the test on the
    pairs of heads `rab` the body meets, and on their swaps `rs`. -/
theorem thin_body_set {B : Obj} (le : B.El → B.El → Bool) (D : Rel SP SP) (Dm : (SP).El → Prop)
    (hD : rep D = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) Dm)
    (ta : Rel SP B) (hta : ta = outl D) (ty : Rel SP (.arr B)) (hty : ty = outr D)
    (tu : Rel SP (.prod B (.arr B)))
    (hUn : ∀ (xs : List B.El) b bs, rep (uncons (Rel.val ty)) xs (b, bs) ↔
      (∃ j, (Rel.val ty).row j = xs) ∧ xs = b :: bs)
    (htu : rep tu = rep ty ≫ rep (uncons (Rel.val ty)))
    (tab : Rel SP (.prod B B)) (htab : rep tab = rpair (rep ta) (rep (outl tu)))
    (rab : Rel (.prod B B) (.prod B B))
    (hrab : rep rab = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun c => ∃ s, rep tab s c)
    (G1 : Rel (.prod B B) (.prod B B)) (ht1 : ∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true))
    (tq1 : Rel SP (.prod B B)) (htq1 : rep tq1 = rep tab ≫ rep G1)
    (tup : Rel SP SP) (htup : rep tup = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) fun s => ∃ c, rep tq1 s c)
    (ss : Rel (.prod B B) (.prod B B)) (hss : rep ss = rpair (rep (outr rab)) (rep (outl rab)))
    (rs : Rel (.prod B B) (.prod B B))
    (hrs : rep rs = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun c => ∃ x, rep ss x c)
    (G2 : Rel (.prod B B) (.prod B B)) (ht2 : ∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true))
    (tq2 : Rel (.prod B B) (.prod B B)) (htq2 : rep tq2 = rep ss ≫ rep G2)
    (sw : Rel (.prod B B) (.prod B B))
    (hsw : rep sw = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun x => ∃ c, rep tq2 x c)
    (tq3 : Rel SP (.prod B B)) (htq3 : rep tq3 = rep tab ≫ rep sw)
    (tdn : Rel SP SP) (htdn : rep tdn = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) fun s => ∃ c, rep tq3 s c)
    (du : Rel SP SP) (hdu : rep du = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) fun s => ∃ c, rep tu s c)
    (l1 : Rel SP SP) (hl1 : ∀ s s', rep l1 s s' ↔ rep D s s' ∧ ¬ rep du s s')
    (l2 : Rel SP SP) (hl2 : ∀ s s', rep l2 s s' ↔ rep du s s' ∧ ¬ rep tup s s')
    (l3 : Rel SP SP) (hl3 : ∀ s s', rep l3 s s' ↔ rep l2 s s' ∧ ¬ rep tdn s s')
    (lone : Rel SP SP) (hlone : rep lone = rep l1 ∪ rep l3)
    (c1 : Rel SP (.arr B)) (hc1 : ∀ s z, rep c1 s z ↔ ∃ b bs, rep lone s (b, bs) ∧ z = b :: bs)
    (ua : Rel SP B) (hua : rep ua = rep tup ≫ rep ta)
    (uu : Rel SP (.prod B (.arr B))) (huu : rep uu = rep tup ≫ rep tu)
    (ru : Rel (.prod B (.arr B)) (.prod B (.arr B)))
    (hru : rep ru = corefl (A := (⟨(Obj.prod B (.arr B)).El⟩ : RelSet.{0})) fun c => ∃ s, rep tu s c)
    (ut : Rel SP (.arr B)) (hut : rep ut = rep uu ≫ rep (outr ru))
    (pu : Rel SP (.prod B (.arr B))) (hpu : rep pu = rpair (rep ua) (rep ut))
    (c2 : Rel SP (.arr B)) (hc2 : ∀ s z, rep c2 s z ↔ ∃ b bs, rep pu s (b, bs) ∧ z = b :: bs)
    (dy : Rel SP (.arr B)) (hdy : rep dy = rep tdn ≫ rep ty)
    (b1 : Rel SP (.arr B)) (hb1 : rep b1 = rep c1 ∪ rep c2)
    (body : Rel SP (.arr B)) (hbody : rep body = rep b1 ∪ rep dy) :
    ∀ a (y v : List B.El), rep body (a, y) v ↔ Dm (a, y) ∧ ((y = [] ∧ v = [a]) ∨ ∃ b bs, y = b :: bs ∧
      ((le a b = true ∧ v = a :: bs) ∨ (le b a = true ∧ v = y) ∨ (le a b = false ∧ le b a = false ∧ v = a :: y))) := by
  have eD : ∀ s s', rep D s s' ↔ s = s' ∧ Dm s := fun s s' => by rw [hD]; exact Iff.rfl
  -- the element and the rest of a state, read off `D`
  have eA : ∀ a y x, rep ta (a, y) x ↔ Dm (a, y) ∧ x = a := by
    intro a y x; rw [hta]
    refine (outl_holds D (a, y) x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eD _ _).1 h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨y, (eD _ _).2 ⟨rfl, hm⟩⟩
  have eY : ∀ a y x, rep ty (a, y) x ↔ Dm (a, y) ∧ x = y := by
    intro a y x; rw [hty]
    refine (outr_holds D (a, y) x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eD _ _).1 h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨a, (eD _ _).2 ⟨rfl, hm⟩⟩
  -- `uncons` of the rest
  have eU : ∀ a y b bs, rep tu (a, y) (b, bs) ↔ Dm (a, y) ∧ y = b :: bs := by
    intro a y b bs; rw [htu, comp_apply]
    constructor
    · rintro ⟨v, h1, h2⟩; obtain ⟨hm, rfl⟩ := (eY _ _ _).1 h1; exact ⟨hm, ((hUn _ b bs).1 h2).2⟩
    · rintro ⟨hm, e⟩
      have h1 : rep ty (a, y) y := (eY _ _ _).2 ⟨hm, rfl⟩
      obtain ⟨i, -, hi⟩ := id h1
      exact ⟨y, h1, (hUn _ b bs).2 ⟨⟨i, hi⟩, e⟩⟩
  -- the pair of heads `(a, b)`
  have eAB : ∀ a y a' b, rep tab (a, y) (a', b) ↔ Dm (a, y) ∧ a' = a ∧ ∃ bs, y = b :: bs := by
    intro a y a' b; rw [htab]
    show rep ta (a, y) a' ∧ rep (outl tu) (a, y) b ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hm, rfl⟩ := (eA _ _ _).1 h1
      obtain ⟨bs, h3⟩ := (outl_holds tu _ b).1 h2
      exact ⟨hm, rfl, bs, ((eU _ _ _ _).1 h3).2⟩
    · rintro ⟨hm, rfl, bs, e⟩
      exact ⟨(eA _ _ _).2 ⟨hm, rfl⟩, (outl_holds tu _ b).2 ⟨bs, (eU _ _ _ _).2 ⟨hm, e⟩⟩⟩
  have eRab : ∀ c c', rep rab c c' ↔ c = c' ∧ ∃ s, rep tab s c := fun c c' => by rw [hrab]; exact Iff.rfl
  -- `up`: the rest is `b :: bs` and `le a b`
  have eUp : ∀ a y s', rep tup (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true := by
    intro a y s'; rw [htup]
    show (a, y) = s' ∧ (∃ c, rep tq1 (a, y) c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [htq1, comp_apply] at hc
      obtain ⟨⟨a', b⟩, h1, h2⟩ := hc
      obtain ⟨hm, rfl, bs, e⟩ := (eAB _ _ _ _).1 h1
      exact ⟨hm, b, bs, e, (ht1 _ _ ((eRab _ _).2 ⟨rfl, _, h1⟩)).1 ⟨c, h2⟩⟩
    · rintro ⟨hm, b, bs, e, hl⟩
      have h1 : rep tab (a, y) (a, b) := (eAB _ _ _ _).2 ⟨hm, rfl, bs, e⟩
      obtain ⟨c, h2⟩ := (ht1 _ _ ((eRab _ _).2 ⟨rfl, _, h1⟩)).2 hl
      exact ⟨c, by rw [htq1, comp_apply]; exact ⟨_, h1, h2⟩⟩
  -- the swap `(b, a)` of a pair of heads, and `down`: the swap passes
  have eOR : ∀ c x, rep (outr rab) c x ↔ (∃ s, rep tab s c) ∧ x = c.2 := by
    intro c x
    refine (outr_holds rab c x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eRab _ _).1 h; subst e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨c.1, (eRab _ _).2 ⟨rfl, hm⟩⟩
  have eOL : ∀ c x, rep (outl rab) c x ↔ (∃ s, rep tab s c) ∧ x = c.1 := by
    intro c x
    refine (outl_holds rab c x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eRab _ _).1 h; subst e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨c.2, (eRab _ _).2 ⟨rfl, hm⟩⟩
  have eSS : ∀ a' b d, rep ss (a', b) d ↔ (∃ s, rep tab s (a', b)) ∧ d = (b, a') := by
    intro a' b d; rw [hss]
    show rep (outr rab) (a', b) d.1 ∧ rep (outl rab) (a', b) d.2 ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hm, e1⟩ := (eOR _ _).1 h1
      obtain ⟨-, e2⟩ := (eOL _ _).1 h2
      exact ⟨hm, Prod.ext e1 e2⟩
    · rintro ⟨hm, rfl⟩; exact ⟨(eOR _ _).2 ⟨hm, rfl⟩, (eOL _ _).2 ⟨hm, rfl⟩⟩
  have eRs : ∀ c c', rep rs c c' ↔ c = c' ∧ ∃ x, rep ss x c := fun c c' => by rw [hrs]; exact Iff.rfl
  have eSw : ∀ a' b c', rep sw (a', b) c' ↔ (a', b) = c' ∧ (∃ s, rep tab s (a', b)) ∧ le b a' = true := by
    intro a' b c'; rw [hsw]
    show (a', b) = c' ∧ (∃ d, rep tq2 (a', b) d) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨d, hd⟩
      rw [htq2, comp_apply] at hd
      obtain ⟨x, h1, h2⟩ := hd
      obtain ⟨hm, rfl⟩ := (eSS _ _ _).1 h1
      exact ⟨hm, (ht2 _ _ ((eRs _ _).2 ⟨rfl, _, h1⟩)).1 ⟨d, h2⟩⟩
    · rintro ⟨hm, hl⟩
      have h1 : rep ss (a', b) (b, a') := (eSS _ _ _).2 ⟨hm, rfl⟩
      obtain ⟨d, h2⟩ := (ht2 _ _ ((eRs _ _).2 ⟨rfl, _, h1⟩)).2 hl
      exact ⟨d, by rw [htq2, comp_apply]; exact ⟨_, h1, h2⟩⟩
  have eDn : ∀ a y s', rep tdn (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le b a = true := by
    intro a y s'; rw [htdn]
    show (a, y) = s' ∧ (∃ c, rep tq3 (a, y) c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [htq3, comp_apply] at hc
      obtain ⟨⟨a', b⟩, h1, h2⟩ := hc
      obtain ⟨hm, rfl, bs, e⟩ := (eAB _ _ _ _).1 h1
      obtain ⟨-, -, hl⟩ := (eSw _ _ _).1 h2
      exact ⟨hm, b, bs, e, hl⟩
    · rintro ⟨hm, b, bs, e, hl⟩
      have h1 : rep tab (a, y) (a, b) := (eAB _ _ _ _).2 ⟨hm, rfl, bs, e⟩
      exact ⟨(a, b), by rw [htq3, comp_apply]; exact ⟨_, h1, (eSw _ _ _).2 ⟨rfl, ⟨_, h1⟩, hl⟩⟩⟩
  have eDu : ∀ a y s', rep du (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧ ∃ b bs, y = b :: bs := by
    intro a y s'; rw [hdu]
    show (a, y) = s' ∧ (∃ c, rep tu (a, y) c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨⟨b, bs⟩, h⟩; obtain ⟨hm, e⟩ := (eU _ _ _ _).1 h; exact ⟨hm, b, bs, e⟩
    · rintro ⟨hm, b, bs, e⟩; exact ⟨(b, bs), (eU _ _ _ _).2 ⟨hm, e⟩⟩
  -- `lone`: the rest is empty, or neither pair of heads passes
  have eLone : ∀ a y s', rep lone (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧
      (y = [] ∨ ∃ b bs, y = b :: bs ∧ le a b = false ∧ le b a = false) := by
    intro a y s'; rw [hlone]
    show rep l1 (a, y) s' ∨ rep l3 (a, y) s' ↔ _
    rw [hl1, hl3, hl2, eD, eDu, eUp, eDn]
    constructor
    · rintro (⟨⟨e, hm⟩, hn⟩ | ⟨⟨⟨e, hm, b, bs, hy⟩, hn1⟩, hn2⟩)
      · refine ⟨e, hm, Or.inl ?_⟩
        cases y with
        | nil => rfl
        | cons b bs => exact absurd ⟨e, hm, b, bs, rfl⟩ hn
      · refine ⟨e, hm, Or.inr ⟨b, bs, hy, ?_, ?_⟩⟩
        · cases h : le a b
          · rfl
          · exact absurd ⟨e, hm, b, bs, hy, h⟩ hn1
        · cases h : le b a
          · rfl
          · exact absurd ⟨e, hm, b, bs, hy, h⟩ hn2
    · rintro ⟨e, hm, hy | ⟨b, bs, hy, h1, h2⟩⟩
      · refine Or.inl ⟨⟨e, hm⟩, ?_⟩
        rintro ⟨-, -, b, bs, hb⟩
        rw [hy] at hb
        exact List.cons_ne_nil _ _ hb.symm
      · refine Or.inr ⟨⟨⟨e, hm, b, bs, hy⟩, ?_⟩, ?_⟩
        · rintro ⟨-, -, b', bs', hb, h⟩
          rw [hy] at hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj hb
          exact Bool.false_ne_true (h1.symm.trans h)
        · rintro ⟨-, -, b', bs', hb, h⟩
          rw [hy] at hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj hb
          exact Bool.false_ne_true (h2.symm.trans h)
  -- each branch of the body
  have eC1 : ∀ a y v, rep c1 (a, y) v ↔ Dm (a, y) ∧
      (y = [] ∨ ∃ b bs, y = b :: bs ∧ le a b = false ∧ le b a = false) ∧ v = a :: y := by
    intro a y v; rw [hc1]
    constructor
    · rintro ⟨b, bs, h, rfl⟩
      obtain ⟨e, hm, hc⟩ := (eLone _ _ _).1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨hm, hc, rfl⟩
    · rintro ⟨hm, hc, rfl⟩; exact ⟨a, y, (eLone _ _ _).2 ⟨rfl, hm, hc⟩, rfl⟩
  have eUA : ∀ a y x, rep ua (a, y) x ↔ (Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true) ∧ x = a := by
    intro a y x; rw [hua, comp_apply]
    constructor
    · rintro ⟨s, h1, h2⟩; obtain ⟨rfl, hu⟩ := (eUp _ _ _).1 h1; exact ⟨hu, ((eA _ _ _).1 h2).2⟩
    · rintro ⟨hu, hx⟩; subst x; exact ⟨(a, y), (eUp _ _ _).2 ⟨rfl, hu⟩, (eA _ _ _).2 ⟨hu.1, rfl⟩⟩
  have eRu : ∀ c c', rep ru c c' ↔ c = c' ∧ ∃ s, rep tu s c := fun c c' => by rw [hru]; exact Iff.rfl
  have eUT : ∀ a y x, rep ut (a, y) x ↔ (Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true) ∧ ∃ b, y = b :: x := by
    intro a y x; rw [hut, comp_apply]
    constructor
    · rintro ⟨⟨b, bs⟩, h1, h2⟩
      rw [huu, comp_apply] at h1
      obtain ⟨s, h3, h4⟩ := h1
      obtain ⟨rfl, hu⟩ := (eUp _ _ _).1 h3
      obtain ⟨w, h5⟩ := (outr_holds ru (b, bs) x).1 h2
      obtain ⟨e, -⟩ := (eRu _ _).1 h5
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨hu, b, ((eU _ _ _ _).1 h4).2⟩
    · rintro ⟨hu, b, e⟩
      have h4 : rep tu (a, y) (b, x) := (eU _ _ _ _).2 ⟨hu.1, e⟩
      refine ⟨(b, x), ?_, (outr_holds ru (b, x) x).2 ⟨b, ?_⟩⟩
      · rw [huu, comp_apply]; exact ⟨(a, y), (eUp _ _ _).2 ⟨rfl, hu⟩, h4⟩
      · exact (eRu _ _).2 ⟨rfl, _, h4⟩
  have eC2 : ∀ a y v, rep c2 (a, y) v ↔ Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true ∧ v = a :: bs := by
    intro a y v; rw [hc2]
    constructor
    · rintro ⟨a', bs, h, rfl⟩
      rw [hpu] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨⟨hm, b, bs', e, hl⟩, ea⟩ := (eUA _ _ _).1 h1
      obtain ⟨-, b', e'⟩ := (eUT _ _ _).1 h2
      subst ea
      rw [e] at e'
      obtain ⟨rfl, rfl⟩ := List.cons.inj e'
      exact ⟨hm, _, _, e, hl, rfl⟩
    · rintro ⟨hm, b, bs, e, hl, rfl⟩
      refine ⟨a, bs, ?_, rfl⟩
      rw [hpu]
      show rep ua (a, y) a ∧ rep ut (a, y) bs
      exact ⟨(eUA _ _ _).2 ⟨⟨hm, b, bs, e, hl⟩, rfl⟩, (eUT _ _ _).2 ⟨⟨hm, b, bs, e, hl⟩, b, e⟩⟩
  have eDY : ∀ a y v, rep dy (a, y) v ↔ Dm (a, y) ∧ (∃ b bs, y = b :: bs ∧ le b a = true) ∧ v = y := by
    intro a y v; rw [hdy, comp_apply]
    constructor
    · rintro ⟨s, h1, h2⟩; obtain ⟨rfl, hm, hd⟩ := (eDn _ _ _).1 h1; exact ⟨hm, hd, ((eY _ _ _).1 h2).2⟩
    · rintro ⟨hm, hd, hv⟩; subst v; exact ⟨(a, y), (eDn _ _ _).2 ⟨rfl, hm, hd⟩, (eY _ _ _).2 ⟨hm, rfl⟩⟩
  intro a y v
  rw [show rep body (a, y) v ↔ (rep c1 (a, y) v ∨ rep c2 (a, y) v) ∨ rep dy (a, y) v by
    rw [hbody, hb1]; exact Iff.rfl, eC1, eC2, eDY]
  constructor
  · rintro ((⟨hm, hc, rfl⟩ | ⟨hm, b, bs, e, h1, rfl⟩) | ⟨hm, ⟨b, bs, e, h1⟩, rfl⟩)
    · rcases hc with hc | ⟨b, bs, e, h1, h2⟩
      · exact ⟨hm, Or.inl ⟨hc, by rw [hc]⟩⟩
      · exact ⟨hm, Or.inr ⟨b, bs, e, Or.inr (Or.inr ⟨h1, h2, rfl⟩)⟩⟩
    · exact ⟨hm, Or.inr ⟨b, bs, e, Or.inl ⟨h1, rfl⟩⟩⟩
    · exact ⟨hm, Or.inr ⟨b, bs, e, Or.inr (Or.inl ⟨h1, rfl⟩)⟩⟩
  · rintro ⟨hm, ⟨hn, rfl⟩ | ⟨b, bs, e, ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩⟩⟩
    · exact Or.inl (Or.inl ⟨hm, Or.inl hn, by rw [hn]⟩)
    · exact Or.inl (Or.inr ⟨hm, b, bs, e, h1, rfl⟩)
    · exact Or.inr ⟨hm, ⟨b, bs, e, h1⟩, rfl⟩
    · exact Or.inl (Or.inl ⟨hm, Or.inr ⟨b, bs, e, h1, h2⟩, rfl⟩)

end Body

open ListN

-- every primitive's hypotheses at the body's values, named as `thin_body_set` names them
set_option hygiene false in
local notation "thinOK" =>
  (uncOK(B, ty) ∧ cmpOK(.arr B, ty, uncons (Rel.val ty)) ∧ pairOK(SP, ta, outl tu) ∧
    oneFit(.prod B B, Rel.n tab, Rel.val tab) ∧ cmpOK(.prod B B, tab, G1) ∧ oneFit(SP, Rel.n tq1, Rel.key tq1) ∧
    pairOK(.prod B B, outr rab, outl rab) ∧ oneFit(.prod B B, Rel.n ss, Rel.val ss) ∧ cmpOK(.prod B B, ss, G2) ∧
    oneFit(.prod B B, Rel.n tq2, Rel.key tq2) ∧ cmpOK(.prod B B, tab, sw) ∧ oneFit(SP, Rel.n tq3, Rel.key tq3) ∧
    oneFit(SP, Rel.n tu, Rel.key tu) ∧ diffOK(SP, SP, D, du) ∧ diffOK(SP, SP, du, tup) ∧ diffOK(SP, SP, l2, tdn) ∧
    uniOK(SP, SP, l1, l3) ∧ consOK(SP, B, lone) ∧ cmpOK(SP, tup, ta) ∧ cmpOK(SP, tup, tu) ∧
    oneFit(.prod B (.arr B), Rel.n tu, Rel.val tu) ∧ cmpOK(.prod B (.arr B), uu, outr ru) ∧ pairOK(SP, ua, ut) ∧
    consOK(SP, B, pu) ∧ cmpOK(SP, tdn, ty) ∧ uniOK(SP, .arr B, c1, c2) ∧ uniOK(SP, .arr B, b1, dy))

section Discharge

open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **`thinLOn`'s body on a coreflexive `D`, read back**: `thin_body_set` with each primitive's read-back
    discharged by its lemma. The body's values are bound by their equations as `thinLOn` binds them (`sw` is
    `swapIn`'s body at `rab`); `h` is every primitive's hypotheses at them (`thinOK`). -/
theorem thin_body_rep {B : Obj} (le : B.El → B.El → Bool) (D : Rel SP SP) (Dm : (SP).El → Prop)
    (hD : rep D = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) Dm)
    (ta : Rel SP B) (hta : ta = outl D) (ty : Rel SP (.arr B)) (hty : ty = outr D)
    (tu : Rel SP (.prod B (.arr B))) (htu : tu = ty ≫ uncons (Rel.val ty))
    (tab : Rel SP (.prod B B)) (htab : tab = pair ta (outl tu))
    (rab : Rel (.prod B B) (.prod B B)) (hrab : rab = ran tab)
    (G1 : Rel (.prod B B) (.prod B B)) (ht1 : ∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true))
    (tq1 : Rel SP (.prod B B)) (htq1 : tq1 = tab ≫ G1) (tup : Rel SP SP) (htup : tup = dom tq1)
    (ss : Rel (.prod B B) (.prod B B)) (hss : ss = pair (outr rab) (outl rab))
    (rs : Rel (.prod B B) (.prod B B)) (hrs : rs = ran ss)
    (G2 : Rel (.prod B B) (.prod B B)) (ht2 : ∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true))
    (tq2 : Rel (.prod B B) (.prod B B)) (htq2 : tq2 = ss ≫ G2) (sw : Rel (.prod B B) (.prod B B)) (hsw : sw = dom tq2)
    (tq3 : Rel SP (.prod B B)) (htq3 : tq3 = tab ≫ sw) (tdn : Rel SP SP) (htdn : tdn = dom tq3)
    (du : Rel SP SP) (hdu : du = dom tu) (l1 : Rel SP SP) (hl1 : l1 = D \ du)
    (l2 : Rel SP SP) (hl2 : l2 = du \ tup) (l3 : Rel SP SP) (hl3 : l3 = l2 \ tdn)
    (lone : Rel SP SP) (hlone : lone = l1 ∪ l3) (c1 : Rel SP (.arr B)) (hc1 : c1 = cons lone)
    (ua : Rel SP B) (hua : ua = tup ≫ ta) (uu : Rel SP (.prod B (.arr B))) (huu : uu = tup ≫ tu)
    (ru : Rel (.prod B (.arr B)) (.prod B (.arr B))) (hru : ru = ran tu)
    (ut : Rel SP (.arr B)) (hut : ut = uu ≫ outr ru) (pu : Rel SP (.prod B (.arr B))) (hpu : pu = pair ua ut)
    (c2 : Rel SP (.arr B)) (hc2 : c2 = cons pu) (dy : Rel SP (.arr B)) (hdy : dy = tdn ≫ ty)
    (b1 : Rel SP (.arr B)) (hb1 : b1 = c1 ∪ c2) (body : Rel SP (.arr B)) (hbody : body = b1 ∪ dy) (h : thinOK) :
    ∀ a (y v : List B.El), rep body (a, y) v ↔ Dm (a, y) ∧ ((y = [] ∧ v = [a]) ∨ ∃ b bs, y = b :: bs ∧
      ((le a b = true ∧ v = a :: bs) ∨ (le b a = true ∧ v = y) ∨ (le a b = false ∧ le b a = false ∧ v = a :: y))) := by
  obtain ⟨⟨u63, uU⟩, ⟨uf, uc⟩, ⟨abf, abp⟩, ⟨rabf, rabp⟩, ⟨q1f, q1c⟩, ⟨upf, upp⟩, ⟨ssf, ssp⟩, ⟨rsf, rsp⟩,
    ⟨q2f, q2c⟩, ⟨swf, swp⟩, ⟨q3f, q3c⟩, ⟨dnf, dnp⟩, ⟨duf, dup⟩, d1, d2, d3, ⟨oN, oNk, oNv, oFk, oFv, oK, oV, ok, ov⟩,
    cs1, ⟨uaf, uac⟩, ⟨uuf, uuc⟩, ⟨ruf, rup⟩, ⟨utf, utc⟩, ⟨puf, pup⟩, cs2, ⟨dyf, dyc⟩,
    ⟨bN, bNk, bNv, bFk, bFv, bK, bV, bk, bv⟩, ⟨yN, yNk, yNv, yFk, yFv, yK, yV, yk, yv⟩⟩ := h
  obtain ⟨uk, uh, ut'⟩ := uU _ rfl _ rfl _ rfl
  obtain ⟨u1, u2, u3, u4⟩ := uc _ rfl
  obtain ⟨ab1, ab2, ab3, ab4, ab5⟩ := abp _ rfl
  obtain ⟨g1, g2, g3, g4⟩ := q1c _ rfl
  obtain ⟨s1, s2, s3, s4, s5⟩ := ssp _ rfl
  obtain ⟨h1, h2, h3, h4⟩ := q2c _ rfl
  obtain ⟨k1, k2, k3, k4⟩ := q3c _ rfl
  obtain ⟨d11, d12⟩ := d1 _ rfl
  obtain ⟨d13, d14⟩ := d12
  obtain ⟨d21, d22⟩ := d2 _ rfl
  obtain ⟨d23, d24⟩ := d22
  obtain ⟨d31, d32⟩ := d3 _ rfl
  obtain ⟨d33, d34⟩ := d32
  obtain ⟨a1, a2, a3, a4⟩ := uac _ rfl
  obtain ⟨w1, w2, w3, w4⟩ := uuc _ rfl
  obtain ⟨t1, t2, t3, t4⟩ := utc _ rfl
  obtain ⟨p1, p2, p3, p4, p5⟩ := pup _ rfl
  obtain ⟨y1, y2, y3, y4⟩ := dyc _ rfl
  refine thin_body_set le D Dm hD ta hta ty hty tu
    (rep_uncons (Rel.val ty) u63 _ rfl _ rfl _ rfl uk uh ut')
    (by rw [htu]; exact rep_comp _ _ (codes_faithful_wf _ _ uf).1 u1 u2 u3 u4)
    tab (by rw [htab]; exact rep_pair _ _ (codes_faithful_wf _ _ abf).1 ab1 ab2 ab3 ab4 ab5)
    rab (by rw [hrab]; exact rep_ran_corefl tab (one_ok _ rabf) (rabp)) G1 ht1
    tq1 (by rw [htq1]; exact rep_comp _ _ (codes_faithful_wf _ _ q1f).1 g1 g2 g3 g4)
    tup (by rw [htup]; exact rep_dom_corefl tq1 (one_ok _ upf) (upp))
    ss (by rw [hss]; exact rep_pair _ _ (codes_faithful_wf _ _ ssf).1 s1 s2 s3 s4 s5)
    rs (by rw [hrs]; exact rep_ran_corefl ss (one_ok _ rsf) (rsp)) G2 ht2
    tq2 (by rw [htq2]; exact rep_comp _ _ (codes_faithful_wf _ _ q2f).1 h1 h2 h3 h4)
    sw (by rw [hsw]; exact rep_dom_corefl tq2 (one_ok _ swf) (swp))
    tq3 (by rw [htq3]; exact rep_comp _ _ (codes_faithful_wf _ _ q3f).1 k1 k2 k3 k4)
    tdn (by rw [htdn]; exact rep_dom_corefl tq3 (one_ok _ dnf) (dnp))
    du (by rw [hdu]; exact rep_dom_corefl tu (one_ok _ duf) (dup))
    l1 (fun s s' => by rw [hl1]; exact rep_diff D du d11 d13 d14 s s')
    l2 (fun s s' => by rw [hl2]; exact rep_diff du tup d21 d23 d24 s s')
    l3 (fun s s' => by rw [hl3]; exact rep_diff l2 tdn d31 d33 d34 s s')
    lone (by rw [hlone]; exact rep_union_full l1 l3 oN oNk oNv oFk oFv (one_ok _ oK) (one_ok _ oV) ok ov)
    c1 (by rw [hc1]; exact rep_cons_ok lone cs1)
    ua (by rw [hua]; exact rep_comp _ _ (codes_faithful_wf _ _ uaf).1 a1 a2 a3 a4)
    uu (by rw [huu]; exact rep_comp _ _ (codes_faithful_wf _ _ uuf).1 w1 w2 w3 w4)
    ru (by rw [hru]; exact rep_ran_corefl tu (one_ok _ ruf) (rup))
    ut (by rw [hut]; exact rep_comp _ _ (codes_faithful_wf _ _ utf).1 t1 t2 t3 t4)
    pu (by rw [hpu]; exact rep_pair _ _ (codes_faithful_wf _ _ puf).1 p1 p2 p3 p4 p5)
    c2 (by rw [hc2]; exact rep_cons_ok pu cs2)
    dy (by rw [hdy]; exact rep_comp _ _ (codes_faithful_wf _ _ dyf).1 y1 y2 y3 y4)
    b1 (by rw [hb1]; exact rep_union_full c1 c2 bN bNk bNv bFk bFv (one_ok _ bK) (one_ok _ bV) bk bv)
    body (by rw [hbody]; exact rep_union_full b1 dy yN yNk yNv yFk yFv (one_ok _ yK) (one_ok _ yV) yk yv)

end Discharge

-- the body's values at the round's coreflexive `D`, each bound by its equation as `thinLOn` binds them, then `J`
set_option hygiene false in
local notation "thinVals(" J ")" =>
  ∀ ta, ta = outl D → ∀ ty, ty = outr D → ∀ tu, tu = ty ≫ uncons (Rel.val ty) → ∀ tab, tab = pair ta (outl tu) →
  ∀ rab, rab = ran tab → ∀ G1, G1 = q rab → ∀ tq1, tq1 = tab ≫ G1 → ∀ tup, tup = dom tq1 →
  ∀ ss, ss = pair (outr rab) (outl rab) → ∀ rs, rs = ran ss → ∀ G2, G2 = q rs → ∀ tq2, tq2 = ss ≫ G2 →
  ∀ sw, sw = dom tq2 → ∀ tq3, tq3 = tab ≫ sw → ∀ tdn, tdn = dom tq3 → ∀ du, du = dom tu → ∀ l1, l1 = D \ du →
  ∀ l2, l2 = du \ tup → ∀ l3, l3 = l2 \ tdn → ∀ lone, lone = l1 ∪ l3 → ∀ c1, c1 = cons lone →
  ∀ ua, ua = tup ≫ ta → ∀ uu, uu = tup ≫ tu → ∀ ru, ru = ran tu → ∀ ut, ut = uu ≫ outr ru →
  ∀ pu, pu = pair ua ut → ∀ c2, c2 = cons pu → ∀ dy, dy = tdn ≫ ty → ∀ b1, b1 = c1 ∪ c2 →
  ∀ body, body = b1 ∪ dy → J

section Headline

/-- **`thinLOn` is `foldOn` at its body**: the step's body `Sf` bound by its defining equation (`hSf`). -/
theorem thinLOn_foldOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) (Sf : Rel SP SP → Rel SP (.arr B))
    (hSf : ∀ D : Rel SP SP, Sf D =
      let a := outl D
      let ys := outr D
      let u := ys ≫ uncons ys.val
      let ab := pair a (outl u)
      let up := dom (ab ≫ q (ran ab))
      let down := dom (ab ≫ swapIn q (ran ab))
      let lone := D \ dom u ∪ ((dom u \ up) \ down)
      cons lone ∪ cons (pair (up ≫ a) (up ≫ u ≫ outr (ran u))) ∪ down ≫ ys) :
    thinLOn q X = foldOn (nilVal B) Sf X := by
  -- `congrArg`, not `congr`: `congr` first tries the two steps up to `rfl`, unfolding the kernels until `whnf` times out
  unfold thinLOn foldOn
  refine congrArg (foldBy X (nilVal B)) (funext fun el => funext fun pend => ?_)
  simp only [demandStep, hSf]

/-- **One round of `thinLOn`, read back**: at the round's pairs `P`, its coreflexive `D = ran P` holds exactly the
    pairs of `P`, and the body `Sf D` takes `(a, y)` of `D` to one bump of `a` into `y` at `le`. `h` is `rep_ran`'s
    hypotheses at `P`, the test read back on the pairs of heads `rab` and on their swaps `rs`, and every
    primitive's hypotheses (`thinOK`), the body's values bound by their equations (`thinVals`). -/
theorem thin_round_rep {B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (le : B.El → B.El → Bool) (Sf : Rel SP SP → Rel SP (.arr B))
    (hSf : ∀ D : Rel SP SP, Sf D =
      let a := outl D
      let ys := outr D
      let u := ys ≫ uncons ys.val
      let ab := pair a (outl u)
      let up := dom (ab ≫ q (ran ab))
      let down := dom (ab ≫ swapIn q (ran ab))
      let lone := D \ dom u ∪ ((dom u \ up) \ down)
      cons lone ∪ cons (pair (up ≫ a) (up ≫ u ≫ outr (ran u))) ∪ down ≫ ys)
    (P : Rel .long SP) (D : Rel SP SP) (hD : D = ran P)
    (h : oneFit(SP, Rel.n P, Rel.val P) ∧ thinVals(
      (∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true)) ∧
      (∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true)) ∧ thinOK)) :
    (∀ s, rep D s s ↔ ∃ r, rep P r s) ∧
    ∀ a (y v : List B.El), rep (Sf D) (a, y) v ↔ rep D (a, y) (a, y) ∧ ((y = [] ∧ v = [a]) ∨
      ∃ b bs, y = b :: bs ∧ ((le a b = true ∧ v = a :: bs) ∨ (le b a = true ∧ v = b :: bs) ∨
        (le a b = false ∧ le b a = false ∧ v = a :: b :: bs))) := by
  obtain ⟨⟨Pf, Pp⟩, hk⟩ := h
  have eD := rep_ran_corefl _ (one_ok _ Pf) (Pp)
  rw [← hD] at eD
  obtain ⟨t1, t2, J⟩ := hk _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  refine ⟨fun s => by rw [eD]; exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩, fun a y v => ?_⟩
  simp only [hSf, swapIn]
  rw [thin_body_rep le D _ eD _ rfl _ rfl _ rfl _ rfl _ rfl _ t1 _ rfl _ rfl _ rfl _ rfl _ t2 _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl J, eD]
  constructor
  · rintro ⟨hm, h | ⟨b, bs, e, h⟩⟩
    · exact ⟨⟨rfl, hm⟩, Or.inl h⟩
    · subst e; exact ⟨⟨rfl, hm⟩, Or.inr ⟨b, bs, rfl, h⟩⟩
  · rintro ⟨⟨-, hm⟩, h | ⟨b, bs, e, h⟩⟩
    · exact ⟨hm, Or.inl h⟩
    · subst e; exact ⟨hm, Or.inr ⟨b, bs, rfl, h⟩⟩

/-- **`thinLOn`, read back**: `xs` goes to `w` exactly when `xs` is a row of `X` and a chain `ys` runs from the
    empty list `ys[xs.length]` to `w = ys[0]`, each link `(xs[t], ys[t+1]) ↦ ys[t]` a pair of round `k`'s `Dr k`
    and one bump of `xs[t]` into `ys[t+1]` at `le` (`[a]` on `[]`; on `b :: bs`, `a :: bs` when `le a b`, `b :: bs`
    when `le b a`, `a :: b :: bs` when neither). The step's body `Sf` is bound by its defining equation (`hSf`);
    the fold's hypotheses are `rep_foldOn`'s (`hS` at `E = B`, `V = .arr B`); `hR'` is, at every round's
    coreflexive `D = Dr k`, `rep_ran`'s at it, the test read back on the pairs of heads `rab` and on their swaps
    `rs`, and every primitive's hypotheses (`thinOK`). -/
theorem rep_thinLOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (le : B.El → B.El → Bool) (X : Vals (.arr B) n)
    (Sf : Rel SP SP → Rel SP (.arr B))
    (hSf : ∀ D : Rel SP SP, Sf D =
      let a := outl D
      let ys := outr D
      let u := ys ≫ uncons ys.val
      let ab := pair a (outl u)
      let up := dom (ab ≫ q (ran ab))
      let down := dom (ab ≫ swapIn q (ran ab))
      let lone := D \ dom u ∪ ((dom u \ up) \ down)
      cons lone ∪ cons (pair (up ≫ a) (up ≫ u ≫ outr (ran u))) ∪ down ≫ ys)
    (T : Rel .long (.arr B)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr B) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits B (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long (.arr B)) (hpend : pend₀ = top (A := .long) (Rel.key T) (nilVal B))
    (hN : (Rel.n T).toNat * (1 : USize).toNat < USize.size) (h63 : (Rel.n T).toNat * (1 : USize).toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· / (1 : USize).toNat)))
    (hB : Vals.PickFits (.arr B) (nilVal B)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· % (1 : USize).toNat)))
    (step : Rel .long B → Rel .long (.arr B) → Rel .long (.arr B)) (hstep : step = demandStep Sf)
    (elK : Nat → Rel .long B) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (hf : ∀ st, f st = rnd(st))
    (Dr : Nat → Rel SP SP) (hD : ∀ k, Dr k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (hR : ∀ i (el : Rel .long B) (pend P S : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend →
      roundAt((.arr B)))
    (hS : let E := B; let V : Obj := .arr B; ∀ i (el : Rel .long E) (pend : Rel .long V), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → stepOn)
    (F : Rel .long (.arr B)) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr B) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits (.arr B) (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd))
    (hR' : ∀ k (D : Rel SP SP), D = Dr k →
      oneFit(SP, Rel.n (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1),
        Rel.val (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1)) ∧ thinVals(
      (∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true)) ∧
      (∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true)) ∧ thinOK)) :
    ∀ (xs : List B.El) w, rep (thinLOn q X) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List (Obj.arr B).El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, (nilVal B).row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length),
          rep (Dr (xs.length - 1 - t)) (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
            (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm)) ∧
          ((ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = [] ∧
              ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = [xs[t]'ht]) ∨
            ∃ b bs, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = b :: bs ∧
              ((le (xs[t]'ht) b = true ∧ ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = xs[t]'ht :: bs) ∨
               (le b (xs[t]'ht) = true ∧ ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = b :: bs) ∨
               (le (xs[t]'ht) b = false ∧ le b (xs[t]'ht) = false ∧
                ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = xs[t]'ht :: b :: bs)))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) := by
  intro xs w
  rw [thinLOn_foldOn q X Sf hSf, rep_foldOn (nilVal B) Sf X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep
    elK hE f hf Dr hD hR hS F hF jc hjc hjO hjn hjM hjA hjC]
  simp only [fun k => (thin_round_rep q le Sf hSf _ (Dr k) (hD k) (hR' k _ rfl)).2]

/-- **`thinLOn`, read back as bumps**: `rep_thinLOn` with each link's pair of `Dr k` discharged — it is a pair of
    the round, the row's element and value, so `xs` goes to `w` exactly when `xs` is a row of `X` and `w` is the
    end of a chain of bumps of the elements of `xs`, from the right, starting from `[]`. `rep_foldBy` at the bump
    itself, each round's step read back by `step_rep` and `thin_round_rep`. Hypotheses as `rep_thinLOn`'s. -/
theorem rep_thinLOn_bump {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (le : B.El → B.El → Bool) (X : Vals (.arr B) n)
    (Sf : Rel SP SP → Rel SP (.arr B))
    (hSf : ∀ D : Rel SP SP, Sf D =
      let a := outl D
      let ys := outr D
      let u := ys ≫ uncons ys.val
      let ab := pair a (outl u)
      let up := dom (ab ≫ q (ran ab))
      let down := dom (ab ≫ swapIn q (ran ab))
      let lone := D \ dom u ∪ ((dom u \ up) \ down)
      cons lone ∪ cons (pair (up ≫ a) (up ≫ u ≫ outr (ran u))) ∪ down ≫ ys)
    (T : Rel .long (.arr B)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr B) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits B (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long (.arr B)) (hpend : pend₀ = top (A := .long) (Rel.key T) (nilVal B))
    (hN : (Rel.n T).toNat * (1 : USize).toNat < USize.size) (h63 : (Rel.n T).toNat * (1 : USize).toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· / (1 : USize).toNat)))
    (hB : Vals.PickFits (.arr B) (nilVal B)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· % (1 : USize).toNat)))
    (step : Rel .long B → Rel .long (.arr B) → Rel .long (.arr B)) (hstep : step = demandStep Sf)
    (elK : Nat → Rel .long B) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (hf : ∀ st, f st = rnd(st))
    (Dr : Nat → Rel SP SP) (hD : ∀ k, Dr k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (hR : ∀ i (el : Rel .long B) (pend P S : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend →
      roundAt((.arr B)))
    (hS : let E := B; let V : Obj := .arr B; ∀ i (el : Rel .long E) (pend : Rel .long V), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → stepOn)
    (F : Rel .long (.arr B)) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr B) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits (.arr B) (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd))
    (hR' : ∀ k (D : Rel SP SP), D = Dr k →
      oneFit(SP, Rel.n (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1),
        Rel.val (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1)) ∧ thinVals(
      (∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true)) ∧
      (∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true)) ∧ thinOK)) :
    ∀ (xs : List B.El) w, rep (thinLOn q X) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List (Obj.arr B).El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, (nilVal B).row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length),
          (ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = [] ∧
              ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = [xs[t]'ht]) ∨
            ∃ b bs, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = b :: bs ∧
              ((le (xs[t]'ht) b = true ∧ ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = xs[t]'ht :: bs) ∨
               (le b (xs[t]'ht) = true ∧ ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = b :: bs) ∨
               (le (xs[t]'ht) b = false ∧ le b (xs[t]'ht) = false ∧
                ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = xs[t]'ht :: b :: bs))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) := by
  intro xs w
  rw [thinLOn_foldOn q X Sf hSf]
  subst hstep
  exact rep_foldBy (nilVal B) X T hT hn hv hp hel pend₀ hpend hN h63 hA hB (demandStep Sf)
    (fun _ (p : B.El × List B.El) v => (p.2 = [] ∧ v = [p.1]) ∨ ∃ b bs, p.2 = b :: bs ∧
      ((le p.1 b = true ∧ v = p.1 :: bs) ∨ (le b p.1 = true ∧ v = b :: bs) ∨
        (le p.1 b = false ∧ le b p.1 = false ∧ v = p.1 :: b :: bs)))
    elK hE f hf hR (fun i _ r v => by
      obtain ⟨hkO, hkn, hkM, hkA, hkB, hkC, hJ⟩ := hS i _ _ rfl rfl _ rfl
      obtain ⟨hjO', hjn', hjM', hjA', hjC'⟩ := hJ _ rfl _ (congrArg Sf (hD i)) _ rfl
      obtain ⟨eD, eB⟩ := thin_round_rep q le Sf hSf _ (Dr i) (hD i) (hR' i _ rfl)
      have h1 := rep_pair (elK i) _ hkO hkn hkM hkA hkB hkC
      rw [step_rep (elK i) _ Sf _ rfl hkO hkn hkM hkA hkB hkC _ rfl _ (congrArg Sf (hD i)) _ rfl
        hjO' hjn' hjM' hjA' hjC' r v]
      refine exists_congr fun e => exists_congr fun u => ?_
      rw [eB, eD]
      have hP : rep (elK i) r e → rep (f^[i] (pend₀, Alg.zero, 0)).1 r u →
          rep (pair (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r (e, u) := fun he hu => by rw [h1]; exact ⟨he, hu⟩
      exact ⟨fun ⟨he, hu, _, hb⟩ => ⟨he, hu, hb⟩, fun ⟨he, hu, hb⟩ => ⟨he, hu, ⟨r, hP he hu⟩, hb⟩⟩)
    F hF jc hjc hjO hjn hjM hjA hjC xs w

end Headline

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.thin_body_set
#print axioms LeetQ.Rel.Rep.thin_body_rep
#print axioms LeetQ.Rel.Rep.thin_round_rep
#print axioms LeetQ.Rel.Rep.rep_thinLOn
#print axioms LeetQ.Rel.Rep.rep_thinLOn_bump
