# The prelude

The prelude: definitions every program sees, elaborated before it by the one entry point (`runText`). A program
that defines one of these names again gets "already defined … in the prelude".

    obj 1 = {∗}                                   -- the terminal object: its one value

    ∈ : α ⟶ [α] ≜ ∋°                              -- membership, the converse of ∋
    _⇒_(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ ∼R ∪ S                  -- implication
    _⊕_(R : α ⟶ β, S : γ ⟶ δ) : α+γ ⟶ β+δ ≜ [R inl, S inr]      -- the sum of relations, A+B ⟶ C+D
    _+_(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ ⟨R,S⟩plus               -- the sum of two values
    frac(R : α ⟶ γ, S : β ⟶ γ) : α ⟶ β ≜ R/S ∩ (S/R)°           -- the symmetric division
    cor(S : α ⟶ β) : α×β ⟶ α×β ≜ dom(π₁S ∩ π₂)                  -- the pairs of S, as a coreflexive

The list functions of B&dM written as their definitions (diagram order); `ran(nil)` is the fold's seed [].

    head : [α] ⟶ α ≜ cons° π₁                                     -- B&dM p.267 head = outl cons°
    tail : [α] ⟶ [α] ≜ cons° π₂                                   -- B&dM p.149 tail = outr cons°
    init : [α] ⟶ [α] ≜ snoc° π₁                                   -- B&dM p.249 init = outl snoc°
    last : [α] ⟶ α ≜ snoc° π₂                                     -- B&dM p.267 last = outr snoc°
    prefix : [α] ⟶ [α] ≜ ⦇ran(nil), nil ∪ cons⦈                -- B&dM p.126 prefix = ⦇[nil, nil ∪ cons]⦈
    suffix : [α] ⟶ [α] ≜ cat° π₂                                  -- B&dM p.127 suffix, dual to prefix: x ⧺ y ↦ y
    concat : [[α]] ⟶ [α] ≜ ⦇ran(nil), cat⦈                    -- B&dM p.129 concat = ⦇[nil, cat]⦈
    subseq : [α] ⟶ [α] ≜ ⦇ran(nil), cons ∪ π₂⦈                -- B&dM p.123 subseq = ⦇[nil, cons ∪ outr]⦈
    tails : [α] ⟶ [[α]] ≜ ⦇ran(nil τ), ⟨⟨π₁,π₂head⟩cons,π₂⟩cons⦈   -- B&dM p.127 tails = ⦇[wrap nil, extend]⦈
    filter(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇ran(nil), dom(π₁p)cons ∪ ((𝟙 − dom(π₁p))π₂)⦈      -- B&dM p.66 ⦇[nil, p outl → cons, outr]⦈
    takewhile(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇ran(nil), dom(π₁p)cons ∪ ((𝟙 − dom(π₁p))nil)⦈  -- B&dM p.174 (7.39) ⦇[nil, p outl → cons, nil]⦈

B&dM p.130 `perm ≜ ⦇[nil, add]⦈`: add puts the head anywhere in the tail. Its converse is itself, a rule the
language keeps for this one name (`Tm.own`), because `perm° = perm` cannot be derived from the fold.

    perm : [α] ⟶ [α] ≜ ⦇ran(nil), add⦈ where add ≜ (𝟙×cat°)⟨π₂π₁,⟨π₁,π₂π₂⟩cons⟩cat
    ordered(Q : α ⟶ α) : [α] ⟶ [α] ≜ 𝟙 − dom(tails ∋ cons°(π₁∼Q ∩ (π₂∋)))   -- every element is Q-related to each later one
    sort(Q : α ⟶ α) : [α] ⟶ [α] ≜ perm ordered(Q)
