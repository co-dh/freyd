# The Rel language against the Lean AOP library

How the rows were enumerated (obligations, not records):
- Table A: every constructor of `Expr`, `OExp`, `Decl`, `Body`, `ObjDef` and `Param` in
  `leetq/LeetQ/Rel/Lang/Syntax.lean`, every entry of `Op.table` (44 builtins) and `Bin.table` (6 infix), and the
  parser-only forms in `Parse.lean` (`where`, `_n_` infix definitions, literals, comments, precedence).
- Internal `Op`/`Expr` nodes with no surface spelling (`own`, `uncons`, `uncat`, `unsnoc`, `foldI`, `flat`, `share`,
  `close`) are not rows; the three named converses are one row.
- Table B: every definition in `leetq/programs/prelude.rel.md`.
- Table C: the laws cited most often, found in `.lake/build/refactor-index.db` (modules `AOP.%`, `Freyd.%`).
- Lean line numbers come from `decl_range` (sl1 + 1); `~` marks a line read off the source because the index holds
  no range for a notation or macro. Statements omit `variable`-bound hypotheses.
- Module names drop `Freyd.` (`S2_10` is `Freyd.S2_10`) and `AOP.` (`A4_5` is `AOP.A4_5`); `A5_6LC` is
  `AOP.A5_6_ListCombinators`, `A5_4P` `AOP.A5_4_PowerRel`, `A1_7` `AOP.A1_7_Pointfree`, `A7_7TW` `AOP.A7_7_TakeWhile`,
  `A7_7F` `AOP.A7_7_Filter`, `A9_3` `AOP.A9_3_Bracket`, `A6_6c` `AOP.A6_6c_ISort`, `A10_3` `AOP.A10_3_Tardy`,
  `A6_SL` `AOP.A6_SnocList`; declarations are in `Freyd.Alg` (list ones in `Freyd.Alg.RelSet.ListRel`).
- Status: `same` = a Lean declaration with the same meaning exists; `differs` = exists, meaning or typing differs
  (the bracketed number is the note below the table); `none` = no Lean declaration found in the index.

## Table A: constructs and builtins

| rel spelling               | Lean declaration (module:line name)     | Lean notation        | status |
|----------------------------|-----------------------------------------|----------------------|-----|
| R S (juxtaposition)        | S1_10:11 Cat.comp                       | ≫ S1_10:26           | same [1] |
| R°                         | S2_10:36 Allegory.recip                 | R° postfix:max       | same |
| ∼R                         | A4_5:~48 neg (R ⇨ 𝟘)                    | ∼R prefix:max        | differs [2] |
| R ∩ S                      | S2_10:36 Allegory.inter                 | ∩ infixl:70          | same |
| R ∪ S                      | S2_20:26 DistributiveAllegory.union     | ∪ infixl:65          | same |
| R − S                      | A4_5:202 sub (R ∩ ∼S)                   | − infixl:65          | differs [2] |
| R/S                        | S2_30:30 DivisionAllegory.div           | / infixl:70          | same |
| R\S                        | S2_30:~340 leftDiv                      | \ (macro S2_30:343)  | same |
| ⟨R,S⟩                      | A5_2:154 RelProd.pair                   | print-only           | differs [3] |
| R×S (relations)            | A5_2:160 prodMap                        | print-only           | differs [3] |
| [R,S]                      | A5_3:48 junc                            | print-only           | differs [4] |
| ⦇e,S⦈ (fold)               | A5_5:52 relCata                         | ⦇R⦈ notation:max     | differs [5] |
| {(a,b),…} literal          | none                                    | none                 | none |
| R ⊑ S                      | S2_10:76 le                             | ⊑ infix:50           | same |
| check X ⊑ Y / X = Y        | none (a Prop)                           | ⊑ , =                | differs [6] |
| print X                    | none                                    | none                 | none |
| where x ≜ …                | none                                    | none                 | none |
| user infix _n_             | none (infixl command)                   | none                 | none |
| precedence levels          | none (Lean has levels)                  | none                 | differs [11] |
| obj B = {a,b,…}            | A6_1_RelSet:34 RelSet                   | ⟨B⟩                  | differs [8] |
| obj N = lo…hi              | A6_1_RelSet:34 RelSet                   | ⟨Int⟩                | differs [8] |
| obj A = B×C alias          | A5_2:54 RelProd.p ; S2_20:184 Coproduct | none                 | differs [3] |
| obj 1 = {∗}                | S2_10:562 UnitaryAllegory.unit_obj      | 1 (print-only)       | same |
| type A×B                   | A5_2:54 RelProd.p                       | none                 | differs [3] |
| type A+B                   | S2_20:184 Coproduct                     | none                 | differs [4] |
| type 𝒫A                    | S2_40:39 PowerAllegory.P                | P A                  | differs [7] |
| type [A]                   | A5_6LC:31 dList                         | dList A              | differs [7] |
| type variable α … ω        | implicit {A : 𝒜}                        | none                 | same |
| R : A ⟶ B ≜ body           | S1_10:25 ⟶                              | ⟶                    | same |
| parameter S : A ⟶ B        | explicit argument                       | ⟶                    | same |
| test body h(S) ≜ E ⊑ F     | none (def into Prop)                    | ⊑                    | differs [6] |
| lifting to families        | none                                    | none                 | none |
| 𝟙                          | S1_10:11 Cat.id                         | 𝟙 A (S1_10:27)       | same |
| 𝟘                          | S2_20:26 DistributiveAllegory.zero      | 𝟘                    | same |
| ⊤                          | A4_4:92 topHom ; S2_30 topMor           | ⊤ print-only         | same |
| ∋                          | S2_40:39 PowerAllegory.eps              | ∋ A                  | differs [9] |
| π₁ , π₂                    | A5_2:54 RelProd.π₁ π₂                   | none                 | differs [3] |
| inl , inr                  | S2_20:184 Coproduct.u₁ u₂               | none                 | differs [4] |
| ≤                          | A5_6LC:373 leq                          | none                 | differs [8] |
| <                          | none                                    | none                 | none |
| succ                       | A5_6LC:343 succ                         | none                 | differs [8] |
| plus                       | A5_6LC:339 plus                         | none                 | differs [8] |
| times                      | none                                    | none                 | none |
| minus                      | none                                    | none                 | none |
| div                        | A5_6LC:346 div                          | none                 | differs [8] |
| mod                        | none                                    | none                 | none |
| max                        | none                                    | none                 | none |
| min                        | none                                    | none                 | none |
| union                      | S2_40:986 union                         | none                 | differs [9] |
| τ                          | S2_40:170 singletonMap                  | none                 | differs [9] |
| nil                        | A1_7:36 nil                             | nil (delab)          | same |
| α (list algebra)           | A5_5:37 InitialAlgebra.α                | I.α                  | differs [12] |
| cons                       | A5_6LC:750 cons                         | none                 | same |
| length                     | A5_6LC:328 length                       | none                 | same |
| sum                        | A5_6LC:323 sum                          | none                 | same |
| dom(R)                     | S2_10:327 dom                           | dom R                | same |
| ran(R)                     | S2_10:330 ran                           | ran R                | same |
| Λ(R)                       | S2_40:74 Λ                              | Λ R ; R%∋            | differs [9] |
| E(R)                       | A4_6:95 existsImage                     | none                 | differs [9] |
| P(R)                       | A5_4P:34 powerRel                       | P(R) notation:max    | differs [10] |
| est(Q)                     | A7_1:39 est                             | est(R) notation:max  | differs [9] |
| thin(Q)                    | A8_1:71 thinRel                         | thin(Q) notation:max | differs [9] |
| F(R) (list map)            | A5_6LC:527 list ; A5_1:48 Relator.map   | none                 | differs [13] |
| inits                      | A5_6LC:852 initsR                       | none                 | same |
| cat                        | A5_6LC:224 cat                          | none                 | same |
| zip                        | A1_7:32 zip                             | none                 | same |
| snoc                       | none (SnocList datatype, A6_SL)         | none                 | none |
| setify                     | A5_6LC:49 setify                        | none                 | differs [9] |
| bagify                     | none (only job-specific A10_3:232)      | none                 | none |
| tic                        | none                                    | none                 | none |
| thinL(Q)                   | A8_3:567 thinL                          | none                 | same |
| merge(Q)                   | A8_3:1147 merge                         | none                 | same |
| loop(F)                    | A9_3:1686 Bracket.loop                  | none                 | same |
| at(i)                      | none                                    | none                 | none |
| named converses cons° cat° | Lean spells the converse: cons° , cat°  | ° postfix            | same |

Notes to Table A:
- [1] Same composition order (diagram order); only the spelling differs, Lean writes `≫`.
- [2] Lean `∼R` is `R ⇨ 𝟘` (Heyting); it is the complement only under `BooleanAllegory`; no instance for `RelSet` is
  indexed.
- [3] Lean takes an explicit `RelProd a b` witness; `⟨R,S⟩` and `R×S` are print-only unexpanders.
- [4] Lean takes an explicit `Coproduct s a₁ a₂` witness; `[R,S]` is a print-only unexpander.
- [5] Lean `⦇R⦈ : I.t ⟶ A` is over an `InitialAlgebra F`; Rel `⦇e,S⦈` is a list fold, seed `e`, step `S : E×V ⟶ V`.
- [6] Rel `check` is evaluated on data; Lean states a `Prop` that a proof must discharge.
- [7] Rel elaborates both `𝒫A` and `[A]` to one array type; Lean `P A` (power object) and `dList A` are different
  objects.
- [8] Rel objects are finite declared universes and arithmetic is partial in range; Lean carriers are total `Int`/`Nat`.
- [9] Rel reads these on arrays `[α]`; Lean reads them on the power object `P A`.
- [10] Rel refuses a closed `P(R)` (its `𝒫` target has no universe, `Elab.applied`); Lean `powerRel` always exists.
- [11] Rel parses juxtaposition and `∩ ∪ − / \ ×` and declared infix at one level, left to right; Lean has levels.
- [12] Rel `α : 1+A×[A] ⟶ [A]` is the list algebra only; Lean `I.α` is the initial algebra of any `F`.
- [13] Rel `F` is the list functor only; Lean `Relator.map` is any relator, `ListRel.list` the list one.

## Table B: the prelude

| name         | rel definition (prelude.rel.md)        | Lean declaration with the same meaning | status |
|--------------|----------------------------------------|----------------------------------------|-----|
| obj 1        | {∗}                                    | S2_10:562 UnitaryAllegory.unit_obj     | same |
| ∈            | α ⟶ [α] ≜ ∋°                           | none (Lean: (∋ A)°)                    | none |
| _⇒_          | ∼R ∪ S                                 | A4_4:102 impl (⇨)                      | differs [2] |
| _⊕_          | [R inl, S inr]                         | A5_3:210 sumMap                        | differs [4] |
| _+_          | ⟨R,S⟩plus                              | none (plus is the value verb only)     | none |
| frac(R,S)    | R/S ∩ (S/R)°                           | S2_30:205 symmDiv                      | same |
| cor(S)       | dom(π₁S ∩ π₂)                          | none                                   | none |
| head         | cons° π₁                               | none                                   | none |
| tail         | cons° π₂                               | none                                   | none |
| init         | snoc° π₁                               | none                                   | none |
| last         | snoc° π₂                               | none                                   | none |
| prefix       | ⦇ran(nil), nil ∪ cons⦈                 | A5_6LC:97 prefix                       | same |
| suffix       | cat° π₂                                | A5_6LC:221 suffix                      | same |
| concat       | ⦇ran(nil), cat⦈                        | A5_6LC:234 concat                      | same |
| subseq       | ⦇ran(nil), cons ∪ π₂⦈                  | A5_6LC:127 subseq                      | same |
| tails        | ⦇ran(nil τ), ⟨⟨π₁,π₂head⟩cons,π₂⟩cons⦈ | A5_6LC:862 tailsR                      | same |
| filter(p)    | fold with dom(π₁p)cons ∪ …             | A7_7F:58 filter                        | same |
| takewhile(p) | fold with dom(π₁p)cons ∪ …             | A7_7TW:283 takewhile                   | same |
| perm         | ⦇ran(nil), add⦈ where add ≜ …          | A5_6LC:81 perm                         | same |
| perm° = perm | built-in rule, not derivable           | none                                   | none |
| ordered(Q)   | 𝟙 − dom(tails ∋ cons°(π₁∼Q ∩ (π₂∋)))   | A5_6LC:171 ordered                     | differs [14] |
| sort(Q)      | perm ordered(Q)                        | A6_6c:180 ISort.sortSpec               | differs [14] |

Notes to Table B: [2], [4] as above.
- [14] Lean `ordered` and `sortSpec` take the order as a `variable` predicate `A → A → Prop` and define sortedness by
  a recursive `orderedP` (`corefl`); Rel `ordered(Q)` is the formula shown. Equality of the two is not stated.

## Table C: laws a calc step would cite

Law, theorem, location; statements follow as indexed (class fields: the text of the class in the source).

| law a calc step cites                 | Lean theorem                                     | module:line |
|---------------------------------------|--------------------------------------------------|-----|
| associativity of composition          | Cat.assoc (class field)                          | S1_10 Cat |
| converse involution                   | Allegory.recip_recip (field)                     | S2_10:36 |
| converse contravariant                | Allegory.recip_comp (field)                      | S2_10:36 |
| converse of ∩                         | Allegory.recip_inter (field)                     | S2_10:36 |
| modular law                           | Allegory.modular (field) ; modular_le_right      | S2_10:36 ; A4_1:47 |
| composition monotone                  | comp_mono_left , comp_mono_right                 | S2_10:146 , :161 |
| converse monotone                     | recip_mono                                       | S2_10:134 |
| ∩ monotone                            | inter_mono                                       | A4_4:41 |
| ∪ monotone                            | union_mono                                       | S2_20:116 |
| thin monotone                         | thinRel_mono                                     | A8_1:209 |
| fold monotone                         | relCata_mono                                     | A6_2:259 |
| division universal property           | le_div_iff                                       | S2_30:54 |
| left division universal property      | le_leftDiv_iff                                   | S2_30:348 |
| symmetric division universal property | le_symmDiv_iff                                   | S2_30:212 |
| Λ universal property                  | Λ_eps_eq' ; Λ_is_map' ; Λ_fusion                 | S2_40 ; S2_40 ; A4_6:74 |
| fold uniqueness                       | eq_relCata_iff_fixed                             | A6_2:161 |
| fold universal property (≤ , ≥)       | relCata_le_of_prefixed , le_relCata_of_postfixed | A6_2:184 , :189 |
| fold fusion                           | relCata_le_comp , comp_le_relCata                | A6_2:218 , :240 |
| est universal property                | le_est_iff                                       | A7_1:47 |
| thin universal property               | le_Λ_comp_thinRel_iff                            | A8_1:136 |
| thin then est                         | thinRel_comp_est                                 | A8_1:318 |
| greedy theorem                        | greedy                                           | A7_2:227 |
| thinning theorem                      | thinning_est                                     | A8_1:523 |
| domain universal property             | dom_UP                                           | A4_2:150 |

Statements (`Freyd.Alg.` prefix dropped; `F.map` is `F(·)`):

```
recip_recip     (R : a ⟶ b) : R°° = R
recip_comp      (R : a ⟶ b) (S : b ⟶ c) : (R ≫ S)° = S° ≫ R°
recip_inter     (R S : a ⟶ b) : (R ∩ S)° = R° ∩ S°
modular         (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) : (R ≫ S) ∩ T = ((R ≫ S) ∩ T) ∩ ((R ∩ (T ≫ S°)) ≫ S)
modular_le_right (R : A ⟶ B) (S : B ⟶ C) (T : A ⟶ C) : (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T)
comp_mono_left  (R : a ⟶ b) (hST : S ⊑ T) : R ≫ S ⊑ R ≫ T
comp_mono_right (h : R₁ ⊑ R₂) (S : b ⟶ c) : R₁ ≫ S ⊑ R₂ ≫ S
recip_mono      (h : R ⊑ S) : R° ⊑ S°
inter_mono      (hR : R ⊑ R') (hS : S ⊑ S') : R ∩ S ⊑ R' ∩ S'
union_mono      (hA : A ⊑ A') (hB : B ⊑ B') : A ∪ B ⊑ A' ∪ B'
thinRel_mono    (h : Q ⊑ R) : thinRel Q ⊑ thinRel R
relCata_mono    (I : InitialAlgebra F) (h : R ⊑ S) : relCata R ⊑ relCata S
le_div_iff      (X : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) : X ⊑ R / S ↔ X ≫ S ⊑ R
le_leftDiv_iff  (X : b ⟶ c) (S : a ⟶ b) (R : a ⟶ c) : X ⊑ (S \ R) ↔ S ≫ X ⊑ R
le_symmDiv_iff  (X : a ⟶ b) (R : a ⟶ c) (S : b ⟶ c) : X ⊑ R /ₛ S ↔ X ≫ S ⊑ R ∧ X° ≫ R ⊑ S
Λ_eps_eq'       (R : a ⟶ b) : Λ R ≫ ∋ b = R                       (statement from source; not in the stmt column)
Λ_fusion        (hf : Map f) (R : A ⟶ B) : Λ (f ≫ R) = f ≫ Λ R
eq_relCata_iff_fixed (I) (R : Alg F C) (X : I.t ⟶ C) : X = I.α° ≫ F.map X ≫ R ↔ X = relCata R
relCata_le_of_prefixed (I) (h : I.α° ≫ F.map X ≫ R ⊑ X) : relCata R ⊑ X
le_relCata_of_postfixed (I) (h : X ⊑ I.α° ≫ F.map X ≫ R) : X ⊑ relCata R
relCata_le_comp (I) : F.map S ≫ T ⊑ R ≫ S → relCata T ⊑ relCata R ≫ S
comp_le_relCata (I) : R ≫ S ⊑ F.map S ≫ T → relCata R ≫ S ⊑ relCata T
le_est_iff      {R : A ⟶ A} {X : P A ⟶ A} : X ⊑ est R ↔ X ⊑ ∋ A ∧ (∋ A)° ≫ X ⊑ R°
le_Λ_comp_thinRel_iff {S : B ⟶ A} {Q : A ⟶ A} {X : B ⟶ P A} :
                X ⊑ Λ S ≫ thinRel Q ↔ X ≫ ∋ A ⊑ S ∧ S° ≫ X ⊑ Q° ≫ (∋ A)°
thinRel_comp_est (hQR : Q ⊑ R) (hQ : 𝟙 A ⊑ Q) (hR : R ≫ R ⊑ R) : est R = thinRel Q ≫ est R
greedy          (I) (htrans : R ≫ R ⊑ R) (hmono : Pres S R) : ⦇S%∋ ≫ est(R)⦈ ⊑ ⦇S⦈%∋ ≫ est(R)
thinning_est    (I) (hQR : Q ⊑ R) (hQ : preorder Q) (hR : preorder R) (hmono : Pres S Q) :
                relCata (Λ (F.map (∋ A) ≫ S) ≫ thinRel Q) ≫ est R ⊑ Λ (relCata … (statement cut by the index column)
dom_UP          {X : A ⟶ A} (hX : Coreflexive X) : dom R ⊑ X ↔ R ⊑ X ≫ R
```

## Gaps

Constructs with status `none` (no Lean declaration): literals `{(a,b),…}`; `print`; `where`; user infix `_n_`;
lifting to a family; `<`; `times`, `minus`, `mod`, `max`, `min`; `snoc`; `bagify`; `tic`; `at(i)`; prelude `∈`, `_+_`,
`cor`, `head`, `tail`, `init`, `last`, and the rule `perm° = perm`.

Constructs with status `differs`: `∼`, `−`, `⇒` (Heyting vs complement); `⟨R,S⟩`, `R×S`, `[R,S]`, `π₁`, `π₂`, `inl`,
`inr`, `⊕`, object `A×B`/`A+B` (explicit witness argument); `⦇e,S⦈` (list fold vs `InitialAlgebra` fold); `check` and
test bodies (evaluate vs prove); `𝒫A`/`[A]` and every power-object operator `∋ Λ E P est thin τ union setify`; numeric
objects and verbs (`≤ succ plus div`, `obj N = lo…hi`); `α`, `F(R)` (fixed to lists); `ordered`, `sort`; precedence.

Instance linking the executable side to the AOP allegory class:
- No. `LeetQ.*` is indexed (27 modules, 155 theorems); no declaration there has `Allegory` in its name or statement,
  `LeetQ.Rel.Algebra` has no indexed declaration, and `module_need` has no edge from any `LeetQ.*` module to an
  `AOP.*` or `Freyd.*` module, although the `leetq` package `require`s `freyd`.
- The AOP side has its own executable representation, `RelRep`/`RelTest` (`AOP.A6_FinRel`), bridged to `RelSet` by
  `RelRep.rel_comp`, `RelTest.rel_conv`, `RelTest.rel_inter`, `RelRep.rel_compT`; it is not leetq's `Rel k v`.
- `RelSet` carries the instances `Allegory` (`AOP.A6_1_RelSet:59`), `DivisionAllegory` (:189),
  `LocallyCompleteDistributiveAllegory` (:198), `UnguardedPowerLCDA` (:260), `TabularUnitaryUnguardedPowerLCDA` (:631),
  `PositiveTabularUnitaryUnguardedDivisionPowerAllegory` (:637); no `BooleanAllegory RelSet` instance is indexed.

Juxtaposition as composition in Lean:
- Lean parses `R S` as function application; composition of `Cat` morphisms is `≫` (`Freyd.S1_10:26`), and in
  `RelSet` a hom is itself a function `A.carrier → B.carrier → Prop`, so `R S` could elaborate as an application
  instead of failing. A translator must insert `≫`.
- `⟨R,S⟩`, `[R,S]`, `R×S` do not parse in Lean as the relational operators (anonymous constructor, list literal,
  product type), and `⊤`, `E(·)` are print-only; the translator must emit `RelProd.pair`, `junc`, `prodMap`, `topHom`,
  `existsImage` with their witness arguments.
