#import "../note-prelude.typ": *
#show: note-chapter.with(4)
// note-split: chapter 4 — this header is written by scripts/note-split and stripped by scripts/note-join
= Relations and Allegories <sec-relations>

== Allegories

== Special properties of arrows

// B&dM Proposition 4.1, p. 90: a function characterised without its converse.
#disp(num: "Proposition 4.1")[
`R:A⟶B, S:B⟶A, 𝟙 A⊑RS, SR⊑𝟙 B ⟹ S=R° and R is a map`
#src[A relation with a two-sided partial inverse under composition — identity below one order,
identity above the other — is that inverse's converse, and R is itself a map.]
]<prop-4-1>
// lean:AOP.A4_2.recip_of_comp_id@460e327c

== Tabular allegories

// B&dM Proposition 4.2, p. 92: inclusion in `R` restated as a factorisation through R's tabulation.
#disp(num: "Proposition 4.2")[
`(f,g) a tabulation of R ⟹ k°h⊑R ⟺ ∃! map m with h=mf, k=mg`
#src[Every pair below `R`'s tabulating pair factors, uniquely, through a single map into the
tabulation's apex.]
  // lean:AOP.A4_3.tabulation_incl_iff@6e0229df
]<prop-4-2>

== Locally complete allegories

== Boolean allegories

== Power allegories
