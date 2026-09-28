# ch6 group A (§6.1–6.4) handoff — checkpoint at 40 calls

Branch worktree-agent-a82a504c6f8de9538, base 372f071 + plan commit 17776d6 (the brief's branch name
worktree-agent-ac101cb3e50aa2e77 does not exist; the plan commit lives on worktree-agent-a7b7ac7503779dde6).

Done (not yet built):
- AOP/A6_2.lean: (6.4)/(6.5) split into relCata_le_comp_step1/2/3, comp_le_relCata_step2.
- AOP/A6_3.lean: Cor 6.1 split into hylo_body_coprod_step1/2; hylo_body_coprod_decompose and
  hylo_eq_mu_coprod made public (the exporter cannot see non-public decls).

Left:
- A6_1_Digits: split cata_converse_eq into public steps; make wrap/snoc/con/embed/op/val public;
  import AOP.A6_1_Digits and AOP.A6_4_FastExp in diag/StrDiagNames.lean (the exporter's env).
- exp/mod (A6_4_FastExp): book chain needs new Lean (a^b as a function, convert surjective, fusion).
- op° lemmas, digits (needs Thm 6.3) — not started.
- diag/aop/06-recursive.typ §6.1–6.4 displays. Selectors: `./scripts/diag-export --prepared --string <decl>.rhs`
  for panels, `--formula <decl>` for #leanf.
