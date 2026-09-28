# ch6 group A (§6.1–6.4) handoff

Branch worktree-agent-a82a504c6f8de9538, base 372f071 + plan commit 17776d6 (the brief's branch
worktree-agent-ac101cb3e50aa2e77 does not exist; the plan commit is on worktree-agent-a7b7ac7503779dde6).
Gates green: `./scripts/cap lake build AOP diag`; every panel selector draws with `diag-export --string`,
every header with `--formula`.

Done (displays in diag/aop/06-recursive.typ):
- (6.1) val°: <val-converse>, AOP/A6_1_Digits cata_converse_step1–6.
- Theorem 6.1, 6.2: one-line references to @mu-laws and §@sec-hylo.
- (6.2) <cata-prefix>, (6.3) <cata-postfix>, (6.4) <cata-fusion-le>, (6.5) <fusion-le-cata>:
  AOP/A6_2 relCata_le_comp_step1–3, comp_le_relCata_step2.
- Corollary 6.1 <hylo-coprod>: AOP/A6_3 hylo_body_coprod_step1–2.
- p.139 op°: proved (op_recip_iff, op_recip_defined, embed_recip_defined) but NOT displayed:
  `diag-export --formula` prints `op° m p` as `op°` (drops a relation's points).
- Exporter: Label.lean's μ rule also prints ν; the fold rule covers Digits/CL/SL `cataR`;
  StrDiagNames has the Digits vocabulary (α, F, wrap, snoc, val, embed, op, Digit⁺, Digit, Decimal);
  Digits.con typed at `F.obj dDec` so its cut matches `F(-)`'s.

Left:
- p.139 digits: `val°` total and the unique solution needs Theorem 6.3 (a hypothesis in Lean).
- p.145 exp, mod (§6.4 TODO lines untouched): the book chain `exp(a) ⊒ convert°convert exp(a)
  = convert°⦇[one,op(a)]⦈ = (μX : …)` needs new Lean in AOP/A6_4_FastExp: `a^b` as a graph, convert
  simple, the fusion `convAlg ≫ pow = F(pow) ≫ expAlg` (pointwise: `a^0=1`, `a^(2n+d)`), then Cor 6.1
  over `F Unit Bit = 𝟏 + (−×Bit)`.  Lean's `exp` today is DEFINED as the hylo, so exp_eq_mu is
  only Theorem 6.2.
- the formula printer's dropped points (above).
