# Corrections in paper/idla_mated_crt-corrected.tex

Surgical corrections to arXiv:2211.04891, each marked `% CORRECTION [Cn]` in the corrected draft, with the published text,
the corrected text and the reason. Evidence: the refute-first check `review-C.md` (fleet directory, 2026-11-03; operator
verdicts in the inbox entry of 13:55 UTC). Line numbers refer to the published source `paper/idla_mated_crt.tex`.

## [C1] The limit constant is c_0 = 2/m_0 (ESCALATIONS E-A3, CONFIRMED)
- Where: new definition after eq:mo (l.720); Lemma 3.3, eq:green-uniform (l.1112); Lemma 3.4 (l.1123); proof of
  Lemma 3.4, last display (l.1172); Lemma 3.5 (l.1246); Lemma 3.7 and the same PDE restated in its proof
  (lemma:convergence-of-the-normalized-exit-time); Theorem 4.1 and the remark after it (theorem:convergence-divisible);
  Lemma 4.8 items 1 and 3 (lemma:subsequential-properties).
- Published: `m_0/6`, `m_0 x`, `m_0 psi`, `-m_0/6`.  Corrected: `c_0/6`, `c_0 x`, `c_0 psi`, `-c_0/6`, with `c_0 := 2/m_0`.
- Reason: with the Green's function normalized by `Delta G = -delta` (l.1493, 1625; HB Prop 2.3), the occupation density
  of standard Brownian motion is `2G`, and the walk at step `m_eps t` approximates `X_t = LBM_{m_0 t}` (l.715). So
  `m_eps^{-1} sum_x G^eps(a_y, x) f(eta(x)) -> m_0^{-1} int 2 G f dmu_h`; the printed `m_0` holds iff `m_0^2 = 2`, false
  for `gamma^2 <= 0.8` (annealed `E[tau_LBM] = 2^{gamma^2-1}/(2-gamma^2)^2`, so `m_0 <= 1.21`). Downstream (Prop 4.2,
  Sections 5, 7, Theorems 1.4, 1.6) uses the constant only qualitatively. Lean: `MatedCRTEnv.c₀` (Defs/Setting.lean).

## [C2] Maximum principle for nonempty finite A (ESCALATIONS E-A4, CONFIRMED)
- Where: Lemma 2.13 (lemma:maximum-principle, l.825).  Published: "For every connected subset A".  Corrected: "For every nonempty finite subset A".
- Reason: for `A = V^eps` (connected, empty boundary) and `u = 1` the inequality fails. For finite nonempty `A` the boundary
  is nonempty and the printed proof works; connectedness is not needed (apply it to each component) and several uses are
  not evidently connected (l.1039-1508, 1806, 2986, 3046). All uses are finite sets.

## [C3] Two-sided bound in Lemma 3.1 (ESCALATIONS E-A7, CONFIRMED)
- Where: Lemma 3.1 (lemma:discrete-potential-tightness, second hypothesis).  Published: `u^eps <= C eps^{-1}`.  Corrected: `|u^eps| <= C eps^{-1}`.
- Reason: `u^eps = -eps^{-2}` meets the published hypotheses and `ubar^eps -> -infinity`. The proof uses the two-sided bound
  (l.1016, 1040) and all four uses provide it (l.1191, 1346, 1419, 1752).

## [C4] Distance to the boundary of the cell union in Lemmas 5.3-5.4 (ESCALATIONS E-A8, TYPO)
- Where: Lemma 5.3 (l.1999), Lemma 5.4 (l.2009), and the set `O_1` in the proof of Proposition 5.1 (l.2018).
- Published: `dist(eta(a), partial eta(Lambda^eps_t)) > delta`.  Corrected: `dist(eta(a), partial overline{Lambda^eps_t}) > delta`.
- Reason: `eta(Lambda^eps_t)` is a finite point set, so the published condition never holds (the lemmas are vacuous and
  `O_1 = emptyset` in the proof of Prop 5.1); the proof of Prop 5.1 (l.2024) uses the cell union `overline{Lambda^eps_t}`.

## [C5] Scale-invariant integrand in the good-annulus event (ESCALATIONS E-A10, PROVISIONAL)
- Where: eq:good-annulus-event (l.2314).  Published: `log(1/|u-v|) + 1`.  Corrected: `log(r/|u-v|) + 1`.
- Reason: for `u, v` in `A_{r,2r}(z)`, `|u - v| < 4r`, so the published left side is at least `(log(1/(4r)) + 1) mu_h(A)`
  while the right side is at most `C mu_h(A)`; the event is a.s. empty for `r < e^{1-C}/4`, contradicting Lemmas 6.4 and 6.5
  (faulty step l.2367: "the probability of E_r(z) does not depend on r or z"). The scale-invariant integrand makes that
  step valid. Provisional: Step 4 of Lemma 6.8 (l.2600) bounds the event through Lemma 2.18 (absolute `log(1/|z-w|)`);
  route (a) scale-invariant Lemma 2.18 vs (b) `r`-dependent `s_2` is open (E-A10). Lemmas 6.4-6.10 are not frozen.

## Not corrections of the paper (Lean statement fidelity, review-S.md, inbox 14:05 UTC)
(S1)-(S7) change the Lean statements only; each is documented in the docstring of the statement it affects:
(S1) Lemmas 2.5, 2.6: field through its circle average process; (S2) Lemmas 3.5, 3.6: `phi`, `psi` Hölder on a
neighbourhood of `cl(B_r(z))`; (S3) Lemma 4.8 item 1 off the pole; (S4) Lemma 7.4 for the stopped odometer on its own
cluster; (S5) one annealed-probability convention (outer integral / outer measure); (S6) Lemma 3.1: `u^eps` are
`sigma(h, eta)`-measurable; (S7) MatedCRT/External (SLE-model inputs, quantum cone scaling).
