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
- Remaining proof-level uses are corrected in [C17].

## [C15] Median start in eq:mo (proof-consistent typo repair)
- The single deterministic `m_0` is the annealed median of the unscaled LBM exit time from `B_{1/2}` started at `0`, not at a free `z`. This agrees with the discrete median in eq:meps.

## [C16] Killed occupation proof in Lemma 3.4 (proof repair)
- Replace the unstopped functional and unjustified interchange by a buffered killed-path argument, convergence of exit times, a second-moment tail estimate, and the audited clock occupation identity. The identity has coefficient `2` for the unscaled clock and `c_0 = 2/m_0` for the paper's process, consistently with [C1]. The complete audited proof and exact citations are in `docs/campaign/OCCUPATION-PROOF.md`; deterministic thinning follows [C11].

## [C17] Remaining proof coefficients (proof repair consistent with [C1])
- Propagate `c_0` for `m_0` and `6/c_0` for `6/m_0` in the proofs of Lemmas 3.3, 3.5, 3.7 and the Section 4 consequences, without changing the time-rescaling definition or the median.

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

## [C7] Source in the killed domain (E-c1-1)
The origin clause of Lemma 4.4 and the mass identity of Lemma 4.5 require `0 ∈ V^ε(Bρ) \ V^ε(∂Bρ)`. Continuity of η at 0 gives this for all sufficiently small ε. The old all-ε clauses fail when the source cell meets ∂Bρ. See AUDIT-C7-C10-USES.md.

## [C8] Lemma 7.2 above cell scale (E-c3-2)
Replace all `s > 0` by `s ≥ ε^β` for a deterministic β > 0, and restrict its application in Proposition 7.1 accordingly. Below cell scale the printed statement is false. See AUDIT-C7-C10-USES.md.

## [C9] Cluster identity (E-x2-2)
The identity with the closure of the positive odometer needs ε < t: for ε ≥ t there is no toppling and the cluster is `{0}`. The two stopped-cluster displays also require the separate consistency of stopped and unstopped odometers. Its earlier application in Proposition 5.1 is not established by ε < t; see AUDIT-C7-C10-USES.md.

## [C10] Scaled boundary data (N1)
In (3.1) replace `C'` by `C' ε⁻¹`; εu satisfies the hypothesis of Lemma 3.2. This addresses the data used in Lemma 3.5. The separate N3 random-subsequence issue is untouched. See AUDIT-C7-C10-USES.md.

## [C11] Deterministic preparation for Lemma 3.1 (N3)
The printed random input sequence precedes a high-probability extraction. First thin each deterministic sequence deterministically, then allow measurable random subsubsequences and countable families on the inherited event. The proof and affected subsequence arguments are updated; C10's ε⁻¹ boundary factor is retained. See AUDIT-C11-C12-USES.md for every use and independent G1–G4 gaps.

## [C12] Fixed-sequence quantifiers in Lemmas 4.6–4.7 (E-x3-2)
Put the deterministic sequence, and in Lemma 4.6 fixed t, before a deterministic thinning and the almost-sure conclusion. Lemma 4.6 states relative compactness on the closed ball, Hölder limits and measurable selection. See AUDIT-C11-C12-USES.md; downstream identification is conditional on independent repairs.

## [C13] Harmonic convergence and boundary representatives (author-approved 2026-11-06)
Lemma 3.6: replace the printed Hölder datum evaluated at the exit-cell representative by continuous datum on the closed disk, evaluated after nearest-point projection. Add uniform convergence and the polynomial same-walk comparison, with the corrected unrestricted-walk proof. Apply the projection convention to Lemma 3.5 boundary data as well. Boundary-cell representatives can lie outside the disk and the exit functional is not everywhere continuous. See `LEMMA36-REPLACEMENT.md` and `AUDIT-L36-USES.md`.

## [C14] Normalized comparison boundary offset (author-approved 2026-11-06)
In the proof of Lemma 4.8, replace `m_eps phi^delta(eta(b)) + delta` by `m_eps (phi^delta(eta(b)) + delta)`. Only the latter gives the stated limiting boundary value and the intended domination. This implements G3 of `PROOF-REPAIRS-G.md` in the paper.

## [C18] Lemma 6.4 constant dependency (author-approved 2026-11-09)
Replace "a constant C depending only on gamma" by "depending only on gamma and c_0". The proof gives C(gamma, c_0); a good annulus forces C >= (1 - log 2)/(16 c_0^2) (packing), and c_0 = c_0(rho, gamma) is the standing choice, so C(gamma) is unjustified (false if inf_rho c_0 = 0). All later uses fix rho. See fleet notes fp-gaps/CHATGPT-s6-constants.md and CHATGPT-6-4-referee.md.

## [C19] Lemma 6.8/6.9 negative-binomial tail events (author-approved 2026-11-10)
In the proof of lemma:chance-of-being-absorbed, eq:number-of-walkers-nb-bound and the display after it bound P[N(.) <= ...]; both events are reversed and now read P[N(k_1) > (s_2^{-1}+C) k_1 | h, eta] <= exp(-c k_1) and P[N((s_2^{-1}+C)^{-1} k) > k | h, eta] <= exp(-c k). The stochastic domination by NegBinom(k_1, s_2) bounds the probability of needing too many walkers; with certain absorption N(m) = m and the printed left side equals 1. Typo-level; the inclusive threshold of the conclusion is routine rounding (the direct proof in notes/fp-gaps/CHATGPT-6-9-claims-referee.md gives s_3 = log(27/16)/4, s_4 = 1/4, s_5 = 1/8 from the uniform constants of LEMMA68). Source: notes/fp-gaps/CHATGPT-6-9-claims-referee.md (G2).

## Readings (not corrections of the paper; line numbers of the corrected draft)

### (R1) The origin vertex `0` and `a^eps_0` (ESCALATIONS E-x3-3, worker A, 2026-11-04)
- Where: the paper writes `0` for the point `eta(0) = 0` of `C` and for the vertex `0` of `eps Z`, whose cell
  `H^eps_0 = eta([-eps, 0])` contains it. The vertex `0` is the source of IDLA and of the divisible sandpile (l.246,
  l.1537-1557), of the obstacle `-(t eps^{-1}) g^eps_{B_rho}(0, .)` (eq:discrete-least-supersolution, l.1570-1571) and
  of `G^eps(0, .)` in Lemmas 5.2-5.3. The vertex `a^eps_y` (smallest vertex whose cell contains `y`,
  eq:plane-to-embedding, l.637) is the source in Theorem 2.11 and Lemmas 3.3, 3.4, 3.6; `X^{0,eps}` in eq:meps (l.729)
  is the walk from `a^eps_0` (`X^{z,eps}` starts at `a^eps_z`, l.723) or from the vertex `0` (l.724). The paper passes
  between the two silently (Lemma 3.3 at `y = 0` gives the convergence of the Section 4 obstacle; same in Section 5).
- Reading: literal at each place, no Lean edit. Vertex `(0 : ℤ)`: `sandpileNormOdometer`, `matedObstacle`
  (Defs/Sandpile.lean:43, 75), `idlaProb` (Defs/Setting.lean), Drafts 4.4, 5.2, 5.3, 7.2-7.4. `vertexOf ε η 0`:
  `MatedCRTEnv.mε` (Defs/Setting.lean:205, the reading `z = 0`); `vertexOf ε η y`: Drafts 2.11, 3.3, 3.4, 3.6.
- Why this is consistent: `a^eps_0 = 0` iff `eta` does not visit `0` before time `-eps`, and almost surely `eta` has no
  negative-time visit to `0`, simultaneously for all `eps > 0`: `MatedCRTEnv.IsValid.ae_vertexOf_zero_eq_zero`
  (MatedCRT/Proofs/Sec4/DivSandpileLowerBound/SourceVertex.lean:125, worker x3, commit 1326986), from the identity case
  of the coordinate-change rule of the mating-of-trees coupling (`igMap`: the curve is rooted at its first visit to `0`)
  and transience. All statements concerned conclude almost surely or in probability, so the two sources are
  interchangeable there. Caveat: the proof rests on the `igMap` field of the bundle (stated in whole-plane form for a
  fixed witness, a documented weak spot, Defs/Setting.lean module docstring); for SLE itself the fact holds because the
  point `eta(0)` of the fixed time `0` is a.s. not a multiple point.
- Lean call sites of the bridge: Proofs/Sec4/DivSandpileLowerBound/ObstacleConvergence.lean:29 (x3, Theorem 4.1 /
  Prop 4.2 obstacle via Lemma 3.3 at `y = 0`); Proofs/Sec5/MeanValueInequality/CellRepresentative.lean:113 (x1,
  deterministic copy `vertexOf_zero_of_no_earlier_visit`, to be fed by x3's `ae_no_earlier_origin_visit`, :98); any
  future comparison of `m_eps` (walk from `vertexOf ε η 0`) with IDLA walkers from the vertex `0` (Sections 5, 6).

## Not corrections of the paper (Lean statement fidelity, review-S.md, inbox 14:05 UTC)
(S1)-(S7) change the Lean statements only; each is documented in the docstring of the statement it affects:
(S1) Lemmas 2.5, 2.6: field through its circle average process; (S2) the frozen Lemmas 3.5, 3.6 use `phi`, `psi` Hölder on a
neighbourhood of `cl(B_r(z))`. The corrected Lemma 3.6 successor instead uses continuous data on the closed disc and
nearest-point projection of exit-cell representatives, with uniform convergence and the Hölder same-walk rate as in
`LEMMA36-REPLACEMENT.md`; the frozen statement is not that successor. Lemma 3.5 also needs the projection convention;
(S3) Lemma 4.8 item 1 off the pole; (S4) Lemma 7.4 for the stopped odometer on its own
cluster; (S5) one annealed-probability convention (outer integral / outer measure); (S6) Lemma 3.1: `u^eps` are
`sigma(h, eta)`-measurable; (S7) MatedCRT/External (SLE-model inputs, quantum cone scaling).
