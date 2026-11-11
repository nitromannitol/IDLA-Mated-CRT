# Corrections in paper/idla_mated_crt-corrected.tex

Surgical corrections to arXiv:2211.04891, each marked `% CORRECTION [Cn]` in the corrected draft, with the published text,
the corrected text and the reason. Evidence: the refute-first check `review-C.md` (fleet directory, 2026-11-03; operator
verdicts in the inbox entry of 13:55 UTC). Line numbers refer to the published source `paper/idla_mated_crt.tex`.

## [C1] The limit constant is lambda_0 = 2/m_0 (written c_0 before 2026-11-11) (ESCALATIONS E-A3, CONFIRMED)
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

- Notation and normalisation (2026-11-11): the limit constant is written lambda_0 := 2/m_0 everywhere it means 2/m_0 (tex and email); the bold radius constant boldsymbol c_0 of Sections 6-7 is unchanged. The constants of Lemma A.3 of [BG20] (proof of the Step 1 bound in Section 3) are renamed c_{BG,0}, c_{BG,1}. The Green's function wording at the two places printed as 'Green's function for standard Brownian motion' (l.504, l.1225) now states the normalisation Delta G = -delta and the occupation density 2G.
## [C15] Median start in eq:mo (proof-consistent typo repair)
- The single deterministic `m_0` is the annealed median of the unscaled LBM exit time from `B_{1/2}` started at `0`, not at a free `z`. This agrees with the discrete median in eq:meps.

## [C16] Killed occupation proof in Lemma 3.4 (proof repair)
- Replace the unstopped functional and unjustified interchange by a buffered killed-path argument, convergence of exit times, a second-moment tail estimate, and the audited clock occupation identity. The identity has coefficient `2` for the unscaled clock and `c_0 = 2/m_0` for the paper's process, consistently with [C1]. The complete audited proof and exact citations are in `docs/campaign/OCCUPATION-PROOF.md`; deterministic thinning follows [C11].

- Appendix B (transcribed from docs/campaign/OCCUPATION-PROOF.md, 2026-11-11) contains the written proof of the occupation identity used in Lemma 3.4 (coefficient 2 for the unscaled clock, lambda_0 for X). Section 3 cites it as Appendix B.
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

- Also (2026-11-11, GAPS-SEC2567A.md E-A8): the four proof occurrences of the boundary predicate in the proof of Proposition 5.1 (dist(eta(a), partial eta(Lambda)) > delta, in the displays after the strict-gap and surplus steps) are replaced by partial overline{Lambda}, the boundary of the cell union, marked [C4].
## [C5] Scale-invariant integrand in the good-annulus event (ESCALATIONS E-A10, CONFIRMED)
- Where: eq:good-annulus-event (l.2314).  Published: `log(1/|u-v|) + 1`.  Corrected: `log(r/|u-v|) + 1`.
- Reason: for `u, v` in `A_{r,2r}(z)`, `|u - v| < 4r`, so the published left side is at least `(log(1/(4r)) + 1) mu_h(A)`
  while the right side is at most `C mu_h(A)`; the event is a.s. empty for `r < e^{1-C}/4`, contradicting Lemmas 6.4 and 6.5
  (faulty step l.2367: "the probability of E_r(z) does not depend on r or z"). The scale-invariant integrand makes that
  step valid. The integrand correction is settled. Step 4 of the printed Lemma 6.8 proof (l.2600) bounded the event through Lemma 2.18 (absolute `log(1/|z-w|)`); that proof is replaced under [C26]. Whether the replacement uses Lemma 2.18 is checked in the [C26] entry (E-A10 route question still to be verified). Lemmas 6.4-6.10 are not frozen.

## [C6] Lemma 3.2 (discrete Hoelder continuity): interior floor, starting vertex, boundary exponent (ledger entry written 2026-11-11)
- Where: Lemma 3.2 (lemma:discrete-holder-continuity), first marker at the lemma's opening line.
- Published: interior bound with factor (eps v |eta(a)-eta(b)|)^xi for all a, b in V(D); one exponent xi and a constant C for the boundary data.
- Corrected: the floor eps^beta in place of eps; the starting vertex a off V(partial D); for each chi in (0,1] an exponent xi' <= chi and a constant C = C(rho,gamma,chi,C') for boundary data with |f(a)-f(b)| <= C'(eps v |eta(a)-eta(b)|)^chi on V(partial D). The typesetting error \eps<TAB>o0 in the two displays is restored to \to.
- Reason: the interior estimate needs the floor eps^beta; the boundary exponent must depend on chi and the constant on C'. Email item: Lemma 3.2.
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

- Also (2026-11-11): the unmarked boundary-stability consequence in the proof of Lemma 4.8 (polynomial boundary data differ from their projected values by o(m_eps)) carries this marker. Appendix C (the replacement argument for Lemma 3.6, transcribed from docs/campaign/LEMMA36-REPLACEMENT.md) is the written proof of this entry, and the uses in Section 4 are listed there.
## [C14] Normalized comparison boundary offset (author-approved 2026-11-06)
In the proof of Lemma 4.8, replace `m_eps phi^delta(eta(b)) + delta` by `m_eps (phi^delta(eta(b)) + delta)`. Only the latter gives the stated limiting boundary value and the intended domination. This implements G3 of `PROOF-REPAIRS-G.md` in the paper.

## [C18] Lemma 6.4 constant dependency (author-approved 2026-11-09)
Replace "a constant C depending only on gamma" by "depending only on gamma and c_0". The proof gives C(gamma, c_0); a good annulus forces C >= (1 - log 2)/(16 c_0^2) (packing), and c_0 = c_0(rho, gamma) is the standing choice, so C(gamma) is unjustified (false if inf_rho c_0 = 0). All later uses fix rho. See fleet notes fp-gaps/CHATGPT-s6-constants.md and CHATGPT-6-4-referee.md.

- Also (2026-11-11): the stale C = C(gamma) in the proof of Lemma 6.4 (printed as C(gamma) at the annulus-hit display) is C(gamma, c_0), i.e. C(gamma, boldsymbol c_0) in the corrected draft.
## [C19] Lemma 6.8/6.9 negative-binomial tail events (author-approved 2026-11-10)
In the proof of lemma:chance-of-being-absorbed, eq:number-of-walkers-nb-bound and the display after it bound P[N(.) <= ...]; both events are reversed and now read P[N(k_1) > (s_2^{-1}+C) k_1 | h, eta] <= exp(-c k_1) and P[N((s_2^{-1}+C)^{-1} k) > k | h, eta] <= exp(-c k). The stochastic domination by NegBinom(k_1, s_2) bounds the probability of needing too many walkers; with certain absorption N(m) = m and the printed left side equals 1. Typo-level; the inclusive threshold of the conclusion is routine rounding (the direct proof in notes/fp-gaps/CHATGPT-6-9-claims-referee.md gives s_3 = log(27/16)/4, s_4 = 1/4, s_5 = 1/8 from the uniform constants of LEMMA68). Source: notes/fp-gaps/CHATGPT-6-9-claims-referee.md (G2).

## [C20] Proposition 4.2: strict interior gap at a fixed time (author-approved 2026-11-10)
The printed proof inferred the strict gap eq:strictly-above-in-interior from continuity alone, which does not exclude a jump of the harmonic-ball family at the fixed time t. Inserted before that display: under the unconditioned law, p(u) = P[Lambda_u != union_{q<u} Lambda_q] is positive for at most countably many u (rational closed-disk codes, pairwise disjoint in u), and Lemma 2.6 (lemma:scale-invariance) gives p(u) = p(bu), so Lambda_t = union_{u<t} Lambda_u a.s.; the obstacle equation (theorem:harmonic-balls (c)) and the strong minimum principle then give v_t > 0 on Lambda_t minus {0}, and compactness gives s > 0. Statement and display unchanged. Sources: notes/fp-gaps/CHATGPT-4-2-strict-gap-proof.md (proof), notes/fp-gaps/CHATGPT-idla-corrections-4-2-5-1.md (text).

## [C21] Proposition 5.1: application of Lemma 5.2 (author-approved 2026-11-10)
The printed proof applied Lemma 5.2 without verifying its hypotheses for the chosen sets (G1a, G1b), used the full sandpile cluster where coverage by the strict positivity set is needed (G1c), and did not justify the stated stopping domain. The proof is replaced by one direct argument: O_1 = cells of B_{delta}^-(Lambda_t), I_eps = Lambda_t^eps intersected with the cells of Lambda_t, the surplus u^eps >= c/eps on O_1 from the strict gap of [C20] and the convergence results, a maximum-principle comparison giving the mean-value inequality on I_eps, the Green-kernel lower bound for the second hypothesis, and the vertexwise proof of Lemma 5.2 (after Lawler-Bramson-Griffeath, Section 3) on the origin component; monotonicity in the stopping domain gives both conclusions. Statement unchanged; supersedes the in-proof comment of [C4]. Sources: notes/fp-gaps/CHATGPT-5-1-gaps-referee.md (repairs), notes/fp-gaps/CHATGPT-idla-corrections-4-2-5-1.md (text).
Independent referee check (notes/fp-gaps/CHATGPT-idla-C20-C21-referee.md): [C20] and [C21] correct and complete; two sentences of surrounding exposition (before lemma:mean-value-ineq and after lemma:L-lower-bound) updated to the new organization (editorial).

## [C22] Lemma 6.8, Step 3: sparsity estimate at the radius r_z (applied 2026-11-10 under the author's standing approval)
Printed: Step 3 bounded |A cap V^eps(B_{c_0 r_z}(eta(b)))| by the sparsity assumption for a single radius-r ball, producing s_1 r^{2 beta^-}; this needs c_0 r_z <= r, which the radius selection r, r_z in [delta, sqrt delta] does not give (counterexample in notes/fp-gaps/CHATGPT-idla-6-8-perstate.md section 4). Corrected: cover B_{c_0 r_z}(eta(b)) by at most (1 + 2 c_0 r_z / r)^2 radius-r balls, so the count is at most 10 s_1 r_z^{beta^-} eps^{-1} (since r^2 <= delta <= r_z and beta^- > 1), and take s_1 < c/10; the rest of Step 3 is unchanged. The statement of Lemma 6.8 is unchanged (s_1 depends only on (rho, gamma)). Text: notes/fp-gaps/CHATGPT-idla-6-8-hRr.md (ChatGPT chat 176).
Independent referee check (notes/fp-gaps/CHATGPT-idla-C22-referee.md, chat 185): [C22] correct (the constant 10 uses c_0 < 1/5, eq:choice-of-constant-annulus; s_1 does not depend on s_0). Editorial in the same proof: \mathbf{r}_{z/4} read as \mathbf{r}_z/4, a missing parenthesis, $ placement in Step 4.

## [C23] Lemma 5.3: dependence of the surplus random variable (applied 2026-11-10 under the author's standing approval)
Printed: The statement wrote \mathfrak{s}=\mathfrak{s}(\delta), even though the existential quantifier comes after both \delta and t. Corrected: write \mathfrak{s}=\mathfrak{s}(\delta,t), so the notation matches the quantifier order; the quantifiers and proof are unchanged. Text: CHAT209-idla-3-1-4-2-5-3-audit-PRO.md, correction 7 (ChatGPT chat 209); exact LaTeX from ChatGPT chat 215.

- Also (2026-11-11, GAPS-SEC2567A.md E-m1-2): the displayed surplus in the proof of the positive-surplus step is written s(rho, gamma, delta, t) (dependence on t, as in the statement).
## [C24] Lemma 7.3: almost-sure simultaneous scope (applied 2026-11-10 under the author's standing approval)
Printed: The statement omitted its ambient probabilistic scope. Corrected: state that the comparison holds almost surely, simultaneously for every eps > 0. The quantifiers over t, B and b, the displayed inequality and the proof are unchanged. Text: CHAT163-idla-7-8-audit-PRO.md, section 4 (ChatGPT chat 163); exact LaTeX from ChatGPT chat 215.

## [C25] Lemma 7.4: positive stopped support and one event simultaneous in t (applied 2026-11-10 under the author's standing approval)
Printed: Lemma 7.4 started from every a in D_eps(t eps^{-1}) and required the path to stay in that cluster, while the increments are for the stopped odometer u_t^eps. Since D_eps(t eps^{-1}) is the closure of the positive stopped support, a starting point can have zero stopped odometer, and the first increment by log(eps^{-1})^{-2} need not hold. The wording also placed "for all t > 0" outside "with polynomially high probability." Corrected: on the single degree-bound event, simultaneously for every t > 0 and every nonzero a in Lambda_t^eps={u_t^eps>0}, construct the increasing path entirely in Lambda_t^eps. The proof now inducts inside Lambda_t^eps and deletes the boundary-start alternative. In Step 3 of Proposition 7.1, apply the path to each a in Lambda_t^eps outside Theta_{tau_{eps,2}} and stop it on first reaching the boundary of Theta_{tau_{eps,2}}. In the same Step 3 the path bound reads "the odometer increases by at most eps^{-omega_0}". Text: CHAT163-idla-7-8-audit-PRO.md, section 4 (ChatGPT chat 163); exact LaTeX from ChatGPT chat 215 (notes/fp-gaps/CHATGPT-215-idla-tex-C23-C25-PRO.md).

## [C26] Lemma 6.8: replacement proof (applied 2026-11-10 under the author's standing approval)
Printed (corrected draft through [C25]): the proof of Lemma 6.8 did not establish the lemma. An independent referee check (ChatGPT chat 225, notes/fp-gaps/CHATGPT-225-idla-C22-referee-PRO.md) found that the Step 1 good annuli lie outside the exit domain of the walk, that after [C5] Steps 2 and 4 still used the old non-scale-invariant logarithmic kernel, and smaller gaps in the Green lower bound, the ball-to-annulus inclusion, the stopping convention and the exponent bookkeeping; the [C22] Step 3 covering estimate is correct locally but is superseded. Corrected: the proof is replaced by a target-scale short-window good-annulus construction with two-sided-shell amplification (the architecture of chats 188, 190, 193). The statement is unchanged; the proof gives the stronger order s_1 = s_1(rho, gamma), s_2 = 1/2 chosen before s_0, only delta depending on s_0. Text: ChatGPT chat 229 (notes/fp-gaps/CHATGPT-229-idla-C26-lemma-6-8-proof-PRO.txt). Compiled: pdflatex 0 errors, 0 undefined references.

## [C27] Section 6, good-annulus event (eq:good-annulus-event): min -> inf (applied 2026-11-10 under the author's standing approval)
Printed: C min over the open annulus A_{r,2r}(z) of mu_h(B_{c_0 r}(w)); no attainment argument, while the [C26] proof substitutes m_R(z) defined as an infimum. Corrected: inf (strictly positive by a finite net and full support). Independent Pro referee of [C26], ChatGPT chat 244 (notes/fp-gaps/CHATGPT-244-idla-C26-lemma-6-8-referee-PRO.md), Gap 1.

## [C28] Lemma 6.5 (lemma:annulus-hit): Weyl comparison for the signed [C5] kernel, and C = C(p, gamma, c_0) (applied 2026-11-10 under the author's standing approval)
Printed: Step 1 compares the ratios L/R for h and h^C by bounded Weyl densities; after [C5] the kernel log(r/|u-v|) + 1 is negative for |u-v| > e r, so bounded densities do not give the multiplicative comparison. Corrected: write d mu_h = q d mu_{h^C} with a <= q <= b, b/a <= A_gamma on A_{r/3,3r}(z); average the h^C event over the circle of radius 3r/2 to bound the annulus mass, bound the positive part of the kernel, and get E_r(z; C) for h with C = A_gamma C_1 (1 + (log 4 - 1)/(1 - log 2)). The statement now records C = C(p, gamma, c_0) (c_0 = c_0(rho, gamma)), consistent with [C18]. Chat 244, Gap 2.

## [C29] Lemma 6.8 proof ([C26], short-window good radii): translated application of Lemma 6.6 (applied 2026-11-10 under the author's standing approval)
Printed (in the [C26] replacement proof; the printed paper of arXiv:2211.04891 has no translation step, and the omission in Lemma 6.4 is [C32]): "Apply Lemma 6.6, after translating by z"; the quantum-cone field is not translation invariant. Corrected: h(z + .) = h~^C + phi_z modulo constants with phi_z(w) = -gamma log|z + w| deterministic and continuous on the annuli (they avoid -z); adding phi_z is invertible on each annular sigma-field modulo constants, so Lemma 6.6 applies to the translated events with the same constants. Chat 244, Gap 3.

## [C30] Lemma 6.8 statement: the event "exits ... through A" defined explicitly (applied 2026-11-10 under the author's standing approval)
Printed: "X^{a,eps} exits V(Theta-bar + B_r) minus Theta through A" (A is a subset of the domain, not of its exit boundary). Corrected: with U = V(Theta-bar + B_r) minus Theta and tau the exit time of U, the event is {X_n in A for every 0 <= n < tau}, as the [C26] proof (eq:c26-bad-event) and Section 7 use it. Chat 244, Gap 4.

## [C31] Definition 6.2 (def:stopped-idla), the Abelian-property lemma (lemma:abelian-IDLA) and the proof of Lemma 6.9: starting sites (applied 2026-11-10 under the author's standing approval)
Printed: a_1, ..., a_k in Theta (Definition 6.2, lemma:abelian-IDLA "subset Theta", proof of Lemma 6.9), while the restarted aggregates start walkers on the boundary of the stopping set and Lemma 6.9 is stated for a_i in cl(Theta). Corrected: a_i in Theta' in Definition 6.2 and lemma:abelian-IDLA (a walker started at an unoccupied vertex is absorbed there at time zero), and a_i in cl(Theta) in the proof of Lemma 6.9. Not a defect of [C26]. Chat 244, Gap 5.

## [C32] Lemma 6.4 proof: translation of the annuli and the number of radii (2026-11-11)
- Where: proof of Lemma 6.4 (lemma:good-prevalance), the application of lemma:annulus-iterate and the choice of K.
- Printed: lemma:annulus-iterate (stated for annuli centred at 0) is applied to the events E_r(z) with z != 0 without a translation step; K = floor(log_7 eps^{-1/2}).
- Corrected: the translation step of Subsection comparison-estimates (h(z+.) = h~ + phi_z modulo constants, phi_z(w) = -gamma log|z+w|, the same argument as the translated application in Lemma 6.8) gives the hypotheses of lemma:annulus-iterate with the same marginal bounds and constants; K = floor(log_7 delta^{-1/2}).
- Reason: the radii r_k lie in [delta, delta^{1/2}] and the number of them is of order log_7 delta^{-1/2}. Email item: Lemma 6.4 (new item, 2026-11-11).

## [C33] Appendix A (obstacle problem): connectedness of V not assumed (E-c1-2, 2026-11-11)
- Where: opening of Appendix A (sec:obstacle-appendix) and a remark after it.
- Published: G undirected, locally finite and infinite; V a finite, connected set containing the origin.
- Corrected: G undirected, locally finite, connected and infinite; V a finite set containing the origin. The remark gives the componentwise argument (paths in G to V^c; finite maximum principle on each component; obstacle zero on components not containing 0).
- Reason: GAPS-SEC2567A.md E-c1-2 (MINIMAL-CORRECTION). The Section 4 reduction can give a disconnected ball-interior set. Email item: Appendix A (new item).

## [C34] Proposition 5.1 proof: boundary vanishing (E-x1-1, 2026-11-11)
- Where: proof of Proposition 5.1, the sentence 'Since w~ = gr_{B_rho}(., 0) = q = 0 on partial Lambda' (before the display for v - v~).
- Printed: the ambient Green function and w~ vanish individually on the cluster boundary.
- Corrected: w~ + (t/eps) gr_{B_rho}(., 0) vanishes on partial Lambda by obstacle contact (the obstacle is -(t/eps) gr_{B_rho}(., 0)); gr_Lambda and q_Lambda vanish there by killing. The statement is unchanged.
- Reason: GAPS-SEC2567A.md E-x1-1 (MINIMAL-CORRECTION). Email item: Proposition 5.1 (new minor item).

## [C35] Lemma 6.9: quantifier order of s_3 (E-c5-1, 2026-11-11)
- Where: statement of lemma:chance-of-being-absorbed.
- Printed: omega and s_3 chosen before s_0; s_4, s_5 after.
- Corrected: omega chosen first; for each s_0 in (0,1) there exist s_3 > 0 and s_4, s_5 in (0,1). The proof is unchanged ([C19] proof kept). The replacement local-rate deduction in GAPS-SEC2567A.md E-c5-1 is NOT applied (see AUDIT-R1-RESPONSES.md, IDLA (A)).
- Reason: the success probability of Lemma 6.7 may depend on s_0. Email item: Lemma 6.9 (new minor item).
## Readings (not corrections of the paper; line numbers of the corrected draft)

### (R1) The origin vertex `0` and `a^eps_0` (ESCALATIONS E-x3-3, the formalization, 2026-11-04)
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
  (MatedCRT/Proofs/Sec4/DivSandpileLowerBound/SourceVertex.lean:125, the formalization, commit 1326986), from the identity case
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

## Transcription notes (appendix audit section)

- T1 (Lemma 3.6 audit of every use). The audit section of docs/campaign/LEMMA36-REPLACEMENT.md (lines 629-703) is transcribed into the audit subsection of Appendix C (paper/idla_mated_crt-corrected.tex, subsection "Uses of Lemma 3.6 in the paper"), with the item labels and text of the source. Two notation points: the constant written c_0 in the source is written lambda_0 (renamed, see the [C1] entry and the notation line of AUDIT-R1-RESPONSES.md); Theorem~\ref{thm:A} is repointed to the label thm:l36-A of the Appendix C theorem; \F is written \mathcal{F}.
- T2 (boundary datum at "about line 2010" of the audited source). The source states that the boundary condition must be f_delta^eps(b) = m_eps(phi^delta(eta(b)) + delta), not m_eps phi^delta(eta(b)) + delta. The corrected paper already displays the corrected form at paper/idla_mated_crt-corrected.tex:2111 (lemma on the convergence of the odometer, proof of the subsequential limits). Line 2010 of the current file lies in a different lemma, so the audit line number refers to an earlier numbering. The transcription keeps the corrected display; no main-text change was made.
