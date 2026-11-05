# Sections 3 and 5: independent statement audit, work in progress

Snapshot: HEAD `00649b287c08f1fb139d2bca9097fccc141a8d61`, 2026-11-05.
Source: `paper/idla_mated_crt-corrected.tex`; source line numbers below are in that file.
The freeze list explicitly says it is not in force; no versioned declaration manifest or pinned
source/declaration hashes were provided. This is therefore a preliminary audit, not a seal or an
independent approval. The standing environment and semantic closure have not yet been fully audited.
`MISMATCH` means a visible syntactic/quantifier difference, not a proof of falsity. A documented
correction or reading is identified separately from operator-approved source corrections.

| Result | Preliminary finding and exact evidence | Reduction status |
| --- | --- | --- |
| 3.1 | **WRONG** (conditional Lean refutation), with a documented source mismatch: source 976–999 allows connected sets; Draft/Section3.lean:42 adds pointwise environment measurability of `u` (S6). Corrected form Steps/Sec3/DiscretePotentialTightness.lean:102 adds open `D` and deterministic polynomially summable scales and changes boundary data to `C'/ε` times the Hölder modulus. Its interior part is weaker but its boundary implication is stronger. The source and Draft both use the corrected absolute bound [C3]. The Draft is **WRONG** under the explicit scaling input and a valid environment: `Audit.Refutations.not_discretePotentialTightnessStmt` proves its negation using a closed segment (E-c1-4). | Only corrected form reduced; both imply a common restriction in Audit/CorrectedForms.lean:83, 93. The reduction is not a proof of the Draft. The current 3.3 and 3.7 reductions use the a.s. tightness step rather than this Draft (the older REDUCTIONS F7 entry is stale). |
| 3.2 | **DIVERGES-DOCUMENTED**: correction [C6] now gives the interior floor `ε^β`, restricts `a` to the interior, and chooses `ξ′` after `χ` and before `C′` (source 1001–1017; Draft/Section3.lean:76). The Draft reflects this order and adds `ξ′ ≤ χ`. The multiplied-distance form needs a separate zero-distance check. | `DiscreteHolderContinuityCorrectedStep` (:71) allows `ξ′` to depend on `C′` and omits `ξ′ ≤ χ`, hence is weaker. Draft implies the step (`Audit/CorrectedForms.lean:114`), with no reverse implication established. Both are cited hypotheses, not proofs. The 3.2 entry in CORRECTED-FORMS.md predates C6 and describes the superseded Draft. |
| 3.3 | **INCOMPLETE**: source 1110–1122 and Draft/Section3.lean:97 have the same probability mode and `[C1]` coefficient `c₀/6`. `S.c₀ = 2/S.m₀` (Defs/Setting.lean:190). Source calls its Green function Brownian occupation Green, whereas the Lean symbol is normalized by `ΔG = -δ`; the factor-of-two convention must be checked together with [C1], not inferred from matching symbols. | Reduction `uniformConvergenceGreenKernel_of_steps` concludes Draft assuming the a.s. tightness step and interior/boundary steps; `uniformConvergenceGreenKernel_final` discharges the latter two and maximum principle, retaining 2.10, 3.4, 2.14, 2.8 and the a.s. tightness step (InteriorStep.lean:73, commit 763b7d7). Existing [C1] proof slip E-m1-1 remains documented. |
| 3.4 | **INCOMPLETE**: source 1124–1133 and Draft/Section3.lean:113 use convergence in probability, `mε⁻¹`, `c₀`, and deterministic `z,r,y`; Lean quantifies over random pointwise measurable `f` with pathwise bounded/Hölder restrictions. Source `f` is defined on the ball but evaluates `f(η(x))` for cells meeting it. For positive ε and continuous η, `three_four_sum_ext` in the audit Lean file proves that the discrete sum depends only on values of `f` on the ball: interior-cell marked points lie in the ball, and the killed Green function vanishes outside the interior. This resolves the off-ball extension question for the sum, conditional on those hypotheses; remaining probabilistic and Green semantics still require audit. Green normalizations remain open as for 3.3. | REDUCTIONS records no committed reduction. |
| 3.5 | **MISMATCH**, documented: source 1240–1260 assumes `φ` Hölder on the closed ball, while Draft/Section3.lean:136 requires it on a larger closed ball (S2), potentially excluding source data. `[C1]` uses `c₀`. Lean quantifies over all discrete solutions satisfying the equations a.s. for each ε; the choice/uniqueness and signed Laplacian semantics require audit. | `discreteDirichletProblem_of_steps` concludes Draft and uses corrected 3.1 plus open steps; it does not establish the source statement without addressing S2. |
| 3.6 | **MISMATCH**, documented: source 1262–1280 assumes `ψ` Hölder on the closed ball; Draft/Section3.lean:161 requires Hölder regularity on a larger ball (S2). Lean takes each deterministic `y` separately, as does the probability convergence reading of the source. Exit-time and time-change semantics remain to check. | `convergenceHarmonicFunctions_of_steps` concludes Draft with two open steps. |
| 3.7 | **INCOMPLETE**: source 1399–1412 and Draft/Section3.lean:177 both state convergence in probability uniformly on the closed ball with `[C1]` coefficient `-c₀/6`. `HasLaplacian` and normalized exit-time definitions require full semantic audit. | `convergenceNormalizedExitTime_of_statements` concludes Draft from 3.3, 3.5, 2.17, 2.18 and the open almost-sure corrected tightness step; it does not assume Draft 3.1 directly. |
| 5.1 | **INCOMPLETE**: source 1971–1982 and Draft/Section5.lean:27 have both unrestricted and stopped clusters, failure on `{t<T}`, and the source stopping set `Vε(Λ_t)`. The outer annealed probability is a documented interpretation (S5), not a literal source correction; `IsConeHarmonicBallFamily`, the cluster and walk laws need closure audit. | `iDLALowerBound_of_volumeGrowth_cellSize` concludes Draft with open stopped-cluster and inner-approximation steps; no unconditional proof. The printed proof stops at the discrete obstacle cluster, while the proposition stops at `Vε(Λ_t)`; the latter remains `IDLALowerBoundStoppedStep` (E-c1-5). |
| 5.2 | **INCOMPLETE**: source 1987–2002 and Draft/Section5.lean:47 include inclusion, origin, measurable connected domains, two Green estimates, and the stopped claim. Draft fixes `K : ℝ → ℝ` deterministic; source does not explicitly say deterministic, so this is a potentially narrower reading requiring a ruling. | Relaxed Step at Steps/Sec5/IDLALowerBound.lean:40 removes several hypotheses and implies Draft (`generalIDLALowerBound_of_relaxed`, :180); reduction from 2.7 and 2.8 is recorded in REDUCTIONS. This is conditional on those inputs. |
| 5.3 | **MISMATCH**: source 2008–2015 explicitly writes `𝔰 = 𝔰(δ)`, while Draft/Section5.lean:67 quantifies `∀ δ t, ... ∃ s`, allowing `s` to depend on `t`. The source wording may be a notational omission; ruling requested in E-m1-2. [C4] is represented by `frontier (fillCells ...)`. | `meanValueInequality_of_surplus` concludes the Draft and assumes an open surplus step and other inputs; it does not establish uniformity of `s` in `t`. |
| 5.4 | **INCOMPLETE**: source 2019–2026 chooses deterministic `q` before `δ,t`; Draft/Section5.lean:85 also chooses `q` before environment, `Λ`, `δ,t`, potentially imposing greater uniformity over representations than the source specifies. [C4] uses the cell union. Real division and real `tsum` semantics at zero/infinity need checking. | `lLowerBound_of_inputs` concludes Draft using cited 2.15, 2.16, 2.9; conditional only. |

A checked logical witness for the 5.3 quantifier distinction is in
`MatedCRT/Audit/StatementsSec3Sec5M1.lean` (`time_dependent_witness_not_uniform`): it is an
abstract counterexample to exchanging quantifiers, not a counterexample to Lemma 5.3 itself.

Remaining for a passing audit: reconstruct every binder into SOURCE/STANDING/TYPING/RULED/EXCESS
with counts, pin exact source and declaration identities, recursively audit `IsValid`, Green,
rescaling, probabilities, stopping, harmonic-ball and Laplacian definitions, and verify every
reduction by exact term-level applications and axiom checks. No FAITHFUL verdict is assigned here. The Draft 3.1 refutation is a conditional Lean theorem; it does not independently settle whether valid environments and its scaling input exist.

## Source identity and Green normalization

SHA-256 at the earlier review (superseded after C6): corrected source `d42d5867a83da66f530c4407bf9e5bc423f04e5b9e2c5ba5567932c09ca106`; Draft Section3 `4541957faaba0cbe632cb7b6b8ee4f680258a38e97f339b7922d77487ad51649`; Draft Section5 `30554ab9e72ac1322f94320c9270695191cb5c9404b9e4023277fcdd2f84edf1`. These are observations, not an operator-approved freeze.

The corrected paper explicitly fixes `ΔG = -δ` and Brownian occupation density `2G` at line 720. The reused definition `HarmonicBalls/Defs/Green.lean:41,70` has Newton kernel `-(2π)⁻¹ log |x-y|` and the same normalization. Thus Lean's `c₀ = 2/m₀` agrees with the corrected source convention in the expressions 3.3–3.5 and 3.7. This is a coefficient comparison, not an independent proof of the Brownian occupation identity or the full Green characterization. The paper's phrase “Green's function for standard Brownian motion” at 1119 must be read with line 720; its occupation density is `2G`. E-m1-3 reports remaining `m₀` references in the proofs of 3.5 and 3.7. E-m1-4 records an independent sign discrepancy and a wrong center in the 3.7 proof.

## Binder inventory for 5.3 (provisional, fail-closed)

Counts below use one row per named variable or logical premise, excluding internal binders of a formula. Instance/environment classification is provisional: standing assumptions have not themselves been independently audited. The source order is δ then t, with a surplus annotated `s(δ)`; the Lean conclusion has `∃ s` after both. `TendsToOneOn` expands to outer `P(F ∩ Eεᶜ) → 0` (Defs/Notation.lean:39).

| Lean binder/input | Bin | Source or reason |
| --- | --- | --- |
| `𝒮` | TYPING | abstract SLE model, Section 1 conventions |
| `γ` | STANDING | γ-LQG, Section 1 |
| `0 < γ` | STANDING | γ in (0,2), Section 1 |
| `γ < 2` | STANDING | same |
| `ρ` | STANDING | fixed in Section 5, line 1967 |
| `0 < ρ` | STANDING | line 1967 |
| `ρ < 1` | STANDING | line 1967 |
| `Ω` | TYPING | probability-space carrier |
| `[MeasurableSpace Ω]` | TYPING | measurable-space carrier |
| `S` | TYPING | packaged field/curve/measure/walk environment |
| `S.IsValid 𝒮 γ` | STANDING, provisional | expands into the seven rows below; not independently validated |
| `isProbabilityMeasure` | STANDING, provisional | probability law of environment |
| `isQuantumCone` | STANDING, provisional | Section 2 quantum cone |
| `isLQGMeasure` | STANDING, provisional | field's LQG measure |
| `isSLE` | STANDING, provisional | independent space-filling SLE |
| `isAreaParametrized` | STANDING, provisional | area parameterization |
| `isLQGClock` | STANDING, provisional | LBM clock; stronger simultaneous conditions not yet audited |
| `matingOfTrees` | EXCESS or unclassified, provisional | Contains named literature results, some consumed by reductions; see E-m1-5. Full bundle not yet audited. |
| `Λ` | TYPING | represents the source harmonic-ball family |
| a.s. `IsConeHarmonicBallFamily` | STANDING, provisional | Theorem 2.3 family; expanded characterization and existence/uniqueness not audited |
| `δ` | SOURCE | line 2009 |
| `t` | SOURCE | line 2009 |
| `0 < δ` | SOURCE | line 2009 |
| `δ < ρ` | SOURCE | line 2009 |
| `0 < t` | SOURCE | line 2009 |

At this level there are 5 SOURCE rows, 13 provisional STANDING rows, 5 TYPING rows, and one provisional EXCESS or unclassified row; these are not final counts because the environment bundle has not been fully expanded. [C4] changes the body of the conclusion, not an input binder. This inventory does not pass the five-bin audit: recursive expansion of the environment and harmonic-ball predicates is unfinished, and quantifier-order issue E-m1-2 remains.

The Lean evidence `relaxed_five_two_implies_draft` explicitly applies the actual relaxed 5.2 producer to the Draft; it does not establish either proposition unconditionally. `#print axioms` for both this implication and the abstract quantifier example reports only `propext`, `Classical.choice`, and `Quot.sound`.


## Checked reduction applications

`MatedCRT/Audit/StatementsSec3Sec5M1.lean` explicitly applies the respective producers in `three_one_corrected_reduction`, `three_three_draft_reduction`, `three_five_draft_reduction`, `three_six_draft_reduction`, `three_seven_draft_reduction`, `five_one_draft_reduction`, `five_two_draft_reduction`, `five_three_draft_reduction`, and `five_four_draft_reduction`. These check the displayed conditional conclusions and their supplied hypotheses; they do not prove the hypotheses or resolve source fidelity. No producer application for 3.2 or 3.4 is claimed here. All eleven `#print axioms` checks in the file report only `propext`, `Classical.choice`, and `Quot.sound`. This does not detect mathematical assumptions packaged in the environment, as E-m1-5 demonstrates.

The checked theorem `three_four_sum_ext` uses pointwise equality on the ball and imposes no summability hypothesis: `tsum_congr` applies term by term, with zero Green function for all vertices outside the killed domain. It does not establish convergence or measurability in Lemma 3.4.


## Lemma 5.4 binder and definition trace (provisional)

The source fixes the γ-quantum-cone/SLE setting and ρ in Section 5 before saying “there exists a deterministic q > 0” (corrected source:1967, 2019–2026). The Lean definition `LLowerBoundStmt` (`Draft/Section5.lean:85`) places `∃ q` after γ, ρ but before the probability carrier, environment, and choice of harmonic-ball family. It therefore requires one q for every valid representation at fixed γ, ρ. Whether the paper's fixed-law formulation entails this is not settled by the word “deterministic.”

| Lean input or local binder | Provisional bin | Evidence / open issue |
| --- | --- | --- |
| `𝒮` | TYPING | SLE-model parameter; equivalence of representations remains open |
| `γ`, `0 < γ`, `γ < 2` | STANDING | Section 1 γ-LQG setting |
| `ρ`, `0 < ρ`, `ρ < 1` | STANDING | fixed immediately before Proposition 5.1 |
| `q`, `0 < q` | SOURCE | source chooses deterministic positive exponent; Lean choice is before environment and family |
| `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | environment carrier and packaged structure |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | expands to seven fields; `matingOfTrees` includes named literature inputs (E-m1-5) |
| `Λ`, a.s. `IsConeHarmonicBallFamily (S.μ ω) (Λ ω)` | UNCLASSIFIED | source uses Theorem 2.3 family; expanded conditions and existence/uniqueness are not yet closed |
| `δ`, `0 < δ`, `δ < ρ`, `t`, `0 < t` | SOURCE | quantified after q in both source and Lean |

`clusterExitTime` is exactly the displayed supremum over positive times with `Λ_t ⊆ B_{ρ/3}` (`Defs/Setting.lean:244`, source:1596–1599), subject to real `sSup` semantics when that set is unbounded. `fillCells` is the indexed union in source:248 (`Defs/Map.lean:195`); `matedDiscreteCluster` unfolds to the obstacle cluster from source:1690 (`Defs/Sandpile.lean:87`). `TendsToOneOn` is outer `P({t < T} ∩ Eεᶜ) → 0` (`Defs/Notation.lean:39`). These are definition-body comparisons, not proofs of finiteness of the stopping time, measurability, or the obstacle characterization. The Green quotient is addressed on the finite first-step event below.


On the event used in the 5.4 reduction, `A = matedDiscreteCluster ...` is finite and the Green first-step equation holds on `A` (`LLowerBound/GreenEstimates.lean:20–35`). `LLowerBound/OfEvents.lean:51–76` obtains finiteness using the finite ambient ball interior and the inclusion `A ⊆ B`, and `OfEvents.lean:90–94` supplies this step from the cited estimates and the separately stated adjacency input. The first-step equation yields `0 < greenFn m A a a` for `a ∈ A` (`GreenMonotonicity.lean:21`); `ObstacleSpecialization/Escape.lean:214` converts the subtype `tsum` into the finite sum. `five_four_green_quotient_semantics` in the audit Lean file checks these two conclusions together. Thus the real-division and `tsum` conventions coincide with the intended quotient on that event, not necessarily for arbitrary environments outside it. This conditional check does not settle E-m1-5 or the full statement audit.


## Cluster exit time: boundedness and dependency

`cluster_exit_time_bounded` in the audit Lean file checks that `0 < clusterExitTime Λ ρ ≤ (μ (ball 0 (ρ / 3))).toReal`, assuming the harmonic-ball family conditions, finite mass of that ball, and some positive `s` with `Λ s ⊆ ball 0 (ρ / 3)`. Thus on these assumptions the real `sSup` agrees with a positive, bounded time-set supremum. This uses `Sec1.clusterExitTime_spec` (`Proofs/Sec1/ScaledClusterExitTime.lean:75`), whose proof obtains boundedness from the family mass identity and measure monotonicity.

The same file obtains the small-time inclusion via `Sec1.exists_pos_subset_ball` (:37), requiring strict growth, and derives the almost-sure conditions in `scaledClusterExitTimeStep_of_steps` (:258–285) with the explicit `ConeHarmonicBallStrictGrowthStep` input and local finiteness of the LQG measure. This is a conditional dependency trace; the proof here does not establish strict growth or its literature status, nor assert an unconditional almost-sure stopping-time theorem.


## Lemma 5.2 binder and reduction trace (provisional)

The source at corrected lines 1987–2002 fixes two environment-measurable connected domains containing 0, positive `Kε`, deterministic positive `q`, and a positive finite environment-measurable random variable `s`. The Lean carrier indexes vertices by integers `k`, representing the source vertex `εk` (`Defs/Map.lean:177`); `O₁`, `O₂` are functions of scale and environment. Its floor is the natural floor `⌊K ε⌋₊`, agreeing with the ordinary floor at positive `K ε`.

| Lean input or premise | Provisional bin | Comparison |
| --- | --- | --- |
| `𝒮`, `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | abstract model and environment carrier; representation semantics open |
| `γ`, `0 < γ`, `γ < 2`, `ρ`, `0 < ρ`, `ρ < 1` | STANDING | paper's fixed quantum-cone setting and Section 5 radius |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | expanded coupling includes mathematical inputs; E-m1-5 |
| `O₁`, `O₂`, their pointwise membership measurability | SOURCE | environment-measurable random vertex sets |
| inclusion, origin membership and `IsVConnected` | SOURCE, provisional | required almost surely separately for every positive ε; source's quantification in ε and graph-domain convention require interpretation |
| `K : ℝ → ℝ`, `∀ ε, 0 < K ε` | SOURCE plus potentially EXTRA | positivity for all real ε is stronger than needed for ε → 0⁺; Lean also makes K deterministic, whereas the source does not explicitly say so |
| `q : ℝ`, `0 < q` | SOURCE | source says deterministic q > 0 |
| `s : Ω → ℝ`, environment measurability and `∀ ω, 0 < s ω` | SOURCE, provisional | real-valued encodes finiteness; pointwise positivity is stronger than an a.s. reading but may admit a harmless modification if measurability is retained |
| probability tending to one of both Green estimates | SOURCE, provisional | outer probability of failure via `ProbTendsToOne`; denominator and real `tsum` need valid finite-domain justification |
| both unrestricted and stopped inclusions | SOURCE, provisional | annealed outer probability and the conditional walk law need closure audit |

`GeneralIDLALowerBoundRelaxedStep` (`Steps/Sec5/IDLALowerBound.lean:40`) removes set measurability, connectedness, origin membership and positivity of `K` while preserving deterministic `K`, positive q and pointwise-positive measurable s. The checked `relaxed_five_two_implies_draft` in the audit Lean file applies the producer explicitly; it establishes a conditional implication only. `walkerSequenceLaw` is `Measure.infinitePi` of `srwLaw` (`Defs/RandomWalk.lean:153`), and `idlaProb` applies `annealedOuterProb` to that family of quenched laws (`Defs/Setting.lean:194`). These are body checks, not yet a proof that the annealed construction agrees with the ordinary joint law for all relevant events.

The proof of Proposition 5.1 applies Lemma 5.2 with `O₂ = Λε_t` (corrected source:2033–2044), whereas its stopped assertion uses `Vε(Λ_t)` (source:1977–1981); see existing E-c1-5. The available 5.1 reduction assumes `IDLALowerBoundStoppedStep`, so it does not claim this proof gap closed.


## Lemmas 3.5 and 3.6 binder and definition traces (provisional)

The corrected source states Lemma 3.5 at lines 1240–1258 and Lemma 3.6 at lines 1262–1274. Their common outer parameters are compared below; the bins remain provisional until the bundled environment has been recursively audited.

| Lean input or local binder | Provisional bin | Comparison |
| --- | --- | --- |
| `𝒮`, `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | model and measurable environment carriers; representation semantics remain open |
| `γ`, `0 < γ`, `γ < 2`, `ρ`, `0 < ρ`, `ρ < 1` | STANDING | paper's quantum-cone setting and fixed radius |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | packaged coupling and mathematical inputs; see E-m1-5 |
| `r`, `z`, `0 < r`, `ball z r ⊆ ball 0 ρ` | SOURCE | deterministic choices in both statements |
| 3.5 `ψ : ℂ → ℝ`, bounded and Hölder on `ball z r` | SOURCE, provisional | source gives ψ only on the ball; Lean uses a global representative |
| 3.5 `φ : ℂ → ℝ`, Hölder on `closedBall z (r+s)` for some `s > 0` | EXCESS relative to printed domain | source only specifies the closed ball; draft documents review-S (S2) because boundary-cell marked points can lie outside it |
| 3.5 `F`, discrete equations | SOURCE, provisional | equations hold almost surely separately for each positive ε; the source names the solution without spelling out this event scope |
| 3.5 `fbar` and its properties | SOURCE, provisional | one random function has the continuum identity, boundary value and Hölder property almost surely; uniform convergence is in probability |
| 3.6 `ψ : ℂ → ℝ`, Hölder on `closedBall z (r+s)` for some `s > 0` | EXCESS relative to printed domain | source states Hölder continuity only on the closed ball; the draft documents the analogous exit-cell issue (S2) |
| 3.6 `y ∈ ball z r` | SOURCE, provisional | Lean quantifies y outside the convergence-in-probability assertion, giving convergence for each deterministic y; it does not assert a single simultaneous almost-sure event |

In 3.5 (`Draft/Section3.lean:136–152`), `HasLaplacian` uses the positive and negative parts of `c₀ * ψ` as densities. Its definition requires local integrability, integrability of every test function against both measures, and the distributional equality (`HarmonicBalls/Defs/Laplacian.lean:67–75`). Agreement with the signed measure in source line 1254 requires the corresponding integrability and signed-density argument; this has not been established by unfolding alone. The convergence predicate uses outer probabilities, and no explicit measurability premise for `fbar` appears in the displayed statement. The checked `three_five_draft_reduction` concludes the exact Draft conditionally. Its producer (`Steps/Sec3/DiscreteDirichletProblem.lean:98–106`) additionally requires `HarmonicBalls.GreenPotentialHolderStmt`, six earlier paper statements, and the three separately stated limit, interior, and boundary steps; no unconditional proof or literature-status closure is claimed.

In 3.6 (`Draft/Section3.lean:161–171`), the walk exit position is evaluated at `(vExitTime A x).toNat`, which defaults to time zero on non-exit (`Defs/RandomWalk.lean:115–117`). The continuum exit position likewise uses `(pathExitTime U f).untopD 0` (`Defs/Setting.lean:221–224`); the rescaled path uses `m₀.toNNReal` (:208–211). Identifying these integrals with the source's exit positions requires the relevant almost-sure finiteness and time-change facts. The checked `three_six_draft_reduction` applies the producer conditionally on walk convergence, the cell-size estimate, and the two exit-comparison steps; it does not discharge those facts or settle S2.


## Lemma 3.7 binder and definition trace (provisional)

The corrected source at lines 1399–1412 fixes deterministic `z` and `r`, asks for uniform convergence in probability on the closed ball, and characterizes the limit by the zero-boundary Dirichlet problem with Laplacian `-(c₀/6) μ_h` [C1]. The Lean proposition is `ConvergenceNormalizedExitTimeStmt` (`Draft/Section3.lean:177–188`).

| Lean input or local binder | Provisional bin | Comparison |
| --- | --- | --- |
| `𝒮`, `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | model and measurable environment carriers; representation semantics remain open |
| `γ`, `0 < γ`, `γ < 2`, `ρ`, `0 < ρ`, `ρ < 1` | STANDING | paper's quantum-cone setting and fixed radius |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | packaged coupling and mathematical inputs; E-m1-5 |
| `r`, `z`, `0 < r`, `ball z r ⊆ ball 0 ρ` | SOURCE | deterministic choices in source 1400 |
| `qbar : Ω → ℂ → ℝ` | SOURCE, provisional | one random limit is chosen for fixed `r,z` and satisfies its Dirichlet conditions almost surely; no explicit measurability field is imposed |
| `ContinuousOn`, `HasLaplacian`, zero sphere values | SOURCE, provisional | continuity selects a boundary-valued solution; full identification with the paper's solution and uniqueness require semantic closure |
| convergence on `closedBall z r` | SOURCE, provisional | convergence in probability with outer failure probabilities; this is neither pointwise convergence nor almost-sure uniform convergence |

The paper's normalized exit time is the sum of `G(a,b)/deg(b)` over the killed-domain vertices (source:773–775). Lean implements that sum as a subtype `tsum` (`Defs/RandomWalk.lean:98–100,111–113`), where the Green function is the real value of an extended nonnegative visit expectation (:88–96). The real-valued conventions return zero on an infinite expectation, and real division returns zero at degree zero; identifying the expression with the source requires the valid-environment finiteness and positive-degree conditions. On finite killed domains, `sum_visitsBeforeExit_mul_eq_occupation` (`Proofs/Sec3/IntegralConvergenceGreenFunction/OccupationGreen.lean:53–59`) relates weighted visits to the path occupation sum when exit is finite; `integrable_visitsBeforeExit_of_expectedExitTime_ne_top` (:119) supplies visit integrability from finite mean exit. These conditional lemmas do not by themselves prove all required environment assumptions.

The negative measure in the displayed `HasLaplacian` is `ENNReal.ofReal (S.c₀ / 6) • S.μ ω`. `MatedCRTEnv.c₀_nonneg` (`Proofs/Sec3/ConvergenceNormalizedExitTime/PotentialBoundary.lean:11`) proves this scalar is nonnegative, so `ofReal` does not truncate a negative coefficient; strict positivity of the median is separately derived as described below. The producer of `NormalizedExitPotentialStep` (`PotentialIdentification.lean:12–19,29–37,73–79`) conditionally derives continuity, the distributional identity, and the zero boundary condition for the Green potential from `BoundedExitTimeRVStmt` and `S.IsValid`. This is a checked producer trace, not a proof that its inputs are source-free or that the full 3.7 statement is unconditional.

The exact Draft reduction (`OfInteriorBoundary.lean:10–18`; checked as `three_seven_draft_reduction`) still assumes the Draft 3.1, six other paper propositions, `NormalizedExitInteriorStep`, and `DiscreteExitBoundaryStep`. The separate almost-sure corrected tightness formulation records the issue applying pointwise bounds to environment-measurable functions (`Steps/Sec3/ConvergenceNormalizedExitTime.lean:52–58`, E-c2-6); it is not substituted into this displayed producer. Existing E-m1-3 and E-m1-4 record the independent coefficient, sign, and center discrepancies in the source proof.


## Exit-time and Green-sum assumptions: further trace

For admissible γ and a valid environment, `MatedCRTEnv.IsValid.ae_normalizedLBMExitTime_any_ball_lt_top` (`Proofs/LBM/BrownianExitBall.lean:129–139`) gives, for each fixed starting point and ball, almost-sure finiteness first in the environment and then in the quenched Brownian law. It derives `0 < S.m₀` from `matedCRTScalingConstantPositive` (`Proofs/Sec4/ConvergenceDivisible/ExitCDF.lean:205–210`) and applies preservation of finite exit under the positive time rescaling (`BrownianExitBall.lean:101–125`). Thus, under these explicit conditions, the continuum `untopD 0` default in the 3.6 trace is absent almost surely. This does not by itself establish convergence of the exit-position integrals or identify the annealed and conditional laws.

For the discrete domain, the proof `ae_normExitTime_laplacian_le_one` (`Proofs/Sec3/ConvergenceNormalizedExitTime/ExitLaplacianBound.lean:24–42`) obtains, on one almost-sure event, finiteness of the killed-domain vertex set for every positive mesh and bounded domain, from continuity and properness of the curve. On that event local finiteness and the deterministic consecutive-edge property give positive degree for every vertex; `KernelIntegralSubsequence.lean:38–51` exhibits this degree argument explicitly. The local-finiteness producer uses `adjacentCellsMeetAeStep`; its proof consumes the `matingOfTrees` bundle, including `boundaryLawBM` and `merge` (`Proofs/MatingOfTrees/AdjacentCells.lean:17–22`), so E-m1-5 remains material.

For a finite killed set on a locally finite multigraph with consecutive edges, `mLaplacian_greenFn` proves finiteness of each visit-count expectation as an internal fact `hfin` (`Proofs/WalkPotential/GreenFirstStep.lean:210–224`) before deriving the Green equation. This establishes that the `toReal` convention in `greenFn` does not discard an infinite visit expectation under those graph assumptions, for every pair of vertices. Its proof uses a finite-domain nonnegative Poisson solution. The finite domain and positive-degree facts above therefore resolve the corresponding conventions on that almost-sure graph event, subject to the source status of the bundled inputs; they do not alone establish finite expected exit time as a separate exported proposition. The finite-mean hypothesis does imply almost-sure finite exit and visit integrability (`OccupationGreen.lean:119–155`), and the explicit-bound statement supplies finite mean only on its stated high-probability events (`Draft/Section2.lean:260–267`), not as an unrestricted assertion for every environment and mesh.


## Lemma 3.4 binder and reduction trace (provisional)

The corrected statement is at source lines 1124–1133 and the Draft is `IntegralConvergenceGreenFunctionStmt` (`Draft/Section3.lean:113–123`).

| Lean input or local binder | Provisional bin | Comparison |
| --- | --- | --- |
| `𝒮`, `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | model and measurable environment carriers; representation semantics remain open |
| `γ`, `0 < γ`, `γ < 2`, `ρ`, `0 < ρ`, `ρ < 1` | STANDING | paper's quantum-cone setting and fixed radius |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | packaged coupling and mathematical inputs; E-m1-5 |
| `r`, `z`, `y`, `0 < r`, `ball z r ⊆ ball 0 ρ`, `y ∈ ball z r` | SOURCE | fixed deterministic parameters |
| `f : Ω → ℂ → ℝ`, pointwise `envSigma`-measurability | SOURCE, provisional | source calls f environment-measurable; equivalence of this pointwise formulation with the intended random-function measurability is not established |
| pointwise-in-ω boundedness and Hölder continuity on the ball | SOURCE, provisional | source says bounded and Hölder; pathwise conditions are stronger than an a.s. reading, though modification on a null set might be possible with the required measurability |
| conclusion `TendstoInProbability` | SOURCE, provisional | `Defs/Notation.lean:64–67` uses the outer measure of strict-error events; no measurability is required in the predicate itself |

The source test function is defined on the open ball, but the displayed discrete sum evaluates marked points of all cells meeting it. The checked theorem `three_four_sum_ext` (`Audit/StatementsSec3Sec5M1.lean:102–113`) proves equality of sums for global representatives agreeing on the ball, assuming positive mesh and a continuous curve. This does not prove that all source random functions admit global representatives with Lean's pointwise measurability, nor integrability of the continuum Green product. The Green convention and finite visit expectation are treated above.

No producer of the full Draft is listed in `REDUCTIONS.md`. The partial theorem `integralConvergenceGreenFunction_of_fixed_and_ae_continuum` (`Proofs/Sec3/IntegralConvergenceGreenFunction/ContinuumTailAssembly.lean:31–54`) proves the exact fixed-parameter convergence after assuming fixed-time occupation convergence, measurability and almost-sure continuum occupation convergence, besides `BoundedExitTimeRVStmt`, `ExitTimeUpperBoundStmt 𝒮` and the explicit literature input `MepsScalingInput 𝒮` (`External/SLE.lean:61–66`). It does not prove those inputs or the universal Draft proposition on its own.

The source proof line 1138 says ε tends to infinity, then restricts to an event on which high-probability estimates hold for all sufficiently small ε. The direction conflicts with the statement's ε → 0, and probability tending to one alone does not imply eventual validity on one common event across all small ε. See E-m1-6; a subsequence or an additional uniform estimate may repair the argument, but is not asserted here.

## Updated 3.1 refutation and 3.7 final reduction

`three_one_draft_refuted` applies `Audit.Refutations.not_discretePotentialTightnessStmt` to the exact Draft, with `MepsScalingInput`, a valid environment and `0 < γ < 2`. The cited proof uses a closed segment, whose interior is empty, and a discontinuous step profile; the theorem refutes the Draft conditional on those assumptions. This warrants **WRONG** for that Lean statement under its standing setting, not an unconditional claim of existence of the setting. The corresponding source allows connected sets (source:976–999), but independently transferring the counterexample to every source convention remains to be checked.

`three_seven_latest_reduction` applies `convergenceNormalizedExitTime_of_statements` (`Proofs/Sec3/ConvergenceNormalizedExitTime/DyadicModulus.lean:159`). It concludes the exact Draft from 3.3, 3.5, 2.17, 2.18 and `DiscretePotentialTightnessAeStep`. The earlier `three_seven_draft_reduction` remains a check of a valid older conditional theorem; its use of false Draft 3.1 does not describe the latest reduction. The a.s. tightness step is still open and its equivalence to the source remains unaudited.

## Lemma 3.2 after [C6]

The current corrected source hash is `5e15864c8a423fc81b1a4b8d18a360b2deb5675c9fa5faa1b2c0f0e6e857b9c0` and current Section3 Draft hash is `4e1b1423ad5bf2d1d9691ff7638454ae1193331b67da031a40f40ad9abc50581`. These observations are not an approved freeze. [C6] is adopted per `ESCALATIONS.md` E-chk-1 and `AUDIT-L32-USES.md`. In the corrected step, `∀ χ C′, ... ∃ ξ′ C` is weaker than the Draft/source `∀ χ, ... ∃ ξ′, ... ∀ C′, ... ∃ C`; it also drops `ξ′ ≤ χ`. `discreteHolderContinuityCorrected_of_draft` checks the implication, but does not establish the reverse. The older `CORRECTED-FORMS.md` 3.2 entry refers to the prior Draft and must not be used as the current comparison. This is a syntactic scope analysis, not a counterexample to either current mathematical estimate.

The 3.3 reduction changed in commit `763b7d7`: the checked `three_three_draft_reduction` now requires `DiscretePotentialTightnessAeStep`, not the false Draft 3.1. The final producer `uniformConvergenceGreenKernel_final` discharges its interior, boundary and maximum principle inputs, retaining the a.s. step and four numbered statements. `REDUCTIONS.md` F7 and its 3.3 line still describe the older producer.
