# Sections 3 and 5: independent statement audit, work in progress

## Current verdict ledger, 2026-11-06

This is a fail-closed ledger, not a seal: `INCOMPLETE` is retained where the
record does not support any of the four requested definitive verdicts. The
freeze is not in force and the missing semantic checks are not presumed true.

| Result | Verdict | Decisive evidence or unresolved check |
| --- | --- | --- |
| 3.1 | WRONG | Conditional Lean refutation `Audit/Refutations.lean:317`, under its explicit scaling and valid-environment hypotheses; closed-segment source interpretation remains a question. |
| 3.2 | DIVERGES-DOCUMENTED | The approved [C6] boundary form allows the exponent to depend on `C'`; Draft requires it beforehand and also requires `ξ' ≤ χ` (see below). The checked-in source at 1008 still states the stronger quantifier order. |
| 3.3 | INCOMPLETE | Brownian occupation versus Laplacian Green normalization remains unchecked; see the Green trace below. |
| 3.4 | INCOMPLETE | Off-ball extension is resolved under the stated conditions, but Green normalization and probabilistic semantics remain open. |
| 3.5 | MISMATCH | Draft requires Hölder data on a larger closed ball than the source (S2). |
| 3.6 | MISMATCH | Draft requires Hölder data on a larger closed ball than the source (S2). |
| 3.7 | INCOMPLETE | `HasLaplacian` and normalized exit-time semantic closure remain open. |
| 5.1 | INCOMPLETE | The ball-family and cluster/walk semantics remain unaudited; stopped-cluster proof gap E-c1-5 is separate from statement fidelity. |
| 5.2 | INCOMPLETE | Draft makes `K` deterministic; the source's intended quantifier needs interpretation. |
| 5.3 | MISMATCH | Draft allows `s` to depend on `t`, unlike source `s(δ)`; see E-m1-2. |
| 5.4 | INCOMPLETE | Uniformity over environments and real division/`tsum` semantics remain unchecked. |

Counts: 0 FAITHFUL, 1 DIVERGES-DOCUMENTED, 3 MISMATCH, 1 conditional WRONG,
6 INCOMPLETE. In particular, the operator's approval of the [C6] dependence
does not itself rewrite the stronger statement in the checked-in TeX or Draft.

### Operator ruling: E-m1-5

On 2026-11-06 the operator accepted the literature facts in
`IsMatingOfTreesCoupling` as frozen phase-2 cited input. Its individual fields
are `isProbabilityMeasure`, `gff`, `gff₀`, `bm_B`, `bm_B'`, `bm_B₀`,
`bm_B₀'`, `indep_cone`, `indep_cone₀`, `igField`, `indep_curve`,
`measurable_curves`, `igMap`, `spaceFilling`, `areaParam`, `areaParam₀`,
`segmentsContainBalls`, `coverage`, `cellMoments`, `boundaryLawBM`,
`boundaryLength`, `merge`, `onlyMerge`, and `visitBound`; see
`LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/IsMatingOfTreesCoupling.lean:61`.
Earlier references to E-m1-5 as unresolved predate this ruling; the ruling
does not settle unrelated carrier, normalization, or quantifier questions.

### E-m1-8: valid-locus characterization

`MatedCRTEnv.IsValid.measurable_walkerSequenceLaw` and
`MatedCRTEnv.IsValid.idlaJointMeasure_eq` in
`MatedCRT/Proofs/IDLA/WalkerLawMeasurable.lean:38` establish measurability and
identify the joint measure with the kernel composition. The new
`MatedCRTEnv.IsValid.jointOuterProb_eq_idlaJointLaw` in
`MatedCRT/Proofs/Defs/JointMeasureCharacterization.lean:11` identifies the
generic joint outer probability with the same measure on every set, not just
measurable sets. Thus the zero fallback is unreachable whenever `S.IsValid`;
the unrestricted total definitions still retain their off-valid-locus fallback.

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
| 3.2 | **DIVERGES-DOCUMENTED**: correction [C6] now gives the interior floor `ε^β`, restricts `a` to the interior, and chooses `ξ′` after `χ` and before `C′` (source 1001–1017; Draft/Section3.lean:76). The Draft reflects this order and the requirement `ξ′ ≤ χ`. The positive-distance and quotient checks below address the multiplied-distance form. | `DiscreteHolderContinuityCorrectedStep` (:71) allows `ξ′` to depend on `C′` and omits `ξ′ ≤ χ`, hence is weaker. Draft implies the step (`Audit/CorrectedForms.lean:114`), with no reverse implication established. Both are cited hypotheses, not proofs. The 3.2 entry in CORRECTED-FORMS.md predates C6 and describes the superseded Draft. |
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
| `s : Ω → ℝ`, environment measurability and `∀ ω, 0 < s ω` | SOURCE, provisional | real-valued encodes finiteness; pointwise positivity is stronger than an a.s. reading. The null-set modification below resolves the basic measurable-version issue, but the full transfer of the probability statement remains unchecked |
| probability tending to one of both Green estimates | SOURCE, provisional | outer probability of failure via `ProbTendsToOne`; denominator and real `tsum` need valid finite-domain justification |
| both unrestricted and stopped inclusions | SOURCE, provisional | annealed outer probability and the conditional walk law need closure audit |

`GeneralIDLALowerBoundRelaxedStep` (`Steps/Sec5/IDLALowerBound.lean:40`) removes set measurability, connectedness, origin membership and positivity of `K` while preserving deterministic `K`, positive q and pointwise-positive measurable s. The checked `relaxed_five_two_implies_draft` in the audit Lean file applies the producer explicitly; it establishes a conditional implication only. `walkerSequenceLaw` is `Measure.infinitePi` of `srwLaw` (`Defs/RandomWalk.lean:153`), and `idlaProb` now evaluates the joint measure (`Defs/Setting.lean:216`). See the joint-law update below; the previous sectionwise outer-integral description is superseded by commit a12c8bf.

The checked `five_two_positive_surplus_version` constructs an everywhere positive function equal almost everywhere to any almost-surely positive real function, while preserving measurability with respect to an arbitrary specified sigma algebra, which can be `S.envSigma`. The separate checked `five_two_probTendsToOne_congr` shows that uniformly almost-sure changes to the events preserve the Draft's outer-probability convergence. Together these supply the null-set modification and the event-convergence transfer for the Green-estimate hypothesis. This does not discharge the hypotheses of the Draft or establish source fidelity for the full statement.

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

The checked `three_five_boundary_cell_marked_point` gives a continuous deterministic curve whose boundary cell has its marked point outside the closed ball at every positive mesh. `three_five_boundary_extensions_differ` constructs two global functions which agree and are Hölder on the closed ball but differ at that marked point. This confirms that the source's boundary data alone do not determine the displayed off-ball evaluation. The example is geometric and does not model a space-filling SLE, a random walk, or a failure of the limiting theorem; it does not decide which source repair is intended.

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

For a finite killed set on a locally finite multigraph with consecutive edges, `mLaplacian_greenFn` proves finiteness of each visit-count expectation as an internal fact `hfin` (`Proofs/WalkPotential/GreenFirstStep.lean:210–224`) before deriving the Green equation. The audit theorem `three_three_green_visit_integral_ne_top` exports that finiteness with those exact graph and domain hypotheses, using the same finite-domain nonnegative Poisson solution and truncated-visit bound. Thus `greenFn`'s `toReal` does not discard an infinite visit expectation under those assumptions, for every pair of vertices. The finite domain and positive-degree facts above therefore resolve the corresponding conventions on that almost-sure graph event, subject to the source status of the bundled inputs; the audit theorem `finite_expectedExitTime` also establishes finite expected exit time under the same hypotheses by summing the finite visit expectations over the finite domain and identifying that sum pathwise with the exit time. Finite mean implies almost-sure finite exit and visit integrability (`OccupationGreen.lean:119–155`), and the explicit-bound statement supplies finite mean only on its stated high-probability events (`Draft/Section2.lean:260–267`), not as an unrestricted assertion for every environment and mesh.


## Lemma 3.3 binder and reduction trace (provisional)

The corrected source statement is at lines 1110–1122; the exact Draft declaration is `UniformConvergenceGreenKernelStmt` (`Draft/Section3.lean:97–105`). No versioned source/declaration manifest is in force, so these bins do not constitute approval.

| Lean input or local binder | Provisional bin | Comparison |
| --- | --- | --- |
| `𝒮`, `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | abstract model and measurable environment carriers |
| `γ`, `0 < γ`, `γ < 2`, `ρ`, `0 < ρ`, `ρ < 1` | STANDING | quantum-cone parameters and fixed Section 3 ball |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | bundled coupling and mathematical inputs; E-m1-5 |
| `r`, `z`, `y`, `0 < r`, `ball z r ⊆ ball 0 ρ`, `y ∈ ball z r` | SOURCE | deterministic ball and pole |
| `δ > 0`, `O ⊆ closedBall z r \ {y}`, `0 < infDist y O` | SOURCE, with empty-set caveat | the source says small positive δ and positive distance; quantification over every δ is equivalent for a monotone error bound, while Mathlib's real `infDist y ∅ = 0` excludes the empty set |
| `ProbTendsToOne` of a pointwise `∀ x ∈ O` error bound | SOURCE, provisional | source displays a supremum bound with probability tending to one; the Lean predicate uses outer measure of failure |

The checked `three_three_empty_test_set` proves the omitted empty-set bound is vacuous and has probability tending to one, including for an arbitrary measure; this does not settle the nonempty-set supremum or continuum Green-function semantics. `rescale` is `mε⁻¹ * u (vertexOf ε η x)` (`Defs/Map.lean:200`), and `greenKernel` divides `greenFn` by the degree at the second argument (`Defs/RandomWalk.lean:95–100`). The preceding finite-visit and positive-degree checks address the totalized real operations on the stated graph event. `three_three_vertexOf_is_least` checks its cell-covering and least-scaled-index properties almost surely in a valid environment, simultaneously for every point and positive mesh; its off-valid-locus totalization remains unaudited. [C1] Green normalization remains open as recorded above.

The checked `three_three_final_reduction` applies `uniformConvergenceGreenKernel_final` (`Proofs/Sec3/UniformConvergenceGreenKernel/InteriorStep.lean:73`) to the exact Draft. It retains 2.10, 3.4, 2.14, 2.8 and `DiscretePotentialTightnessAeStep` as hypotheses; it does not prove them. This supersedes the older reduction listed in `REDUCTIONS.md` for the current dependency audit.

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

The source test function is defined on the open ball, but the displayed discrete sum evaluates marked points of all cells meeting it. `three_four_measurable_extension` proves that a random function on any domain whose individual evaluations are measurable has a global representative with the same pointwise measurability and the same values on the domain. Thus its restrictions retain the original boundedness and Hölder properties. `three_four_sum_ext` proves equality of discrete sums for global representatives agreeing on the ball, assuming positive mesh and a continuous curve. These results do not establish that the source's random-function measurability implies measurability of every evaluation, or integrability of the continuum Green product. The Green convention and finite visit expectation are treated above.

No producer of the full Draft is listed in `REDUCTIONS.md`. The partial theorem `integralConvergenceGreenFunction_of_fixed_and_ae_continuum` (`Proofs/Sec3/IntegralConvergenceGreenFunction/ContinuumTailAssembly.lean:31–54`) proves the exact fixed-parameter convergence after assuming fixed-time occupation convergence, measurability and almost-sure continuum occupation convergence, besides `BoundedExitTimeRVStmt`, `ExitTimeUpperBoundStmt 𝒮` and the explicit literature input `MepsScalingInput 𝒮` (`External/SLE.lean:61–66`). It does not prove those inputs or the universal Draft proposition on its own.

The source proof line 1138 says ε tends to infinity, then restricts to an event on which high-probability estimates hold for all sufficiently small ε. The direction conflicts with the statement's ε → 0, and probability tending to one alone does not imply eventual validity on one common event across all small ε. See E-m1-6; a subsequence or an additional uniform estimate may repair the argument, but is not asserted here.

## Updated 3.1 refutation and 3.7 final reduction

`three_one_draft_refuted` applies `Audit.Refutations.not_discretePotentialTightnessStmt` to the exact Draft, with `MepsScalingInput`, a valid environment and `0 < γ < 2`. The cited proof uses a closed segment, whose interior is empty, and a discontinuous step profile; the theorem refutes the Draft conditional on those assumptions. This warrants **WRONG** for that Lean statement under its standing setting, not an unconditional claim of existence of the setting. The corresponding source allows connected sets (source:976–999), but independently transferring the counterexample to every source convention remains to be checked.

`three_seven_latest_reduction` applies `convergenceNormalizedExitTime_of_statements` (`Proofs/Sec3/ConvergenceNormalizedExitTime/DyadicModulus.lean:159`). It concludes the exact Draft from 3.3, 3.5, 2.17, 2.18 and `DiscretePotentialTightnessAeStep`. The earlier `three_seven_draft_reduction` remains a check of a valid older conditional theorem; its use of false Draft 3.1 does not describe the latest reduction. The a.s. tightness step is still open and its equivalence to the source remains unaudited.

## Lemma 3.2 after [C6]

The current corrected source hash is `5e15864c8a423fc81b1a4b8d18a360b2deb5675c9fa5faa1b2c0f0e6e857b9c0` and current Section3 Draft hash is `4e1b1423ad5bf2d1d9691ff7638454ae1193331b67da031a40f40ad9abc50581`. These observations are not an approved freeze. [C6] is adopted per `ESCALATIONS.md` E-chk-1 and `AUDIT-L32-USES.md`. In the corrected step, `∀ χ C′, ... ∃ ξ′ C` is weaker than the Draft/source `∀ χ, ... ∃ ξ′, ... ∀ C′, ... ∃ C`; it also drops `ξ′ ≤ χ`. `discreteHolderContinuityCorrected_of_draft` checks the implication, but does not establish the reverse. The older `CORRECTED-FORMS.md` 3.2 entry refers to the prior Draft and must not be used as the current comparison. This is a syntactic scope analysis, not a counterexample to either current mathematical estimate.

`three_two_interior_distance_pos` checks that the marked point of an interior cell has positive distance to the frontier of a proper domain, for nonnegative mesh. An interior cell makes the domain nonempty; connectedness of the complex plane makes the frontier nonempty; and the marked point belongs to the cell, which does not meet the frontier. Domains contained in the bounded ball of the statement are proper. `three_two_holder_quotient_iff` checks the algebraic equivalence of the Draft's multiplied inequality and the source quotient when the numerator is nonnegative and the distance is positive. This check concerns the denominator, not the other semantic obligations of the lemma.

The 3.3 reduction changed in commit `763b7d7`: the checked `three_three_draft_reduction` now requires `DiscretePotentialTightnessAeStep`, not the false Draft 3.1. The final producer `uniformConvergenceGreenKernel_final` discharges its interior, boundary and maximum principle inputs, retaining the a.s. step and four numbered statements. `REDUCTIONS.md` F7 and its 3.3 line still describe the older producer.

## Proposition 5.1: binder and semantic trace (provisional)

The following rows enumerate the outer inputs of `IDLALowerBoundStmt` (`Draft/Section5.lean:27–38`). The bins for the environment and family are provisional: expanding a bundle into fields does not by itself validate those fields as standing assumptions. The SOURCE count refers to the five named parameter/inequality rows, not the family fields.

| Binder or expanded input | Bin | Source or remaining check |
| --- | --- | --- |
| `𝒮` | TYPING | Abstract SLE model; the model's adequacy is E-A1. |
| `γ`, `0 < γ`, `γ < 2` | STANDING | Section 1 fixes `γ ∈ (0,2)`. |
| `ρ`, `0 < ρ`, `ρ < 1` | STANDING | Section 5 introduction, source:1967. |
| `Ω`, `[MeasurableSpace Ω]`, `S` | TYPING | Carrier, measurable structure, and environment representation. |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | Seven fields shown in the 5.3 inventory; mating-of-trees package has unresolved E-m1-5. |
| `Λ` | TYPING | Representation of the source's family from Theorem 2.3. |
| family a.s.: each `IsHarmonicBall` | STANDING, provisional | Theorem 2.3 calls each a harmonic ball; HB `Defs/HarmonicBall.lean:79` expands this to openness, origin, positive finite mass, and the harmonic mean-value property. |
| family a.s.: mass `t`, null boundary, regular open | STANDING, provisional | HB `Draft/Section1.lean:58`, source:514. |
| family a.s.: boundedness, connectedness, origin, monotonicity, Hausdorff continuity, intersection | STANDING, provisional | HB `Draft/Section1.lean:58`, source:515. |
| family a.s.: obstacle identity, continuity, Laplacian and boundary zero | STANDING, provisional | `Defs/Setting.lean:231`, source:516–526; full characterization and uniqueness remain unaudited. |
| `δ`, `t`, `0 < δ`, `δ < ρ`, `0 < t` | SOURCE | Proposition 5.1, source:1973. |

At this nonrecursive level there are 5 SOURCE, 10 provisional STANDING, 5 TYPING and 1 UNCLASSIFIED input rows, counting grouped entries by the individual variables or inequalities in each row, but each grouped family condition as one row. No RULED or EXCESS input is yet verified; unclassified bundled inputs prevent a passing count. The proof does not introduce an explicit `Λ`-measurability premise; the conclusion uses outer probabilities. The source chooses its family through the unique a.s. theorem, whereas Lean universally quantifies over a family satisfying the a.s. predicate; whether all such representations have the required measurable and uniqueness properties remains open.

The two clauses have precisely the same `δ,t` and event `t < clusterExitTime`; `innerNbhd` (`Defs/Notation.lean:29`) uses extended distance to the complement, corresponding to source:238–243 when that distance convention agrees. `fillCells` and `cellVertices` (`Defs/Map.lean:187–196`) match the displayed union and stopping set. `idlaProb` (`Defs/Setting.lean:216`) now evaluates the joint measure built from the independent quenched walk law; see the joint-law update below for the valid-setting characterization and the totalization issue. `idlaStep` (`Defs/RandomWalk.lean:130`) leaves the state unchanged when a path never exits the occupied set; proving this fallback has zero probability for all finitely many walkers under the setting is still required for full source semantics. This is an unresolved obligation, not an asserted counterexample.

The strict-gap final producer `iDLALowerBound_final_of_strictGap` (`Proofs/Sec5/IDLALowerBound/Final.lean:48`) returns the exact Draft, including both stopped and unrestricted clauses. The explicit application `five_one_strict_gap_reduction` in the audit module checks its complete listed hypotheses; in particular it still takes the stopped mean-value and quotient inputs, and the strict obstacle-gap and surplus inputs. It is a conditional reduction, not an unconditional proof or closure of E-c1-5.

## Updated IDLA joint-law trace (commit a12c8bf)

`idlaProb` now evaluates `idlaJointMeasure` (`Defs/Setting.lean:193–198,216`), rather than the sectionwise outer integral. For `hS : S.IsValid 𝒮 γ`, `hS.measurable_walkerSequenceLaw` (`Proofs/IDLA/WalkerLawMeasurable.lean:38`) proves measurability for every mesh and start; `hS.idlaJointMeasure_eq` (:69) identifies the totalized measure with `hS.idlaJointLaw`, the measure/kernel composition of the environment law and the independent walker law. `five_one_idla_joint_law` checks this identity on arbitrary events. For measurable events `idlaJointLaw_apply` (:78) identifies it with the integral of the section probabilities. No equality of the joint outer measure and the sectionwise outer integral on arbitrary nonmeasurable events follows from this result.

The public definitions `idlaJointMeasure` and generic `jointOuterProb` (`Defs/Notation.lean:57`) return the zero measure when the kernel is nonmeasurable. That off-valid-locus fallback fails the definition audit's public-carrier/default-branch criterion (E-m1-8); `idlaJointMeasure_eq` proves the fallback is not taken under `S.IsValid`, but does not make the exported total definition source-characterized on its entire carrier. This is a definition-surface finding, not a counterexample to 5.1 under its stated validity premise. The `IsValid` coupling fields used to establish measurability still require their own source audit (E-m1-5).

`five_one_fixed_set_exits` now checks the fixed-set part of the nonexit issue: if `expectedExitTime m A a ≠ ⊤`, then a walk under `srwLaw m a` has a first exit site almost surely. It applies `ae_vExitTime_ne_top_of_expectedExitTime_ne_top` (`OccupationGreen.lean:135`) to the definition of `firstExitSite`. `five_one_finite_set_exits` now discharges the finite-mean premise for every fixed finite set on a locally finite multigraph with consecutive edges, using `finite_expectedExitTime`. `five_one_all_finite_sets_exit` strengthens this to simultaneous exit from every finite set for one walk, using countability of finite subsets of ℤ. `five_one_all_walkers_exit_finite_sets` uses the finite-dimensional marginals of `walkerSequenceLaw` to obtain the property simultaneously for all walkers. Finally, `five_one_current_aggregates_exit` applies it to both the unrestricted and stopped current aggregates at every release, using `foldl_idlaStep_card` for finiteness. These quenched results hold for each fixed graph satisfying local finiteness and consecutive-edge assumptions. `five_one_measurable_all_walkers_exit` establishes measurability using countability; `five_one_joint_all_walkers_exit` transfers the result to the joint law for each positive mesh in a valid environment, using `ae_isLocallyFiniteMult` (with the proved `adjacentCellsMeetAeStep`) and `mult_succ_ne_zero`. `five_one_joint_current_aggregates_exit` then covers all releases of both the unrestricted aggregate and the aggregate stopped in an arbitrary environment-dependent set. This rules out the nonexit fallback almost surely in these IDLA processes; it does not establish the remaining source fidelity or the lower-bound proposition.

## Lemma 3.1 binder inventory and corrected-form scope

The following inventory is for the exact Draft `DiscretePotentialTightnessStmt`
(`Draft/Section3.lean:42`), compared with corrected source:977–999. Classification
of standing bundles remains provisional until `IsValid` is independently audited.
Each table row is one counted item, with grouped parameters/premises explicitly
identified as such; this is not a substitute for recursively auditing the bundles.

| Draft binder or premise | Bin | Source or finding |
| --- | --- | --- |
| `𝒮` | TYPING | Abstract representation of the SLE model; semantic adequacy remains open. |
| `γ` with `0 < γ`, `γ < 2` | STANDING | Paper's standing parameter regime. |
| `ρ` with `0 < ρ`, `ρ < 1` | STANDING | Section 3 setting, source:957. |
| `Ω`, measurable-space instance, `S` | TYPING | Representation of the probability environment. |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | Its seven fields include the mating-of-trees bundle; see E-m1-5. |
| `D`, `D ⊆ ball 0 ρ`, `IsConnected D` | SOURCE | source:977–978 says connected set; no openness premise. |
| `E`, its environment measurability, positivity, and pointwise convergence to zero | SOURCE, provisional | source:978; positivity and pointwise rather than a.s. requirements are explicit choices of versions, not automatically licensed by the source. |
| `u : Ω → ℕ → ℤ → ℝ` | TYPING | Total representatives of functions on random vertex sets; restriction to those vertices requires semantic verification. |
| pointwise environment measurability of every `u n a` | EXCESS relative to literal source | Source:979 only calls the scale sequence measurable; review-S (S6) adds this input for measurable choice, without a source correction. |
| `C`, environment measurability, positivity | SOURCE, provisional | source:986; Lean asks positivity at every ω, so an a.s.-version argument is still required if this is interpreted only a.s. |
| uniform absolute Laplacian and function bounds | RULED, provisional | source:981–985, [C3]; Lean requires them for every ω and n. The source's random-environment convention does not explicitly make the `∀ ω` scope clear. |

At this grouped outer level: SOURCE 2, STANDING 2, TYPING 3, RULED 1,
EXCESS 1, UNCLASSIFIED 1. These counts do not classify the internal fields
or the conclusion's quantified variables. The conclusion places a measurable
index map `Φ` outside the a.s. event; on that event it requires strict
monotonicity, a continuous limit, compact uniform convergence and, for the
same subsequence, the boundary upgrade. Its compact test is `IsCompact O` and
`closure O ⊆ D`. For non-open `D`, this admits `O = D` for a compact closed
segment, which is used in the conditional Lean refutation. The source's
notation `O ⋐ D` has an interior-containment convention ambiguity on non-open
sets; the Lean refutation therefore establishes the Draft error and does not
by itself settle every interpretation of the source.

The corrected `DiscretePotentialTightnessCorrectedStmt` adds `IsOpen D` and
`IsPolySummableScales e`; the latter expands to positive `e j` and summability
of `e j ^ p` for every `p > 0` (Steps/Sec3/DiscretePotentialTightness.lean:90).
It also restricts every random mesh to `range e` and replaces the boundary
modulus constant `C'` by `C'/ε`. These changes affect different directions of
the implication, so the checked common restriction is not a proof of the
Draft. The a.s. interior-only `DiscretePotentialTightnessAeStep` has different
hypothesis and conclusion scope again; its use in 3.3 and 3.7 is conditional.

For 3.2, `three_two_constant_dependent_exponent_not_uniform` checks an abstract
positive-real predicate for which `∀ C > 0, ∃ ξ > 0` holds but `∃ ξ > 0,
∀ C > 0` fails. It demonstrates that the corresponding exchange of quantifiers
needs mathematical justification. It is not a counterexample to either
Hölder statement, and the example does not establish non-implication between
the actual two propositions.


## Grouped binder inventory for Lemma 3.2

This is a preliminary outer-binder inventory, not a freeze or a recursive
audit of `IsValid`. Each row counts one group. Source: corrected paper
1001–1017; Draft/Section3.lean:76.

| Draft binder or premise | Bin | Source or finding |
| --- | --- | --- |
| `𝒮` | TYPING | Abstract SLE model; semantic adequacy remains open. |
| `γ`, `0 < γ`, `γ < 2` | STANDING | Standing parameter regime. |
| `ρ`, `0 < ρ`, `ρ < 1` | STANDING | Section 3 setting, source:957. |
| `ξ`, `A`, `β` and their positivity/range constraints | SOURCE | Existential conclusion witnesses, depending on `ρ` and `γ`. |
| `χ`, `0 < χ`, `χ ≤ 1` | SOURCE | Boundary Hölder exponent. |
| `ξ′`, its range and `ξ′ ≤ χ` | SOURCE | Existential witness chosen after `χ` and before `C′`. |
| `C′`, `0 < C′` | SOURCE | Boundary Hölder constant. |
| `C`, `0 < C` | SOURCE | Existential witness chosen after `C′`. |
| `Ω`, measurable-space instance, `S` | TYPING | Probability environment representation. |
| `S.IsValid 𝒮 γ` | UNCLASSIFIED | Its seven fields include mating-of-trees assumptions; see E-m1-5. |
| `D`, containment in the ball, openness, connectedness | SOURCE | The paper specifies a connected domain; the usual domain convention includes openness. |
| `f` and discrete harmonicity on interior vertices | SOURCE, provisional | Total representative on `ℤ`, with harmonicity restricted to interior cell vertices; the cell definitions require semantic verification. |
| Simple connectedness and boundary Hölder estimate | SOURCE, provisional | Conditional inputs to the boundary estimate; the precise boundary-cell interpretation remains to be checked. |

Grouped counts: SOURCE 8, STANDING 2, TYPING 2, UNCLASSIFIED 1. These
counts do not classify the validity bundle's fields or the quantified vertices
inside either estimate. The constants are chosen before the environment in
Lean; this uniformity across all valid representations also depends on the
unresolved adequacy of `IsValid`.

After fixing the witnesses and parameters, the source states the interior and
boundary estimates on separate polynomially high probability events. The
Draft requests their conjunction on one event.
`three_two_poly_high_prob_conjunction` checks that the two formulations of
polynomial high probability are equivalent for arbitrary event families,
without assuming event measurability. This observation does not address the
different witness order in `DiscreteHolderContinuityCorrectedStep`, or the
remaining correspondence of the events' mathematical content.


## Lemma 3.2: vertex-set supremum

The source's supremum is over vertices whose cells meet `D` (source:1008),
and the Draft uses a real indexed supremum over the subtype `cellVertices`
(Draft/Section3.lean:84). Since real indexed suprema are total, their intended
finite nonempty interpretation needs justification.

The checked `three_two_bounded_domain_cell_vertices_finite` proves that, on
one almost-sure event under `S.IsValid`, every positive mesh and every domain
contained in the ball has finitely many cell vertices. It uses continuity and
properness of the space-filling curve and compactness of the closed ball.
`three_two_nonempty_domain_cell_vertices` proves on an almost-sure event that
every nonempty domain has a cell vertex at every positive mesh, using
surjectivity and `Tightness.mem_cell_vertexOf`. The Draft's `IsConnected D`
includes nonemptiness. Taking the intersection of these events gives the
finite nonempty index set needed for the usual supremum interpretation.
These checks use the validity bundle and do not independently audit its source
characterization or prove the Hölder estimate.

The checked `three_two_vertex_supremum_is_maximum` supplies the remaining
order-theoretic step: for any finite nonempty vertex set and any real-valued
function, the Draft's indexed supremum of absolute values equals an attained
value which bounds all the other values. Together with the two a.s. cell-set
checks above, this validates the finite-supremum convention on their common
event; it does not establish the source characterization of the validity bundle.


## Lemma 3.3: tolerance and supremum conventions

The source requires the error estimate for each sufficiently small positive
`δ` (source:1113); the Draft quantifies over every positive `δ`
(Draft/Section3.lean:101). `three_three_small_tolerances_suffice` proves this
extension for arbitrary error functions and test sets, assuming one positive
upper threshold for the small tolerances. It uses monotonicity of the event and
the existing `ProbTendsToOne.mono'`; no event measurability is assumed.

For a nonempty test set, `three_three_pointwise_bound_iff_supremum` proves
that the Draft's pointwise upper bound is equivalent to boundedness above of
the error range together with the corresponding real indexed supremum bound.
The pointwise bound itself supplies boundedness. This qualification matters:
Lean's real supremum is total, so a bare supremum inequality alone does not
characterize pointwise bounds without a boundedness premise. The previously
checked empty-set result handles the omitted empty test set. These are
order/probability-convention checks; they do not establish Green-function
normalization, source measurability, or the estimate itself.


## Lemma 3.3: least cell containing a point

The paper defines `a_x^ε` as the smallest element of `εℤ` whose cell
contains `x` (source:635–638); `vertexOf` takes the integer infimum of those
cell indices (Defs/Map.lean:182). `three_three_vertexOf_is_least` verifies on
one almost-sure event under `S.IsValid` that, for every `ε > 0` and every
point, the chosen cell contains the point and its scaled index is no larger
than that of any other containing cell. The proof uses curve continuity,
properness and surjectivity and finiteness of cells meeting a singleton. This
checks the least-choice interpretation on the valid locus; it neither audits
the validity bundle's source characterization nor the off-locus infimum.


## Lemma 3.3: positive distance from the pole

The source requires `O` to lie at positive distance from `y`
(source:1113); the Draft uses `0 < infDist y O`
(Draft/Section3.lean:101). `three_three_infDist_pos_iff_separated` proves
that this is exactly nonemptiness of `O` plus a uniform strictly positive
lower bound for `dist y x` over `x ∈ O`. The previously checked
`three_three_empty_test_set` covers the empty-set case, which the real
`infDist` convention excludes. `three_three_pole_not_mem_of_infDist_pos`
checks that positive infimum distance also excludes the pole, so that part of
the displayed set-difference premise is redundant under the distance premise.
These deterministic checks do not prove the Green-function convergence.


## Lemma 3.4: joint test-function measurability

`three_four_joint_measurable_on_ball` proves that the Draft's pointwise
environment measurability, together with its pathwise Hölder condition,
implies joint measurability of `(ω, x) ↦ f ω x` on the product of the
environment sigma-algebra and the Borel sigma-algebra of the ball. The result
uses Mathlib's `MeasureTheory.measurable_uncurry_of_continuous_of_measurable`
after restricting the spatial argument to the ball. It does not require the
probability measure or boundedness.

This checks joint measurability for the Draft hypotheses; it does not decide
whether the paper's phrase “σ(h, η)-measurable function” means measurability
into a particular function space, nor whether that reading is equivalent to
its evaluation-wise formulation. It also does not establish the integrability
or the convergence assertion.


## Lemma 3.4: pathwise test-function versions

`three_four_good_event_modification` proves that if the boundedness and
Hölder properties hold on an environment-measurable event `G`, then replacing
the test function by zero off `G` preserves pointwise environment
measurability and yields both properties for every environment. The modified
function agrees with the original at every spatial point on `G`. Thus, when
`G` additionally has probability one, the all-environments requirements can
be met by an almost-surely equal version. The theorem does not assert that
every almost-sure good event admits a full-probability environment-measurable
subset, or separately prove invariance of the convergence statement under
this modification.
