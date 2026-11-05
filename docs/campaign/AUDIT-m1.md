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
| 3.1 | **MISMATCH**, documented: source 976–999 allows connected sets; Draft/Section3.lean:42 adds pointwise environment measurability of `u` (S6). Corrected form Steps/Sec3/DiscretePotentialTightness.lean:102 adds open `D` and deterministic polynomially summable scales and changes boundary data to `C'/ε` times the Hölder modulus. Its interior part is weaker but its boundary implication is stronger. The source and Draft both use the corrected absolute bound [C3]. A non-open counterexample is argued at Steps/Sec3/DiscretePotentialTightness.lean:13–18, not verified here in Lean. | Only corrected form reduced; both imply a common restriction in Audit/CorrectedForms.lean:83, 93. The reduction is not a proof of the Draft. 3.3 and 3.7 still consume the Draft (REDUCTIONS F7). |
| 3.2 | **MISMATCH**, documented: source 1001–1017 and Draft/Section3.lean:76 use one exponent `ξ` independent of boundary exponent `χ`; corrected step at Steps/Sec3/DiscretePotentialTightness.lean:71 chooses `ξ'` after `χ`, restricts the first estimate to interior `a` and changes the floor from `ε` to `ε^β`. The draft's multiplication by boundary distance also requires care at zero distance. | Draft implies corrected step, checked in Audit/CorrectedForms.lean:114; reverse implication and proof of either not established. Literature ruling pending. |
| 3.3 | **INCOMPLETE**: source 1110–1122 and Draft/Section3.lean:97 have the same probability mode and `[C1]` coefficient `c₀/6`. `S.c₀ = 2/S.m₀` (Defs/Setting.lean:190). Source calls its Green function Brownian occupation Green, whereas the Lean symbol is normalized by `ΔG = -δ`; the factor-of-two convention must be checked together with [C1], not inferred from matching symbols. | Reduction `uniformConvergenceGreenKernel_of_steps` concludes Draft but assumes Draft 3.1 and open steps (REDUCTIONS 3.3). Existing [C1] proof slip E-m1-1 remains documented. |
| 3.4 | **INCOMPLETE**: source 1124–1133 and Draft/Section3.lean:113 use convergence in probability, `mε⁻¹`, `c₀`, and deterministic `z,r,y`; Lean quantifies over random pointwise measurable `f` with pathwise bounded/Hölder restrictions. Source `f` is defined on the ball but evaluates `f(η(x))` for cells meeting it. For positive ε and continuous η, `three_four_sum_ext` in the audit Lean file proves that the discrete sum depends only on values of `f` on the ball: interior-cell marked points lie in the ball, and the killed Green function vanishes outside the interior. This resolves the off-ball extension question for the sum, conditional on those hypotheses; remaining probabilistic and Green semantics still require audit. Green normalizations remain open as for 3.3. | REDUCTIONS records no committed reduction. |
| 3.5 | **MISMATCH**, documented: source 1240–1260 assumes `φ` Hölder on the closed ball, while Draft/Section3.lean:136 requires it on a larger closed ball (S2), potentially excluding source data. `[C1]` uses `c₀`. Lean quantifies over all discrete solutions satisfying the equations a.s. for each ε; the choice/uniqueness and signed Laplacian semantics require audit. | `discreteDirichletProblem_of_steps` concludes Draft and uses corrected 3.1 plus open steps; it does not establish the source statement without addressing S2. |
| 3.6 | **MISMATCH**, documented: source 1262–1280 assumes `ψ` Hölder on the closed ball; Draft/Section3.lean:161 requires Hölder regularity on a larger ball (S2). Lean takes each deterministic `y` separately, as does the probability convergence reading of the source. Exit-time and time-change semantics remain to check. | `convergenceHarmonicFunctions_of_steps` concludes Draft with two open steps. |
| 3.7 | **INCOMPLETE**: source 1399–1412 and Draft/Section3.lean:177 both state convergence in probability uniformly on the closed ball with `[C1]` coefficient `-c₀/6`. `HasLaplacian` and normalized exit-time definitions require full semantic audit. | `convergenceNormalizedExitTime_of_interior_discrete_boundary` concludes Draft, but assumes Draft 3.1 and open steps (REDUCTIONS F7). |
| 5.1 | **INCOMPLETE**: source 1971–1982 and Draft/Section5.lean:27 have both unrestricted and stopped clusters, failure on `{t<T}`, and the source stopping set `Vε(Λ_t)`. The outer annealed probability is a documented interpretation (S5), not a literal source correction; `IsConeHarmonicBallFamily`, the cluster and walk laws need closure audit. | `iDLALowerBound_of_volumeGrowth_cellSize` concludes Draft with open stopped-cluster and inner-approximation steps; no unconditional proof. |
| 5.2 | **INCOMPLETE**: source 1987–2002 and Draft/Section5.lean:47 include inclusion, origin, measurable connected domains, two Green estimates, and the stopped claim. Draft fixes `K : ℝ → ℝ` deterministic; source does not explicitly say deterministic, so this is a potentially narrower reading requiring a ruling. | Relaxed Step at Steps/Sec5/IDLALowerBound.lean:40 removes several hypotheses and implies Draft (`generalIDLALowerBound_of_relaxed`, :180); reduction from 2.7 and 2.8 is recorded in REDUCTIONS. This is conditional on those inputs. |
| 5.3 | **MISMATCH**: source 2008–2015 explicitly writes `𝔰 = 𝔰(δ)`, while Draft/Section5.lean:67 quantifies `∀ δ t, ... ∃ s`, allowing `s` to depend on `t`. The source wording may be a notational omission; ruling requested in E-m1-2. [C4] is represented by `frontier (fillCells ...)`. | `meanValueInequality_of_surplus` concludes the Draft and assumes an open surplus step and other inputs; it does not establish uniformity of `s` in `t`. |
| 5.4 | **INCOMPLETE**: source 2019–2026 chooses deterministic `q` before `δ,t`; Draft/Section5.lean:85 also chooses `q` before environment, `Λ`, `δ,t`, potentially imposing greater uniformity over representations than the source specifies. [C4] uses the cell union. Real division and real `tsum` semantics at zero/infinity need checking. | `lLowerBound_of_inputs` concludes Draft using cited 2.15, 2.16, 2.9; conditional only. |

A checked logical witness for the 5.3 quantifier distinction is in
`MatedCRT/Audit/StatementsSec3Sec5M1.lean` (`time_dependent_witness_not_uniform`): it is an
abstract counterexample to exchanging quantifiers, not a counterexample to Lemma 5.3 itself.

Remaining for a passing audit: reconstruct every binder into SOURCE/STANDING/TYPING/RULED/EXCESS
with counts, pin exact source and declaration identities, recursively audit `IsValid`, Green,
rescaling, probabilities, stopping, harmonic-ball and Laplacian definitions, and verify every
reduction by exact term-level applications and axiom checks. No FAITHFUL verdict is assigned here.

## Source identity and Green normalization

SHA-256 at this review: corrected source `d42d5867a83da66f530c4407bf9e5bc423f04e5b9e2c5ba5567932c09ca106`; Draft Section3 `4541957faaba0cbe632cb7b6b8ee4f680258a38e97f339b7922d77487ad51649`; Draft Section5 `30554ab9e72ac1322f94320c9270695191cb5c9404b9e4023277fcdd2f84edf1`. These are observations, not an operator-approved freeze.

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

`clusterExitTime` is exactly the displayed supremum over positive times with `Λ_t ⊆ B_{ρ/3}` (`Defs/Setting.lean:244`, source:1596–1599), subject to real `sSup` semantics when that set is unbounded. `fillCells` is the indexed union in source:248 (`Defs/Map.lean:195`); `matedDiscreteCluster` unfolds to the obstacle cluster from source:1690 (`Defs/Sandpile.lean:87`). `TendsToOneOn` is outer `P({t < T} ∩ Eεᶜ) → 0` (`Defs/Notation.lean:39`). These are definition-body comparisons, not proofs of finiteness of the stopping time, measurability, the obstacle characterization, positivity of the Green denominator, or agreement of a real `tsum` with a finite sum. The last points remain part of semantic closure.
