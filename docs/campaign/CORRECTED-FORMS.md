# CORRECTED-FORMS: corrected and relaxed statements proved in place of Draft statements

Worker A, 2026-11-04 (tree at de71d03). For each numbered result that a worker proved or reduced in a corrected or
relaxed form instead of its Draft statement, this file gives: the Draft Stmt, the corrected Prop (file:line, author),
the escalation, the exact logical relation, and whether the Draft is false as drafted. Every implication marked
"Lean" is checked in `MatedCRT/Audit/CorrectedForms.lean` (namespace `MatedCRT.Audit.CorrectedForms`), as a named
theorem or as an `example` restating a worker's theorem. Paths are relative to `MatedCRT/`. All corrected Props are
tracked at HEAD de71d03. (The runner has no per-path `git log`, so first commits are given only where a report or
escalation names them.)

Legend: **C ⇒ D**: the corrected form implies the Draft. **D ⇒ C**: the Draft implies the corrected form (the
correction weakens the result). **FALSE (Lean)**: refuted in Lean. **FALSE (argument)**: refuted by a written
argument only (escalation or review). **unproved**: no refutation known, and no proof of the Draft form.

## Summary

| Result | Draft Stmt | Corrected Prop | Relation | Draft status |
| --- | --- | --- | --- | --- |
| 3.1 | DiscretePotentialTightnessStmt | DiscretePotentialTightnessCorrectedStmt | neither; both ⇒ common part (Lean) | **FALSE (Lean)** (E-c1-4; Audit/Refutations) |
| 3.1 (a.s.) | (corrected 3.1, as used by 3.7) | DiscretePotentialTightnessAeStep | neither (Ae: a.s. hypotheses, interior conclusion) | open step (E-c2-6) |
| 3.2 | DiscreteHolderContinuityStmt | DiscreteHolderContinuityCorrectedStep | D ⇒ C (Lean) | FALSE (argument, review-L32 F1) |
| 4.4 | DiscreteLaplacianBoundStmt | DiscreteLaplacianBoundCorrectedStmt | D ⇒ C (Lean) | **FALSE (Lean)** |
| 4.5 | DiscreteConservationOfMassStmt | DiscreteConservationOfMassCorrectedStmt | D ⇒ C (Lean) | **FALSE (Lean)** |
| 5.1 (stopped part) | IDLALowerBoundStmt (2nd conjunct) | IDLALowerBoundStoppedStep ⇐ Stopped{MeanValueInequality,LLowerBound}Step | Step = consumed conjunct; steps = 5.3/5.4 on V^ε(Λ_t) | proof gap (E-c1-5); statement unchanged |
| 5.2 | GeneralIDLALowerBoundStmt | GeneralIDLALowerBoundRelaxedStep | C ⇒ D (Lean, c2) | true: reduced through C |
| 6.3 | AbelianIDLAStmt | AbelianIDLAAnyStartStep | C ⇒ D (Lean, c5); both proved | PROVED |
| 6.7 | ConstantOrderLowerBoundStmt | ConstantOrderLowerBoundLogStmt | D ⇒ C (Lean, c5) | unproved |
| 6.8 | ConstantOrderLowerBoundDivStmt | ConstantOrderLowerBoundDivLogStmt | D ⇒ C (Lean) | unproved |
| 6.9 | ChanceOfBeingAbsorbedStmt | ...LocalRateStmt; ...LogLossStmt | D ⇒ LocalRate ⇒ LogLoss (Lean, c5) | unproved |
| 7.2 | MassBoundOdometerStmt | MassBoundOdometerAboveScaleStmt | D ⇒ C (Lean) | FALSE (argument, E-c3-2) |
| 7.4 | CrudeUpperBoundStmt (already the corrected Λ-form) | (printed form: not in Lean) | Draft = correction (S4) | Draft reduced; printed form FALSE (argument, E-c3-1) |
| 7.1 | DivSandpileUpperBoundStmt (unchanged) | consumes corrected 7.2 and 6.8 (b) | rerouted (d17f14c) | Draft 7.1 reduced, no step |

Counts: **C ⇒ D: 2** (5.2, 6.3). **D ⇒ C: 7** (3.2, 4.4, 4.5, 6.7, 6.8, 6.9, 7.2), so in these cases the
correction weakens the result. **Neither: 2** (3.1, 3.1 a.s.). **False as drafted: 5.** Three are refuted in Lean
(3.1, 4.4, 4.5), and two by argument only (3.2, 7.2; their Lean refutations are planned in Audit/Refutations.lean).
The printed 7.4 is also false, but its Draft is already the corrected form. **Merely unproved: 3** (6.7, 6.8, 6.9).

Re-sync c1, 2026-11-05 (HEAD 00649b2 + af9fe69): corrected 4.4 and 4.5 are now PROVED with no hypothesis
(`discreteLaplacianBoundCorrected`, `discreteConservationOfMassCorrected`, Proofs/Sec4/ObstacleSpecialization/
Final.lean:33, 38; E-c1-2 resolved), so every consumer rerouted to them (5.3, 5.1, 7.2-7.4) no longer carries 4.4.
The consumers of the false Drafts are all rerouted in their final forms: 4.6 (`subsequentialConvergence_of_inputs`,
corrected 3.2, no Draft 3.1/4.4), 4.8 (`subsequentialProperties_of_inputs`, no Draft 4.4), 3.7
(`convergenceNormalizedExitTime_of_statements`, a.s. corrected 3.1), 7.1 (`divSandpileUpperBound_of_meshScaling`,
corrected 7.2, 6.8 (b)). Checked in Audit/Reductions.lean, section `FinalForms`.

## Entries

**3.1** Draft `DiscretePotentialTightnessStmt` (Draft/Section3.lean:42). Corrected
`DiscretePotentialTightnessCorrectedStmt` (Steps/Sec3/DiscretePotentialTightness.lean:102, c1). Escalation: E-c1-4
(`IsOpen D`), review-L32 N1 (Hölder data `C' ε⁻¹ (ε ∨ |·|)^χ`) and N3 (scales `E ω n` in a deterministic sequence `e`
with `∑ e_j^p < ∞` for all `p > 0`). Relation: neither form implies the other. The corrected form weakens the Draft:
it asks for open `D` and polynomially summable scales. N1 strengthens it: for `ε < 1` the Draft's Hölder hypothesis
implies the scaled one, so the corrected "moreover" part covers more data. Lean: both forms imply their common part
`DiscretePotentialTightnessOnOpenStmt` (corrected hypotheses, Draft conclusion), by
`discretePotentialTightnessOnOpen_of_draft` and `discretePotentialTightnessOnOpen_of_corrected`. Draft status: FALSE
(argument) for non-open `D`. E-c1-4 takes `D = cl B_{ρ/2}` and `O = D` with oscillating harmonic data; this is not in
Lean. N3 (random scales) is UNCLEAR. Consumers of the Draft (3.3, 3.7, 4.6; REDUCTIONS F7) use open `D` only. They
reroute to the common part if they thin their deterministic sequence to a polynomially summable one (review-L32 N3).

**3.2** Draft `DiscreteHolderContinuityStmt` (Draft/Section3.lean:76, cited GMS19 Thm 3.9). Corrected
`DiscreteHolderContinuityCorrectedStep` (Steps/Sec3/DiscretePotentialTightness.lean:71, c1, verbatim from review-L32
"Minimal corrected statement"). Escalation: (L2), review-L32 F1/F2. Relation: D ⇒ C, Lean
`discreteHolderContinuityCorrected_of_draft` (`β = 1/2`, `ξ' = ξ`). C ⇏ D: the corrected first estimate is only for
interior `a` with floor `ε^β`, and `ξ'` is chosen after `χ`. Draft status: FALSE (argument). F1 is CONFIRMED with an
explicit counterexample for `χ < ξ` (review-L32 §F1), which is not in Lean. The first estimate (F2) is UNCLEAR as
printed. Neither form is proved here: it is a cited result, used as a hypothesis.

**4.4** Draft `DiscreteLaplacianBoundStmt` (Draft/Section4.lean:76). Corrected `DiscreteLaplacianBoundCorrectedStmt`
(Steps/Sec4/ObstacleSpecialization.lean:528, c1). It adds `0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)` to the origin claim. Escalation:
E-c1-1. Relation: D ⇒ C, Lean `discreteLaplacianBoundCorrected_of_draft`. C ⇏ D. Draft status: **FALSE (Lean)**.
`discreteLaplacianBound_ae_measure_ball_eq_top` shows that the Draft forces `μ_h(B_ρ) = ∞` a.s. The cell
`η([-ε,0])` has mass `ε`, so for `ε > μ_h(B_ρ)` the origin is not interior, `Λ^ε_{2ε} = ∅`, and the claim
`0 ∈ Λ^ε_{2ε}` fails. Then `not_discreteLaplacianBoundStmt` gives `¬ DiscreteLaplacianBoundStmt 𝒮` for any valid
environment whose `μ_h` is a.s. locally finite (Fact 2.2 I, `LQGMeasurePropertiesStmt`, cited; local finiteness from the
dyadic limit in de71d03). The
corrected form is reduced (`discreteLaplacianBoundCorrected_of_inputs`, Proofs/Sec4/ObstacleSpecialization.lean:110)
modulo `BallInteriorConnectedStep` (E-c1-2, suspected false; owner A: weaken `IsObstacleSetting.connected`).
Consumers of the false Draft: 7.2 (above scale), 7.3 and 7.4 are **rerouted here** to the corrected form, which keeps
the only conjunct they use. Lean: `stoppedOdometerLaplacianStep_of_corrected`,
`massBoundOdometerAboveScale_of_corrected`, `odometerBoundMass_of_corrected`, `crudeUpperBound_of_corrected`. Not
rerouted: 4.6, 4.8 (x3), 5.3 (x1, uses 4.4 corrected already), 7.1 (through 7.2-7.4).

**4.5** Draft `DiscreteConservationOfMassStmt` (Draft/Section4.lean:94). Corrected
`DiscreteConservationOfMassCorrectedStmt` (Steps/Sec4/ObstacleSpecialization.lean:541, c1). It adds
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)` to the mass identity. Escalation: E-c1-1. Relation: D ⇒ C, Lean
`discreteConservationOfMassCorrected_of_draft`. Draft status: **FALSE (Lean)**.
`discreteConservationOfMass_ae_measure_ball_eq_top` uses that for `ε > μ_h(B_ρ)`, `Λ^ε_ε = ∅` and `Δ^ε w̃ = 0` on `V`
(adjacent cells meet, `adjacentCellsMeetAeStep`), so the identity reads `0 = 1`. Then
`not_discreteConservationOfMassStmt` follows (same local-finiteness hypothesis as 4.4).

**5.2** Draft `GeneralIDLALowerBoundStmt` (Draft/Section5.lean:47). Relaxed `GeneralIDLALowerBoundRelaxedStep`
(Steps/Sec5/IDLALowerBound.lean:40, c2). It drops the `σ(h,η)`-measurability and connectivity of `O₁, O₂`, the
condition `0 ∈ O₁` and `K_ε > 0`. Escalation: E-c2-1 (resolved without a statement change, 727dab9). Relation:
C ⇒ D, Lean `generalIDLALowerBound_of_relaxed` (Steps/Sec5/IDLALowerBound.lean:180, c2). D ⇒ C is not claimed:
relaxing hypotheses strengthens the result. Draft status: true modulo cited inputs. The relaxed form is reduced to
Lemmas 2.7 and 2.8 (cited) in 727dab9 (`generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize`,
Proofs/Measurability/EnvSigma.lean).

**6.3** Draft `AbelianIDLAStmt` (Draft/Section6.lean:46, FROZEN). Corrected `AbelianIDLAAnyStartStep`
(Steps/Sec6/IterativeBound.lean:110, c5). It drops `a_i ∈ Θ` (any starting sites). Escalation: E-c5-2. Relation:
C ⇒ D, Lean `AbelianIDLAAnyStartStep.abelianIDLA` (:115). Both are PROVED with no hypothesis
(`AbelianIDLA.abelianIDLAAnyStartStep`, `AbelianIDLA.abelianIDLA`, Proofs/Sec6/AbelianIDLA/Statement.lean:115, 119;
a4e6f83). Ruling needed only on whether to restate the frozen 6.3 in its stronger form, which 6.10 uses.

**6.7** Draft `ConstantOrderLowerBoundStmt` (Draft/Section6.lean:102). Corrected `ConstantOrderLowerBoundLogStmt`
(Steps/Sec6/ConstantOrderLowerBound.lean:34, c5): `s₂` becomes `s₂ (1 + |log r|)⁻²`. Escalation: E-A10 verdict (b)
(c4). Relation: D ⇒ C, Lean `ConstantOrderLowerBoundStmt.logLoss` (:48, c5). C ⇏ D. Draft status: unproved. It is
reduced to the Draft 6.8 (`constantOrderLowerBound`). The corrected form is reduced to 6.8 (b)
(`constantOrderLowerBoundLog`, Proofs/Sec6/ConstantOrderLowerBound/LogLoss.lean:60).

**6.8** Draft `ConstantOrderLowerBoundDivStmt` (Draft/Section6.lean:121). Corrected
`ConstantOrderLowerBoundDivLogStmt` (Steps/Sec6/ConstantOrderLowerBoundDiv.lean:32, c4): `1 - s₂` becomes
`1 - s₂ (1 + |log r|)⁻²`. Escalation: E-A10 verdict (b). Relation: D ⇒ C, Lean `constantOrderLowerBoundDivLog_of_draft`
(= x2's `Sec7.constantOrderLowerBoundDivLog_of_fixed`, Proofs/Sec7/DivSandpileUpperBound/LogSurvival.lean:13). Draft
status: unproved. E-A10 shows that route (a) needs a new scale-invariant Green bound
(`ExitTimeScaleInvariantStep`); there is no counterexample. The corrected form is reduced
(`constantOrderLowerBoundDiv_of_steps`) modulo `GoodScaleEventMeasurableStep`. That step is false as drafted
(E-c2-4); its a.s. form is in d248b7c.

**6.9** Draft `ChanceOfBeingAbsorbedStmt` (Draft/Section6.lean:140). It has two corrected forms (c5; the log forms are in 746a5f1):
- `ChanceOfBeingAbsorbedLocalRateStmt` (Steps/Sec6/ChanceOfBeingAbsorbed.lean:34): `s₃` is chosen after `s₀`
  (E-c5-1).
- `ChanceOfBeingAbsorbedLogLossStmt` (Steps/Sec6/IterativeBound.lean:73): the local rate, with rates
  `s₃, s₄ ∝ (1 + |log r|)⁻²` (E-A10 (b)).

Relation: D ⇒ LocalRate ⇒ LogLoss, Lean `ChanceOfBeingAbsorbedStmt.localRate` (:49),
`ChanceOfBeingAbsorbedLocalRateStmt.logLoss` (IterativeBound.lean:82) and `ChanceOfBeingAbsorbedStmt.logLoss`
(:102). Draft status: unproved, and not derivable from 6.7 by the printed proof (E-c5-1: `s₃ ≤ -log(1 - s₂(s₀))`).
LocalRate is proved from the Draft 6.7 (`chanceOfBeingAbsorbedLocalRate`, Proofs/Sec6/ChanceOfBeingAbsorbed/
Chernoff.lean:387). LogLoss is proved from 6.7 (b) (`chanceOfBeingAbsorbedLogLoss_of_steps`). The only consumer, 6.10
(`IterativeBoundStmt`, statement unchanged), is proved from LogLoss (`iterativeBound_of_div`).

**7.2** Draft `MassBoundOdometerStmt` (Draft/Section7.lean:34). Corrected `MassBoundOdometerAboveScaleStmt`
(Steps/Sec7/MassBoundOdometer.lean:48, c3): only radii `s ≥ ε^β`. Escalation: E-c3-2. Relation: D ⇒ C, Lean
`massBoundOdometerAboveScale_of_massBoundOdometer` (`β = 1`). Draft status: FALSE (argument). E-c3-2 gives a
counterexample for every realization and small `ε`: `s` below the cell scale, `Θ` the component of `0` off one cell.
It is not in Lean. The corrected form is proved from 2.16, 2.8 (cited) and Draft 4.4 (`massBoundOdometerAboveScale_of
_draft`, :158), and **here from the corrected 4.4** (`massBoundOdometerAboveScale_of_corrected`). The consumer 7.1
is rerouted to the corrected form (d17f14c, `divSandpileUpperBound_of_meshScaling`; REDUCTIONS F1 resolved).

**7.4** Draft `CrudeUpperBoundStmt` (Draft/Section7.lean:67) is already the corrected form (review-S (S4), A):
`a ∈ Λ^ε_t \ {0}`, with paths in `Λ^ε_t`. The printed form (paths in `D_ε(t ε⁻¹)` for the stopped odometer) is FALSE
(argument, E-c3-1 (1)) and has a proof gap (E-c3-1 (2)). It is not stated in Lean. Proved from Draft 4.4
(`crudeUpperBound_of_draft`, c3) and **here from the corrected 4.4** (`crudeUpperBound_of_corrected`, with
`DegreeBoundInput`, GMS19 Lemma 2.6).

**3.1, refutation in Lean (2026-11-05).** `Audit.Refutations.not_discretePotentialTightnessStmt`
(Audit/Refutations.lean:320; worker A, committed by c1): `MepsScalingInput 𝒮 → S.IsValid 𝒮 γ → ¬
DiscretePotentialTightnessStmt 𝒮` for every valid environment (axioms: propext, Classical.choice, Quot.sound). `D` is the
closed segment `[0, 1/4]` (empty interior, so the Laplacian hypothesis is vacuous), `O = D`, data
`u^ε(a) = m_ε 1{Re η(a) > 1/8}`; no subsequence of the rescalings converges uniformly on `D` to a continuous limit.
Status of 3.1 is now **FALSE (Lean)**.

**3.1 (a.s. form)** `DiscretePotentialTightnessAeStep` (Steps/Sec3/ConvergenceNormalizedExitTime.lean:59, c2).
Escalation: E-c2-6. As the corrected 3.1 (open `D`, polynomially summable deterministic scales), but the bounds
`|Δ^ε u^ε| ≤ C` (interior vertices) and `|u^ε| ≤ C ε⁻¹` are required only `∀ᵐ ω, ∀ᶠ n`, and the conclusion is the
interior part (compact `O` with `cl O ⊆ D`). Relation: neither form implies the other in Lean (weaker hypotheses,
weaker conclusion). The printed lemma is an a.s. statement, so this is its faithful interior form; the `∀ ω` form of
the frozen statements cannot be applied to functions of `S.mult` (E-c2-6). Consumer: 3.7
(`convergenceNormalizedExitTime_of_statements`, Proofs/Sec3/ConvergenceNormalizedExitTime/DyadicModulus.lean:159,
980cf27). Status: open step (its proof should be the pathwise proof of the corrected 3.1; owner to be assigned).

**5.1 (stopped part)** Draft `IDLALowerBoundStmt` (Draft/Section5.lean, unchanged). Escalation: E-c1-5. The printed
proof (corrected.tex 2042) bounds walkers stopped upon exiting `Λ^ε_t`, while the statement (1981) and its use in 6.1
(2862) stop them upon exiting `V^ε(Λ_t)`; `Λ^ε_t ⊄ V^ε(Λ_t)` in general. Carved: `IDLALowerBoundStoppedStep`
(Steps/Sec5/IDLALowerBound.lean:68) = the consumed conjunct, derived (7fdfd3c, `iDLALowerBoundStopped_of_steps`,
Proofs/Sec5/IDLALowerBound/Stopped.lean) from Lemma 5.2 (relaxed), 2.8 and `StoppedMeanValueInequalityStep`,
`StoppedLLowerBoundStep` (Lemmas 5.3, 5.4 with `Λ^ε_t` replaced by `V^ε(Λ_t)`; Stopped.lean:33, 51). Relation: the
steps are neither weaker nor stronger than 5.3/5.4 (different domain). Final form `iDLALowerBound_final_of_strictGap`
(Proofs/Sec5/IDLALowerBound/Final.lean:48). Operator ruling pending (keep the steps, or restate the stopping set).

**7.1 via 7.2 above scale** Draft `DivSandpileUpperBoundStmt` (Draft/Section7.lean, unchanged). The earlier reduction
consumed the false Draft 7.2 and the Draft 6.8 (REDUCTIONS F1, F3). Final form (d17f14c)
`divSandpileUpperBound_of_meshScaling` (Proofs/Sec7/DivSandpileUpperBound/ShellIterationOfMeshScaling.lean:43):
`MepsScalingInput`, Theorems 2.3, 4.1, Lemmas 6.8 (b) `ConstantOrderLowerBoundDivLogStmt`, 2.7, corrected 7.2
`MassBoundOdometerAboveScaleStmt`, 3.3, 2.8, 7.3, 7.4; no open step (`ShellIterationStep` proved from
`MepsScalingInput`, `StoppedShellConfinementStep` no longer needed). No change to the statement of 7.1.

**Not corrected forms:** 6.10 is proved as drafted from 6.8 (b); the E-c5-1 remark on `C` before `s₀` is met with
`C = 1`. 4.6 (E-x3-2, quantifier order) has no corrected Prop yet; its reduction uses Draft 4.6 steps (x3). The x2
findings E-x2-2 (`D(M) = {0} ∪ cl{v > 0}`) concern a printed identity, not a Draft Stmt.

**Paper corrections C7–C10 (2026-11-06).** See `AUDIT-C7-C10-USES.md`: C7 requires the source in the killed domain for the two affected clauses; C8 restricts Lemma 7.2 to `s ≥ ε^β`; C9 restricts the global cluster identity to `ε < t`, with stopped/unstopped consistency additionally required for the two stopped-cluster displays; C10 changes the boundary modulus in Lemma 3.1 to `C' ε⁻¹`. These changes do not resolve the separate consistency use in Proposition 5.1 or N3.


**C7 Draft synchronization (2026-11-06).** The existing proved successors
`DiscreteLaplacianBoundCorrectedStmt` and `DiscreteConservationOfMassCorrectedStmt` now reside in
`Draft/Section4.lean`; their definitions and their downstream names are unchanged. The source-cell
hypothesis appears only in the respective origin and mass-identity clauses, exactly as in corrected
paper lines 1881–1893. The old Draft declarations remain as refuted historical forms.

**C8 Draft synchronization (2026-11-06).** `MassBoundOdometerAboveScaleStmt` is now in
`Draft/Section7.lean` with the same name and definition, including `s ≥ ε^β` (corrected paper
Lemma 7.2). Its existing proof and the Proposition 7.1 reduction already use this form. The
frozen `MassBoundOdometerStmt` remains as a historical form.

**C9 cluster identities (2026-11-06).** `Sandpile.cluster_eq_closure_of_one_lt` in
`Proofs/Sandpile/ClusterIdentityCorrected.lean` proves corrected equation
`eq:cluster-definition` for initial mass `M > 1`, under the deterministic sandpile hypotheses.
`Sandpile.cluster_eq_closure_of_mesh_lt_time` specializes it to `M = t / ε` with `0 < ε < t`.
`Sandpile.cluster_eq_closure_of_consistency` adds the explicit equality of stopped and global
positive odometer sets for `eq:cluster-and-lambdat`. This does not establish consistency at the
Proposition 5.1 use; that separate gap is recorded in `AUDIT-C7-C10-USES.md`.

**C12 prepared Lemma 4.6 (2026-11-06).** `SubsequentialConvergencePreparedStmt` in
`Draft/Section4Prepared.lean` fixes the time and deterministic input sequence before choosing
the deterministic thinning and its almost-sure event. It asserts relative compactness, Hölder
regularity of every uniform limit, and measurable selection on that thinning.
`OdometerPreparedCompactnessStep` and `OdometerPreparedSelectionStep` in
`Steps/Sec4/SubsequentialConvergencePrepared.lean` name the two remaining obligations;
`subsequentialConvergencePrepared_of_steps` assembles them. The compactness step currently
now consumes `DiscretePotentialTightnessPreparedStmt`, the C10/C11 successor of 3.1.
`convergenceDivisible_of_prepared` in `Proofs/Sec4/ConvergenceDivisible/Prepared.lean`
reroutes Theorem 4.1 through the successor, its existing uniqueness and event-measurability
inputs, and Lemma 4.8. Other historical consumers still use the old 4.6 statement.


**C10/C11 prepared Lemma 3.1 (2026-11-06).** `DiscretePotentialTightnessPreparedStmt`
in `Draft/Section3Prepared.lean` places an arbitrary deterministic input sequence before a
deterministic thinning and a common almost-sure event, then quantifies over countable domain
families and measurable data. `PreparedHolderBoundary` has the paper's `C′ / ε` factor at
every scale. `PreparedTightnessPathwiseStep` and `PreparedTightnessSelectionStep` in
`Steps/Sec3/DiscretePotentialTightnessPrepared.lean` are separate open proof obligations;
`discretePotentialTightnessPrepared_of_steps` assembles them. The selection step is a sufficient
general selection principle and is not claimed proved. The prior polynomial-scale form remains
for historical reductions and is not equivalent to this successor. The prepared 4.6 compactness
step now takes the new successor.

**C12 measurable-exit route (2026-11-06).**
`convergenceDivisible_of_prepared_measurable_exit` in
`Proofs/Sec4/ConvergenceDivisible/PreparedEventMeasurability.lean` derives Theorem 4.1 from
the prepared 4.6, 4.8, obstacle uniqueness, adjacent-cell intersection, and null measurability
of the exit event. The continuum version and error-event measurability in this route use only
the fixed-time prepared convergence; the older all-times statements remain historical forms.


**C11, Lemma 3.3 route (2026-11-06).** `GreenKernelInteriorPreparedStep` and
`GreenKernelBoundaryPreparedStep` in `Steps/Sec3/UniformConvergenceGreenKernelPrepared.lean`
replace the old 3.1 antecedent with `DiscretePotentialTightnessPreparedStmt`;
`uniformConvergenceGreenKernel_of_prepared_steps` assembles Lemma 3.3. These two prepared
steps are open obligations, not consequences proved here; in particular they must handle
the eventually almost-sure hypotheses and the separate identification gaps in
`AUDIT-C11-C12-USES.md`.

**C10/C11, Lemma 3.5 route (2026-11-06).** `DirichletInteriorPreparedStep` and
`DirichletBoundaryPreparedStep` in `Steps/Sec3/DiscreteDirichletProblemPrepared.lean`
consume the prepared 3.1 successor; `discreteDirichletProblem_of_prepared_steps` assembles
3.5 with the existing continuum step. Both prepared steps remain open and retain the
independent barrier issue recorded in `AUDIT-C11-C12-USES.md`.

**C11, Lemma 3.7 route.** `NormalizedExitInteriorPreparedStep` is an open interior-convergence obligation using the prepared Lemma 3.1 input. `convergenceNormalizedExitTime_of_prepared_steps` assembles it with the existing boundary estimates; the independent G1/G2 issues remain open.

**C12, Lemmas 4.7 and 4.8.** `EquiboundedStmt` (Draft/Section4.lean:127) already places the deterministic sequence and thinning before the almost-sure event, as corrected at paper lines 1915–1923. `SubsequentialPropertiesPreparedStmt` (Draft/Section4PropertiesPrepared.lean) gives the fixed-time, prepared-sequence 4.8 statement with relative compactness and every-limit properties. `subsequentialPropertiesPrepared_of_steps` assembles it from 4.6 and the open `OdometerPropertiesPreparedIdentificationStep`; the independent comparison gap G3 remains. `convergenceDivisible_of_prepared_properties_measurable_exit` routes Theorem 4.1 through this corrected 4.8 and explicit uniqueness, adjacent-cell and exit-event measurability inputs.

**C9 downstream comparison (2026-11-06).** `matedDiscreteCluster_closure_subset_sandpileCluster` in `Proofs/Sec4/DivSandpileLowerBound/CorrectedClusterComparison.lean` proves the one-sided inclusion using the odometer comparison and `0 < ε < t`. `sandpileCluster_eq_matedDiscreteCluster_closure_of_consistency` proves the corrected stopped-cluster equality under equality of the global odometer support and the discrete obstacle cluster; this equality is not established in Proposition 5.1. Its needed inner inclusion is already isolated as `DiscreteClusterInnerBoundStep` (Steps/Sec5/IDLALowerBound.lean:58), obtained conditionally from `ObstacleClusterInnerApproximationStep` (Steps/Sec4/DivSandpileLowerBound.lean:20). The distinct issue of the walkers stopped on continuum cells remains `IDLALowerBoundStoppedStep`.

**C11, prepared local compactness.** `preparedTightness_singleDomain` in `Proofs/Sec3/DiscretePotentialTightness/PreparedSingleDomain.lean` specializes the prepared 3.1 statement to almost-sure bounds for one domain. `GreenEnvironment.prepared_compactness_of_eventual_estimates` in `Proofs/Sec3/UniformConvergenceGreenKernel/PreparedLocalCompactness.lean` combines this with measurable clipping, proving local convergence on a deterministic thinning and a measurable random further subsequence from eventually harmonic, bounded data. This supplies a prepared replacement for the deterministic-input use of the older local compactness lemma; the Green-kernel identification obligations and G4 remain open.

**C11, random-index local compactness.** `GreenEnvironment.prepared_compactness_of_eventual_estimates_random` in `Proofs/Sec3/UniformConvergenceGreenKernel/PreparedRandomCompactness.lean` proves the random-index analogue: the deterministic thinning is fixed before an arbitrary environment-measurable sequence of indices bounded below by their positions. The measurable clipping argument preserves eventual bounds along this sequence. This is conditional on the prepared Lemma 3.1 and does not discharge the separate Green-kernel identification obligations.

**C11, prepared Green-kernel reduction.** `greenKernelBoundaryPreparedStep` in `Proofs/Sec3/UniformConvergenceGreenKernel/PreparedBoundaryStep.lean` proves the prepared boundary obligation using the existing maximum-principle argument. `greenKernelInteriorPreparedStep_of_subsequence` in `PreparedInteriorStep.lean` reduces prepared interior convergence in probability to the open `GreenKernelPreparedSubsequenceStep`, which asserts subsequential identification on deterministic and measurable random refinements. This step must still be proved from prepared compactness and the occupation/degree inputs, including the independent G4 constant issue. The earlier entry saying the boundary step is open is superseded by this result.

**C11, final prepared Lemma 3.3 route.** `uniformConvergenceGreenKernel_of_prepared_subsequence` in `Proofs/Sec3/UniformConvergenceGreenKernel/PreparedFinal.lean` assembles the prepared 3.1 input, cited 2.10/2.14/3.4 and 2.8, and the open `GreenKernelPreparedSubsequenceStep`. The latter is not proved by the prepared compactness lemmas alone: those currently require exact environment measurability of graph multiplicities and cell sets, while `exists_envSigma_measurable_mult` and `exists_envSigma_measurable_cellVertices` provide almost-sure versions. Adapting clipping to these versions and identifying the limits remain separate work; G4 is unresolved.

**C11, almost-sure environmental versions.** `GreenEnvironment.prepared_compactness_of_eventual_estimates_random_ae` in `Proofs/Sec3/UniformConvergenceGreenKernel/PreparedRandomCompactnessAE.lean` proves random-index prepared compactness without exact environment measurability of the graph or cell sets. It clips against environment-measurable versions and transfers the bounds and equality back on their common almost-sure event. This removes the measurability limitation of the earlier compactness bridge; connecting it to `GreenKernelPreparedSubsequenceStep` and the independent G4 identification remains.


**C11, prepared Green-kernel subsequences proved.** `GreenEnvironment.exists_prepared_subseq_greenKernel_uniform` in `Proofs/Sec3/UniformConvergenceGreenKernel/PreparedInteriorSubsequence.lean` prepares the deterministic compactness thinning before the measurable random index sequence, and proves limit identification using the stated degree-measure and Green-occupation convergence inputs. `greenKernelPreparedSubsequenceStep` discharges the previously open prepared subsequence step; `uniformConvergenceGreenKernel_of_prepared_tightness` derives Lemma 3.3 from prepared tightness and the stated 2.10, 3.4, 2.14, and cell-size inputs. This supersedes the earlier entries describing the subsequence step as open. It does not establish the occupation input or independently close G4: the claimed normalization is assumed in `IntegralConvergenceGreenFunctionStmt`, and the paper's printed `m₀/6` in the Lemma 3.3 proof still requires the correction recorded in `PROOF-REPAIRS-G.md`.
