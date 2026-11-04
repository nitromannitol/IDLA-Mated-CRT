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
| 3.1 | DiscretePotentialTightnessStmt | DiscretePotentialTightnessCorrectedStmt | neither; both ⇒ common part (Lean) | FALSE (argument, E-c1-4) |
| 3.2 | DiscreteHolderContinuityStmt | DiscreteHolderContinuityCorrectedStep | D ⇒ C (Lean) | FALSE (argument, review-L32 F1) |
| 4.4 | DiscreteLaplacianBoundStmt | DiscreteLaplacianBoundCorrectedStmt | D ⇒ C (Lean) | **FALSE (Lean)** |
| 4.5 | DiscreteConservationOfMassStmt | DiscreteConservationOfMassCorrectedStmt | D ⇒ C (Lean) | **FALSE (Lean)** |
| 5.2 | GeneralIDLALowerBoundStmt | GeneralIDLALowerBoundRelaxedStep | C ⇒ D (Lean, c2) | true: reduced through C |
| 6.3 | AbelianIDLAStmt | AbelianIDLAAnyStartStep | C ⇒ D (Lean, c5); both proved | PROVED |
| 6.7 | ConstantOrderLowerBoundStmt | ConstantOrderLowerBoundLogStmt | D ⇒ C (Lean, c5) | unproved |
| 6.8 | ConstantOrderLowerBoundDivStmt | ConstantOrderLowerBoundDivLogStmt | D ⇒ C (Lean) | unproved |
| 6.9 | ChanceOfBeingAbsorbedStmt | ...LocalRateStmt; ...LogLossStmt | D ⇒ LocalRate ⇒ LogLoss (Lean, c5) | unproved |
| 7.2 | MassBoundOdometerStmt | MassBoundOdometerAboveScaleStmt | D ⇒ C (Lean) | FALSE (argument, E-c3-2) |
| 7.4 | CrudeUpperBoundStmt (already the corrected Λ-form) | (printed form: not in Lean) | Draft = correction (S4) | Draft reduced; printed form FALSE (argument, E-c3-1) |

Counts: **C ⇒ D: 2** (5.2, 6.3). **D ⇒ C: 7** (3.2, 4.4, 4.5, 6.7, 6.8, 6.9, 7.2), so in these cases the
correction weakens the result. **Neither: 1** (3.1). **False as drafted: 5.** Two are refuted in Lean (4.4, 4.5), and
three by argument only (3.1, 3.2, 7.2). The printed 7.4 is also false, but its Draft is already the corrected form.
**Merely unproved: 3** (6.7, 6.8, 6.9).

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
(x2) still uses the false Draft 7.2 (REDUCTIONS F1).

**7.4** Draft `CrudeUpperBoundStmt` (Draft/Section7.lean:67) is already the corrected form (review-S (S4), A):
`a ∈ Λ^ε_t \ {0}`, with paths in `Λ^ε_t`. The printed form (paths in `D_ε(t ε⁻¹)` for the stopped odometer) is FALSE
(argument, E-c3-1 (1)) and has a proof gap (E-c3-1 (2)). It is not stated in Lean. Proved from Draft 4.4
(`crudeUpperBound_of_draft`, c3) and **here from the corrected 4.4** (`crudeUpperBound_of_corrected`, with
`DegreeBoundInput`, GMS19 Lemma 2.6).

**Not corrected forms:** 6.10 is proved as drafted from 6.8 (b); the E-c5-1 remark on `C` before `s₀` is met with
`C = 1`. 4.6 (E-x3-2, quantifier order) has no corrected Prop yet; its reduction uses Draft 4.6 steps (x3). The x2
findings E-x2-2 (`D(M) = {0} ∪ cl{v > 0}`) concern a printed identity, not a Draft Stmt.
