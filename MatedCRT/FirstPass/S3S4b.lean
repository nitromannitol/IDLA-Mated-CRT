import MatedCRT.FirstPass.Frozen.S3S4b
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.IntegralConvergenceGreenFunctionFinal
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedHarmonicInputs
import MatedCRT.Steps.Sec2.BoundedExitTimeRV

/-!
# First pass: paper-owned results 3.4 and 3.5 (task fp-S3S4b, q2)

Each `firstPass_<section>_<number>` takes as hypotheses only Draft statements of numbered results, the frozen external
inputs of `MatedCRT/FirstPass/Frozen/S3S4b.lean` and `MatedCRT/FirstPass/Frozen/S3S4.lean`, and the External input
`MepsScalingInput`. Lemma 2.7 (`VolumeGrowthStmt`) is passed where the committed reduction derives Lemma 2.17.

Lemma 3.5 is proved here in its corrected form [C13] (`DiscreteDirichletProblemCorrectedStmt`, boundary datum
`φ(π_D(η(b)))`), which is the form of the paper's corrected statement. The Draft form `DiscreteDirichletProblemStmt`
(boundary datum `φ(η(b))`, Hölder `φ` on a neighbourhood; review-S2) is not proved in this file: it needs the Steps
`DirichletInteriorStep` and `DirichletBoundaryStep` (MatedCRT/Steps/Sec3/DiscreteDirichletProblem.lean:51, :74), see the report.
-/

namespace MatedCRT

/-- **Lemma 3.4** (lemma:integral-convergence-of-greens-function), corrected [C1, C16]: `IntegralConvergenceGreenFunctionStmt`.
Hypotheses: Lemma 2.7 (`VolumeGrowthStmt`, which gives Lemma 2.17 `BoundedExitTimeRVStmt` through `boundedExitTimeRV_of_steps`),
Lemma 2.18 (`ExitTimeUpperBoundStmt`), `MepsScalingInput` (External), Lemma 2.11 (`RandomWalkToLBMStmt`, cited), Lemma 2.8
(`CellSizeEstimateStmt`, cited), and the frozen inputs: the Revuz occupation identity `FrozenLBMGreenOccupation`, the truncated
random-walk-to-LBM convergence `FrozenTruncatedDetFixedTime` (both operator rulings), and the frozen planar Brownian outward
excursion `FrozenBrownianOutwardExcursionAtExit`. Proof: the committed reduction `integralConvergenceGreenFunction_final`. -/
theorem firstPass_3_4 {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (h18 : ExitTimeUpperBoundStmt 𝒮)
    (hscale : MepsScalingInput 𝒮) (h211 : RandomWalkToLBMStmt 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hrevuz : FrozenLBMGreenOccupation 𝒮) (hdet : FrozenTruncatedDetFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  integralConvergenceGreenFunction_final (boundedExitTimeRV_of_steps h27) h18 hscale hrevuz hdet h211 hcell hexc

/-- **Lemma 3.5** (lemma:discrete-dirichlet-problem), corrected form [C13]: `DiscreteDirichletProblemCorrectedStmt`, the
discrete Dirichlet problem with boundary datum `m_ε φ(π_D(η(b)))` and Hölder `φ` on `cl(B_r(z))` only. Hypotheses: Lemma 2.7
(`VolumeGrowthStmt`), `MepsScalingInput` (External), Lemma 2.10 (`DegreeMeasureConvergenceStmt`), Lemma 3.4
(`IntegralConvergenceGreenFunctionStmt`, numbered result; see `firstPass_3_4`), Lemma 2.14 (`GreenKernelUpperBoundStmt`), Lemma 2.8
(`CellSizeEstimateStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`), the frozen corrected Lemma 3.2 (`FrozenDiscreteHolderContinuityCorrected`),
the frozen finite-domain Dirichlet representation (`FrozenFiniteDomainDirichletRepresentation`), and the corrected Lemma 3.6
(`CorrectedHarmonicConvergenceStmt`, a numbered result not yet discharged by a first-pass theorem). Proof: the committed
reduction `discreteDirichletProblemCorrected_of_corrected_harmonic_estimates`, which uses no Step hypothesis. -/
theorem firstPass_3_5_corrected {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hfinite : FrozenFiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  discreteDirichletProblemCorrected_of_corrected_harmonic_estimates 𝒮 h27 hm h210 h34 h214 h28 h218 hH hfinite h36

#print axioms firstPass_3_4
#print axioms firstPass_3_5_corrected

end MatedCRT
