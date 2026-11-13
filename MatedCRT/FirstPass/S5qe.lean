import MatedCRT.FirstPass.S5qd
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.S3i.LensStep
import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected

/-!
# Proposition 5.1 with the certified reference model without its frozen truncated-laws conjunct

`CertifiedReferenceModel ν 𝒮` (`FirstPass/SLERef/Certified.lean:54`) has eighteen conjuncts; conjunct 17 is the frozen
Prop `FrozenTruncatedQuenchedLawsFixedTime 𝒮` (line 71). The chain of Proposition 5.1 (`closed_5_1_canon_noCell_derived_closed`,
`FirstPass/S5qd.lean:192`) no longer projects that conjunct, but its hypothesis type still contains it. This file gives the
hypothesis type without it:

* `CertifiedReferenceModelCore ν 𝒮`: the seventeen other conjuncts, in the same order;
* `CertifiedReferenceModel.toCore`: the full model gives the core;
* core projections, the core variants of the Lemmas 3.3, 3.4, 3.5 on the chain (their bodies are those of
  `closed_3_3`, `closed_3_4_hdetSwap`, `closed_3_5_hdetSwap`, with the truncated quenched laws
  given by `MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs`, `FirstPass/S3t/BLEnvelopeClosure.lean:43`);
No new frozen Prop and no new hypothesis: the core is a strengthening of the hypothesis (fewer conjuncts), and the
conclusions are unchanged. Terminology: Armstrong–Kuusi–Mourrat for the obstacle problem; Berestycki–Gwynne for the BG20
Green bound; Duplantier–Sheffield for the LQG measure.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- The certified reference model without its conjunct `FrozenTruncatedQuenchedLawsFixedTime 𝒮` (conjunct 17 of
`CertifiedReferenceModel`, `FirstPass/SLERef/Certified.lean:54`). The seventeen other conjuncts are in the same order. -/
def CertifiedReferenceModelCore (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel) : Prop :=
  HasNormalizedSLELaw 𝒮 ν ∧
  SLEModelClosureInput 𝒮 ∧
  MepsScalingInput 𝒮 ∧
  DegreeBoundInput 𝒮 ∧
  CellSizeEstimateStmt 𝒮 ∧
  CountingMeasureConvergenceStmt 𝒮 ∧
  DegreeMeasureConvergenceStmt 𝒮 ∧
  FrozenConeScalingLaw 𝒮 ∧
  FrozenLBMGreenOccupationRescaled 𝒮 ∧
  HasReferenceEnvironments 𝒮 ∧
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundStmt 𝒮 ∧
  FrozenDiscreteHolderContinuityCorrected 𝒮 ∧
  BG20Prop51 𝒮 ∧
  FPSimilarityTransferCorrected 𝒮

/-- The full certified reference model gives the core one (the frozen conjunct 17 is dropped). -/
theorem CertifiedReferenceModel.toCore {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (h : CertifiedReferenceModel ν 𝒮) : CertifiedReferenceModelCore ν 𝒮 := by
  unfold CertifiedReferenceModel at h
  unfold CertifiedReferenceModelCore
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h18⟩

namespace CertifiedReferenceModelCore

variable {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}

theorem mepsScaling (h : CertifiedReferenceModelCore ν 𝒮) : MepsScalingInput 𝒮 := h.2.2.1

theorem cellSizeEstimate (h : CertifiedReferenceModelCore ν 𝒮) : CellSizeEstimateStmt 𝒮 := h.2.2.2.2.1

theorem degreeMeasureConvergence (h : CertifiedReferenceModelCore ν 𝒮) : DegreeMeasureConvergenceStmt 𝒮 :=
  h.2.2.2.2.2.2.1

theorem frozenConeScaling (h : CertifiedReferenceModelCore ν 𝒮) : FrozenConeScalingLaw 𝒮 :=
  h.2.2.2.2.2.2.2.1

theorem frozenLBMGreenOccupation (h : CertifiedReferenceModelCore ν 𝒮) : FrozenLBMGreenOccupationRescaled 𝒮 :=
  h.2.2.2.2.2.2.2.2.1

theorem randomWalkToLBM (h : CertifiedReferenceModelCore ν 𝒮) : RandomWalkToLBMStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.1

theorem greenKernelUpperBound (h : CertifiedReferenceModelCore ν 𝒮) : GreenKernelUpperBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

theorem greenKernelLowerBound (h : CertifiedReferenceModelCore ν 𝒮) : GreenKernelLowerBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exitTimeUpperBound (h : CertifiedReferenceModelCore ν 𝒮) : ExitTimeUpperBoundStmt 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem frozenDiscreteHolderContinuityCorrected (h : CertifiedReferenceModelCore ν 𝒮) :
    FrozenDiscreteHolderContinuityCorrected 𝒮 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end CertifiedReferenceModelCore

/-- The existence statement `FrozenCertifiedReferenceModelExists` (`FirstPass/SLERef/Certified.lean:80`) gives an
existence statement for the core. -/
theorem FrozenCertifiedReferenceModelExists.core (h : FrozenCertifiedReferenceModelExists) :
    ∃ (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel), CertifiedReferenceModelCore ν 𝒮 := by
  obtain ⟨ν, 𝒮, hC⟩ := h
  exact ⟨ν, 𝒮, hC.toCore⟩

end MatedCRT

namespace MatedCRT.FirstPassClosure

/-- Lemma 3.6 (corrected), core form: `closed_3_6_corrected` (`FirstPass/Closure/Section3.lean:57`) with the core
certified model. -/
theorem closed_3_6_corrected_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    CorrectedHarmonicConvergenceStmt 𝒮 :=
  MatedCRT.FirstPass36.firstPass_3_6_convergence_corrected (𝒮 := 𝒮) hC.randomWalkToLBM hC.cellSizeEstimate
    hC.mepsScaling hexc hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.4 (integral convergence of the Green function), core form: `closed_3_4_hdetSwap`
(`FirstPass/HdetSwap.lean:65`) with the truncated quenched laws from the four-binder theorem
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`), which needs
no closure input. -/
theorem closed_3_4_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (h27 : VolumeGrowthStmt)
    (hexc : BrownianOutwardExcursionAtExitStep) : IntegralConvergenceGreenFunctionStmt 𝒮 :=
  MatedCRT.S3S4c.firstPass_3_4 (𝒮 := 𝒮) h27 hC.exitTimeUpperBound hC.mepsScaling hC.frozenLBMGreenOccupation
    (MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs hC.randomWalkToLBM hC.cellSizeEstimate
      hC.mepsScaling hexc)

/-- Lemma 3.3 (uniform convergence of the Green kernel), core form: `closed_3_3` (`FirstPass/Closure/Section3.lean:43`)
with its Lemma 3.4 input `closed_3_4_core`. -/
theorem closed_3_3_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (𝒮 := 𝒮) (h34 := closed_3_4_core ν hC h27 hexc) hC.degreeMeasureConvergence
    hC.greenKernelUpperBound hC.cellSizeEstimate h27 hC.exitTimeUpperBound hC.mepsScaling
    hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.5 (discrete Dirichlet problem, corrected), core form: `closed_3_5_hdetSwap` (`FirstPass/S5qd.lean:175`) with the
core certified model. -/
theorem closed_3_5_core {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  firstPass_3_5_corrected (𝒮 := 𝒮) h27 hC.mepsScaling hC.degreeMeasureConvergence
    (closed_3_4_core ν hC h27 hexc) hC.greenKernelUpperBound hC.cellSizeEstimate hC.exitTimeUpperBound
    hC.frozenDiscreteHolderContinuityCorrected MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved
    (closed_3_6_corrected_core ν hC hexc)

open _root_.HarmonicBalls MeasureTheory Set Filter Topology in

#print axioms MatedCRT.CertifiedReferenceModel.toCore
#print axioms MatedCRT.FrozenCertifiedReferenceModelExists.core
#print axioms MatedCRT.FirstPassClosure.closed_3_3_core
#print axioms MatedCRT.FirstPassClosure.closed_3_5_core

end MatedCRT.FirstPassClosure
