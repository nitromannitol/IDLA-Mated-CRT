import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 4 (task fp-Closure-counted-results, fp-Closure-round3, worker z1)

Closed: 4.3 (`closed_4_3`), 4.4 (`closed_4_4`, corrected form), 4.5 (`closed_4_5`, corrected form) take no SLE input.
4.7 (`closed_4_7`) is stated for a model `𝒮` with certified reference model `hC : CertifiedReferenceModel ν 𝒮` (chat 186);
its inputs `ExitTimeUpperBoundStmt 𝒮` and `MepsScalingInput 𝒮` are `hC.exitTimeUpperBound` and `hC.mepsScaling`.
Not closed: 4.1 (gap G3), 4.6 and 4.8 (gap G3 and 3.7).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 4.3 (discrete basic properties). No further hypotheses. -/
theorem closed_4_3 {𝒮 : SpaceFillingSLEModel} : DiscreteBasicPropertiesStmt 𝒮 :=
  firstPass_4_3 (𝒮 := 𝒮)

/-- Lemma 4.4 (discrete Laplacian bound), corrected form `DiscreteLaplacianBoundCorrectedStmt`. No further hypotheses. -/
theorem closed_4_4 {𝒮 : SpaceFillingSLEModel} : DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  firstPass_4_4_corrected (𝒮 := 𝒮)

/-- Lemma 4.5 (discrete conservation of mass), corrected form `DiscreteConservationOfMassCorrectedStmt`. No further
hypotheses. -/
theorem closed_4_5 {𝒮 : SpaceFillingSLEModel} : DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  firstPass_4_5_corrected (𝒮 := 𝒮)

/-- Lemma 4.7 (equiboundedness), for a model `𝒮` with certified reference model `hC`. -/
theorem closed_4_7 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : EquiboundedStmt 𝒮 :=
  firstPass_4_7 (𝒮 := 𝒮) h27 hC.exitTimeUpperBound hC.mepsScaling

end MatedCRT
