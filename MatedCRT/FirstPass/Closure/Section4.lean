import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results, Section 4 (task fp-Closure-counted-results, worker z1)

Closed for a model `𝒮` with normalized law `ν`: 4.3 (`closed_4_3`), 4.4 (`closed_4_4`, corrected form), 4.5 (`closed_4_5`,
corrected form), 4.7 (`closed_4_7`, `ExitTimeUpperBoundStmt` from the package). Not closed: 4.1 (gap G3), 4.6 and 4.8
(gap G3 and 3.7).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 4.3 (discrete basic properties), for a model with normalized law `ν`. No further hypotheses. -/
theorem closed_4_3 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (_hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (_hLaw : HasNormalizedSLELaw 𝒮 ν) : DiscreteBasicPropertiesStmt 𝒮 :=
  firstPass_4_3 (𝒮 := 𝒮)

/-- Lemma 4.4 (discrete Laplacian bound), corrected form `DiscreteLaplacianBoundCorrectedStmt`, for a model with normalized
law `ν`. No further hypotheses. -/
theorem closed_4_4 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (_hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (_hLaw : HasNormalizedSLELaw 𝒮 ν) : DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  firstPass_4_4_corrected (𝒮 := 𝒮)

/-- Lemma 4.5 (discrete conservation of mass), corrected form `DiscreteConservationOfMassCorrectedStmt`, for a model with
normalized law `ν`. No further hypotheses. -/
theorem closed_4_5 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (_hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (_hLaw : HasNormalizedSLELaw 𝒮 ν) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  firstPass_4_5_corrected (𝒮 := 𝒮)

/-- Lemma 4.7 (equiboundedness), for a model with normalized law `ν`. -/
theorem closed_4_7 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt)
    (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 :=
  firstPass_4_7 (𝒮 := 𝒮) h27 (slePkg_exitTimeUpper hνC hLaw) hm

end MatedCRT
