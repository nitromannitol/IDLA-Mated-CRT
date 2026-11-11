import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 5

Closed for a model `𝒮` with certified reference model `hC : CertifiedReferenceModel ν 𝒮`: 5.2 (`closed_5_2`,
input `hC.cellSizeEstimate`), 5.4 (`closed_5_4`, inputs `hC.greenKernelLowerBound`, `hC.countingMeasureConvergence` and the
explicit `GreenFunctionCrudeBoundStmt 𝒮`). Not closed: 5.3 (gaps G9 and 4.1); 5.1 is not in the counted set.
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 5.2 (general IDLA lower bound), for a model `𝒮` with certified reference model `hC`. -/
theorem closed_5_2 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : GeneralIDLALowerBoundStmt 𝒮 :=
  firstPass_5_2 (𝒮 := 𝒮) h27 hC.cellSizeEstimate

/-- Lemma 5.4 (L lower bound), for a model `𝒮` with certified reference model `hC`. -/
theorem closed_5_4 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  firstPass_5_4 (𝒮 := 𝒮) h215 hC.greenKernelLowerBound hC.countingMeasureConvergence

end MatedCRT
