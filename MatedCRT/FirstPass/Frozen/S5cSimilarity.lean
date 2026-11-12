import MatedCRT.Defs.Setting
import MatedCRT.Defs.QuantumCone

/-!
# Scaled area measure of the similarity transfer

`FPScaledMeasure` is the scaled area measure `μ_{h^{(b)}}` of the similarity transfer `FPSimilarityTransferCorrected` (`MatedCRT/FirstPass/SLERef/Similarity.lean`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The scaled area measure `μ_{h^{(b)}}(A) = b⁻¹ μ_h(R_b A)`, in the Lean form of `rescaledMeasure`: the pushforward of `μ` by `x ↦ R⁻¹ x`, times `b⁻¹`. The image-set formula `μ.map (x ↦ R⁻¹ x) (A) = μ(R • A)` holds only for `R ≠ 0` (for `R = 0` the Lean inverse `0⁻¹ = 0` collapses the map, so the identity with `μ_h(R_b A)` fails); the source's `R_b` is a.s. positive, a point to be kept explicit in the input.
Truth check: the positivity of `R_b` is to be kept explicit in the input. -/
noncomputable def FPScaledMeasure (μ : Measure ℂ) (R b : ℝ) : Measure ℂ :=
  ENNReal.ofReal b⁻¹ • μ.map fun x => (R : ℂ)⁻¹ * x

end MatedCRT
