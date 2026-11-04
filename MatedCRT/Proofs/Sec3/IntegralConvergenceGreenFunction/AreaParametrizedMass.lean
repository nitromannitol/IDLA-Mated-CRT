import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TestFunctionTightness

/-! Positive mass of open sets for area-parametrized space-filling curves. -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- Every nonempty open set has positive mass when a continuous surjective
curve is parametrized by the measure of its time intervals. -/
theorem IsAreaParametrized.measure_open_pos {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ U := by
  obtain ⟨x, hxU⟩ := hne
  obtain ⟨t, rfl⟩ := hη.2.2.1 x
  have hpre : IsOpen (η ⁻¹' U) := hU.preimage hη.1
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hpre t hxU
  have hsub : η '' Icc (t - δ / 2) (t + δ / 2) ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    apply hδsub
    rw [mem_ball, Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hmass := hη.2.2.2 (t - δ / 2) (t + δ / 2) (by linarith)
  have hpos : 0 < μ (η '' Icc (t - δ / 2) (t + δ / 2)) := by
    rw [hmass, ENNReal.ofReal_pos]
    linarith
  exact hpos.trans_le (measure_mono hsub)

end MatedCRT
