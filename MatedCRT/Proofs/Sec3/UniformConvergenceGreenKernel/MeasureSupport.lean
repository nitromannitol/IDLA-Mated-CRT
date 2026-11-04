import MatedCRT.Defs.Setting
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Full support of area-parametrized measures -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology

/-- A measure which parametrizes a continuous space-filling curve assigns
positive mass to every nonempty open set. -/
theorem IsAreaParametrized.isOpenPosMeasure {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) : μ.IsOpenPosMeasure := by
  constructor
  intro U hU ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := hη.2.2.1 x
  have ht : η ⁻¹' U ∈ 𝓝 t := (hU.preimage hη.1).mem_nhds hx
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hab : t - d / 2 < t + d / 2 := by linarith
  have hsub : η '' Icc (t - d / 2) (t + d / 2) ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    apply hball
    simp only [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  apply ne_of_gt
  calc
    0 < μ (η '' Icc (t - d / 2) (t + d / 2)) := by
      rw [hη.2.2.2 _ _ hab]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    _ ≤ μ U := measure_mono hsub

end MatedCRT
