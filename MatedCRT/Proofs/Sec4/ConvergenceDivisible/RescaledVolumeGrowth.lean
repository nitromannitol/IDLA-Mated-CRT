import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthComparison
import MatedCRT.Steps.Sec1.Convergence
import HarmonicBalls.Proofs.Sec2.AffineField

/-! # Volume growth and the rescaled quantum-cone measure -/

namespace MatedCRT

open MeasureTheory Metric Set HarmonicBalls

/-- The mass of a ball under a positive dilation and mass rescaling. -/
theorem rescaledMeasure_ball (μ : Measure ℂ) {s : ℝ} (hs : 0 < s)
    (b : ℝ) (z : ℂ) (r : ℝ) :
    rescaledMeasure μ s b (ball z r) =
      (ENNReal.ofReal b)⁻¹ * μ (ball ((s : ℂ) * z) (s * r)) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold rescaledMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  congr 1
  simpa [div_eq_mul_inv, mul_comm, Complex.norm_real, Real.norm_of_nonneg hs.le] using
    map_affine_ball μ hs' 0 z r

/-- Growth for the rescaled measure on a ball transfers to the original
measure on the corresponding dilated ball, with slack in the exponents. -/
theorem volumeGrowth_of_rescaledMeasure
    {μ : Measure ℂ} {s b R βm βp : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hV : VolumeGrowth (rescaledMeasure μ s b) R βm βp) :
    VolumeGrowth μ (s * R) (βm + 1) (βp / 2) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  apply volumeGrowth_of_scaled_ballMass_comparison hV hb hb.le (inv_pos.mpr hs)
    (f := fun z => (s : ℂ)⁻¹ * z)
  · intro z hz
    simp only [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have h : ‖z‖ / s < R := (div_lt_iff₀ hs).mpr (by simpa [mul_comm] using hz)
    simpa [div_eq_inv_mul] using h
  · refine ⟨1, by norm_num, fun r hr hr1 z hz => ?_⟩
    have heq : ENNReal.ofReal b *
        rescaledMeasure μ s b (ball ((s : ℂ)⁻¹ * z) (s⁻¹ * r)) = μ (ball z r) := by
      rw [rescaledMeasure_ball μ hs b, mul_inv_cancel_left₀ hs', mul_inv_cancel_left₀ hs.ne']
      rw [← ENNReal.ofReal_inv_of_pos hb, ← mul_assoc,
        ← ENNReal.ofReal_mul hb.le, mul_inv_cancel₀ hb.ne', ENNReal.ofReal_one, one_mul]
    exact ⟨le_of_eq heq, le_of_eq heq.symm⟩

end MatedCRT
