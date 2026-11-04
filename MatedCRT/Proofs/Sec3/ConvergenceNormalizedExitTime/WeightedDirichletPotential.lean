import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.WeightedPotential
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.WeightedSourceMeasure
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GeneralPotentialTranslation
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GeneralPotentialContinuity

/-! Green representation for the buffered-bump Dirichlet source. -/

namespace MatedCRT

open MeasureTheory Metric Filter Set Laplacian _root_.HarmonicBalls
open scoped ENNReal

/-- The weighted Green potential satisfies the continuum Dirichlet problem
for a bounded nonnegative source on any ball. -/
theorem weightedGreenPotential_satisfies_dirichlet
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {r r₀ β c : ℝ} {z : ℂ}
    (hr : 0 < r) (hr₀ : 0 < r₀) (hβ : 0 < β) (hc : 0 ≤ c)
    (hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball z r,
      μ (ball x s) ≤ ENNReal.ofReal (s ^ β))
    (φ : ℂ → ℝ) (hφm : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ1 : ∀ x, φ x ≤ 1) :
    let q := fun x => c * ∫ y in ball z r, greenFunction (ball z r) x y * φ y ∂μ
    ContinuousOn q (closedBall z r) ∧
      HasLaplacian q (μ.withDensity fun x => ENNReal.ofReal (c * -φ x))
        (μ.withDensity fun x => ENNReal.ofReal (-(c * -φ x))) (ball z r) ∧
      ∀ x ∈ sphere z r, q x = 0 := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (φ x))
  have hle : ν ≤ μ := withDensity_ofReal_le_of_le_one μ φ hφ1
  let : IsLocallyFiniteMeasure ν := Measure.isLocallyFiniteMeasure_of_le hle
  have hνup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball z r,
      ν (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hs₀ x hx
    exact (hle _).trans (hup s hs hs₀ x hx)
  have hcont := ballGreenPotential_continuousOn_of_upper ν hr hr₀ hβ hνup
  have hlap := ballGreenPotential_hasLaplacian_of_upper ν hr hr₀ hβ hνup hcont
  have heq (x : ℂ) : (∫ y in ball z r, greenFunction (ball z r) x y ∂ν) =
      ∫ y in ball z r, greenFunction (ball z r) x y * φ y ∂μ := by
    change (∫ y in ball z r, greenFunction (ball z r) x y
      ∂μ.withDensity (fun y => ENNReal.ofReal (φ y))) = _
    have hm : Measurable (fun y : ℂ => ENNReal.ofReal (φ y)) :=
      ENNReal.measurable_ofReal.comp hφm
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_ball]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    simp [ENNReal.toReal_ofReal (hφ0 y), smul_eq_mul, mul_comm]
  have hfun : (fun x => c * ∫ y in ball z r, greenFunction (ball z r) x y ∂ν) =
      (fun x => c * ∫ y in ball z r, greenFunction (ball z r) x y * φ y ∂μ) := by
    funext x
    rw [heq]
  have hscaled := hasLaplacian_const_mul_zero_left hlap hc
  rw [hfun] at hscaled
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfun]
    exact hcont.const_mul c
  · rw [negativeBump_positive_source_eq_zero μ hc φ hφ0,
      negativeBump_negative_source_eq_smul μ hc φ hφm]
    exact hscaled
  · intro x hx
    have hx' : x ∉ ball z r := by
      rw [mem_sphere] at hx
      rw [mem_ball]
      linarith
    simp [greenFunction_of_notMem_left hx']

end MatedCRT
