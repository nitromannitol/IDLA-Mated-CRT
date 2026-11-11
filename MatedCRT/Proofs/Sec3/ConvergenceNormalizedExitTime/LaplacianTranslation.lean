import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredNormalizedPotential
import MatedCRT.LPStaging.Analysis.LaplacianCalculus

/-! Translation of test functions and the planar Laplacian. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set Laplacian _root_.HarmonicBalls

/-- The planar Laplacian commutes with translation. -/
theorem laplacian_comp_add_right (f : ℂ → ℝ) (z x : ℂ) :
    Δ (fun w => f (w + z)) x = Δ f (x + z) :=
  LatticeProb.LaplacianCalculus.laplacian_comp_add_right f z x

/-- Translating a test function on a ball yields a test function on the
corresponding centered ball. -/
theorem isTestFunction_ball_comp_add {φ : ℂ → ℝ} {z : ℂ} {r : ℝ}
    (hφ : IsTestFunction (ball z r) φ) :
    IsTestFunction (ball (0 : ℂ) r) (fun w => φ (w + z)) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight z
  have he : (fun w : ℂ => φ (w + z)) = φ ∘ e := rfl
  refine ⟨hφ.1.comp (by fun_prop), ?_, ?_⟩
  · rw [he]
    exact hφ.2.1.comp_homeomorph e
  · rw [he, tsupport_comp_eq_preimage]
    intro x hx
    have hx' := hφ.2.2 hx
    simpa [e, mem_ball, dist_eq_norm] using hx'

/-- A weak Laplacian identity on the centered ball transports to a translated
ball when the potential is continuous and the measure is locally finite. -/
theorem hasLaplacian_of_centered_translate
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {q : ℂ → ℝ} {z : ℂ} {r : ℝ}
    (hqc : ContinuousOn q (closedBall z r))
    (hq : HasLaplacian (fun x => q (x + z)) 0
      (Measure.map (fun x : ℂ => x - z) μ) (ball 0 r)) :
    HasLaplacian q 0 μ (ball z r) := by
  refine ⟨(hqc.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ => ?_⟩
  refine ⟨integrable_zero_measure, hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1, ?_⟩
  have htest := isTestFunction_ball_comp_add hφ
  obtain ⟨_, _, heq⟩ := hq.2 (fun x => φ (x + z)) htest
  have hmap : (∫ x, φ (x + z) ∂Measure.map (fun x : ℂ => x - z) μ) =
      ∫ x, φ x ∂μ := by
    have hf : (fun x : ℂ => x - z) = (Homeomorph.addRight (-z) : ℂ → ℂ) := by
      funext x
      simp [sub_eq_add_neg]
    rw [hf, (Homeomorph.addRight (-z)).isClosedEmbedding.integral_map]
    simp [← sub_eq_add_neg]
  have hpair : (∫ x, q (x + z) * Δ (fun w => φ (w + z)) x) =
      ∫ x, q x * Δ φ x := by
    simp_rw [laplacian_comp_add_right]
    exact integral_add_right_eq_self (fun x => q x * Δ φ x) z
  rw [integral_zero_measure, zero_sub, hmap, hpair] at heq
  simpa only [integral_zero_measure, zero_sub] using heq

end MatedCRT
