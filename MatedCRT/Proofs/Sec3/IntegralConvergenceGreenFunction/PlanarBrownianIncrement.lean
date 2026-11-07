import MarkovProcess.Examples.BrownianMotion
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathOccupationEnergy

/-! # Gaussian increments of planar Brownian motion -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess HarmonicBalls
open scoped NNReal

/-- An increment of standard planar Brownian motion has the centered planar
Gaussian law with covariance equal to the elapsed time. -/
theorem planarBrownianMotion_map_increment (z : ℂ) (s t : ℝ≥0) (hst : s ≤ t) :
    (planarBrownianMotion z).map (fun b => b t - b s) = planarGaussian 0 (t - s) := by
  let F : ContinuousPath ℝ → ℝ := fun b => b t - b s
  let G : ContinuousPath ℝ × ContinuousPath ℝ → ℝ × ℝ := fun p => (F p.1, F p.2)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := (hF.comp measurable_fst).prodMk (hF.comp measurable_snd)
  have hC : Measurable (fun b : ContinuousPath ℂ => b t - b s) := by fun_prop
  have hcomm : (fun b : ContinuousPath ℂ => b t - b s) ∘ complexPathOfReIm =
      Complex.measurableEquivRealProd.symm ∘ G := by
    funext p
    apply Complex.ext <;> simp [G, F, complexPathOfReIm_apply]
  rw [planarBrownianMotion_apply, Measure.map_map hC measurable_complexPathOfReIm,
    hcomm, ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable hG,
    show G = Prod.map F F from rfl, ← Measure.map_prod_map _ _ hF hF]
  simp only [F, brownianMotion_map_increment _ _ _ hst, planarGaussian,
    Complex.zero_re, Complex.zero_im]

/-- The expected Riesz kernel of a planar Brownian increment is the
corresponding integral against its centered planar Gaussian law. -/
theorem planarBrownianMotion_expected_increment_energy (z : ℂ) (s t : ℝ≥0)
    (hst : s ≤ t) (a : ℝ) :
    (∫⁻ b, rieszEnergyKernel a (b t) (b s) ∂(planarBrownianMotion z)) =
      ∫⁻ w, rieszEnergyKernel a w 0 ∂(planarGaussian 0 (t - s)) := by
  have hk : Measurable (fun w : ℂ => rieszEnergyKernel a w 0) :=
    (measurable_rieszEnergyKernel a).comp (measurable_id.prodMk measurable_const)
  have hinc : Measurable (fun b : ContinuousPath ℂ => b t - b s) := by fun_prop
  rw [← planarBrownianMotion_map_increment z s t hst, lintegral_map hk hinc]
  apply lintegral_congr
  intro b
  simp [rieszEnergyKernel, dist_eq_norm]

end MatedCRT
