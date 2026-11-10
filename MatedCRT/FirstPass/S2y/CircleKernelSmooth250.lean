import MatedCRT.FirstPass.S2y.ConeDecoder250
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower1

/-!
# Smoothness of the circle kernel (fp-S2y-decoder-250, z8; chat 250 §1.2)

The circle kernel `circleKernel φ ε x = (2π)⁻¹ ∫₀^{2π} φ(x - ε e^{iθ}) dθ` of a test function is again a test function.
This is needed because the whole-plane GFF pairs only with test functions (`IsWholePlaneGFF.covariance_eq`). The
smoothness is the parametric-integral lemma `QuantumZipper.K3.contDiff_integral_comp_sub` (Lattice-Probability,
`GreenLower1.lean`, the package used by this repository), applied to the finite measure `circleMeasure250 ε`, the image of
the uniform measure on `(0, 2π]` under `θ ↦ circleMap 0 ε θ`.
-/

open MeasureTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ContDiff

namespace MatedCRT.LQGMeasure

/-- The uniform measure on the circle `∂B_ε(0)` (total mass `2π`), as a measure on `ℂ`: the image of Lebesgue measure
on `(0, 2π]` under `θ ↦ ε e^{iθ}`. -/
noncomputable def circleMeasure250 (ε : ℝ) : Measure ℂ :=
  Measure.map (fun θ : ℝ => circleMap 0 ε θ) (volume.restrict (Ioc (0 : ℝ) (2 * π)))

instance circleMeasure250_isFinite (ε : ℝ) : IsFiniteMeasure (circleMeasure250 ε) := by
  unfold circleMeasure250
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  infer_instance

/-- The circle kernel as an integral against the circle measure. -/
lemma circleKernel_eq_integral_circleMeasure250 {φ : ℂ → ℝ} (hφ : Continuous φ) (ε : ℝ) (x : ℂ) :
    circleKernel φ ε x = (2 * π)⁻¹ * ∫ y, φ (x - y) ∂(circleMeasure250 ε) := by
  unfold circleKernel circleMeasure250
  have hm : Continuous fun y : ℂ => φ (x - y) := hφ.comp (continuous_const.sub continuous_id)
  rw [integral_map (f := fun y : ℂ => φ (x - y)) (continuous_circleMap 0 ε).aemeasurable
    hm.aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le (by positivity)]

/-- **The circle kernel of a test function is smooth**, hence a test function up to compact support. -/
theorem circleKernel_contDiff250 {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) (ε : ℝ) :
    ContDiff ℝ ∞ (circleKernel φ ε) := by
  obtain ⟨hs, hc, -⟩ := hφ
  have hfun : circleKernel φ ε = fun x => (2 * π)⁻¹ * ∫ y, φ (x - id y) ∂(circleMeasure250 ε) := by
    funext x
    rw [circleKernel_eq_integral_circleMeasure250 hs.continuous ε x]
    rfl
  rw [hfun]
  refine contDiff_infty.mpr fun n => ?_
  exact contDiff_const.mul (QuantumZipper.K3.contDiff_integral_comp_sub (circleMeasure250 ε) continuous_id n hs hc)

end MatedCRT.LQGMeasure
