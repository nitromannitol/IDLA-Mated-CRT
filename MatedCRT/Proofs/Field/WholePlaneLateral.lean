import MatedCRT.Proofs.Field.WholePlaneBrownian
import MatedCRT.Proofs.Field.ConeRadialCov
import MatedCRT.Proofs.Field.ConeRadialSums

/-!
# Radial and lateral circle averages of a whole-plane GFF (eq:gff, circle level)

For a circle-average field `hcirc` (`h_r(z)`), write `V_u = h_{e^{-u}}(0)` for the radial process and
`A_{r,z} = ⨍_{∂B_r(z)} h_{|x|}(0) dx` for the radial circle average (the subtracted term of `lateralEval`), and
`L_{r,z} = h_r(z) - A_{r,z}` for the lateral circle average. This file collects the deterministic and kernel-level
facts used for the comparison of the cone with the whole-plane field (eq:gff):

* `wholePlaneGFFCov_circle_origin`: the whole-plane covariance of a circle at `z` and a circle at `0` is the circle
  average of the radial kernel `K(s, |x|)` (`radialCov`, Duplantier-Sheffield 2011, Section 3.1);
* `cov_circle_radV`: `Cov(h_r(z), V_u) = ⨍_{∂B_r(z)} K(e^{-u}, |x|)`;
* `radAvg_eq_levelIntegral`: for `r < |z|`, `A_{r,z}` is the level integral of the radial process over the circle
  parameter, `∫ V_{-log|z + r e^{iθ}|} dθ / 2π` (the input of `levelIntegral_versions`).
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls Real
open scoped NNReal
open MatedCRT.Field.ConeRadial

/-- The radial function `u ↦ h_{e^{-u}}(0)` of a sample of circle averages. -/
noncomputable def radV (hcirc : ℝ → ℂ → ℝ) (u : ℝ) : ℝ := hcirc (Real.exp (-u)) 0

/-- The radial circle average `A_{r,z} = ⨍_{∂B_r(z)} h_{|x|}(0) dx` (the subtracted term of `lateralEval`). -/
noncomputable def radAvg (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun x => hcirc ‖x‖ 0) z r

/-- The lateral circle average `L_{r,z} = h_r(z) - A_{r,z}` (`lateralEval (.circle r z)`). -/
noncomputable def latCirc (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  hcirc r z - radAvg hcirc r z

/-- The whole-plane covariance of the circle at `z` of radius `r` with the circle at `0` of radius `s > 0` is the
circle average of the radial kernel. -/
lemma wholePlaneGFFCov_circle_origin {r s : ℝ} (hs : 0 < s) (z : ℂ) :
    wholePlaneGFFCov (.circle r z) (.circle s 0) = Real.circleAverage (fun x => radialCov s ‖x‖) z r := by
  show Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) 0 s) z r = _
  congr 1
  funext x
  exact circleAverage_wholePlaneCov hs x

/-- `Cov(h_r(z), V_u) = ⨍_{∂B_r(z)} K(e^{-u}, |x|)`. -/
lemma cov_circle_radV {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) (u : ℝ) :
    covariance (fun ω => hcirc ω r z) (fun ω => radV (hcirc ω) u) P
      = Real.circleAverage (fun x => radialCov (Real.exp (-u)) ‖x‖) z r := by
  have h := hh.covariance_eq (.circle r z) (.circle (Real.exp (-u)) 0) hr (Real.exp_pos _)
  rw [wholePlaneGFFCov_circle_origin (Real.exp_pos _) z] at h
  exact h

/-- For `r < |z|` the circle avoids `0`, and the radial circle average is a level integral over the circle parameter
`θ ∈ (0, 2π]` of the radial process at the level `-log |z + r e^{iθ}|`. -/
lemma radAvg_eq_levelIntegral (hcirc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (hzr : r < ‖z‖) :
    radAvg hcirc r z = MatedCRT.Field.Level.levelIntegral (volume.restrict (Ioc (0 : ℝ) (2 * π)))
      (fun _ => (2 * π)⁻¹) (fun θ => -Real.log ‖circleMap z r θ‖) (fun u => radV hcirc u) := by
  have hpos : ∀ θ : ℝ, 0 < ‖circleMap z r θ‖ := by
    intro θ
    have h1 : ‖z‖ - r ≤ ‖circleMap z r θ‖ := by
      have h2 : ‖circleMap z r θ - z‖ = r := by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
      have h3 := norm_sub_norm_le z (circleMap z r θ)
      rw [norm_sub_rev] at h3
      linarith
    linarith
  unfold radAvg Real.circleAverage MatedCRT.Field.Level.levelIntegral radV
  rw [intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
  simp only [integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp only [neg_neg]
  rw [Real.exp_log (hpos θ)]

end MatedCRT.Field
