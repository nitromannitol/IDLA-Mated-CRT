import MatedCRT.FirstPass.S6j.ExitTailCombine
import LatticeProb.Prob.BrownianStayScaled

/-!
# Planar Brownian motion stays in a ball up to a displacement time only with superpolynomially small probability

[BG20, (6.22)] for planar Brownian motion, in the scaled form used in the proof of Lemma 6.10: for `0 < ζ < 1` and
`p ∈ ℕ` there is `C` such that for every starting point `z`, every scale `a > 0` and every `0 < r < 1`, planar Brownian
motion started at `z` stays in `B_a(z)` up to its `K`-th displacement time of size `a r`, `K = ⌊r ^ -(2 + ζ)⌋`, with
probability at most `C r ^ p`. It is the planar form (via the half-speed parametrisation) of the Brownian estimate of
Lattice-Probability.
-/

namespace MatedCRT.ExitTailUpperBrownian

open Set MeasureTheory _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **[BG20, (6.22)] for planar Brownian motion.** -/
theorem planarBrownianMotion_stays_by_stepTime_superpoly {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (a : ℝ), 0 < a → ∀ r : ℝ, 0 < r → r < 1 →
      planarBrownianMotion z {b | ∀ t : ℝ≥0, (t : ℝ≥0∞) <
          LatticeProb.stepTime (⇑b) (a * r) ⌊r ^ (-(2 + ζ))⌋₊ → ‖b t - z‖ < a}
        ≤ ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ := LatticeProb.measure_stays_in_ball_superpoly_scaled.{0} 2 two_pos hζ0 hζ1 p
  refine ⟨C, fun z a ha r hr0 hr1 => ?_⟩
  have hB := PlanarBrownianSpace.isBrownianSpace_halfSpeedPath z
  set a' : ℝ≥0 := ⟨a, ha.le⟩ with ha'
  set r' : ℝ≥0 := ⟨r, hr0.le⟩ with hr'
  have haa : (a' : ℝ) = a := rfl
  have hrr : (r' : ℝ) = r := rfl
  have h1 := hC _ (planarBrownianMotion z) _ hB a' (NNReal.coe_pos.mp (by rw [haa]; exact ha)) r'
    (NNReal.coe_pos.mp (by rw [hrr]; exact hr0)) (NNReal.coe_lt_one.mp (by rw [hrr]; exact hr1))
  rw [haa, hrr] at h1
  refine le_trans (measure_mono ?_) h1
  intro b hbS s hs
  let φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (2⁻¹ : ℝ≥0) (by norm_num)
  have hφ : ∀ t, φ t = 2⁻¹ * t := fun _ => rfl
  have hcongr : ∀ k, LatticeProb.stepTime (fun t => PlanarBrownianSpace.halfSpeedPath z t b) (a * r) k =
      LatticeProb.stepTime (⇑b ∘ φ) (a * r) k :=
    ExitTailCombine.stepTime_eq_of_norm_sub_eq (fun s t => by
      simp only [PlanarBrownianSpace.halfSpeedPath, Function.comp_apply, hφ, ← map_sub,
        LinearIsometryEquiv.norm_map, sub_sub_sub_cancel_right]) _
  rw [hcongr, LatticeProb.coe_lt_stepTime_comp_iff] at hs
  rw [PlanarBrownianSpace.norm_halfSpeedPath]
  exact hbS (φ s) hs

end MatedCRT.ExitTailUpperBrownian
