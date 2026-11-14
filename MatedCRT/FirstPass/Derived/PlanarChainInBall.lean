import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import LatticeProb.Prob.BrownianChainInBall

/-!
# Chains of displacement times of planar Brownian motion inside a ball

Tightness of the number of steps for planar Brownian motion, in the scaled form used for chained exits:
for `0 < ζ < 1` and `p ∈ ℕ` there is `C` such that for every starting point `z`, every scale `a > 0` and
every `0 < r < 1`, with probability at least `1 - C r ^ p` no nondecreasing chain of times
`τ 0 ≤ τ 1 ≤ ⋯` whose first `K = ⌊r ^ -(2 + ζ)⌋` increments of planar Brownian motion started at `z` have
modulus at least `2 a r` has `‖b t - z‖ < a` for all `t ≤ τ K`.

It is the planar form (via the half-speed parametrisation `t ↦ b (t / 2) - z` and the chain `2 τ`) of the
chain estimate of Lattice-Probability.

## Main statement
* `planarBrownianMotion_separated_chain_in_ball_superpoly`.
-/

namespace MatedCRT.PlanarChainInBall

open Set MeasureTheory _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **Chains of separated times inside a ball, planar Brownian motion.** -/
theorem planarBrownianMotion_separated_chain_in_ball_superpoly {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (p : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (a : ℝ), 0 < a → ∀ r : ℝ, 0 < r → r < 1 →
      planarBrownianMotion z {b | ∃ τ : ℕ → ℝ≥0, Monotone τ ∧
          (∀ n < ⌊r ^ (-(2 + ζ))⌋₊, 2 * (a * r) ≤ ‖b (τ (n + 1)) - b (τ n)‖) ∧
          ∀ t ≤ τ ⌊r ^ (-(2 + ζ))⌋₊, ‖b t - z‖ < a}
        ≤ ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨C, hC⟩ :=
    LatticeProb.measure_separated_chain_in_ball_superpoly_scaled.{0} 2 two_pos hζ0 hζ1 p
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
  rintro b ⟨τ, hτ, hsep, hin⟩
  have e : ∀ s : ℝ≥0, (2⁻¹ : ℝ≥0) * (2 * s) = s := fun s => by
    rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero' ℝ≥0), one_mul]
  refine ⟨fun n => 2 * τ n, fun m n hmn => mul_le_mul_of_nonneg_left (hτ hmn) (by positivity),
    fun n hn => ?_, fun t ht => ?_⟩
  · have h2 := hsep n hn
    simp only [PlanarBrownianSpace.halfSpeedPath, ← map_sub, LinearIsometryEquiv.norm_map,
      sub_sub_sub_cancel_right, e]
    exact h2
  · rw [PlanarBrownianSpace.norm_halfSpeedPath]
    refine hin _ ?_
    calc (2⁻¹ : ℝ≥0) * t ≤ 2⁻¹ * (2 * τ ⌊r ^ (-(2 + ζ))⌋₊) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = τ ⌊r ^ (-(2 + ζ))⌋₊ := e _

end MatedCRT.PlanarChainInBall
