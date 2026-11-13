import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# Dilation of distributional circle averages

The deterministic part of the circle identification in env-steps.tex:325–330.
The imported circle mollifier and affine test are from Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open HarmonicBalls
open LQGMetric LQGMetric.CircleAvg

namespace MatedCRT.Sec1

/-- The mollified circle of a dilated distribution is its pairing with the
correspondingly dilated circle test. -/
theorem mollAvg_affineComp_zero (H : DistC) (R r : ℝ) (z : ℂ) (n : ℕ) :
    mollAvg (affineComp R 0 H) n z r = H (affTest R 0 (circBump n z r)) := by
  rw [mollAvg_eq, affTest, map_smul, smul_eq_mul]
  rfl

/-- A convergent family of dilated circle tests recovers the circle average of
the dilated and shifted distribution, for any distribution and any shift. -/
theorem circleAvg_rescaledDistribution_of_tendsto
    (γ b R r : ℝ) (H : DistC) (z : ℂ) (a : ℝ)
    (h : Tendsto (fun n => H (affTest R 0 (circBump n z r))) atTop (𝓝 a)) :
    circleAvg (rescaledDistribution γ b H R) r z =
      a + (lqgQ γ * Real.log R - γ⁻¹ * Real.log b) := by
  apply circleAvg_eq_of_tendsto
  simp only [rescaledDistribution, mollAvg_addConst, mollAvg_affineComp_zero]
  exact h.add_const _

end MatedCRT.Sec1
