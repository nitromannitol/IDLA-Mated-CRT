import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine

/-!
# Dilation of distributional circle averages

The deterministic part of the circle identification in env-steps.tex:325–330.
The approximation boundary below isolates the passage from the represented
field and its continuous circles to dilated mollifiers on one common event.
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

/-- The unresolved distribution-circle approximation passage: for a cone,
all positive dilations of the countable grid-circle mollifiers recover the
supplied continuous circles on one event. This is a convergence statement
about test pairings, with no random scale or distribution-law assumption. -/
def ConeDilationCircleApproximationStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsQuantumCone γ P hC hcirc →
      ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ n m : ℕ, ∀ k a d : ℤ, 0 < k →
        Tendsto (fun j => hC ω (affTest R 0
          (circBump j (FieldCircle.gridPt m a d) ((k : ℝ) / 2 ^ n)))) atTop
          (𝓝 (hcirc ω (R * ((k : ℝ) / 2 ^ n)) (R * FieldCircle.gridPt m a d)))

/-- The simultaneous approximation passage implies the fixed-grid step,
including for arbitrary supplied representatives and a random positive scale. -/
theorem rescaledConeDistributionCircleGridStep_of_approximation
    (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (happrox : ConeDilationCircleApproximationStep) :
    RescaledConeDistributionCircleGridStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb H R hHm hRm hrep hR
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have hp := ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  filter_upwards [happrox γ hγ hγ2 Ω S.P S.hC S.hcirc hS.isQuantumCone,
    hrep, hR, hp] with ω ha hrepω hRω hpω
  intro n m k a d hk
  have hpos : 0 < R ω := hRω ▸ hpω
  have ht := ha (R ω) hpos n m k a d hk
  have ht' : Tendsto (fun j => H ω (affTest (R ω) 0
      (circBump j (FieldCircle.gridPt m a d) ((k : ℝ) / 2 ^ n)))) atTop
      (𝓝 (S.hcirc ω (R ω * ((k : ℝ) / 2 ^ n))
        (R ω * FieldCircle.gridPt m a d))) := by
    apply ht.congr
    intro j
    exact hrepω _
  rw [circleAvg_rescaledDistribution_of_tendsto γ b (R ω) _ (H ω) _ _ ht']
  simp only [rescaledCircle]
  ring

end MatedCRT.Sec1
