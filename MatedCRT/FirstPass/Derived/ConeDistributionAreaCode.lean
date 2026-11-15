import MatedCRT.FirstPass.Derived.ConeRadialUniform

/-! # Recovery of cone area from a matching distribution -/

noncomputable section

open MeasureTheory
open HarmonicBalls

namespace MatedCRT

/-- A universal measurable decoder recovers the area measure of a quantum cone
from any distribution whose test pairings agree with the cone on one event. -/
theorem exists_measurable_distribution_coneArea (γ : ℝ) :
    ∃ M : LQGMetric.DistC → Measure ℂ, Measurable M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {μ : Ω → Measure ℂ}
        {H : Ω → LQGMetric.DistC},
        IsQuantumCone γ S.P S.hC S.hcirc → IsLQGMeasure S.P γ S.hcirc μ →
        (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
        ∀ᵐ ω ∂S.P, M (H ω) = μ ω := by
  obtain ⟨M, hM, hrec⟩ := exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone γ
  refine ⟨M ∘ pairingCodeOf, hM.comp measurable_pairingCodeOf, ?_⟩
  intro Ω _ S μ H hcone hμ hH
  filter_upwards [hrec hcone hμ, hH] with ω hrecω hHω
  have heq : fieldPairingCode S ω = pairingCodeOf (H ω) := by
    funext φ
    exact hHω (MatedCRT.Field.toTestC φ.2)
  change M (pairingCodeOf (H ω)) = μ ω
  rw [← heq]
  exact hrecω

end MatedCRT
