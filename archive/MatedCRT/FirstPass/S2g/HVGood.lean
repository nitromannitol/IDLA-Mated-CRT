import MatedCRT.FirstPass.S2e
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw

/-! # The volume-growth input `hvgood` of the S2e reduction, derived

`hvgood` (`FirstPass/S2e.lean:225`) asks for the a.s. volume growth of the rescaled measures at radius `3/4`. It is the
instance `R = 3/4` of `IsConeField.ae_rescaledVolumeGrowth_inside_unit` (`Proofs/Sec2/ConeFamilyMeasurable/MeasureLaw.lean:98`),
which uses only `VolumeGrowthStmt` (Lemma 2.7), the cone scaling `QuantumConeScalingInput` and `ConeLQGScalingStep`. So `hvgood`
is not an extra hypothesis: it follows from the same inputs as the reduction. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls

/-- **`hvgood` from the volume-growth input and the cone scaling.** For every cone field and every `b > 0`, almost
surely the rescaled measure at the random radius `coneScaleRadius γ (hcirc ω) b` has volume growth at radius `3/4`. -/
theorem hvgood_of_volumeGrowth (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → ∀ b : ℝ, 0 < b →
      ∀ᵐ ω ∂P, ∃ βminus βplus, VolumeGrowth
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (3 / 4) βminus βplus := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  exact hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg hb (by norm_num) (by norm_num)

end MatedCRT
