import MatedCRT.FirstPass.Derived.ConeReferenceLQG

/-! # Reference cone area on a common sample space -/

open MeasureTheory Set HarmonicBalls MarkovProcess

namespace MatedCRT.FirstPass.Derived

/-- The continuous radial correction transports an LQG limit on the same
sample space, for any path chosen on that space. -/
theorem isLQGMeasure_coneRef_of_same_space
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {c : Ω → ℝ → ℂ → ℝ} {w : Ω → ContinuousPath ℝ} {μ : Ω → Measure ℂ}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hμ : IsLQGMeasureOfField P γ γ c μ) :
    IsLQGMeasure P γ (fun ω => coneRefCircle γ (c ω) (w ω))
      (fun ω => coneRefMeasure γ (c ω) (w ω) (μ ω)) := by
  filter_upwards [hc, hμ] with ω hcω hμω
  exact isLQGLimit_coneRef γ hcω (w ω) hμω

end MatedCRT.FirstPass.Derived
