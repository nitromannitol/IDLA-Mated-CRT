import MatedCRT.FirstPass.Derived.UniformStartVariableRadiusTransfer

/-!
# Transfer of curve-law bounds via radius selection

A one-sided bound for a curve comparison function transfers to paths stopped on a fixed disc
when small comparison values give close stopped paths on some sufficiently large disc.
-/

open Set Metric MeasureTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- A radius-selection rule transfers an all-set curve-law bound to a fixed disc. -/
theorem exists_forall_stopAtExit_le_of_radius_selection {Ω : Type*} [MeasurableSpace Ω]
    {ρ R κ : ℝ} (hρR : ρ < R) (hκ : 0 < κ) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) ρ, ∀ (ν : Measure Ω) (W : Ω → ℝ≥0 → ℂ),
      (∀ w, Continuous (W w)) →
      ∀ (D : (ℝ≥0 → ℂ) → (ℝ≥0 → ℂ) → ℝ≥0∞) (t : ℝ≥0∞),
      (∀ g b, D g b < t → ∃ r : ℝ, R + κ < r ∧
        cmpEDist (stopAtExit (ball (0 : ℂ) r) g) (stopAtExit (ball (0 : ℂ) r) b) < ENNReal.ofReal δ) →
      (∀ S : Set (ℝ≥0 → ℂ), ν {w | W w ∈ S} ≤
        planarBrownianMotion z {b | ∃ g ∈ S, D g ⇑b < t} + ENNReal.ofReal δ) →
      ∀ A : Set (ℝ≥0 → ℂ), ν {w | stopAtExit (ball (0 : ℂ) R) (W w) ∈ A} ≤
        planarBrownianMotion z
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) R) ⇑b) f < ENNReal.ofReal ε} +
          ENNReal.ofReal θ := by
  obtain ⟨δ, hδ, htransfer⟩ := exists_forall_stopAtExit_le_of_forall_le_variable (Ω' := Ω) hρR hκ hε hθ
  refine ⟨δ, hδ, fun z hz ν W hW D t hselect hbound => htransfer z hz ν W hW ?_⟩
  intro S
  exact (hbound S).trans (add_le_add (measure_mono (fun b ⟨g, hg, hD⟩ =>
    ⟨g, hg, hselect g ⇑b hD⟩)) le_rfl)

end MatedCRT.StopAtExitCmp
