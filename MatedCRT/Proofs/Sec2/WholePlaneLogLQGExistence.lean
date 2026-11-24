import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Proofs.Field.WholePlaneExistence
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-!
# The LQG measure of the whole-plane GFF with a `γ`-log singularity

`WholePlaneLogLQGExistenceStep`, the existence step of Lemma 2.4: for `γ ∈ (0, 2)` there is a probability space with a
whole-plane GFF `h^ℂ` and the `γ`-LQG measure of `h^ℂ - γ log |·|`. The field is `MatedCRT.Field.wholePlaneGFF_exists`
and the measure is `HarmonicBalls.lqgMeasureExistence_derived` at the insertion `α₀ = γ`, which is below `Q`.

## Main statements

* `wholePlaneLogLQGExistenceStep_holds`.
-/

open MeasureTheory HarmonicBalls

namespace MatedCRT

/-- **A whole-plane GFF with the `γ`-LQG measure of `h^ℂ - γ log |·|` exists** for every `γ ∈ (0, 2)`. -/
theorem wholePlaneLogLQGExistenceStep_holds : WholePlaneLogLQGExistenceStep := by
  intro γ hγ hγ2
  obtain ⟨Ω, mΩ, P, hC, hcirc, hP, hG⟩ := MatedCRT.Field.wholePlaneGFF_exists
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P γ γ hC hcirc hG hγ hγ2 (gamma_lt_lqgQ hγ hγ2)
  exact ⟨Ω, mΩ, P, hC, hcirc, μ, hP, hG, hμ⟩

end MatedCRT
