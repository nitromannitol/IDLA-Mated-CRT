import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureInputs
import LatticeProb.LQG.GMCRatioLimitMeasure
import MatedCRT.FirstPass.S2VG.Literature

/-!
# The coordinate change rule of the γ-LQG measure: transport from the library form

`LQGMeasureCoordChange` (HB `Proposed/LQG.lean:131`) and its library copy
`LatticeProb.LQG.LQGMeasureCoordChangeLP` state the same property: for a whole-plane GFF `h^ℂ`, `0 < γ < 2`,
`α₀ < Q_γ` and a γ-LQG measure `μ` of `h^ℂ - α₀ log |·|`, almost surely for all `a ≠ 0` and `b` the push-forward of
`μ` under `x ↦ (x - b)/a` is the γ-LQG limit of the circle averages `ε, z ↦ h_{|a| ε}(a z + b) + Q_γ log |a|`
(Duplantier-Sheffield 2011, Proposition 2.1; Sheffield-Wang arXiv:1605.06171, Theorems 1.1 and 1.4).
The definitions match through the bridges `isWholePlaneGFF_iff`, `isLQGMeasureOfField_iff` and `isLQGLimit_iff`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory HarmonicBalls

/-- The library form `LQGMeasureCoordChangeLP` of the coordinate change rule gives the paper form
`LQGMeasureCoordChange`, for the same field, exponents and circle-average process. -/
theorem lqgMeasureCoordChange_of_LP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LatticeProb.LQG.LQGMeasureCoordChangeLP P γ α₀ hC hcirc) :
    LQGMeasureCoordChange P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hα μ hμ
  filter_upwards [h ((HarmonicBalls.LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG) hγ hγ2 hα μ
    ((HarmonicBalls.LPBridge.isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)] with ω hω a ha b
  exact (HarmonicBalls.LPBridge.isLQGLimit_iff _ _ _).2 (hω a ha b)

/-- The cited input `LitCoordChange` (the coordinate change rule of the γ-LQG measure of a whole-plane GFF, `α₀ = 0`;
Duplantier-Sheffield 2011, Proposition 2.1) holds: it is the library theorem `lqgMeasureCoordChangeLP_zero`
(the circle-average approximations along every ratio sequence `r 2^{-k}` converge to the same γ-LQG measure),
transported to the paper form. -/
theorem litCoordChange_holds : MatedCRT.S2VG.LitCoordChange := fun _ _ P γ hC hcirc =>
  lqgMeasureCoordChange_of_LP P γ 0 hC hcirc (LatticeProb.LQG.lqgMeasureCoordChangeLP_zero P γ hC hcirc)

end MatedCRT.FirstPass.Derived
