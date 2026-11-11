import MatedCRT.Defs.GaussianMultiplicativeChaos

/-! # Circle-average clock and GMC normalization -/

namespace MatedCRT

open MeasureTheory

/-- A circle average whose variance is `log (1 / ε)` has exactly the
normalization used in the LQG clock. -/
theorem varianceNormalized_exp_eq_clock_density (γ ε x : ℝ) (hε : 0 < ε) :
    Real.exp (γ * x - (γ ^ 2 / 2) * Real.log ε⁻¹) =
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * x) := by
  rw [Real.log_inv, Real.rpow_def_of_pos hε, ← Real.exp_add]
  congr 1
  ring

/-- If circle-average variance is `log (1 / ε)`, variance-normalized GMC
is the reference measure weighted by the LQG clock density. -/
theorem gmcApprox_eq_clock_density {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (σ : Measure E) (γ ε : ℝ) (hε : 0 < ε)
    (H : Ω → E → ℝ)
    (hvar : ∀ x, (∫ ω, (H ω x) ^ 2 ∂P) = Real.log ε⁻¹) (ω : Ω) :
    gmcApprox P σ γ H ω = σ.withDensity (fun x => ENNReal.ofReal
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ω x))) := by
  unfold gmcApprox
  congr 1
  funext x
  rw [hvar x, varianceNormalized_exp_eq_clock_density γ ε (H ω x) hε]

end MatedCRT
