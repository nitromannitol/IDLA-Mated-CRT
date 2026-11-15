import MatedCRT.FirstPass.Derived.ConeReferenceData
import LatticeProb.Analysis.TestFunctionLogIntegrable
import LatticeProb.LQG.ConeReplacementPairing

/-! # Reference cone pairings for arbitrary tests -/

noncomputable section

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- Combine the logarithmic and continuous radial corrections in a reference
cone pairing, for a test function with arbitrary compact support. -/
theorem coneRefPairing_eq_integral_correction
    (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (c : ℝ → ℂ → ℝ) (w : C(ℝ≥0, ℝ))
    (hc : ContinuousOn (fun r => c r 0) (Ioi 0))
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    coneRefPairing γ hC c w φ = hC φ +
      ∫ z, φ z * (γ * (-Real.log ‖z‖) + coneRefField c w z) := by
  have hlog : Integrable (fun z : ℂ => φ z * (γ * (-Real.log ‖z‖))) := by
    have h := (LatticeProb.TestFunctionLogIntegrable.integrable_test_mul_log_norm hφ).const_mul (-γ)
    convert h using 1
    funext z
    ring
  have hrad : Integrable (fun z : ℂ => φ z * coneRefField c w z) :=
    (hφ.1.continuous.mul (continuous_coneRefField hc w)).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have heq : (fun z : ℂ => φ z * (γ * (-Real.log ‖z‖) + coneRefField c w z)) =
      fun z => φ z * (γ * (-Real.log ‖z‖)) + φ z * coneRefField c w z := by
    funext z
    ring
  rw [heq, integral_add hlog hrad, coneRefPairing, fieldPairing]
  have hint : (∫ z, φ z * (γ * (-Real.log ‖z‖))) =
      -γ * ∫ z, φ z * Real.log ‖z‖ := by
    have he : (fun z : ℂ => φ z * (γ * (-Real.log ‖z‖))) =
        fun z => (-γ) * (φ z * Real.log ‖z‖) := by
      funext z
      ring
    rw [he, integral_const_mul]
  rw [hint]
  ring

/-- A distribution with the same base field and the combined radial
correction has the reference cone pairings on all tests. -/
theorem coneRefPairing_eq_of_field_decomposition
    (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (c : ℝ → ℂ → ℝ) (w : C(ℝ≥0, ℝ))
    (Y H : LQGMetric.DistC) (g : ℂ → ℝ)
    (hc : ContinuousOn (fun r => c r 0) (Ioi 0))
    (hhC : ∀ φ : LQGMetric.TestC, hC φ = Y φ)
    (hg : LocallyIntegrable g volume)
    (hdec : H = Y + MatedCRTHarmonic.MoTPort.ofFunC g)
    (heq : g =ᵐ[volume] fun z => γ * (-Real.log ‖z‖) + coneRefField c w z) :
    ∀ φ : LQGMetric.TestC, coneRefPairing γ hC c w φ = H φ := by
  intro φ
  have hφ : IsTestFunction univ (φ : ℂ → ℝ) :=
    ⟨φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
  rw [coneRefPairing_eq_integral_correction γ hC c w hc hφ, hhC φ, hdec,
    add_apply, MatedCRTHarmonic.MoTPort.ConeCirc.ofFunC_apply' hg]
  congr 1
  apply integral_congr_ae
  filter_upwards [heq] with z hz
  rw [hz]

end MatedCRT.FirstPass.Derived
