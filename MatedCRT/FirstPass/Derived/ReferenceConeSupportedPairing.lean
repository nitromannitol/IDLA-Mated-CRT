import MatedCRT.FirstPass.Derived.CouplingReferenceCone

/-! # Reference cone pairings on the unit disk -/

noncomputable section

open MeasureTheory HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- A reference cone agrees with its logarithmically shifted base field on
    every test supported in the closed unit disk. -/
theorem coneRefPairing_eq_field_add_log_of_supported
    (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (c : ℝ → ℂ → ℝ) (w : C(ℝ≥0, ℝ))
    (φ : LQGMetric.TestC) (hφ : ∀ z : ℂ, 1 < ‖z‖ → φ z = 0) :
    coneRefPairing γ hC c w φ = hC φ + ∫ z, φ z * (γ * (-Real.log ‖z‖)) := by
  have hzero : (fun z : ℂ => φ z * coneRefField c w z) = 0 := by
    funext z
    by_cases hz : ‖z‖ ≤ 1
    · simp only [Pi.zero_apply, coneRefField, coneRefProfile_of_le hz, mul_zero]
    · simp only [Pi.zero_apply, hφ z (lt_of_not_ge hz), zero_mul]
  rw [coneRefPairing, hzero, integral_zero', add_zero, fieldPairing]
  have heq : (fun z : ℂ => φ z * (γ * (-Real.log ‖z‖))) =
      fun z => (-γ) * (φ z * Real.log ‖z‖) := by
    funext z
    ring
  rw [heq, integral_const_mul]
  ring

/-- A common supported-pairing event identifies a cone with the reference
    cone built from the very same base field, simultaneously for all tests. -/
theorem ae_referenceCone_pairing_eq_of_supported
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (Y H : Ω → LQGMetric.DistC) (hC : Ω → (ℂ → ℝ) → ℝ)
    (c : Ω → ℝ → ℂ → ℝ)
    (F : Ω → C(ℝ≥0, ℝ))
    (hhC : ∀ ω (φ : LQGMetric.TestC), hC ω φ = Y ω φ)
    (hpair : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC,
      (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
      H ω φ = Y ω φ + ∫ z, φ z * (γ * (-Real.log ‖z‖))) :
    ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC,
      (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
      coneRefPairing γ (hC ω) (c ω) (F ω) φ = H ω φ := by
  filter_upwards [hpair] with ω hω
  intro φ hφ
  rw [coneRefPairing_eq_field_add_log_of_supported γ _ _ _ φ hφ, hhC ω φ, hω φ hφ]

end MatedCRT.FirstPass.Derived
