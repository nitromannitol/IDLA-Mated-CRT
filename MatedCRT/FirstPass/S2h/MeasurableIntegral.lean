import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurability of the integral in the measure (fp-S2h, z1)

For a measurable real function `φ` on `ℂ`, the map `ν ↦ ∫ φ dν` from `Measure ℂ` (Giry σ-algebra) is measurable.
Standard formula: `∫ φ dν = (∫⁻ φ⁺ dν).toReal - (∫⁻ φ⁻ dν).toReal` on the set where both lower integrals are finite
(the integrable case), and `∫ φ dν = 0` otherwise. Used for the local codes `localCode φs` of `FirstPass/S2h.lean`.
-/

namespace MatedCRT

open MeasureTheory Set

open scoped Classical in
/-- `ν ↦ ∫ φ dν` is Giry-measurable for a measurable real function `φ` on `ℂ` (standard; no hypothesis on `ν`). -/
theorem measurable_integral_measure_real {φ : ℂ → ℝ} (hφ : Measurable φ) :
    Measurable fun ν : Measure ℂ => ∫ x, φ x ∂ν := by
  have hpos : Measurable fun ν : Measure ℂ => ∫⁻ x, ENNReal.ofReal (φ x) ∂ν :=
    Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hφ)
  have hneg : Measurable fun ν : Measure ℂ => ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν :=
    Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hφ.neg)
  have hpt : ∀ x, ‖φ x‖ₑ = ENNReal.ofReal (φ x) + ENNReal.ofReal (-φ x) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total 0 (φ x) with h | h
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 h), add_zero, abs_of_nonneg h]
    · rw [ENNReal.ofReal_of_nonpos h, zero_add, abs_of_nonpos h]
  have hint : ∀ ν : Measure ℂ, Integrable φ ν ↔
      (∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ⊤ ∧ ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν < ⊤) := by
    intro ν
    have hfin : (∫⁻ x, ‖φ x‖ₑ ∂ν) = (∫⁻ x, ENNReal.ofReal (φ x) ∂ν) + ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν := by
      rw [lintegral_congr hpt]
      exact lintegral_add_left (ENNReal.measurable_ofReal.comp hφ) _
    constructor
    · intro h
      have h' : (∫⁻ x, ‖φ x‖ₑ ∂ν) < ⊤ := h.2
      rw [hfin] at h'
      exact ENNReal.add_lt_top.1 h'
    · rintro ⟨h1, h2⟩
      refine ⟨hφ.aestronglyMeasurable, ?_⟩
      show (∫⁻ x, ‖φ x‖ₑ ∂ν) < ⊤
      rw [hfin]
      exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  have key : ∀ ν : Measure ℂ, ∫ x, φ x ∂ν =
      if (∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ⊤ ∧ ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν < ⊤) then
        (∫⁻ x, ENNReal.ofReal (φ x) ∂ν).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂ν).toReal else 0 := by
    intro ν
    split_ifs with h
    · exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part ((hint ν).2 h)
    · exact integral_undef (fun hi => h ((hint ν).1 hi))
  have hS : MeasurableSet {ν : Measure ℂ |
      ∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ⊤ ∧ ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν < ⊤} :=
    (measurableSet_lt hpos measurable_const).inter (measurableSet_lt hneg measurable_const)
  have hmeas : Measurable fun ν : Measure ℂ =>
      if (∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ⊤ ∧ ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν < ⊤) then
        (∫⁻ x, ENNReal.ofReal (φ x) ∂ν).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂ν).toReal else 0 :=
    Measurable.ite hS ((hpos.ennreal_toReal).sub hneg.ennreal_toReal) measurable_const
  have hfun : (fun ν : Measure ℂ => ∫ x, φ x ∂ν) = fun ν : Measure ℂ =>
      if (∫⁻ x, ENNReal.ofReal (φ x) ∂ν < ⊤ ∧ ∫⁻ x, ENNReal.ofReal (-φ x) ∂ν < ⊤) then
        (∫⁻ x, ENNReal.ofReal (φ x) ∂ν).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂ν).toReal else 0 :=
    funext key
  rw [hfun]
  exact hmeas

end MatedCRT
