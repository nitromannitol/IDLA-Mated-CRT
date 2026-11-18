import MatedCRT.External.RevuzTimeChange
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM

/-!
# Lebesgue measure is invariant for planar Brownian motion

For every time `t` and Borel set `S ⊆ ℂ`, `∫ P_z[B_t ∈ S] dz = |S|`: Lebesgue measure is an invariant
measure of planar Brownian motion. This is the stationarity behind the Revuz measure
`revuz planarLaw A`, which is taken with respect to Lebesgue measure (Revuz–Yor (1999), Chapter X, §2).
The proof writes `P_z` as the translate by `z` of `P_0` and exchanges the two integrals.
-/

open MeasureTheory Set MarkovProcess
open scoped ENNReal

namespace MatedCRT

/-- **Lebesgue measure is invariant for planar Brownian motion**: `∫ P_z[B_t ∈ S] dz = |S|`. -/
theorem lintegral_planarLaw_eval_mem (t : NNReal) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ z, planarLaw z {ω | ω t ∈ S} = volume S := by
  have hmeas : Measurable fun p : ℂ × ContinuousPath ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 t + p.1) :=
    (measurable_const.indicator hS).comp
      (((continuous_eval_const t).measurable.comp measurable_snd).add measurable_fst)
  have hpt : ∀ z : ℂ, planarLaw z {ω | ω t ∈ S} =
      ∫⁻ b, S.indicator (fun _ => (1 : ℝ≥0∞)) (b t + z) ∂HarmonicBalls.planarBrownianMotion 0 := by
    intro z
    have hT : MeasurableSet (StopAtExitCmp.translatePath z ⁻¹' {ω : ContinuousPath ℂ | ω t ∈ S}) :=
      ((continuous_eval_const t).measurable hS).preimage
        (StopAtExitCmp.translatePath z).continuous.measurable
    rw [planarLaw, StopAtExitCmp.planarBrownianMotion_apply_eq_translatePath z,
      ← lintegral_indicator_one hT]
    congr 1
  simp_rw [hpt]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hin : ∀ b : ContinuousPath ℂ,
      ∫⁻ z, S.indicator (fun _ => (1 : ℝ≥0∞)) (b t + z) = volume S := by
    intro b
    have := lintegral_add_left_eq_self (μ := (volume : Measure ℂ))
      (S.indicator fun _ => (1 : ℝ≥0∞)) (b t)
    rw [this]
    exact lintegral_indicator_one hS
  simp_rw [hin]
  rw [lintegral_const, measure_univ, mul_one]

end MatedCRT
