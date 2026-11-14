import MatedCRT.FirstPass.Derived.TimeScalePathBridge

/-!
# Annealed exit times under deterministic time scaling

A common deterministic time change scales the median of the annealed
exit-time distribution. This identifies the scale from a normalized median.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

variable {Ω α : Type*} [MeasurableSpace Ω] [MetricSpace α]
  [MeasurableSpace α] [BorelSpace α]

/-- The exit-time distribution of a mixture of time-scaled laws is obtained
by scaling the argument of the original mixture's distribution function. -/
theorem lintegral_exitCdf_eq_of_ae_timeScalePath
    (U : Set α) (hU : IsOpen U) (P : Measure Ω)
    {K L : Ω → Measure (ContinuousPath α)} {c : ℝ≥0} (hc : c ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, L ω = (K ω).map (LatticeProb.timeScalePath c)) (x : ℝ) :
    (∫⁻ ω, exitCdf U (L ω) x ∂P) =
      ∫⁻ ω, exitCdf U (K ω) ((c : ℝ) * x) ∂P := by
  apply lintegral_congr_ae
  filter_upwards [hlaw] with ω hω
  rw [hω, ← timeScalePath_eq_latticeProb]
  exact exitCdf_map_timeScalePath U hU hc (K ω) x

/-- A deterministic nonzero time scale divides the annealed exit median. -/
theorem medianOf_lintegral_exitCdf_eq_of_ae_timeScalePath
    (U : Set α) (hU : IsOpen U) (P : Measure Ω)
    {K L : Ω → Measure (ContinuousPath α)} {c : ℝ≥0} (hc : c ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, L ω = (K ω).map (LatticeProb.timeScalePath c)) :
    medianOf (fun x => ∫⁻ ω, exitCdf U (L ω) x ∂P) =
      medianOf (fun x => ∫⁻ ω, exitCdf U (K ω) x ∂P) / (c : ℝ) := by
  have heq : (fun x => ∫⁻ ω, exitCdf U (L ω) x ∂P) =
      fun x => (∫⁻ ω, exitCdf U (K ω) ((c : ℝ) * x) ∂P) :=
    funext (lintegral_exitCdf_eq_of_ae_timeScalePath U hU P hc hlaw)
  rw [heq]
  exact medianOf_comp_mul (fun x => ∫⁻ ω, exitCdf U (K ω) x ∂P)
    (by exact_mod_cast (pos_iff_ne_zero.mpr hc : 0 < c))

/-- Unit annealed exit median identifies the deterministic time scale. -/
theorem coe_eq_medianOf_lintegral_exitCdf_of_ae_timeScalePath
    (U : Set α) (hU : IsOpen U) (P : Measure Ω)
    {K L : Ω → Measure (ContinuousPath α)} {c : ℝ≥0} (hc : c ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, L ω = (K ω).map (LatticeProb.timeScalePath c))
    (hunit : medianOf (fun x => ∫⁻ ω, exitCdf U (L ω) x ∂P) = 1) :
    (c : ℝ) = medianOf (fun x => ∫⁻ ω, exitCdf U (K ω) x ∂P) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have h := medianOf_lintegral_exitCdf_eq_of_ae_timeScalePath U hU P hc hlaw
  rw [hunit] at h
  exact (div_eq_one_iff_eq hc').mp h.symm |>.symm

end MatedCRT
