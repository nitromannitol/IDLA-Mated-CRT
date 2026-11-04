import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TestFunctionTightness
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CompactMassMeasurable

/-! Positive mass of open sets for area-parametrized space-filling curves. -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- Every nonempty open set has positive mass when a continuous surjective
curve is parametrized by the measure of its time intervals. -/
theorem IsAreaParametrized.measure_open_pos {μ : Measure ℂ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ U := by
  obtain ⟨x, hxU⟩ := hne
  obtain ⟨t, rfl⟩ := hη.2.2.1 x
  have hpre : IsOpen (η ⁻¹' U) := hU.preimage hη.1
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hpre t hxU
  have hsub : η '' Icc (t - δ / 2) (t + δ / 2) ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    apply hδsub
    rw [mem_ball, Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hmass := hη.2.2.2 (t - δ / 2) (t + δ / 2) (by linarith)
  have hpos : 0 < μ (η '' Icc (t - δ / 2) (t + δ / 2)) := by
    rw [hmass, ENNReal.ofReal_pos]
    linarith
  exact hpos.trans_le (measure_mono hsub)

/-- The mass of a fixed nonempty ball is bounded away from zero in
probability. The compact inner ball makes the mass almost-everywhere measurable. -/
theorem MatedCRTEnv.IsValid.exists_ball_mass_lower_bound
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (z : ℂ) {r : ℝ} (hr : 0 < r) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ q : ℝ, 0 < q ∧ S.P {ω | S.μ ω (ball z r) < ENNReal.ofReal q} < δ := by
  let := hS.isProbabilityMeasure
  let X : Ω → ℝ≥0∞ := fun ω => S.μ ω (closedBall z (r / 2))
  have hXm : AEMeasurable X S.P := hS.aemeasurable_lqg_compact_mass_ennreal (isCompact_closedBall z (r / 2))
  have hpos : ∀ᵐ ω ∂S.P, 0 < X ω := by
    filter_upwards [hS.isAreaParametrized] with ω hη
    apply (hη.measure_open_pos isOpen_ball ⟨z, mem_ball_self (show 0 < r / 4 by positivity)⟩).trans_le
    exact measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hfinite : ∀ᵐ ω ∂S.P, (X ω)⁻¹ < ⊤ := by
    filter_upwards [hpos] with ω hω
    exact lt_top_iff_ne_top.2 (ENNReal.inv_ne_top.2 hω.ne')
  obtain ⟨n, hn⟩ := exists_nat_measure_gt_lt S.P (fun ω => (X ω)⁻¹) hXm.inv hfinite hδ
  refine ⟨((n : ℝ) + 1)⁻¹, by positivity, (measure_mono ?_).trans_lt hn⟩
  intro ω hω
  have hsub : closedBall z (r / 2) ⊆ ball z r := closedBall_subset_ball (by linarith)
  have hsmall : X ω < ENNReal.ofReal (((n : ℝ) + 1)⁻¹) :=
    (measure_mono hsub).trans_lt hω
  have hsmall' : X ω < ((n : ℝ≥0∞) + 1)⁻¹ := by
    simpa [ENNReal.ofReal_inv_of_pos (by positivity : 0 < (n : ℝ) + 1),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ n) (by positivity : (0 : ℝ) ≤ 1)] using hsmall
  have : (n : ℝ≥0∞) + 1 < (X ω)⁻¹ := ENNReal.lt_inv_iff_lt_inv.1 hsmall'
  exact lt_of_le_of_lt (by simp) this

end MatedCRT
