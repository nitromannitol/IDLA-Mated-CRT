import MatedCRT.FirstPass.Derived.LBMDefinesTimeChangedBM
import MatedCRT.FirstPass.Derived.LQGMeasureNeZeroWiring
import MatedCRT.FirstPass.Derived.ValidApproximantBallBound

/-!
# The rescaled Liouville Brownian law field of a valid environment defines a time-changed Brownian motion

For `0 < γ < 2` and a valid mated-CRT environment `S` with a measurable version `H` of its field, almost surely
the Borel law field `lbmPathLawField γ (pairJ ⊤ (H ω))` is, at every starting point `z`, the law under planar
Brownian motion from `z` of the rescaled Liouville Brownian path `u ↦ b (F_ω(b)⁻¹ (m₀ u))`, `F_ω = S.clock ω`
(`MatedCRTEnv.IsValid.ae_lbmLawFieldSelection_eq`, the continuity `lbmLawContinuity_of_isValid` and
`S.m₀ = lbmExitMedian γ`), hence it defines a time-changed Brownian motion
(`definesTimeChangedBM_of_isTimeChangeClock`, Berestycki–Gwynne (2020), Definition 7.2).

* `ae_definesTimeChangedBM_lbmPathLawField`: the quenched statement, for almost every `ω`.
-/

set_option autoImplicit false

open MeasureTheory MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The Liouville Brownian law field defines a time-changed Brownian motion, quenched.** For a valid environment
at `0 < γ < 2` and a measurable version `H` of its field, almost surely the law field
`lbmPathLawField γ (pairJ ⊤ (H ω))` of the rescaled Liouville Brownian motion satisfies Definition 7.2 of
Berestycki–Gwynne (2020). -/
theorem ae_definesTimeChangedBM_lbmPathLawField {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, DefinesTimeChangedBM (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) := by
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hΛ := hS.ae_lbmLawFieldSelection_eq hH hrep (lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS)
  have hm : S.m₀ = lbmExitMedian γ := by
    rw [hS.m₀_eq_lawFieldExitMedian hH (measurable_lbmLawFieldSelection_coordCircleGood γ)
      (hΛ.mono fun ω h => h 0), hS.map_pairJ_eq_quantumConeCoordLaw hH hrep, lbmExitMedian]
  have hc : (lbmExitMedian γ).toNNReal ≠ 0 := by
    rw [← hm]
    exact (Real.toNNReal_pos.2 hm0).ne'
  filter_upwards [hΛ, hS.isLQGClock] with ω hω hclock
  choose hg hK using hω
  refine definesTimeChangedBM_of_isTimeChangeClock (F := S.clock ω) hc (fun z => (hclock z).2) hg ?_
  intro z
  have hmeas : Measurable (LatticeProb.timeScalePath (E := ℂ) (lbmExitMedian γ).toNNReal) :=
    (LatticeProb.continuous_timeScalePath _).measurable
  have h1 : ((lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) =
      (((lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω)) z :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))).map
        (LatticeProb.timeScalePath (lbmExitMedian γ).toNNReal) := by
    rw [lbmPathLawField, rescaledLBMLawField_apply]
    exact ProbabilityMeasure.toMeasure_map _
  rw [h1, hK z]
  exact AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable (hg z)

end MatedCRT.FirstPass.Derived
