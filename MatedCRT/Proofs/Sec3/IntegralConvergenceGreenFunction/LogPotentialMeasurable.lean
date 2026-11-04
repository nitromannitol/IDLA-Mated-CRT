import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMassMeasurable
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.EventCountable

/-! Measurability of the largest-exit-time random variable on a ball. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- The logarithmic potential on an open ball is an almost-everywhere
measurable function of a valid LQG environment. -/
theorem MatedCRTEnv.IsValid.aemeasurable_largestExitTimeRV_ball
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (ρ : ℝ) :
    AEMeasurable (fun ω => largestExitTimeRV (S.μ ω) (ball 0 ρ)) S.P := by
  obtain ⟨w, hw⟩ := TopologicalSpace.exists_dense_seq ℂ
  have hrep (ω : Ω) : largestExitTimeRV (S.μ ω) (ball 0 ρ) =
      ⨆ i : ℕ, ⨆ (_ : w i ∈ ball (0 : ℂ) ρ),
        ∫⁻ u in ball (0 : ℂ) ρ, AnnulusEventCountable.logKernel 1 (w i) u ∂S.μ ω := by
    unfold largestExitTimeRV
    have h := AnnulusEventCountable.iSup_setLIntegral_logKernel_eq_dense
      (m := S.μ ω) (V := ball 0 ρ) (r := 1) isOpen_ball zero_lt_one hw
    simpa only [AnnulusEventCountable.logKernel, norm_sub_rev] using h
  simp_rw [hrep]
  refine AEMeasurable.iSup fun i => AEMeasurable.iSup fun _ => ?_
  rw [show (fun ω => ∫⁻ u in ball (0 : ℂ) ρ,
      AnnulusEventCountable.logKernel 1 (w i) u ∂S.μ ω) =
      (fun ω => ∫⁻ u, (ball (0 : ℂ) ρ).indicator
        (AnnulusEventCountable.logKernel 1 (w i)) u ∂S.μ ω) by
    funext ω
    exact (lintegral_indicator isOpen_ball.measurableSet _).symm]
  exact hS.aemeasurable_lqg_lintegral _
    ((AnnulusEventCountable.measurable_logKernel 1 (w i)).indicator isOpen_ball.measurableSet)

end MatedCRT
