import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WholePlaneCircleVariance
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockGMCNormalization
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GMCExpectation
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousFieldMeasurable

/-! # Expected whole-plane circle clock mass -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls
open scoped NNReal

/-- For a finite reference measure in the unit disk, the regularized LQG
clock density has expected mass equal to the reference mass. -/
theorem IsWholePlaneGFF.clockDensity_integral_real_apply
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {U : Set ℂ} (r : ℝ) (hr : 0 < r)
    (hU : ∀ z ∈ U, ‖z‖ + r ≤ 1)
    (σ : Measure U) [IsFiniteMeasure σ] (γ : ℝ) (S : Set U) (hS : MeasurableSet S) :
    let ν : Ω → Measure U := fun ω => σ.withDensity (fun z => ENNReal.ofReal
      (r ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω r z)))
    Integrable (fun ω => (ν ω).real S) P ∧ (∫ ω, (ν ω).real S ∂P) = σ.real S := by
  obtain ⟨g, hg, heq⟩ := exists_jointlyMeasurable_of_ae_continuous P
    (fun ω (z : U) => hcirc ω r z)
    (fun z => (h.measurable_circle r z hr).aemeasurable) (by
      filter_upwards [h.ae_continuousOn_circle] with ω hω
      exact hω.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun z : U => ⟨hr, Set.mem_univ _⟩))
  let H : Ω → U → ℝ := fun ω z => g (ω, z)
  let K : Ω → U → ℝ := fun ω z => hcirc ω r z
  have hgauss : ∀ z : U, ∃ v : ℝ≥0, HasLaw (fun ω => H ω z) (gaussianReal 0 v) P := by
    intro z
    have hG := h.hasGaussianLaw_circle hr z
    have hmean : (∫ ω, hcirc ω r z ∂P) = 0 := h.integral_eq_zero (.circle r z) hr
    refine ⟨(variance (fun ω => hcirc ω r z) P).toNNReal, ?_⟩
    refine ⟨(hg.comp (measurable_id.prodMk measurable_const)).aemeasurable, ?_⟩
    rw [Measure.map_congr (heq.mono fun ω hω => hω z), hG.map_eq_gaussianReal, hmean]
  have hv : ∀ z : U, (∫ ω, (H ω z) ^ 2 ∂P) = ∫ ω, (K ω z) ^ 2 ∂P := by
    intro z
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    simp [H, K, hω z]
  have hvar : ∀ z : U, (∫ ω, (K ω z) ^ 2 ∂P) = Real.log r⁻¹ :=
    fun z => MatedCRT.IsWholePlaneGFF.circle_secondMoment_inside_unit h hr z (hU z z.property)
  have hchaos : ∀ᵐ ω ∂P, gmcApprox P σ γ H ω = gmcApprox P σ γ K ω := by
    filter_upwards [heq] with ω hω
    apply withDensity_congr_ae
    filter_upwards [] with z
    simp only [H, K, hω z, hv z]
  have hm := gmcApprox_integral_real_apply P σ γ H S hS hg hgauss
  have hm' : (fun ω => (gmcApprox P σ γ H ω).real S) =ᵐ[P]
      (fun ω => (gmcApprox P σ γ K ω).real S) := hchaos.mono fun ω hω => by
        dsimp only
        rw [hω]
  have he : ∀ ω, gmcApprox P σ γ K ω = σ.withDensity (fun z => ENNReal.ofReal
      (r ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω r z))) :=
    gmcApprox_eq_clock_density P σ γ r hr K hvar
  exact ⟨by simpa only [he] using hm.1.congr hm',
    by simpa only [he] using (integral_congr_ae hm').symm.trans hm.2⟩

end MatedCRT
