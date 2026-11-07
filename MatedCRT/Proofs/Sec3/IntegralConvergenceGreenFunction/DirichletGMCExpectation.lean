import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GMCExpectation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.DirichletCircleMeasurable

/-! # Expected Dirichlet circle-average chaos -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory HarmonicBalls

/-- The variance-normalized chaos of Dirichlet circle averages has the
reference expectation, including when the original field is only specified
up to almost-sure spatial continuity. -/
theorem IsDirichletGFF.gmcApprox_integral_real_apply
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {D U : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsDirichletGFF P D h hcirc) (ε : ℝ) (hε : 0 < ε)
    (hdisks : ∀ z ∈ U, Metric.closedBall z ε ⊆ D)
    (σ : Measure U) [IsFiniteMeasure σ] (γ : ℝ) (S : Set U) (hS : MeasurableSet S) :
    Integrable (fun ω => (gmcApprox P σ γ (fun ω z => hcirc ω ε z) ω).real S) P ∧
      (∫ ω, (gmcApprox P σ γ (fun ω z => hcirc ω ε z) ω).real S ∂P) = σ.real S := by
  obtain ⟨g, hg, heq, hgauss⟩ := hGFF.exists_jointlyMeasurable_circle_gaussian ε hε hdisks
  let H : Ω → U → ℝ := fun ω z => g (ω, z)
  let K : Ω → U → ℝ := fun ω z => hcirc ω ε z
  have hv : ∀ z, (∫ ω, (H ω z) ^ 2 ∂P) = ∫ ω, (K ω z) ^ 2 ∂P := by
    intro z
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    simp [H, K, hω z]
  have hchaos : ∀ᵐ ω ∂P, gmcApprox P σ γ H ω = gmcApprox P σ γ K ω := by
    filter_upwards [heq] with ω hω
    apply withDensity_congr_ae
    filter_upwards [] with z
    simp only [H, K, hω z, hv z]
  have hm := MatedCRT.gmcApprox_integral_real_apply P σ γ H S hS hg hgauss
  have hm' : (fun ω => (gmcApprox P σ γ H ω).real S) =ᵐ[P]
      (fun ω => (gmcApprox P σ γ K ω).real S) := hchaos.mono fun ω hω => by dsimp only; rw [hω]
  exact ⟨hm.1.congr hm', (integral_congr_ae hm').symm.trans hm.2⟩

end MatedCRT
