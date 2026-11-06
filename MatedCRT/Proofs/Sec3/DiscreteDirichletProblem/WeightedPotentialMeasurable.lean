import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.RandomMeasureIntegral
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GreenPart
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.VolumeGrowthInsideUnit

/-! Pointwise measurability of the signed Green potential. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric _root_.HarmonicBalls

/-- Volume growth and the local boundedness of the source give a measurable
version of every section of the Dirichlet Green potential. -/
theorem MatedCRTEnv.IsValid.aemeasurable_weightedGreenPotential
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {r : ℝ} {z x : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hx : x ∈ closedBall z r) {ψ : ℂ → ℝ} (hψc : ContinuousOn ψ (ball z r))
    {M : ℝ} (hψb : ∀ y ∈ ball z r, |ψ y| ≤ M) :
    AEMeasurable (fun ω => ∫ y in ball z r,
      greenFunction (ball z r) x y * ψ y ∂S.μ ω) S.P := by
  classical
  let q : ℂ → ℝ := (ball z r).indicator ψ
  have hq : Measurable q := by
    change Measurable ((ball z r).piecewise ψ (fun _ => 0))
    exact hψc.measurable_piecewise continuousOn_const measurableSet_ball
  let f : ℂ → ℝ := fun y => greenFunction (ball z r) x y * q y
  have hf : Measurable f := (measurable_greenFunction isOpen_ball x).mul hq
  have hi : ∀ᵐ ω ∂S.P, Integrable f (S.μ ω) := by
    filter_upwards [hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1,
      hS.isLQGMeasure] with ω hv hm
    let : IsLocallyFiniteMeasure (S.μ ω) := hm.isLocallyFiniteMeasure
    obtain ⟨βm, βp, hv⟩ := hv
    have hI := (greenPart_integrable_holder hv hr hball hψc hψb).1 x hx
    have heq : f = (ball z r).indicator (fun y => greenFunction (ball z r) x y * ψ y) := by
      funext y
      by_cases hy : y ∈ ball z r <;> simp [f, q, hy]
    rw [heq]
    exact hI.integrable_indicator measurableSet_ball
  apply (hS.aemeasurable_lqg_integral_of_ae_integrable f hf hi).congr
  filter_upwards [] with ω
  simp only [f, q, ← indicator_mul_right, integral_indicator measurableSet_ball]

end MatedCRT
