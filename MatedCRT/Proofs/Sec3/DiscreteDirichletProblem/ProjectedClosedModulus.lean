import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedContinuum

/-! The projected continuum candidate has a closed-disk probability modulus. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The continuum Dirichlet candidate is uniformly equicontinuous in
probability on the entire closed disk. -/
theorem projectedDirichletLimit_closedBall_modulus_of_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψb : ∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M)
    (hψh : IsHolderContinuousOn ψ (ball z r)) (hφ : IsHolderContinuousOn φ (closedBall z r))
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r, dist x y < δ ∧
      t < |dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω x -
        dirichletLimit S r z ψ (fun x => φ (ballRetraction z r x)) ω y|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  let φ' := fun x => φ (ballRetraction z r x)
  obtain ⟨M, hM⟩ := hψb
  obtain ⟨Cψ, χψ, hχψ, _, hHψ⟩ := hψh
  have hψc : ContinuousOn ψ (ball z r) := hHψ.continuousOn hχψ
  obtain ⟨Cφ, χφ, hχφ, _, hHφ⟩ := holder_ballRetraction hr (by linarith : 0 ≤ r) z hφ
  have hφc : ContinuousOn φ' (closedBall z r) := hHφ.continuousOn hχφ
  have hrepr := dirichletLimit_ae_poisson_sub_green 𝒮 hγ hγ2 S hS hr ψ φ' hφc
  apply pointwiseMeasurable_modulus_small_in_probability S.P (closedBall z r)
    (isCompact_closedBall z r) (dirichletLimit S r z ψ φ') ?_ ?_ ht he
  · intro x hx
    have hpot := hS.aemeasurable_weightedGreenPotential h27 hγ hγ2 hρ1 hr hball hx hψc hM
    apply (aemeasurable_const.sub (aemeasurable_const.mul hpot)).congr
    filter_upwards [hrepr] with ω hω
    exact (congrFun hω x).symm
  · filter_upwards [hrepr, hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1,
      hS.isLQGMeasure] with ω hω hv hm
    let : IsLocallyFiniteMeasure (S.μ ω) := hm.isLocallyFiniteMeasure
    obtain ⟨βm, βp, hv⟩ := hv
    rw [hω]
    have hpc := continuousOn_discPoissonExtension hr (hφc.mono sphere_subset_closedBall)
    obtain ⟨C, χ, hχ, _, hp⟩ := (greenPart_integrable_holder hv hr hball hψc hM).2
    exact hpc.sub (continuousOn_const.mul (hp.continuousOn hχ))

end MatedCRT

#print axioms MatedCRT.projectedDirichletLimit_closedBall_modulus_of_volumeGrowth
