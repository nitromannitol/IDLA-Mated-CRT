import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.WeightedPotentialMeasurable
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.InteriorSteps
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PointwiseModulusProbability

/-! The continuum modulus in Lemma 3.5. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- The random continuum candidate is the Poisson extension minus the signed
Green potential on a single almost sure event. -/
theorem dirichletLimit_ae_poisson_sub_green
    (𝒮 : SpaceFillingSLEModel) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (ψ φ : ℂ → ℝ)
    (hφ : ContinuousOn φ (closedBall z r)) :
    ∀ᵐ ω ∂S.P, dirichletLimit S r z ψ φ ω = fun x => discPoissonExtension φ z r x -
      S.c₀ * ∫ y in ball z r, greenFunction (ball z r) x y * ψ y ∂S.μ ω := by
  have hm₀ := hS.m₀_pos hγ hγ2
  filter_upwards [hS.isLQGClock] with ω hc
  funext x
  unfold dirichletLimit
  by_cases hx : x ∈ ball z r
  · rw [ite_eq_left hx, discPoissonExtension_of_mem hx,
      ← integral_pathExitPosition_eq_discPoissonIntegral hr hφ hx]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [(hc x).2, ae_planarBrownianMotion_eval_zero x,
      ae_planarBrownianMotion_exit_any_ball_lt_top x z r] with b hclock hstart hfin
    rw [rescaledLBMExitPosition_eq_brownianExitPosition isOpen_ball hclock
      (by rw [hstart]; exact hx) hfin hm₀, pathExitPosition_eq_eval_exitTime]
  · rw [ite_eq_right hx, discPoissonExtension_of_notMem hx, greenPart_eq_zero_of_notMem hx,
      mul_zero, sub_zero]

/-- The continuum modulus required in the interior reduction follows from
volume growth and the measurable signed Green potential. -/
theorem dirichletLimitModulusStep_of_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) : DirichletLimitModulusStep 𝒮 := by
  intro h36 h34 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ φ hψb hψh hφ r' hr' hr'r t ht e he
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨M, hM⟩ := hψb
  obtain ⟨Cψ, χψ, hχψ, -, hHψ⟩ := hψh
  have hψc : ContinuousOn ψ (ball z r) := hHψ.continuousOn hχψ
  obtain ⟨s, hs, Cφ, χφ, hχφ, -, hHφ⟩ := hφ
  have hφc : ContinuousOn φ (closedBall z r) :=
    (hHφ.continuousOn hχφ).mono (closedBall_subset_closedBall (by linarith))
  have hrepr := dirichletLimit_ae_poisson_sub_green 𝒮 hγ hγ2 S hS hr ψ φ hφc
  apply pointwiseMeasurable_modulus_small_in_probability S.P (closedBall z r')
    (isCompact_closedBall z r') (dirichletLimit S r z ψ φ) ?_ ?_ ht he
  · intro x hx
    have hx' : x ∈ closedBall z r := closedBall_subset_closedBall hr'r.le hx
    have hpot := hS.aemeasurable_weightedGreenPotential h27 hγ hγ2 hρ1 hr hball hx' hψc hM
    apply (aemeasurable_const.sub (aemeasurable_const.mul hpot)).congr
    filter_upwards [hrepr] with ω hω
    exact (congrFun hω x).symm
  · filter_upwards [hrepr, hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1,
      hS.isLQGMeasure] with ω hω hv hm
    let : IsLocallyFiniteMeasure (S.μ ω) := hm.isLocallyFiniteMeasure
    obtain ⟨βm, βp, hv⟩ := hv
    rw [hω]
    have hpc := continuousOn_discPoissonExtension hr (hφc.mono sphere_subset_closedBall)
    obtain ⟨C, χ, hχ, -, hp⟩ := (greenPart_integrable_holder hv hr hball hψc hM).2
    exact (hpc.sub (continuousOn_const.mul (hp.continuousOn hχ))).mono
      (closedBall_subset_closedBall hr'r.le)

end MatedCRT
