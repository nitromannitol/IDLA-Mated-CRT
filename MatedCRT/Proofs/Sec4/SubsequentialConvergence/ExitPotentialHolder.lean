import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.WeightedPotentialMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundary

/-! Hölder regularity of the continuum exit-time barrier. -/

namespace MatedCRT

open MeasureTheory Metric Filter Topology Set _root_.HarmonicBalls
open scoped NNReal

/-- Volume growth gives Hölder regularity of the normalized Green exit
potential up to the boundary of the ball. -/
theorem normalizedExitGreenPotential_ae_holder_of_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) :
    ∀ᵐ ω ∂S.P, IsHolderContinuousOn (normalizedExitGreenPotential S r z ω)
      (closedBall z r) := by
  filter_upwards [hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hρ1,
    hS.isLQGMeasure] with ω hv hm
  let : IsLocallyFiniteMeasure (S.μ ω) := hm.isLocallyFiniteMeasure
  obtain ⟨βm, βp, hv⟩ := hv
  have hg := (greenPart_integrable_holder (M := 1) hv hr hball
    (ψ := fun _ => (1 : ℝ)) (by fun_prop) (by simp)).2
  have hz : IsHolderContinuousOn (fun _ : ℂ => (0 : ℝ)) (closedBall z r) := by
    refine ⟨0, 1, one_pos, le_rfl, ?_⟩
    apply holderOnWith_of_dist_le
    intro x hx y hy
    simp
  have hh := hz.sub_const_mul isBounded_closedBall hg (-(S.c₀ / 6))
  change IsHolderContinuousOn (fun x => S.c₀ / 6 *
    ∫ y in ball z r, greenFunction (ball z r) x y ∂S.μ ω) (closedBall z r)
  simpa using hh

/-- The exit potential decays with a Hölder modulus at every boundary point. -/
theorem normalizedExitGreenPotential_ae_boundary_holder_of_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) :
    ∀ᵐ ω ∂S.P, ∃ C χ : ℝ≥0, 0 < χ ∧ χ ≤ 1 ∧
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r,
        |normalizedExitGreenPotential S r z ω x| ≤ C * dist x y ^ (χ : ℝ) := by
  filter_upwards [normalizedExitGreenPotential_ae_holder_of_volumeGrowth
    𝒮 h27 hγ hγ2 hρ1 S hS hr hball] with ω hω
  obtain ⟨C, χ, hχ, hχ1, hh⟩ := hω
  refine ⟨C, χ, hχ, hχ1, ?_⟩
  intro x hx y hy
  have hb := hh.dist_le hx (sphere_subset_closedBall hy)
  rw [Real.dist_eq, normalizedExitGreenPotential_eq_zero_on_sphere S hy ω, sub_zero] at hb
  exact hb

end MatedCRT
