import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final

/-! # Source cell at small mesh -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- Continuity at the origin places its cell inside the disk for small mesh. -/
theorem exists_small_mesh_zero_mem_ballInterior {η : ℝ → ℂ} {ρ : ℝ}
    (hη : ContinuousAt η 0) (hη0 : η 0 = 0) (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → (0 : ℤ) ∈ ballInterior ε η ρ := by
  rw [Metric.continuousAt_iff] at hη
  obtain ⟨δ, hδ, hclose⟩ := hη ρ hρ
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have hcell : cell ε η 0 ⊆ ball 0 ρ := by
    rintro x ⟨s, hs, rfl⟩
    have hs' : -ε ≤ s ∧ s ≤ 0 := by simpa [cell] using hs
    have hd : dist s 0 < δ := by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith
    simpa [mem_ball, hη0] using hclose hd
  have hzero : (0 : ℂ) ∈ cell ε η 0 := by
    refine ⟨0, ?_, hη0⟩
    simp [hε.le]
  refine ⟨⟨0, hzero, mem_ball_self hρ⟩, ?_⟩
  rintro ⟨x, hx, hfront⟩
  have hxball := hcell hx
  rw [frontier_ball (0 : ℂ) hρ.ne', mem_sphere] at hfront
  exact (ne_of_lt (mem_ball.mp hxball)) hfront

/-- On sufficiently small meshes the source condition in corrected Lemma 4.4
    holds simultaneously for all masses. -/
theorem ae_small_mesh_origin_in_cluster (𝒮 : SpaceFillingSLEModel)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε < δ → 0 < t → 1 < t / ε →
      (0 : ℤ) ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t := by
  filter_upwards [hS.isAreaParametrized, discreteLaplacianBoundCorrected 𝒮 γ hγ hγ2 ρ hρ hρ1 Ω S hS]
    with ω hη hbound
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_mesh_zero_mem_ballInterior hη.1.continuousAt hη.2.1 hρ
  exact ⟨δ, hδ, fun ε t hε hεδ ht hmass => (hbound t ε ht hε).2.2.2 hmass (hsmall ε hε hεδ)⟩

/-- On sufficiently small meshes the source condition in corrected Lemma 4.5
    holds, so confinement implies conservation of mass. -/
theorem ae_small_mesh_conservation_of_mass (𝒮 : SpaceFillingSLEModel)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε < δ → 0 < t →
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
        vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) →
      ∑' a : ballInterior ε (S.η ω) ρ,
        matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a *
          (matedDeg (S.mult ε ω) a : ℝ) = t / ε := by
  filter_upwards [hS.isAreaParametrized,
    discreteConservationOfMassCorrected 𝒮 γ hγ hγ2 ρ hρ hρ1 Ω S hS] with ω hη hbound
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_mesh_zero_mem_ballInterior hη.1.continuousAt hη.2.1 hρ
  exact ⟨δ, hδ, fun ε t hε hεδ ht hconf =>
    (hbound t ε ht hε).2.2 (hsmall ε hε hεδ) hconf⟩

end MatedCRT
