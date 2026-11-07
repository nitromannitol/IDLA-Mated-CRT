import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedPreparedBoundary
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Convergence
import MatedCRT.External.SLE

/-! Transfer of the prepared vertex modulus to spatial harmonic functions. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory

/-- The median scaling estimate turns a vertex modulus on a closed disk into
an asymptotic spatial modulus for its rescaled discrete functions. -/
theorem projected_spatial_modulus_of_vertex_modulus
    {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (ω : Ω) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (ε : ℕ → ℝ) (u : ℕ → ℤ → ℝ)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective (S.η ω))
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : IsVertexAsymptoticallyEquicontinuous ε (S.η ω) u (closure (ball z r))) :
    Tightness.IsAsymptoticallyEquicontinuousOn
      (fun n => rescale (S.mε (ε n)) (ε n) (S.η ω) (u n)) (closedBall z r) := by
  obtain ⟨Cm, hCm1, hmS⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmS Ω S hS
  have hCm : 0 < Cm := one_pos.trans hCm1
  have hmev : ∀ᶠ n in atTop, 0 ≤ (S.mε (ε n))⁻¹ ∧
      (S.mε (ε n))⁻¹ ≤ Cm * ε n := by
    filter_upwards [hε0.eventually (gt_mem_nhds hε₀)] with n hn
    have h := (hmε (ε n) (hε n) hn).1
    have hpos : 0 < Cm⁻¹ * (ε n)⁻¹ := mul_pos (inv_pos.2 hCm) (inv_pos.2 (hε n))
    refine ⟨inv_nonneg.2 (hpos.le.trans h), ?_⟩
    have h2 := inv_anti₀ hpos h
    rwa [mul_inv, inv_inv, inv_inv] at h2
  apply Tightness.isAsymptoticallyEquicontinuousOn_rescale isBounded_closedBall
    hη hp hsurj hε hε0 hCm hmev
  simpa [closure_ball z hr.ne'] using hV

end MatedCRT

#print axioms MatedCRT.projected_spatial_modulus_of_vertex_modulus
