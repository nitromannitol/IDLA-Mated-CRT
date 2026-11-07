import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedEventualModulus
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitSize

/-! Size and spatial modulus for projected harmonic comparisons. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls

/-- Projected harmonic functions with Hölder data have a spatial modulus
along any polynomially summable mesh sequence. -/
theorem ae_projected_harmonic_spatial_modulus_of_holder_data
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r))
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (φ : ℂ → ℝ) (hφ : IsHolderContinuousOn φ (closedBall z r))
    (u : Ω → ℕ → ℤ → ℝ)
    (hdata : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) (u ω n) a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (frontier (ball z r)),
        u ω n b = S.mε (e n) * φ (ballRetraction z r (vertexPoint (e n) (S.η ω) b)))) :
    ∀ᵐ ω ∂S.P, Tightness.IsAsymptoticallyEquicontinuousOn
      (fun n => rescale (S.mε (e n)) (e n) (S.η ω) (u ω n)) (closedBall z r) := by
  obtain ⟨L, χ, hχ, hχ1, hholder⟩ := hφ
  have hφ : IsHolderContinuousOn φ (closedBall z r) := ⟨L, χ, hχ, hχ1, hholder⟩
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).bddAbove_image (hholder.continuousOn hχ).abs
  have hφbound : ∀ x ∈ closedBall z r, |φ x| ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  obtain ⟨A, hA, hscale⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscaleε⟩ := hscale Ω S hS
  have hA0 : 0 < A := by linarith
  have hbound : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (u ω n) a| ≤ (0 : ℝ)) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), e n * |u ω n b| ≤ A * M) := by
    filter_upwards [hdata] with ω hω
    filter_upwards [hω, he0.eventually (gt_mem_nhds hε₀)] with n hn hnε
    have hε := he.1 n
    have hscale' := (hscaleε (e n) hε hnε).2
    have hmed : 0 ≤ S.mε (e n) := medianOf_nonneg _
    have hscaled : e n * S.mε (e n) ≤ A := by
      have hh := mul_le_mul_of_nonneg_left hscale' hε.le
      have heq : e n * (A * (e n)⁻¹) = A := by field_simp
      linarith
    refine ⟨?_, ?_⟩
    · intro a ha
      simp [hn.1 a ha]
    · intro b hb
      have hb' : b ∈ cellVertices (e n) (S.η ω) (frontier (ball z r)) := by
        simpa [frontier_ball z hr.ne'] using hb
      rw [hn.2 b hb', abs_mul, abs_of_nonneg hmed]
      have hf := hφbound (ballRetraction z r (vertexPoint (e n) (S.η ω) b))
        (ballRetraction_mem z hr (vertexPoint (e n) (S.η ω) b))
      nlinarith [mul_le_mul hscaled hf (abs_nonneg (φ (ballRetraction z r (vertexPoint (e n) (S.η ω) b)))) hA0.le]
  have hsize := ae_eventual_dirichlet_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS
    hr hD e he he0 u (show (0 : ℝ) ≤ 0 by rfl) hbound
  filter_upwards [hsize, hdata, ae_eventual_projected_harmonic_spatial_modulus hH hm hγ hγ2 hρ hρ1
    S hS e he hr hD hsimply] with ω ⟨B, hB⟩ hd hmod
  apply hmod (fun _ => e) u (fun _ => |B| + 1) φ (fun n => mem_range_self n) he0 he.1
    (by positivity) hφ
  filter_upwards [hB, hd] with n hn hd
  refine ⟨?_, hd.1, hd.2⟩
  intro a ha
  apply (le_div_iff₀ (he.1 n)).2
  nlinarith [hn a ha, le_abs_self B]

end MatedCRT

#print axioms MatedCRT.ae_projected_harmonic_spatial_modulus_of_holder_data
