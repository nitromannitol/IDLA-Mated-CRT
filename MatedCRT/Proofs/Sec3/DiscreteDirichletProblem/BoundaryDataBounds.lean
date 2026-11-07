import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitSize
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent
import MatedCRT.External.SLE

/-! Boundary and Laplacian bounds for the discrete Dirichlet problem. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls

/-- Cell-size and median estimates bound the prescribed data along any
polynomially summable mesh sequence. -/
theorem ae_eventual_dirichlet_data_bounds
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) {C M : ℝ}
    (hψ : ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∀ x ∈ closedBall z (r + s), |φ x| ≤ M)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)) :
    ∃ A : ℝ, ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (F (e n) ω) a| ≤ C) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), e n * |F (e n) ω b| ≤ A) := by
  obtain ⟨K, hK, hscale⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscale⟩ := hscale Ω S hS
  obtain ⟨a, ha, _, hrad⟩ := exists_vanishing_closedBall_cellRadius 𝒮 h28 hγ hγ2 hρ hρ1 hr hD S hS
  have hrad0 : Tendsto (fun n => e n ^ a) atTop (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.comp he0
  have hsmall : ∀ᶠ n in atTop, e n < ε₀ ∧ e n ^ a < s :=
    (he0.eventually (gt_mem_nhds hε₀)).and (hrad0.eventually (gt_mem_nhds hs))
  refine ⟨K * M, ?_⟩
  filter_upwards [Tightness.ae_eventually_mem_of_polyHighProb hrad he,
    ae_all_iff.mpr (fun n => hF (e n) (he.1 n)), hS.isAreaParametrized] with ω hradω hFω hη
  filter_upwards [hradω, hsmall] with n hcell hn
  have hε := he.1 n
  have hscale' := hscale (e n) hε hn.1
  have hK0 : 0 < K := by linarith
  have hmpos : 0 < S.mε (e n) :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hK0) (inv_pos.mpr hε)) hscale'.1
  constructor
  · intro b hb
    rw [(hFω n).1 b hb]
    exact hψ _ (Sec7.cell_subset_ball_of_mem_interiorCellVertices hη.1 hb
      (Sec7.vertexPoint_mem_cell hε.le b))
  · intro b hb
    have hFb := (hFω n).2 b hb
    obtain ⟨p, hpc, hps⟩ := hb
    have hb' : b ∈ cellVertices (e n) (S.η ω) (closedBall z r) :=
      ⟨p, hpc, sphere_subset_closedBall hps⟩
    have hpdist := hcell b hb' p hpc
    have hv : vertexPoint (e n) (S.η ω) b ∈ closedBall z (r + s) := by
      rw [mem_closedBall]
      have hp := mem_sphere.mp hps
      linarith [dist_triangle (vertexPoint (e n) (S.η ω) b) p z]
    rw [hFb, abs_mul, abs_of_pos hmpos]
    have hscaled : e n * S.mε (e n) ≤ K := by
      have h := mul_le_mul_of_nonneg_left hscale'.2 hε.le
      have heq : e n * (K * (e n)⁻¹) = K := by field_simp
      linarith
    nlinarith [mul_le_mul hscaled (hφ _ hv) (abs_nonneg (φ (vertexPoint (e n) (S.η ω) b))) hK0.le]

/-- The prescribed Dirichlet data yield the eventual size estimate needed
for prepared potential tightness. -/
theorem ae_eventual_dirichlet_size_of_data
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) {C M : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∀ x ∈ closedBall z (r + s), |φ x| ≤ M)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)) :
    ∀ᵐ ω ∂S.P, ∃ B : ℝ, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (F (e n) ω) a| ≤ C) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), e n * |F (e n) ω a| ≤ B) := by
  obtain ⟨A, hdata⟩ := ae_eventual_dirichlet_data_bounds h28 hm hγ hγ2 hρ hρ1 S hS
    hr hs hD ψ φ hψ hφ e he he0 F hF
  have hsize := ae_eventual_dirichlet_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS
    hr hD e he he0 (fun ω n => F (e n) ω) hC hdata
  filter_upwards [hdata, hsize] with ω hd ⟨B, hB⟩
  exact ⟨B, hd.and hB |>.mono (fun _ h => ⟨h.1.1, h.2⟩)⟩

end MatedCRT
