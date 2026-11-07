import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitSize
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent
import MatedCRT.External.SLE
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableLocalBounds
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ModulusFromRandomBounds

/-! Boundary and Laplacian bounds for the discrete Dirichlet problem. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

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

/-- Hölder boundary data and locally measurable solution values give an
environment-measurable size bound on the cells meeting the disk. -/
theorem MatedCRTEnv.IsValid.dirichlet_measurable_size_bound
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s)))
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b))
    (hversion : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), v ω a = F (e n) ω a) :
    ∃ B : Ω → ℝ, Measurable[S.envSigma] B ∧ (∀ ω, 1 ≤ B ω) ∧
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
          |matedLaplacian (S.mult (e n) ω) (F (e n) ω) a| ≤ C) ∧
        (∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), |F (e n) ω a| ≤ B ω / e n) := by
  obtain ⟨s, hs, L, χ, hχ, _, hh⟩ := hφ
  have hc : ContinuousOn (fun x => |φ x|) (closedBall z (r + s)) := (hh.continuousOn hχ).abs
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (r + s)).bddAbove_image hc
  have hφb : ∀ x ∈ closedBall z (r + s), |φ x| ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  have hb := ae_eventual_dirichlet_size_of_data h28 hm h218 h217 hγ hγ2 hρ hρ1 S hS
    hr hs hD ψ φ hC hψ hφb e he he0 F hF
  have hb' : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), e n * |F (e n) ω a| ≤ C := by
    filter_upwards [hb] with ω ⟨B, hB⟩
    exact ⟨B, hB.mono fun _ hn => hn.2⟩
  obtain ⟨B, hBm, hB, hbound⟩ := hS.exists_measurable_local_bound_of_eventual
    (ball z r) (Or.inl isOpen_ball) isBounded_ball e he.1 (fun ω n => F (e n) ω) hversion hb'
  refine ⟨B, hBm, hB, ?_⟩
  filter_upwards [hb, hbound] with ω ⟨_, hlap⟩ hboundω
  filter_upwards [hlap] with n hn
  exact ⟨hn.1, hboundω n⟩

/-- Prepared tightness gives the interior modulus when measurable versions of
the discrete solutions are available. -/
theorem MatedCRTEnv.IsValid.dirichlet_modulus_of_measurable_versions
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψ : ∃ C : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s)))
    (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b))
    (hversion : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧ ∀ᵐ ω ∂S.P, v ω = F ε ω)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ ball z r)
    (t : ℝ) (ht : 0 < t) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < d ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ δ := by
  obtain ⟨C, hC⟩ := hψ
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hψ' : ∀ x ∈ ball z r, |ψ x| ≤ C' := fun x hx => (hC x hx).trans (le_max_left _ _)
  apply hS.rescale_modulus_of_eventual_random_bounds h31 hγ hγ2 hρ hρ1
    (ball z r) hD isOpen_ball (isConnected_ball hr) K hK hKD F hversion ?_ t ht hδ
  intro e he
  have hepoly := isPolySummableScales_of_lt_half_pow he
  have he0 : Tendsto e atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) from
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    · intro n; exact (he n).1.le
    · intro n; exact (he n).2.le
  have hv : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices (e n) (S.η ω) (ball z r), v ω a = F (e n) ω a := by
    intro n
    obtain ⟨v, hv, heq⟩ := hversion (e n) (he n).1
    refine ⟨v, hv, ?_⟩
    filter_upwards [heq] with ω hω a ha
    rw [hω]
  obtain ⟨B, hBm, hBpos, hb⟩ := hS.dirichlet_measurable_size_bound h28 hm h218 h217
    hγ hγ2 hρ hρ1 hr hD ψ φ hC' hψ' hφ e hepoly he0 F hF hv
  refine ⟨id, strictMono_id, fun ω => max C' (B ω), ?_, ?_, ?_⟩
  · exact measurable_const.max hBm
  · intro ω
    exact lt_of_lt_of_le (by linarith [hBpos ω]) (le_max_right _ _)
  · filter_upwards [hb] with ω hω
    filter_upwards [hω] with n hn
    simp only [id_eq]
    refine ⟨fun a ha => (hn.1 a ha).trans (le_max_left _ _), fun a ha => ?_⟩
    exact (hn.2 a ha).trans (div_le_div_of_nonneg_right (le_max_right _ _) (he n).1.le)

end MatedCRT
