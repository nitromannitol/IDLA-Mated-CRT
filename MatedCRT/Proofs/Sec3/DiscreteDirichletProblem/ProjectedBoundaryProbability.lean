import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedBoundaryValues

/-! Projected boundary data converge uniformly in probability on the circle. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- For projected Hölder data, small cells imply uniform convergence of the
rescaled discrete boundary values on the Euclidean circle. -/
theorem projectedDirichlet_boundary_values_in_probability
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (ψ φ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ)
    (hdata : ProjectedDirichletData S r z ψ φ F) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω))
      (fun _ => φ) (sphere z r) := by
  obtain ⟨C, χ, hχ, _, hφ⟩ := hdata.2.2.1
  obtain ⟨K, hK, hscale⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscale⟩ := hscale Ω S hS
  intro δ hδ
  have hpow : Tendsto (fun t : ℝ => t ^ (χ : ℝ)) (𝓝 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (χ : ℝ) (Or.inr χ.coe_nonneg)).tendsto
    have hχr : (0 : ℝ) < χ := by exact_mod_cast hχ
    simpa only [Real.zero_rpow (ne_of_gt hχr)] using h
  have hlim : Tendsto (fun d : ℝ => (C : ℝ) * (2 * d) ^ (χ : ℝ)) (𝓝 0) (𝓝 0) := by
    have htwo : Tendsto (fun d : ℝ => 2 * d) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto (fun d : ℝ => 2 * d) (𝓝 0) (𝓝 (2 * 0)))
    simpa using tendsto_const_nhds.mul (hpow.comp htwo)
  have hsmall : ∀ᶠ d in 𝓝[>] (0 : ℝ), (C : ℝ) * (2 * d) ^ (χ : ℝ) < δ :=
    (hlim.eventually (Iio_mem_nhds hδ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨d, hdsmall, hd⟩ := (hsmall.and self_mem_nhdsWithin).exists
  let R : ℝ := ‖z‖ + r + 1
  have hprob := hS.probTendsToOne_small_cells R d hd
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have hev := ENNReal.tendsto_nhds_zero.1 hprob e he
  filter_upwards [hev, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hε₀)] with ε hE hε hεsmall
  have hKpos : 0 < K := by linarith
  have hM : S.mε ε ≠ 0 := ne_of_gt ((mul_pos (inv_pos.mpr hKpos) (inv_pos.mpr hε)).trans_le
    (hscale ε hε hεsmall).1)
  calc
    S.P {ω | ∃ x ∈ sphere z r, δ < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x - φ x|} ≤
      S.P {ω | ∀ k ∈ cellVertices ε (S.η ω) (ball 0 R),
        diam (cell ε (S.η ω) k) ≤ d}ᶜ := by
      apply measure_mono_ae
      filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hdata.2.2.2 ε hε] with ω harea hp hF
      rintro ⟨x, hx, hbig⟩ hgood
      have hcell := Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
      have hxR : x ∈ ball (0 : ℂ) R := by
        rw [mem_ball]
        have ht := dist_triangle x z 0
        have hxs := mem_sphere.mp hx
        simp only [dist_zero_right] at ht ⊢
        dsimp [R]
        linarith
      have hdiam := hgood (vertexOf ε (S.η ω) x) ⟨x, hcell, hxR⟩
      have hbound := abs_rescale_projected_boundary_sub_le hε hr hM harea.1 φ hφ
        (F ε ω) hF.2 hx hcell hdiam
      linarith
    _ ≤ e := hE

end MatedCRT

#print axioms MatedCRT.projectedDirichlet_boundary_values_in_probability
