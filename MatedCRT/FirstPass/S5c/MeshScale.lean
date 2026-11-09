import MatedCRT.External.SLE

/-!
# FIRST PASS, Lemma 5.3 and E-c1-5: mesh scaling along a sequence (B2 plumbing)

From the external input `MepsScalingInput` (External/SLE.lean:63; the median of the embedded exit time satisfies
`C⁻¹ ε⁻¹ ≤ m_ε ≤ C ε⁻¹` for small `ε`), along any sequence of positive meshes `ε_k → 0` we get eventually
`0 < m_{ε_k}` and `1 ≤ m_{ε_k} ε_k C`. These are the hypotheses `hmε` and `hCmε` of `surplus_bound_of_threshold`
(PathwiseSurplus.lean:22) along the B2 subsequence (CHATGPT-5-1-B2-Ec15.md §1).
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology

/-- **Mesh scaling along a sequence** (B2): see the module docstring. -/
theorem mesh_scale_eventually {𝒮 : SpaceFillingSLEModel} (hM : MepsScalingInput 𝒮) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∃ C : ℝ, 1 < C ∧ ∀ ε : ℕ → ℝ, (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
      ∀ᶠ k in atTop, 0 < S.mε (ε k) ∧ 1 ≤ S.mε (ε k) * ε k * C := by
  obtain ⟨C, hC1, hCS⟩ := hM γ hγ0 hγ2
  obtain ⟨ε₀, hε₀, hbound⟩ := hCS Ω S hS
  refine ⟨C, hC1, fun ε hpos hlim => ?_⟩
  have hC0 : 0 < C := by linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hε₀)] with k hk
  have hεk : 0 < ε k := hpos k
  obtain ⟨h1, h2⟩ := hbound (ε k) hεk hk
  have hεC : 0 < ε k * C := mul_pos hεk hC0
  have hlow : 0 < C⁻¹ * (ε k)⁻¹ := mul_pos (inv_pos.2 hC0) (inv_pos.2 hεk)
  refine ⟨lt_of_lt_of_le hlow h1, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right h1 hεC.le
  have hid : C⁻¹ * (ε k)⁻¹ * (ε k * C) = 1 := by
    field_simp [hεk.ne', hC0.ne']
  linarith

end MatedCRT.S5c
