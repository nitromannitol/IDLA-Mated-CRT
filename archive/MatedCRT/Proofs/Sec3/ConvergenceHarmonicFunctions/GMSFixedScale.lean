import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSDiskMargin

/-! # A fixed comparison scale for the GMS estimate -/

namespace MatedCRT

open Set Metric Filter Topology

/-- For a fixed disk in a smaller centered disk, a positive comparison radius
can be chosen independently of the mesh. It eventually dominates the cell and
annulus scales while its enlarged disk remains inside the larger disk. -/
theorem exists_fixed_gms_comparison_scale {ρ ρ' a b r : ℝ}
    (hρ : 0 < ρ) (hρρ' : ρ < ρ') (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∃ T : ℝ, 0 < T ∧ T ≤ r ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 ∧
        2 * (100 * ε ^ a + ε ^ b) < T ∧
        ∀ z : ℂ, ball z r ⊆ ball 0 ρ →
          r + 3 * ε ^ a + dist z 0 + ε ^ a + 2 * T < ρ' := by
  let T := min r ((ρ' - ρ) / 8)
  have hT : 0 < T := lt_min hr (by linarith)
  have hTr : T ≤ r := min_le_left _ _
  have hTgap : T ≤ (ρ' - ρ) / 8 := min_le_right _ _
  let c := min (T / 404) ((ρ' - ρ) / 8)
  have hc : 0 < c := lt_min (by linarith) (by linarith)
  have hcT : c ≤ T / 404 := min_le_left _ _
  have hcgap : c ≤ (ρ' - ρ) / 8 := min_le_right _ _
  have hlimA : Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ a) :=
      continuous_id.rpow_const (fun _ => Or.inr ha.le)
    simpa [Real.zero_rpow ha.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlimB : Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ b) :=
      continuous_id.rpow_const (fun _ => Or.inr hb.le)
    simpa [Real.zero_rpow hb.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ⟨T, hT, hTr, ?_⟩
  filter_upwards [hlimA (Iio_mem_nhds hc), hlimB (Iio_mem_nhds hc),
    self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hεa hεb hε hεone
  change ε ^ a < c at hεa
  change ε ^ b < c at hεb
  have hεpos : 0 < ε := hε
  refine ⟨hεpos, hεone.le, ?_, ?_⟩
  · linarith
  · intro z hball
    have hbound := dist_center_add_radius_le_of_ball_subset hr hρ hball
    linarith

end MatedCRT

#print axioms MatedCRT.exists_fixed_gms_comparison_scale
