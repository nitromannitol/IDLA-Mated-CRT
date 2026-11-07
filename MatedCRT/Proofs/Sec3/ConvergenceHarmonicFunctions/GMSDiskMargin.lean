import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSUniformRate
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusRadialSeparation

/-! # Comparison-disk margin for the GMS estimate -/

namespace MatedCRT

open Set Metric Filter Topology

/-- A disk contained in a centered disk has its radius plus the distance of
its center bounded by the radius of the centered disk. -/
theorem dist_center_add_radius_le_of_ball_subset {z : ℂ} {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hball : ball z r ⊆ ball 0 ρ) :
    dist z 0 + r ≤ ρ := by
  have hc : closedBall z r ⊆ closedBall (0 : ℂ) ρ := by
    have h := closure_mono hball
    rwa [closure_ball z hr.ne', closure_ball (0 : ℂ) hρ.ne'] at h
  obtain ⟨e, _, he⟩ := exists_outward_unit_direction 0 z
  have hray := he r hr.le
  have hmem : z + r • e ∈ closedBall z r := mem_closedBall.mpr (by rw [hray.1])
  have hdist := mem_closedBall.mp (hc hmem)
  rw [hray.2] at hdist
  exact hdist

/-- A fixed positive comparison-disk margin eventually dominates both the
cell scale and the mesoscopic annulus scale. The conclusion is uniform over
all disks contained in the smaller centered disk. -/
theorem eventually_gms_disk_margin {ρ ρ' a c : ℝ}
    (hρ : 0 < ρ) (hρρ' : ρ < ρ') (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ (z : ℂ) (r : ℝ), 0 < r →
      ball z r ⊆ ball 0 ρ →
      r + 3 * ε ^ a + dist z 0 + ε ^ a + 2 * (ε ^ c / 2) < ρ' := by
  have ha0 : Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ a) :=
      continuous_id.rpow_const (fun _ => Or.inr ha.le)
    simpa [Real.zero_rpow ha.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc0 : Tendsto (fun ε : ℝ => ε ^ c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ c) :=
      continuous_id.rpow_const (fun _ => Or.inr hc.le)
    simpa [Real.zero_rpow hc.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hgap : 0 < (ρ' - ρ) / 5 := by linarith
  filter_upwards [ha0 (Iio_mem_nhds hgap), hc0 (Iio_mem_nhds hgap)] with ε hεa hεc
  intro z r hr hball
  have hbound := dist_center_add_radius_le_of_ball_subset hr hρ hball
  change ε ^ a < (ρ' - ρ) / 5 at hεa
  change ε ^ c < (ρ' - ρ) / 5 at hεc
  linarith

/-- If the mesoscopic exponent is smaller than each cell and annulus
exponent, its scale eventually dominates the microscopic cutoff. -/
theorem eventually_gms_mesoscopic_scale {a b c : ℝ} (ha : c < a) (hb : c < b) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      4 * (100 * ε ^ a + ε ^ b) ≤ ε ^ c / 2 := by
  have ha' : 0 < a - c := sub_pos.mpr ha
  have hb' : 0 < b - c := sub_pos.mpr hb
  have hlimA : Tendsto (fun ε : ℝ => ε ^ (a - c)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ (a - c)) :=
      continuous_id.rpow_const (fun _ => Or.inr ha'.le)
    simpa [Real.zero_rpow ha'.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlimB : Tendsto (fun ε : ℝ => ε ^ (b - c)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε ^ (b - c)) :=
      continuous_id.rpow_const (fun _ => Or.inr hb'.le)
    simpa [Real.zero_rpow hb'.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hlimA (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
    hlimB (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000)),
    self_mem_nhdsWithin] with ε hεa hεb hε
  have hε0 : 0 < ε := hε
  have hpos : 0 ≤ ε ^ c := (Real.rpow_pos_of_pos hε0 _).le
  change ε ^ (a - c) < 1 / 1000 at hεa
  change ε ^ (b - c) < 1 / 1000 at hεb
  have hA := mul_le_mul_of_nonneg_left hεa.le hpos
  have hB := mul_le_mul_of_nonneg_left hεb.le hpos
  have hpowA : ε ^ a = ε ^ c * ε ^ (a - c) := by
    rw [← Real.rpow_add hε0]
    congr 1; ring
  have hpowB : ε ^ b = ε ^ c * ε ^ (b - c) := by
    rw [← Real.rpow_add hε0]
    congr 1; ring
  rw [hpowA, hpowB]
  nlinarith

end MatedCRT

#print axioms MatedCRT.dist_center_add_radius_le_of_ball_subset
#print axioms MatedCRT.eventually_gms_disk_margin

#print axioms MatedCRT.eventually_gms_mesoscopic_scale
