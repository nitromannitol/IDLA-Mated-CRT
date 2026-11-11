import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffPathUniform

/-!
# Lemma 3.4: grid step approximations of bounded Lipschitz path functionals

For a bounded Lipschitz path functional `F` (for the local uniform distance), the map `v ↦ F (stepPath m v)` is continuous on
grid sequences `v : ℕ → ℂ`, where `stepPath m v` is the step path `t ↦ v ⌊m t⌋` of mesh `1/m`; and the grid step
approximations of a continuous path converge to it in the local uniform distance. Consequently the measurability of `F` along
approximate Liouville paths reduces to the measurability of finitely many evaluations, without any measurable structure on the
path space (paper argument for `LBMPathFunctionalMeasurableStep`).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- The step path with grid values `v` at mesh `1 / m`: `t ↦ v ⌊m t⌋`. -/
noncomputable def stepPath (m : ℕ) (v : ℕ → ℂ) (t : ℝ≥0) : ℂ :=
  v ⌊(m : ℝ≥0) * t⌋₊

/-- **Continuity on grid values.** For a bounded Lipschitz path functional `F`, the functional of the step path is continuous
in the grid values (product topology on `ℕ → ℂ`). -/
theorem continuous_boundedLipschitz_stepPath {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    (m : ℕ) : Continuous fun v : ℕ → ℂ => F (stepPath m v) := by
  obtain ⟨-, L, hL⟩ := hF
  refine continuous_iff_continuousAt.2 fun v => ?_
  have hd : Tendsto (fun w : ℕ → ℂ => localUniformDist (stepPath m w) (stepPath m v)) (𝓝 v) (𝓝 0) := by
    refine tendsto_localUniformDist_of_forall_le (fun w => stepPath m w) (stepPath m v) fun K η hη => ?_
    have hcoord : ∀ᶠ w in 𝓝 v, ∀ j ∈ Finset.range (m * K + 1), dist (w j) (v j) < η :=
      (Filter.eventually_all_finset _).2 fun j _ =>
        Metric.tendsto_nhds.1 ((continuous_apply j).tendsto v) η hη
    filter_upwards [hcoord] with w hw t ht
    have hfl : ⌊(m : ℝ≥0) * t⌋₊ ≤ m * K := by
      have h1 : (m : ℝ≥0) * t ≤ ((m * K : ℕ) : ℝ≥0) := by
        push_cast
        exact mul_le_mul_of_nonneg_left ht zero_le
      exact (Nat.floor_le_floor h1).trans (le_of_eq (Nat.floor_natCast _))
    have hidx : ⌊(m : ℝ≥0) * t⌋₊ ∈ Finset.range (m * K + 1) := Finset.mem_range.2 (by omega)
    have key := hw _ hidx
    rw [dist_eq_norm] at key
    exact key.le
  show Tendsto (fun w => F (stepPath m w)) (𝓝 v) (𝓝 (F (stepPath m v)))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun w => dist_nonneg) (fun w => ?_) (by simpa using hd.const_mul L)
  rw [Real.dist_eq]
  exact hL _ _

/-- **Grid step approximations of a continuous path converge.** The step paths `t ↦ f (⌊m t⌋ / m)` converge to `f` in the
local uniform distance as the mesh `1 / m` tends to zero. -/
theorem tendsto_localUniformDist_gridStep {f : ℝ≥0 → ℂ} (hf : Continuous f) :
    Tendsto (fun m : ℕ => localUniformDist (fun t => f (((⌊(m : ℝ≥0) * t⌋₊ : ℕ) : ℝ≥0) / (m : ℝ≥0))) f)
      atTop (𝓝 0) := by
  refine tendsto_localUniformDist_of_forall_le _ f fun K η hη => ?_
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) η hη
  filter_upwards [eventually_gt_atTop ⌈1 / δ⌉₊] with m hm t ht
  have hm1 : 1 / δ < (m : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := lt_trans (one_div_pos.2 hδ) hm1
  have hmδ : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hδ] at hm1
    linarith
  have hk1 : ((⌊(m : ℝ≥0) * t⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) * (t : ℝ) := by
    have h := NNReal.coe_le_coe.2 (Nat.floor_le (by positivity : (0 : ℝ≥0) ≤ (m : ℝ≥0) * t))
    simpa using h
  have hk2 : (m : ℝ) * (t : ℝ) < ((⌊(m : ℝ≥0) * t⌋₊ : ℕ) : ℝ) + 1 := by
    have h := NNReal.coe_lt_coe.2 (Nat.lt_floor_add_one ((m : ℝ≥0) * t))
    simpa using h
  set k : ℕ := ⌊(m : ℝ≥0) * t⌋₊ with hk
  set u : ℝ≥0 := (k : ℝ≥0) / (m : ℝ≥0) with hu
  have hu_real : (u : ℝ) = (k : ℝ) / (m : ℝ) := by simp [hu]
  have hut : (u : ℝ) ≤ (t : ℝ) := by
    rw [hu_real, div_le_iff₀ hmpos]
    linarith
  have htu : (t : ℝ) - (u : ℝ) < 1 / (m : ℝ) := by
    have h3 : (t : ℝ) < ((k : ℝ) + 1) / (m : ℝ) := by
      rw [lt_div_iff₀ hmpos]
      linarith
    rw [hu_real]
    linarith [h3, add_div (k : ℝ) 1 (m : ℝ)]
  have hd : dist u t < δ := by
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hut)]
    linarith
  have hut' : u ≤ t := by exact_mod_cast hut
  have hmem : u ∈ Icc (0 : ℝ≥0) K := ⟨zero_le, hut'.trans ht⟩
  have htmem : t ∈ Icc (0 : ℝ≥0) K := ⟨zero_le, ht⟩
  have key := hcont u hmem t htmem hd
  rw [dist_eq_norm] at key
  exact key.le

end MatedCRT
