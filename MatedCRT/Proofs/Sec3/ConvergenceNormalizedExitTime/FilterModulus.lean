import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AsymptoticModulusFromCompactness

/-! Sequential criterion for a modulus as the mesh tends to zero. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- If every positive mesh sequence tending to zero has an asymptotic modulus,
then the modulus holds for the full one-sided mesh limit. -/
theorem asymptotic_modulus_of_mesh_sequences
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → ℝ → Set Ω)
    (hmono : ∀ δ δ' ε, δ ≤ δ' → E δ ε ⊆ E δ' ε)
    (hseq : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ n in atTop, P (E δ (ε n)) ≤ e)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (E δ ε) ≤ e := by
  classical
  by_contra hcontra
  have hbad : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < 1 / ((n : ℝ) + 1) ∧
      e < P (E (1 / ((n : ℝ) + 1)) ε) := by
    intro n
    by_contra hnone
    apply hcontra
    refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show 0 < 1 / ((n : ℝ) + 1) by positivity)] with ε hε
    intro hεpos
    change (0 : ℝ) < ε at hεpos
    have hεlt : ε < 1 / ((n : ℝ) + 1) := by
      have := hε
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hεpos] at this
      exact this
    exact le_of_not_gt (fun hgt => hnone ⟨ε, hεpos, hεlt, hgt⟩)
  choose ε hε using hbad
  have hlim : Tendsto ε atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
    · exact fun n => (hε n).1.le
    · exact fun n => (hε n).2.1.le
  obtain ⟨δ, hδ, hgood⟩ := hseq ε (fun n => (hε n).1) hlim e he
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).eventually (Iio_mem_nhds hδ)
  obtain ⟨n, hn, hn'⟩ := (hsmall.and hgood).exists
  have hcompare : P (E (1 / ((n : ℝ) + 1)) (ε n)) ≤ P (E δ (ε n)) :=
    measure_mono (hmono _ _ _ hn.le)
  exact (not_lt_of_ge (hcompare.trans hn')) (hε n).2.2

end MatedCRT
