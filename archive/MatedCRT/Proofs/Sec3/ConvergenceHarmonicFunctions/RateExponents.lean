import MatedCRT.Draft.Section3HarmonicCorrected
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicCutoff

/-! # Exponents in the corrected stopping-location comparison -/

namespace MatedCRT

/-- The full range in the replacement proof, lines 377–386, can be obtained
by choosing the cell-size exponent strictly below its upper endpoint. -/
theorem exists_cell_exponent_for_sameWalk_rate {γ bAnn χ q : ℝ}
    (hγ : 0 < γ) (hχ : 0 < χ) (hq : 0 < q)
    (hqmax : q < χ * min (2 / (2 + γ) ^ (2 : ℕ)) bAnn) :
    ∃ a : ℝ, 0 < a ∧ a < 2 / (2 + γ) ^ (2 : ℕ) ∧
      q < min a bAnn * χ := by
  have hu : 0 < 2 / (2 + γ) ^ (2 : ℕ) := by positivity
  have hqa : q / χ < 2 / (2 + γ) ^ (2 : ℕ) := by
    apply (div_lt_iff₀ hχ).2
    have := lt_of_lt_of_le hqmax (mul_le_mul_of_nonneg_left (min_le_left _ _) hχ.le)
    nlinarith
  have hqb : q / χ < bAnn := by
    apply (div_lt_iff₀ hχ).2
    have := lt_of_lt_of_le hqmax (mul_le_mul_of_nonneg_left (min_le_right _ _) hχ.le)
    nlinarith
  refine ⟨(q / χ + 2 / (2 + γ) ^ (2 : ℕ)) / 2, ?_, ?_, ?_⟩
  · positivity
  · linarith
  · have hm : q / χ < min ((q / χ + 2 / (2 + γ) ^ (2 : ℕ)) / 2) bAnn :=
      lt_min (by linarith) hqb
    exact (div_lt_iff₀ hχ).1 hm

/-- Every exponent in the stated rate range admits a cell-size exponent and
a mesh threshold at which the annulus cutoff is below the excursion scale. -/
theorem exists_cell_exponent_and_mesh_threshold_for_sameWalk_rate
    {γ bAnn χ q : ℝ} (hγ : 0 < γ) (hχ : 0 < χ) (hq : 0 < q)
    (hqmax : q < χ * min (2 / (2 + γ) ^ (2 : ℕ)) bAnn) :
    ∃ a δ : ℝ, 0 < a ∧ a < 2 / (2 + γ) ^ (2 : ℕ) ∧ 0 < δ ∧
      q < min a bAnn * χ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        4 * (100 * ε ^ a + ε ^ bAnn) ≤ ε ^ (q / χ) / 2 := by
  obtain ⟨a, ha, hau, haq⟩ := exists_cell_exponent_for_sameWalk_rate hγ hχ hq hqmax
  have hp : q / χ < min a bAnn := (div_lt_iff₀ hχ).2 haq
  obtain ⟨δ, hδ, hcut⟩ :=
    mesoscopic_cutoff_eventually_le_smaller_power (a := a) (b := bAnn) hp
  exact ⟨a, δ, ha, hau, hδ, haq, hcut⟩

end MatedCRT
