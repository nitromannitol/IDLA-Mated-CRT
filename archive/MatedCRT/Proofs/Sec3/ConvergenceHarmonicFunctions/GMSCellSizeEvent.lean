import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent

/-! # Polynomially likely cell-size event at a prescribed exponent -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls

/-- The upper bound in the cell-size estimate holds at every
exponent below the critical exponent, with polynomially high probability. -/
theorem cellSize_polyHighProb_of_lt_critical (𝒮 : SpaceFillingSLEModel)
    (h28 : CellSizeEstimateStmt 𝒮) {γ ρ a : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : a < 2 / (2 + γ) ^ 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P fun ε => {ω | ∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
      diam (cell ε (S.η ω) i) ≤ ε ^ a} := by
  let ζ := min ((2 / (2 + γ) ^ 2 - a) / 2) (1 / 2)
  have hζ : 0 < ζ := by
    dsimp [ζ]
    exact lt_min (by linarith) (by norm_num)
  have hζ1 : ζ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hexp : a ≤ 2 / (2 + γ) ^ 2 - ζ := by
    have h := min_le_left ((2 / (2 + γ) ^ 2 - a) / 2) (1 / 2)
    change ζ ≤ _ at h
    linarith
  obtain ⟨p, hp, C, ε₀, hε₀, hprob⟩ := h28 γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS
  refine ⟨p, hp, C, min ε₀ 1, lt_min hε₀ one_pos, ?_⟩
  intro ε hε hsmall
  have hε₀' : ε < ε₀ := hsmall.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hsmall.trans_le (min_le_right _ _)).le
  calc
    _ ≤ S.P {ω | ¬ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) i) ∧
          diam (cell ε (S.η ω) i) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)} := by
      apply measure_mono
      intro ω hbad hgood
      apply hbad
      intro i hi
      exact (hgood i hi).2.trans (Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp)
    _ ≤ _ := hprob ε hε hε₀'

end MatedCRT

#print axioms MatedCRT.cellSize_polyHighProb_of_lt_critical
