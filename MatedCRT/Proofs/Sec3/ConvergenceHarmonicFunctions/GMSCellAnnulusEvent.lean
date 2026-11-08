import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellSizeEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSAnnulusSurvival
import MatedCRT.Steps.Sec3.PolynomialGoodEventIntersection

/-! Joint cell-size and annulus good event in outer probability. -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls
open scoped ENNReal

/-- The cell-size and GMS annulus conditions hold jointly with polynomially
high probability. The exceptional-set bound uses outer measure; the event is
not asserted to be environment measurable. -/
theorem MatedCRTEnv.IsValid.cellSize_and_annulus_polyHighProb
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ a : ℝ} (hS : S.IsValid 𝒮 γ)
    (hcell : CellSizeEstimateStmt 𝒮) (hgms : GMSAnnulusDisconnectionStmt 𝒮)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : a < 2 / (2 + γ) ^ 2) :
    ∃ β p κ C ε₀ : ℝ, 0 < β ∧ 0 < p ∧ p < 1 ∧ 0 < κ ∧ 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ¬ ((∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
        (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
          ball z (2 * s) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
            {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}))} ≤
        ENNReal.ofReal (C * ε ^ κ) := by
  obtain ⟨α, β, hα, hβ, hρg⟩ := hgms.with_subunit_probability γ hγ hγ2
  obtain ⟨p, hp, hp1, henv⟩ := hρg ρ hρ hρ1
  obtain ⟨D, δ, hD, hδ, hG⟩ := henv Ω S hS
  obtain ⟨k, hk, C, ε₁, hε₁, hE⟩ :=
    cellSize_polyHighProb_of_lt_critical 𝒮 hcell hγ hγ2 hρ hρ1 ha S hS
  refine ⟨β, p, min k α, max C 0 + D, min ε₁ (min δ 1), hβ, hp, hp1,
    lt_min hk hα, add_nonneg (le_max_right _ _) hD,
    lt_min hε₁ (lt_min hδ one_pos), ?_⟩
  intro ε hε hsmall
  have hε₁' : ε < ε₁ := hsmall.trans_le (min_le_left _ _)
  have hδ' : ε < δ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let E : Set Ω := {ω | ∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
    diam (cell ε (S.η ω) i) ≤ ε ^ a}
  let F : Set Ω := {ω | ∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
    ball z (2 * s) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
    ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
      {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
        walkDisconnectsBeforeHit (S.mult ε ω)
          (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}}
  have he : S.P Eᶜ ≤ ENNReal.ofReal (max C 0 * ε ^ k) := by
    apply (hE ε hε hε₁').trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _)
  have hf : S.P Fᶜ ≤ ENNReal.ofReal (D * ε ^ α) := hG ε hε hδ' hε1
  exact measure_compl_inter_le_polynomial S.P E F hε hε1.le (le_max_right _ _) hD he hf

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.cellSize_and_annulus_polyHighProb
