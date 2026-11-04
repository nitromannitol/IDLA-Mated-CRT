import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ScaledSecondMoment
import MatedCRT.Proofs.Infra.Setting

/-! Uniform control of normalized exit-time moments on an enlarged ball. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Lemmas 2.17 and 2.18 give a finite, environment-dependent bound for the
normalized second moment, uniformly over the admissible domains and starting
vertices. The event has polynomially high probability as the mesh tends to zero. -/
theorem scaled_secondMoment_finite_bound_polyHighProb {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮)
    (hscale : MepsScalingInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ B : ℝ, 0 < B ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → PolyHighProb S.P fun ε => {ω |
        largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤ ∧
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D,
            ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2 ≤
              ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2} := by
  obtain ⟨α, hα, hmoment⟩ := scaled_secondMoment_polyHighProb h18 hscale hγ hγ2
  obtain ⟨q, hq, h17q⟩ := h17 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨B, hB, hP⟩ := hmoment ρ hρ hρ1
  refine ⟨B, hB, ?_⟩
  intro Ω _ S hS
  let ρ' := (1 + ρ) / 2
  have hρρ' : ρ < ρ' := by dsimp [ρ']; linarith
  have hρ'1 : ρ' < 1 := by dsimp [ρ']; linarith
  have hG : S.P {ω | (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'),
      largestExitTimeRV (S.μ ω) D) < ⊤}ᶜ = 0 := by
    rw [Set.compl_ofPred]
    exact ae_iff.mp (h17q ρ' (hρ.trans hρρ') hρ'1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  obtain ⟨r₁, hr₁, hr₁s⟩ := exists_pos_rpow_lt hα (sub_pos.mpr hρρ')
  apply polyHighProb_of_inter_subset (hP Ω S hS) hG hr₁
  intro ε hε hεr ω hω
  have hGω : (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'),
      largestExitTimeRV (S.μ ω) D) < ⊤ := hω.2
  have hle : largestExitTimeRV (S.μ ω) (ball 0 ρ') ≤
      (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ'), largestExitTimeRV (S.μ ω) D) :=
    le_iSup₂_of_le (ball 0 ρ') Subset.rfl le_rfl
  have hfinite := hle.trans_lt hGω
  refine ⟨hfinite, ?_⟩
  intro D hD hDsub hμ a ha
  have hεα := hr₁s ε hε hεr
  have hsub : thickening (ε ^ α) D ⊆ ball 0 ρ' :=
    ((thickening_subset_of_subset _ hDsub).trans (thickening_ball 0 _ ρ)).trans
      (ball_subset_ball (by linarith))
  have hD' : D ⊆ ball (0 : ℂ) ρ' := hDsub.trans (ball_subset_ball hρρ'.le)
  have hpotential := thickened_logPotential_le_largestExitTimeRV (S.μ ω) D
    (ball 0 ρ') (ε ^ α) hD' hsub
  exact (hω.1 D hD hDsub hμ a ha).trans (by gcongr)

/-- The finite second-moment bound controls every normalized exit-time tail
on the same polynomially high probability event. -/
theorem scaled_exitTime_tail_finite_bound_polyHighProb {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮)
    (hscale : MepsScalingInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∃ B : ℝ, 0 < B ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ → PolyHighProb S.P fun ε => {ω |
        largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤ ∧
        ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ →
          ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
          ∀ a ∈ cellVertices ε (S.η ω) D, ∀ T : ℝ≥0∞, T ≠ ⊤ →
            T * (∫⁻ x in {x | T ≤
                ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
                  (vExitTime (interiorCellVertices ε (S.η ω) D) x : ℝ≥0∞)},
              ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
                (vExitTime (interiorCellVertices ε (S.η ω) D) x : ℝ≥0∞)
                ∂srwLaw (S.mult ε ω) a) ≤
              ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2} := by
  obtain ⟨α, hα, h⟩ := scaled_secondMoment_finite_bound_polyHighProb h17 h18 hscale hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨B, hB, hP⟩ := h ρ hρ hρ1
  refine ⟨B, hB, ?_⟩
  intro Ω _ S hS
  apply (hP Ω S hS).mono
  intro ε ω hω
  refine ⟨hω.1, ?_⟩
  intro D hD hDsub hμ a ha T hT
  exact (scaled_exitTime_tail_le_secondMoment _ _ _ _ T hT).trans
    (hω.2 D hD hDsub hμ a ha)

end MatedCRT
