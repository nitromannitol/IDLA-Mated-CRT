import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CorrectedInteriorBoundary
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PreparedCompactness

/-! Prepared normalized exit-time convergence with projected Dirichlet data. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- Interior convergence in Lemma 3.7 from the prepared Lemma 3.1 and the
other cited results, including the almost-sure eventual bounds. -/
def NormalizedExitInteriorPreparedCorrectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  UniformConvergenceGreenKernelStmt 𝒮 → DiscreteDirichletProblemCorrectedStmt 𝒮 →
  BoundedExitTimeRVStmt → ExitTimeUpperBoundStmt 𝒮 → DiscretePotentialTightnessPreparedStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ r' : ℝ, r' < r →
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r')

/-- Lemma 3.7 from the prepared interior step and the existing boundary estimates. -/
theorem convergenceNormalizedExitTime_of_corrected_prepared_steps (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (hinterior : NormalizedExitInteriorPreparedCorrectedStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball
  refine ⟨normalizedExitGreenPotential S r z,
    normalizedExitPotentialStep_of_boundedExitTime 𝒮 h217 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball, ?_⟩
  apply uniformOn_closedBall_of_interior_boundary
  · intro r' _ hr'
    exact hinterior h33 h35 h217 h218 h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball r' hr'
  · intro δ hδ e he
    have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
    obtain ⟨r₁, hr₁0, hr₁r, h₁⟩ := discreteExitBoundary_of_corrected_statements 𝒮 h33 h35 h217
      hγ hγ2 hρ hρ1 S hS hr hball hδ he2
    obtain ⟨r₂, hr₂0, hr₂r, h₂⟩ := normalizedExitGreenPotential_boundary_small_of_statements
      𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hδ he2
    refine ⟨max r₁ r₂, lt_of_lt_of_le hr₁0 (le_max_left _ _), max_lt hr₁r hr₂r, ?_⟩
    filter_upwards [h₁] with ε hε
    calc
      S.P {ω | ∃ x ∈ closedBall z r \ closedBall z (max r₁ r₂),
          δ < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x| ∨
          δ < |normalizedExitGreenPotential S r z ω x|} ≤
        S.P ({ω | ∃ x ∈ closedBall z r \ closedBall z r₁,
          δ < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x|} ∪
        {ω | ∃ x ∈ closedBall z r \ closedBall z r₂,
          δ < |normalizedExitGreenPotential S r z ω x|}) := by
            apply measure_mono
            rintro ω ⟨x, ⟨hx, hxout⟩, h⟩
            have hx₁ : x ∉ closedBall z r₁ := fun hx' =>
              hxout (closedBall_subset_closedBall (le_max_left _ _) hx')
            have hx₂ : x ∉ closedBall z r₂ := fun hx' =>
              hxout (closedBall_subset_closedBall (le_max_right _ _) hx')
            rcases h with h | h
            · exact Or.inl ⟨x, ⟨hx, hx₁⟩, h⟩
            · exact Or.inr ⟨x, ⟨hx, hx₂⟩, h⟩
      _ ≤ _ := measure_union_le _ _
      _ ≤ e / 2 + e / 2 := add_le_add hε h₂
      _ = e := ENNReal.add_halves e

/-- The prepared form of Lemma 3.1 yields the interior step of Lemma 3.7. -/
theorem normalizedExitInteriorPreparedCorrectedStep (𝒮 : SpaceFillingSLEModel) :
    NormalizedExitInteriorPreparedCorrectedStep 𝒮 := by
  intro h33 h35 h217 h218 h31 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball r' hr'
  apply normalizedExitInterior_of_discrete_modulus_corrected 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1
    S hS hr hr' hball
  intro t ht e he
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply mesh_modulus_of_dyadic_prepared_compactness S.P (closedBall z r')
    (isCompact_closedBall _ _) _ t ht ?_ ?_ he
  · intro ε hε δ
    obtain ⟨A, hAm, hAe⟩ := hS.exists_envSigma_measurable_exit_oscillation ε hε
      (ball z r) (Or.inl isOpen_ball) (closedBall z r') (isCompact_closedBall _ _) δ t
    apply (hS.nullMeasurableSet_of_envSigma hAm).congr
    filter_upwards [hAe] with ω hω
    exact propext hω
  · exact exit_compactness_dyadic_of_prepared 𝒮 h218 h217 h31 hγ hγ2 hρ hρ1 S hS hr hr' hball

/-- Lemma 3.7 from its prepared tightness input and the cited estimates. -/
theorem convergenceNormalizedExitTime_of_corrected_prepared (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_corrected_prepared_steps 𝒮 h33 h35 h217 h218 h31
    (normalizedExitInteriorPreparedCorrectedStep 𝒮)

/-- Lemma 3.7 with prepared tightness supplied by the discrete estimates. -/
theorem convergenceNormalizedExitTime_of_corrected_prepared_estimates (𝒮 : SpaceFillingSLEModel)
    (hm : MepsScalingInput 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_corrected_prepared 𝒮 h33 h35 h217 h218
    (discretePotentialTightnessPrepared_of_inputs hm h217 h218 hH)

end MatedCRT

#print axioms MatedCRT.convergenceNormalizedExitTime_of_corrected_prepared_estimates
