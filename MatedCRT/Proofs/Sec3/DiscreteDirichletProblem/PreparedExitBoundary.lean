import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitTimeBoundaryStep
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedBoundaryProbability

/-! Projected boundary control after deterministic preparation. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Prepared ordinary exit-time boundary decay, the barrier estimate in
corrected Lemma 3.5, Step 3, paper lines 1555–1605. -/
def PreparedExitTimeBoundaryDecayStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ e : ℕ → ℝ, (∀ n, 0 < e n ∧ e n < (1 / 2) ^ n) →
  ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
        (S.mε (e (ψ (φ n))))⁻¹ * (expectedExitTime (S.mult (e (ψ (φ n))) ω)
          (interiorCellVertices (e (ψ (φ n))) (S.η ω) (ball z r))
          (vertexOf (e (ψ (φ n))) (S.η ω) x)).toReal ≤ k

/-- Prepared exit-time decay implies the projected boundary-pair modulus. -/
theorem projectedDirichletBoundaryModulusStep_of_prepared_exitTime_decay
    (𝒮 : SpaceFillingSLEModel) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hfinite : FiniteDomainDirichletRepresentation)
    (hdecay : PreparedExitTimeBoundaryDecayStep 𝒮) :
    ProjectedDirichletBoundaryModulusStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hD ψ φ F hdata t ht a ha
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  have : ContractibleSpace (ball z r) :=
    (convex_ball z r).contractibleSpace ⟨z, by simpa using hr⟩
  have hsimply : SimplyConnectedSpace (ball z r) := SimplyConnectedSpace.ofContractible _
  obtain ⟨C, hC⟩ := hdata.1
  apply mesh_modulus_of_prepared_dyadic_modulus S.P
    (fun δ ε => {ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r, dist x y < δ ∧
      t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|}) ?_ ?_ ?_ ha
  · intro δ δ' ε hδ ω hω
    obtain ⟨x, hx, y, hy, hxy, hval⟩ := hω
    exact ⟨x, hx, y, hy, hxy.trans_le hδ, hval⟩
  · intro δ ε hε
    obtain ⟨v, hvm, hv⟩ := hS.exists_envSigma_projected_solution_of_finiteDomain
      hγ hγ2 hfinite ε hε hr ψ φ hdata.2.1 hdata.2.2.1 (F ε) (hdata.2.2.2 ε hε)
    obtain ⟨w, hwm, hw⟩ := hS.exists_envSigma_projected_closedDisk_version ε hr φ
      hdata.2.2.1 (F ε) v hvm hv (by
        filter_upwards [hdata.2.2.2 ε hε] with ω hω
        exact hω.2)
    exact hS.nullMeasurableSet_rescale_boundary_pair_local ε hε (F ε) w hwm
      (closedBall z r) (sphere z r) (isCompact_closedBall z r)
      (isCompact_sphere z r) sphere_subset_closedBall hw δ t
  · intro e he θ hθ
    obtain ⟨σ, hσ, hq⟩ := hdecay γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hD e he θ hθ
    refine ⟨σ, hσ, ?_⟩
    have he' : ∀ n, 0 < e (θ (σ n)) ∧ e (θ (σ n)) < (1 / 2 : ℝ) ^ n := by
      intro n
      refine ⟨(he _).1, (he _).2.trans_le ?_⟩
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hσ.id_le n |>.trans (hθ.id_le _))
    have hpoly := isPolySummableScales_of_lt_half_pow he'
    filter_upwards [ae_projected_boundary_pair_modulus_of_exitTime_boundary_decay hH hm h218 h217
      hγ hγ2 hρ hρ1 S hS hr hD hsimply (fun n => e (θ (σ n))) hpoly hpoly.tendsto_zero
      ψ φ hdata.2.2.1 (le_max_right C 0)
      (fun x hx => (hC x hx).trans (le_max_left C 0)) F hdata.2.2.2 hq] with ω hω
    obtain ⟨δ, hδ, hmod⟩ := hω t ht
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hmod] with n hn
    rintro ⟨x, hx, y, hy, hxy, hval⟩
    exact (not_lt_of_ge (hn x hx y hy (by simpa [dist_eq_norm] using hxy.le))) hval

/-- Corrected Lemma 3.5 from its pointwise and prepared barrier steps. -/
theorem discreteDirichletProblemCorrected_of_prepared_exitTime_decay
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hfinite : FiniteDomainDirichletRepresentation)
    (hP : ProjectedDirichletPointwiseStep 𝒮) (hdecay : PreparedExitTimeBoundaryDecayStep 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  discreteDirichletProblemCorrected_of_boundary_modulus 𝒮 h27 hm h218 hH h28 hfinite hP
    (projectedDirichletBoundaryModulusStep_of_prepared_exitTime_decay 𝒮 hH hm h218
      (boundedExitTimeRV_of_steps h27) hfinite hdecay)

/-- Divisible-sandpile convergence from the prepared exit-time barrier. -/
theorem convergenceDivisible_of_prepared_exitTime_decay_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : ConeEnvironmentScalingStep 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hdecay : PreparedExitTimeBoundaryDecayStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_boundary_modulus_coneScaling 𝒮 hm h210 h34 h214 h28 h218 hH h27 hcone
    hfinite hP (projectedDirichletBoundaryModulusStep_of_prepared_exitTime_decay 𝒮 hH hm h218
      (boundedExitTimeRV_of_steps h27) hfinite hdecay)

end MatedCRT

#print axioms MatedCRT.projectedDirichletBoundaryModulusStep_of_prepared_exitTime_decay
#print axioms MatedCRT.discreteDirichletProblemCorrected_of_prepared_exitTime_decay
#print axioms MatedCRT.convergenceDivisible_of_prepared_exitTime_decay_coneScaling
