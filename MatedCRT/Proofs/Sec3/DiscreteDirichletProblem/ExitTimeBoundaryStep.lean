import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedFiniteBoundary
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.BoundaryModulusInputs

/-! The ordinary exit-time barrier in the corrected Dirichlet proof. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Boundary decay of the normalized ordinary exit-time barrier along
deterministic rapidly decreasing scales. This is the remaining barrier
estimate in corrected Lemma 3.5, Step 3, paper lines 1575–1605. The
quantifier over every such sequence is stronger than the paper's prepared
deterministic subsequence; this step remains unproved. -/
def OrdinaryExitTimeBoundaryDecayStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ e : ℕ → ℝ, (∀ n, 0 < e n ∧ e n < (1 / 2) ^ n) →
    ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
        (S.mε (e n))⁻¹ * (expectedExitTime (S.mult (e n) ω)
          (interiorCellVertices (e n) (S.η ω) (ball z r))
          (vertexOf (e n) (S.η ω) x)).toReal ≤ k

/-- The ordinary exit-time barrier gives the boundary-pair modulus, using
the finite-domain Green representation for measurable versions. -/
theorem projectedDirichletBoundaryModulusStep_of_exitTime_decay
    (𝒮 : SpaceFillingSLEModel) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hfinite : FiniteDomainDirichletRepresentation)
    (hdecay : OrdinaryExitTimeBoundaryDecayStep 𝒮) :
    ProjectedDirichletBoundaryModulusStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hD ψ φ F hdata t ht a ha
  have : ContractibleSpace (ball z r) :=
    (convex_ball z r).contractibleSpace ⟨z, by simpa using hr⟩
  have hsimply : SimplyConnectedSpace (ball z r) := SimplyConnectedSpace.ofContractible _
  exact projected_boundary_modulus_of_finiteDomain_and_exitTime_decay hH hm h218 h217 hfinite
    hγ hγ2 hρ hρ1 S hS hr hD hsimply ψ φ F hdata
    (hdecay γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hD) t ht ha

/-- Corrected Lemma 3.5 reduces to its projected pointwise step and the
ordinary exit-time boundary barrier, together with the stated estimates. -/
theorem discreteDirichletProblemCorrected_of_exitTime_decay
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hfinite : FiniteDomainDirichletRepresentation)
    (hP : ProjectedDirichletPointwiseStep 𝒮) (hdecay : OrdinaryExitTimeBoundaryDecayStep 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  discreteDirichletProblemCorrected_of_boundary_modulus 𝒮 h27 hm h218 hH h28 hfinite hP
    (projectedDirichletBoundaryModulusStep_of_exitTime_decay 𝒮 hH hm h218
      (boundedExitTimeRV_of_steps h27) hfinite hdecay)

/-- Divisible-sandpile convergence with the ordinary exit-time barrier in
place of the projected Dirichlet boundary hypothesis. -/
theorem convergenceDivisible_of_exitTime_decay_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : ConeEnvironmentScalingStep 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hdecay : OrdinaryExitTimeBoundaryDecayStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_boundary_modulus_coneScaling 𝒮 hm h210 h34 h214 h28 h218 hH h27 hcone
    hfinite hP (projectedDirichletBoundaryModulusStep_of_exitTime_decay 𝒮 hH hm h218
      (boundedExitTimeRV_of_steps h27) hfinite hdecay)

end MatedCRT

#print axioms MatedCRT.projectedDirichletBoundaryModulusStep_of_exitTime_decay
#print axioms MatedCRT.discreteDirichletProblemCorrected_of_exitTime_decay
#print axioms MatedCRT.convergenceDivisible_of_exitTime_decay_coneScaling
