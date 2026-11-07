import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitCompactness
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitGreenPointwise
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryPairLocal
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PreparedCompactness

/-! Interior convergence of the ordinary exit-time barrier. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- The ordinary expected exit-time barrier converges uniformly in
probability on compact subdisks. -/
theorem expectedExit_uniform_interior_of_prepared
    (𝒮 : SpaceFillingSLEModel) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r) (hball : ball z r ⊆ ball 0 ρ) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω) (fun a =>
        (expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r)) a).toReal))
      (fun ω x => 6 * normalizedExitGreenPotential S r z ω x) (closedBall z r') := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply uniformInProbability_of_separate_moduli S.P (closedBall z r') (isCompact_closedBall z r') _ _
  · intro y hy
    have h := pointwise_expectedExitTime_of_green_and_estimates h34 h217 h218 hm
      hγ hγ2 hρ hρ1 S hS hr hball (mem_ball.2 ((mem_closedBall.1 hy).trans_lt hr'))
    convert h using 1
    · rfl
    · funext ω
      simp only [normalizedExitGreenPotential]
      ring
  · intro t ht e he
    apply mesh_modulus_of_dyadic_prepared_compactness S.P (closedBall z r')
      (isCompact_closedBall _ _) _ t ht ?_ ?_ he
    · intro ε hε δ
      obtain ⟨v, hvm, hv⟩ := hS.exists_envSigma_measurable_expectedExitTime ε (ball z r) (Or.inl isOpen_ball)
      apply hS.nullMeasurableSet_rescale_boundary_pair_local ε hε _ v hvm
        (closedBall z r') (closedBall z r') (isCompact_closedBall _ _) (isCompact_closedBall _ _)
        Subset.rfl ?_ δ t
      filter_upwards [hv] with ω hω a ha
      exact hω a
    · intro e he ψ hψ
      obtain ⟨φ, hφ, hc⟩ := expectedExit_compactness_dyadic_of_prepared 𝒮 h218 h217 h31
        hγ hγ2 hρ hρ1 S hS hr hball e he ψ hψ
      refine ⟨φ, hφ, ?_⟩
      filter_upwards [hc] with ω hω θ hθ
      obtain ⟨η, hη, u, hu, hconv⟩ := hω θ hθ
      have hsub : closure (closedBall z r') ⊆ ball z r := by
        rw [isClosed_closedBall.closure_eq]
        exact closedBall_subset_ball hr'
      exact ⟨η, hη, u, hu.mono (subset_closure.trans hsub), hconv _ (isCompact_closedBall _ _) hsub⟩
  · intro t ht e he
    obtain ⟨δ, hδ, hmod⟩ := normalizedExitGreenPotential_modulus_small 𝒮 h33 h217
      hγ hγ2 hρ hρ1 S hS hr hr' hball (show 0 < t / 6 by positivity) he
    refine ⟨δ, hδ, (measure_mono ?_).trans hmod⟩
    rintro ω ⟨x, hx, y, hy, hxy, hbad⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [← mul_sub, abs_mul, abs_of_pos (show (0 : ℝ) < 6 by norm_num)] at hbad
    linarith

end MatedCRT

#print axioms MatedCRT.expectedExit_uniform_interior_of_prepared
