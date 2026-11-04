import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps

/-!
# Lemma 3.7 from the interior and boundary estimates

The deterministic assembly covers the closed ball by a smaller closed ball
and its complement, using the triangle inequality on the boundary layer.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Local convergence and simultaneous boundary control imply convergence
on the closed ball. -/
theorem uniformOn_closedBall_of_interior_boundary {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℝ → Ω → ℂ → ℝ) (v : Ω → ℂ → ℝ)
    (z : ℂ) (r : ℝ)
    (hinner : ∀ r' : ℝ, 0 < r' → r' < r →
      TendstoUniformlyOnInProbability P u v (closedBall z r'))
    (hboundary : ∀ δ : ℝ, 0 < δ → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ProbTendsToOne P (fun ε => {ω | ∀ x ∈ closedBall z r \ closedBall z r',
        |u ε ω x| ≤ δ ∧ |v ω x| ≤ δ})) :
    TendstoUniformlyOnInProbability P u v (closedBall z r) := by
  classical
  intro δ hδ
  obtain ⟨r', hr'0, hr'r, hboundary'⟩ := hboundary (δ / 2) (by linarith)
  have hinner' : ProbTendsToOne P (fun ε => {ω | ∀ x ∈ closedBall z r',
      |u ε ω x - v ω x| ≤ δ}) := by
    simpa only [ProbTendsToOne, compl_ofPred, not_forall, not_imp, not_le, exists_prop] using
      hinner r' hr'0 hr'r δ hδ
  have hgood : ProbTendsToOne P (fun ε => {ω | ∀ x ∈ closedBall z r,
      |u ε ω x - v ω x| ≤ δ}) := by
    apply (hinner'.inter hboundary').mono_pos
    intro ε hε ω hω x hx
    by_cases hx' : x ∈ closedBall z r'
    · exact hω.1 x hx'
    · have h := hω.2 x ⟨hx, hx'⟩
      calc
        |u ε ω x - v ω x| ≤ |u ε ω x| + |v ω x| := abs_sub _ _
        _ ≤ δ := by linarith [h.1, h.2]
  simpa only [ProbTendsToOne, compl_ofPred, not_forall, not_imp, not_le, exists_prop] using hgood

/-- Lemma 3.7, reduced to the three displayed potential, interior and
boundary steps. -/
theorem convergenceNormalizedExitTime_of_steps (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hpotential : NormalizedExitPotentialStep 𝒮)
    (hinterior : NormalizedExitInteriorStep 𝒮)
    (hboundary : NormalizedExitBoundaryStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball
  refine ⟨normalizedExitGreenPotential S r z, hpotential γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball, ?_⟩
  apply uniformOn_closedBall_of_interior_boundary
  · exact hinterior h33 h29 h219 h35 h31 h28 h217 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
  · exact hboundary h219 h28 h217 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball

end MatedCRT
