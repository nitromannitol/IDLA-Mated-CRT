import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.OfSteps

/-!
# Lemma 3.7 from the interior and boundary estimates

The deterministic assembly covers the closed ball by a smaller closed ball
and its complement, using the triangle inequality on the boundary layer.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Local convergence and simultaneous boundary control imply convergence
on the closed ball. -/
theorem uniformOn_closedBall_of_interior_boundary {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℝ → Ω → ℂ → ℝ) (v : Ω → ℂ → ℝ)
    (z : ℂ) (r : ℝ)
    (hinner : ∀ r' : ℝ, 0 < r' → r' < r →
      TendstoUniformlyOnInProbability P u v (closedBall z r'))
    (hboundary : ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |u ε ω x| ∨ δ < |v ω x|} ≤ e) :
    TendstoUniformlyOnInProbability P u v (closedBall z r) := by
  classical
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨r', hr'0, hr'r, hboundary'⟩ := hboundary (δ / 2) (by linarith) (e / 2) he2
  have hinner' := ENNReal.tendsto_nhds_zero.1 (hinner r' hr'0 hr'r δ hδ) (e / 2) he2
  filter_upwards [hinner', hboundary'] with ε hi hb
  calc
    P {ω | ∃ x ∈ closedBall z r, δ < |u ε ω x - v ω x|} ≤
        P ({ω | ∃ x ∈ closedBall z r', δ < |u ε ω x - v ω x|} ∪
          {ω | ∃ x ∈ closedBall z r \ closedBall z r',
            δ / 2 < |u ε ω x| ∨ δ / 2 < |v ω x|}) := by
      apply measure_mono
      intro ω hω
      obtain ⟨x, hx, herr⟩ := hω
      by_cases hx' : x ∈ closedBall z r'
      · exact Or.inl ⟨x, hx', herr⟩
      · right
        refine ⟨x, ⟨hx, hx'⟩, ?_⟩
        by_contra hn
        push Not at hn
        have htri := abs_sub (u ε ω x) (v ω x)
        linarith [hn.1, hn.2]
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hi hb
    _ = e := ENNReal.add_halves e

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
