import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.UniformFromModuli

/-! # Pointwise boundary reduction for corrected Lemma 3.6 -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- Convergence of the projected discrete harmonic extension at boundary
points. This is the boundary-strip part of `LEMMA36-REPLACEMENT.md`,
lines 543–574. -/
def CorrectedBoundaryPointwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, ContinuousOn ψ (closedBall z r) → ∀ y ∈ sphere z r,
    TendstoInProbability S.P (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y)
      (fun _ => ψ y)

/-- The rescaled LBM exit expectation at an interior point is almost surely
the deterministic Poisson extension. -/
theorem ae_lbmExitExpectation_eq_poisson {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {r : ℝ} {z y : ℂ}
    (hr : 0 < r) (hy : y ∈ ball z r) {ψ : ℂ → ℝ}
    (hψ : ContinuousOn ψ (closedBall z r)) :
    ∀ᵐ ω ∂S.P,
      (∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y) = discPoissonExtension ψ z r y := by
  have hm₀ := hS.m₀_pos hγ hγ2
  filter_upwards [hS.isLQGClock] with ω hc
  rw [discPoissonExtension_of_mem hy, ← integral_pathExitPosition_eq_discPoissonIntegral hr hψ hy]
  refine integral_congr_ae ?_
  filter_upwards [(hc y).2, ae_planarBrownianMotion_eval_zero y,
    ae_planarBrownianMotion_exit_any_ball_lt_top y z r] with b hclock hstart hfin
  rw [rescaledLBMExitPosition_eq_brownianExitPosition isOpen_ball hclock
    (by rw [hstart]; exact hy) hfin hm₀, pathExitPosition_eq_eval_exitTime]

/-- The unrestricted-walk exit argument handles the interior; only boundary
pointwise convergence remains to obtain pointwise Poisson convergence on the
closed disc. -/
theorem correctedPoissonPointwise_of_projectedExit_boundary (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (hcell : CorrectedProjectedExitCellStep 𝒮)
    (hboundary : CorrectedBoundaryPointwiseStep 𝒮) : CorrectedPoissonPointwiseStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ y hy
  by_cases hyInterior : y ∈ ball z r
  · exact (correctedHarmonic_pointwise_of_projectedExit 𝒮 h211 hexc hX hcell hγ hγ2 hρ hρ1
      S hS hr hball hψ hyInterior).congr_ae
      (ae_lbmExitExpectation_eq_poisson hγ hγ2 S hS hr hyInterior hψ)
  · have hyBoundary : y ∈ sphere z r := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hy, hyInterior⟩
    rw [discPoissonExtension_of_notMem hyInterior]
    exact hboundary γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ y hyBoundary

/-- Interior convergence and a closed-disc modulus also imply convergence at
the boundary, by approximation from inside the disc. -/
theorem correctedBoundaryPointwise_of_projectedExit_modulus (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (hcell : CorrectedProjectedExitCellStep 𝒮)
    (hmod : CorrectedHarmonicModulusStep 𝒮) : CorrectedBoundaryPointwiseStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ y hy t ht
  apply ENNReal.tendsto_nhds_zero.2
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have ht3 : 0 < t / 3 := by linarith
  obtain ⟨δF, hδF, hF⟩ := hmod γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ
    (t / 3) ht3 (e / 2) he2
  have hcont := continuousOn_discPoissonExtension hr (hψ.mono sphere_subset_closedBall)
  obtain ⟨δU, hδU, hU⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall z r).uniformContinuousOn_of_continuous hcont) (t / 3) ht3
  have hyclosed : y ∈ closedBall z r := sphere_subset_closedBall hy
  have hycl : y ∈ closure (ball z r) := by rw [closure_ball z hr.ne']; exact hyclosed
  obtain ⟨w, hw, hwy⟩ := Metric.mem_closure_iff.mp hycl (min δF δU) (lt_min hδF hδU)
  have hdistF : dist y w < δF := hwy.trans_le (min_le_left δF δU)
  have hdistU : dist w y < δU := by
    simpa [dist_comm] using hwy.trans_le (min_le_right δF δU)
  have hUw := hU w (ball_subset_closedBall hw) y hyclosed hdistU
  rw [Real.dist_eq, discPoissonExtension_of_notMem (disjoint_left.mp sphere_disjoint_ball hy)] at hUw
  have hpoint := (correctedHarmonic_pointwise_of_projectedExit 𝒮 h211 hexc hX hcell hγ hγ2 hρ hρ1
    S hS hr hball hψ hw).congr_ae (ae_lbmExitExpectation_eq_poisson hγ hγ2 S hS hr hw hψ)
  have hpointε := ENNReal.tendsto_nhds_zero.1 (hpoint (t / 3) ht3) (e / 2) he2
  filter_upwards [hF, hpointε] with ε hFε hpointε
  calc
    S.P {ω | t < |projectedDiscreteHarmonicExtension S r z ψ ε ω y - ψ y|} ≤
        S.P ({ω | ∃ x ∈ closedBall z r, ∃ x' ∈ closedBall z r, dist x x' < δF ∧
          t / 3 < |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
            projectedDiscreteHarmonicExtension S r z ψ ε ω x'|} ∪
          {ω | t / 3 < |projectedDiscreteHarmonicExtension S r z ψ ε ω w -
            discPoissonExtension ψ z r w|}) := by
      apply measure_mono
      intro ω hbad
      simp only [mem_ofPred_eq, mem_union] at *
      by_contra hn
      simp only [not_or, not_lt] at hn
      have hfirst : |projectedDiscreteHarmonicExtension S r z ψ ε ω y -
          projectedDiscreteHarmonicExtension S r z ψ ε ω w| ≤ t / 3 := by
        by_contra hc
        exact hn.1 ⟨y, hyclosed, w, ball_subset_closedBall hw, hdistF, lt_of_not_ge hc⟩
      have hsecond := hn.2
      have htri := abs_add_le
        (projectedDiscreteHarmonicExtension S r z ψ ε ω y -
          projectedDiscreteHarmonicExtension S r z ψ ε ω w)
        (projectedDiscreteHarmonicExtension S r z ψ ε ω w - discPoissonExtension ψ z r w)
      have htri' := abs_add_le
        ((projectedDiscreteHarmonicExtension S r z ψ ε ω y -
          projectedDiscreteHarmonicExtension S r z ψ ε ω w) +
          (projectedDiscreteHarmonicExtension S r z ψ ε ω w - discPoissonExtension ψ z r w))
        (discPoissonExtension ψ z r w - ψ y)
      have heq : ((projectedDiscreteHarmonicExtension S r z ψ ε ω y -
          projectedDiscreteHarmonicExtension S r z ψ ε ω w) +
          (projectedDiscreteHarmonicExtension S r z ψ ε ω w - discPoissonExtension ψ z r w)) +
          (discPoissonExtension ψ z r w - ψ y) =
          projectedDiscreteHarmonicExtension S r z ψ ε ω y - ψ y := by ring
      rw [heq] at htri'
      linarith
    _ ≤ _ := (measure_union_le _ _).trans (by simpa only [ENNReal.add_halves] using add_le_add hFε hpointε)

/-- The convergence assertion follows from the projected cell comparison and
the closed-disc asymptotic modulus. -/
theorem correctedHarmonicConvergence_of_projectedExit_modulus (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (hcell : CorrectedProjectedExitCellStep 𝒮)
    (hmod : CorrectedHarmonicModulusStep 𝒮) : CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_uniform 𝒮 (correctedPoissonUniform_of_modulus 𝒮
    (correctedPoissonPointwise_of_projectedExit_boundary 𝒮 h211 hexc hX hcell
      (correctedBoundaryPointwise_of_projectedExit_modulus 𝒮 h211 hexc hX hcell hmod)) hmod)

end MatedCRT
