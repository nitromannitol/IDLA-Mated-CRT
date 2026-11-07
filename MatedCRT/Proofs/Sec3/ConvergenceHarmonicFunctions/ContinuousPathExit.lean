import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.Final

/-! # Continuous boundary data for the unrestricted-walk exit step -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The continuous-mapping part of corrected Lemma 3.6, for arbitrary continuous
boundary data on the closed disc. See `LEMMA36-REPLACEMENT.md`, lines 105–119. -/
theorem continuousBoundary_interpolatedExit_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {r : ℝ} {z y : ℂ}
    (hr : 0 < r) (hy : y ∈ ball z r) {ψ : ℂ → ℝ}
    (hcont : ContinuousOn ψ (closedBall z r)) :
    TendstoInProbability S.P (interpolatedExitExpectation S r z y ψ)
      (fun ω => ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y) := by
  have hψR : Continuous fun x => ψ (ballRetraction z r x) :=
    hcont.comp_continuous (continuous_ballRetraction z hr) (ballRetraction_mem z hr)
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont
  have hKpos : 0 < |C| + 1 := by positivity
  have hψK : ∀ x, |ψ (ballRetraction z r x)| ≤ |C| + 1 := fun x => by
    have h1 := hC _ (ballRetraction_mem z hr x)
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self C]
  have hK := tendstoInProbability_const_mul
    (tendstoInProbability_exitValueFunctional 𝒮 h211 hexc hX interpolatedWalkMeasurableStep
      hγ hγ2 S hS hr hy hψR hKpos hψK) hKpos
  have hL : ∀ ε ω, (|C| + 1) * ∫ x, exitValueFunctional z r ψ (|C| + 1)
      (interpolatedWalk ε (S.η ω) (S.mε ε) x) ∂(srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) =
      interpolatedExitExpectation S r z y ψ ε ω := fun ε ω => by
    rw [interpolatedExitExpectation, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change (|C| + 1) * (ψ (ballRetraction z r (pathExitPosition (ball z r)
      (interpolatedWalk ε (S.η ω) (S.mε ε) x))) / (|C| + 1)) = _
    field_simp
  simp only [hL] at hK
  refine hK.congr_ae ?_
  filter_upwards [hS.ae_normalizedLBMExitPosition_mem_sphere hγ hγ2 hy] with ω hω
  rw [← integral_const_mul]
  refine integral_congr_ae (hω.mono fun b hb => ?_)
  change (|C| + 1) * (ψ (ballRetraction z r (pathExitPosition (ball z r)
    (rescaledLBMPath (S.clock ω) S.m₀ b))) / (|C| + 1)) = _
  rw [ballRetraction_of_mem z hr (sphere_subset_closedBall hb)]
  field_simp

end MatedCRT
