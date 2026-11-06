import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelopeOn
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedFunctional
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity

/-!
# Truncated walk convergence for path functionals (Theorem 2.11)

For a path functional `G`, bounded and continuous (within continuous paths) at almost every rescaled
LBM path from `z`, the conditional expectations of `G` along the interpolated walk converge in
probability to those along the LBM path (`walkFunctional_tendstoInProbability_of_ae_continuousWithin`).
Continuity is only required on the class of continuous paths, which is where the walk and the LBM
paths live; this is the hypothesis satisfied by the truncated occupation functional at regular exits
(`TruncatedFunctional.lean`). The proof is Theorem 2.11 (`RandomWalkToLBMStmt`, bounded Lipschitz
tests) with the path-class envelopes (`PathEnvelopeOn.lean`). The measurability input
`LBMPathFunctionalMeasurableStep` is taken as a hypothesis.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- **Truncated walk convergence** (Theorem 2.11 for path functionals continuous within continuous paths
at almost every rescaled LBM path). -/
theorem walkFunctional_tendstoInProbability_of_ae_continuousWithin (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (z : ℂ)
    (G : (ℝ≥0 → ℂ) → ℝ) (M : ℝ) (hM : ∀ w : ℝ≥0 → ℂ, Continuous w → |G w| ≤ M)
    (hGW : ∀ ε ω, AEStronglyMeasurable (fun x => G (interpolatedWalk ε (S.η ω) (S.mε ε) x))
      (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)))
    (hcont : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion z,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {w : ℝ≥0 → ℂ | Continuous w} ∧
      PathFunctionalContinuousWithinAt {w : ℝ≥0 → ℂ | Continuous w} G
        (rescaledLBMPath (S.clock ω) S.m₀ b)) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, G (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z))
      (fun ω => ∫ b, G (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  set c : ℝ := max M 1 with hc_def
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc0 : c ≠ 0 := hc.ne'
  have hGc : ∀ w ∈ {w : ℝ≥0 → ℂ | Continuous w}, |G w / c| ≤ 1 := by
    intro w hw
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    exact (hM w hw).trans (le_max_left _ _)
  have key := tendstoInProbability_of_ae_continuousWithin_pathFunctional S.P
    (Q := fun ε ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z))
    (fun _ _ => inferInstance)
    (W := fun ε ω x => interpolatedWalk ε (S.η ω) (S.mε ε) x)
    (R := fun _ => planarBrownianMotion z) (fun _ => inferInstance)
    (X := fun ω b => rescaledLBMPath (S.clock ω) S.m₀ b)
    (fun F hF => h211 γ hγ hγ2 Ω S hS ({z} : Set ℂ) isCompact_singleton z rfl F hF)
    {w : ℝ≥0 → ℂ | Continuous w} ⟨fun _ => 0, continuous_const⟩
    (fun w => G w / c) hGc
    (fun ε ω => Filter.Eventually.of_forall fun x => continuous_interpolatedWalk ε (S.mε ε) (S.η ω) x)
    (fun ε ω => (continuous_id.div_const c).comp_aestronglyMeasurable (hGW ε ω))
    (fun F hF ε ω => (interpolatedWalkMeasurableStep ε (S.mε ε) (S.η ω) (S.mult ε ω)
      (vertexOf ε (S.η ω) z)).1 F hF)
    (fun F hF => (hX γ hγ hγ2 Ω S hS z F hF).1)
    (fun F hF => (hX γ hγ hγ2 Ω S hS z F hF).2)
    (by
      filter_upwards [hcont] with ω hω
      filter_upwards [hω] with b hb
      exact ⟨hb.1, hb.2.div_const c⟩)
  have key2 := tendstoInProbability_const_mul key hc
  have e1 : ∀ ε ω, ∫ x, G (interpolatedWalk ε (S.η ω) (S.mε ε) x)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z) =
      c * ∫ x, G (interpolatedWalk ε (S.η ω) (S.mε ε) x) / c
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z) := by
    intro ε ω
    rw [← integral_const_mul]
    congr 1
    funext x
    field_simp
  have e2 : ∀ ω, ∫ b, G (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z =
      c * ∫ b, G (rescaledLBMPath (S.clock ω) S.m₀ b) / c ∂planarBrownianMotion z := by
    intro ω
    rw [← integral_const_mul]
    congr 1
    funext b
    field_simp
  have hfun1 : (fun ε ω => ∫ x, G (interpolatedWalk ε (S.η ω) (S.mε ε) x)
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z)) =
      fun ε ω => c * ∫ x, G (interpolatedWalk ε (S.η ω) (S.mε ε) x) / c
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z) :=
    funext fun ε => funext fun ω => e1 ε ω
  have hfun2 : (fun ω => ∫ b, G (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z) =
      fun ω => c * ∫ b, G (rescaledLBMPath (S.clock ω) S.m₀ b) / c ∂planarBrownianMotion z :=
    funext fun ω => e2 ω
  rw [hfun1, hfun2]
  exact key2

end MatedCRT
