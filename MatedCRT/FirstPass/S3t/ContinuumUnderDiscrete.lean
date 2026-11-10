import MatedCRT.FirstPass.S3t.BLExtension
import MatedCRT.FirstPass.S3t.Bounds
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PathFunctionalStep
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkExitMeasurable
import MatedCRT.Draft.Section2

/-!
# Truncated quenched laws, Step 5: convergence of the continuum stopped functional under the discrete law
(fp-S3t-truncated-continuum, z10)

Source: notes/fp-gaps/CHATGPT-idla-3-4-truncated-laws.md, Step 5 (l.308-338). Step 2 (`quenched_integral_tendsto_of_bl_of_ae_continuous`,
`BLExtension.lean`) with the bounded-Lipschitz input `RandomWalkToLBMStmt 𝒮` (Theorem 2.11), applied to the path
functional `H = stoppedOccupation (ball z r) T g`. Its measurability inputs are discharged by existing lemmas:
`interpolatedWalkMeasurableStep` (quenched side), `lbmPathFunctionalMeasurableStep_holds` (Brownian side), and
`aestronglyMeasurable_stoppedOccupation_interpolatedWalk` (proved here, as the existing truncated-occupation lemma uses
`(pathExitTime D w).toReal` rather than `(min (ofReal T) (pathExitTime D w)).toReal`).

The only input not yet proved is `hcont`: continuity of the stopped occupation at the almost surely regular exits of the
limiting LBM (Step 3 `continuousAt_stoppedOccupation` with Step 4 `ae_regularExit_rescaledLBM`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- Measurability of the stopped occupation of the interpolated walk, on the walk law. -/
theorem aestronglyMeasurable_stoppedOccupation_interpolatedWalk {μ : Measure (ℕ → ℤ)} (ε : ℝ) (η : ℝ → ℂ)
    (m : ℝ) (z : ℂ) (r T : ℝ) {g : ℂ → ℝ} (hg : Continuous g) :
    AEStronglyMeasurable (fun x : ℕ → ℤ => stoppedOccupation (ball z r) T g (interpolatedWalk ε η m x)) μ := by
  have hτ : Measurable (fun x : ℕ → ℤ => pathExitTime (ball z r) (interpolatedWalk ε η m x)) :=
    measurable_pathExitTime_interpolatedWalk ε η m z r
  have ha : Measurable (fun x : ℕ → ℤ =>
      (min (ENNReal.ofReal T) (pathExitTime (ball z r) (interpolatedWalk ε η m x))).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_const.min hτ)
  have hu : Measurable (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
      g (interpolatedWalk ε η m x t.toNNReal)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun x => hg.comp ((continuous_interpolatedWalk ε m η x).comp continuous_real_toNNReal))
      (fun t => hg.measurable.comp (measurable_interpolatedWalk_apply ε η m t.toNNReal))
  set E : Set (ℝ × (ℕ → ℤ)) :=
    {q | 0 < q.1} ∩
      {q | q.1 ≤ (min (ENNReal.ofReal T) (pathExitTime (ball z r) (interpolatedWalk ε η m q.2))).toReal} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (ha.comp measurable_snd))
  have hFm := hu.indicator hEm
  have hsm : StronglyMeasurable (fun x : ℕ → ℤ => ∫ t : ℝ,
      E.indicator (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
        g (interpolatedWalk ε η m x t.toNNReal)) (t, x)) :=
    StronglyMeasurable.integral_prod_left' hFm.stronglyMeasurable
  have heq : (fun x : ℕ → ℤ => stoppedOccupation (ball z r) T g (interpolatedWalk ε η m x)) =
      fun x : ℕ → ℤ => ∫ t : ℝ,
        E.indicator (Function.uncurry fun (t : ℝ) (x : ℕ → ℤ) =>
          g (interpolatedWalk ε η m x t.toNNReal)) (t, x) := by
    funext x
    unfold stoppedOccupation
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  rw [heq]
  exact hsm.aestronglyMeasurable

/-- **Step 5.** Convergence in probability of the quenched expectation of the stopped occupation `H = stoppedOccupation
(ball z r) T g` under the discrete walk law from `vertexOf ε η y`, to the continuum quenched expectation under planar
Brownian motion from `y`. The inputs are the bounded-Lipschitz convergence `RandomWalkToLBMStmt 𝒮` (Theorem 2.11) and
`hcont`, the almost-sure continuity of `H` at the regular exits of the limiting LBM (Steps 3 and 4; `_hy` is the
starting-point hypothesis that Step 4 needs when `hcont` is derived). -/
theorem stoppedOccupation_tendsto_discrete {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (hS : S.IsValid 𝒮 γ) {y z : ℂ} {r T : ℝ} (_hy : y ∈ ball z r) (hT : 0 ≤ T) {g : ℂ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, |g x| ≤ M)
    (hcont : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      PathFunctionalContinuousAt (stoppedOccupation (ball z r) T g) (rescaledLBMPath (S.clock ω) S.m₀ b)) :
    MatedCRT.TendstoInProbability S.P
      (fun ε ω => ∫ q, stoppedOccupation (ball z r) T g (interpolatedWalk ε (S.η ω) (S.mε ε) q)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, stoppedOccupation (ball z r) T g (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  -- continuity within the whole path space `𝒞 = univ` is continuity
  have hcontW : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      PathFunctionalContinuousWithinAt Set.univ (stoppedOccupation (ball z r) T g)
        (rescaledLBMPath (S.clock ω) S.m₀ b) :=
    hcont.mono fun ω h => h.mono fun b hb η hη => by
      obtain ⟨ρ, hρ, hh⟩ := hb η hη
      exact ⟨ρ, hρ, fun v _ hv => hh v hv⟩
  exact quenched_integral_tendsto_of_bl_of_ae_continuous
    (fun ε ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) (fun _ _ => inferInstance)
    (fun ε ω q => interpolatedWalk ε (S.η ω) (S.mε ε) q) (planarBrownianMotion y)
    (fun ω b => rescaledLBMPath (S.clock ω) S.m₀ b) Set.univ Set.univ_nonempty
    (fun _ _ => Eventually.of_forall fun _ => Set.mem_univ _)
    (Eventually.of_forall fun _ => Eventually.of_forall fun _ => Set.mem_univ _)
    (fun F hF => h211 γ hγ0 hγ2 Ω S hS {y} isCompact_singleton y (mem_singleton y) F hF)
    (fun F hF ε ω => (interpolatedWalkMeasurableStep ε (S.mε ε) (S.η ω) (S.mult ε ω)
      (vertexOf ε (S.η ω) y)).1 F hF)
    (fun F hF => ((lbmPathFunctionalMeasurableStep_holds 𝒮) γ hγ0 hγ2 Ω S hS y F hF).1)
    (fun F hF => ((lbmPathFunctionalMeasurableStep_holds 𝒮) γ hγ0 hγ2 Ω S hS y F hF).2)
    (stoppedOccupation (ball z r) T g) ⟨T * M, fun w => abs_stoppedOccupation_le (D := ball z r) hgb hT w⟩
    (fun ε ω => aestronglyMeasurable_stoppedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε) z r T hg)
    hcontW

end MatedCRT.TruncatedLaws
