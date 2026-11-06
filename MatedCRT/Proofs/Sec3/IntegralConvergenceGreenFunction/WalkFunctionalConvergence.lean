import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkMeasurability

/-!
# Truncated walk convergence for bounded path functionals (Theorem 2.11)

For a bounded measurable functional `G` of paths that is continuous at almost every rescaled LBM path
from `z`, the conditional expectations of `G` along the interpolated walk converge in probability to the
conditional expectations of `G` along the LBM path (`walkFunctional_tendstoInProbability_of_ae_continuous`).
It is built from Theorem 2.11 (`RandomWalkToLBMStmt`, for deterministic bounded Lipschitz functionals),
the Pasch--Hausdorff envelopes (`tendstoInProbability_of_ae_continuous_pathFunctional`), the walk
measurability (`interpolatedWalkMeasurableStep`) and the measurability input
`LBMPathFunctionalMeasurableStep`. This covers deterministic functionals only; the environment-dependent
functionals `φ^{f(ω)}_T` of Lemma 3.4 need the open step E-c2-9.
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- The interpolated walk, as a function of the step sequence `x : ℕ → ℤ`, is measurable for the product
σ-algebra: each time-`t` value is a fixed combination of two coordinates of `x`. -/
theorem measurable_interpolatedWalk (ε mε : ℝ) (η : ℝ → ℂ) :
    Measurable (fun x : ℕ → ℤ => interpolatedWalk ε η mε x) := by
  have hv : Measurable (vertexPoint ε η) := Measurable.of_discrete
  refine Measurable.of_eval fun t => ?_
  unfold interpolatedWalk
  dsimp only
  exact (measurable_const.mul (hv.comp (measurable_pi_apply _))).add
    (measurable_const.mul (hv.comp (measurable_pi_apply _)))

/-- Division by a positive constant preserves continuity of a path functional at a path. -/
theorem pathFunctionalContinuousAt_div_const {G : (ℝ≥0 → ℂ) → ℝ} {w : ℝ≥0 → ℂ}
    (hG : PathFunctionalContinuousAt G w) {c : ℝ} (hc : 0 < c) :
    PathFunctionalContinuousAt (fun v => G v / c) w := by
  intro η hη
  obtain ⟨ρ, hρ, hbound⟩ := hG (η * c) (mul_pos hη hc)
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  have h := hbound v hv
  show |G v / c - G w / c| ≤ η
  rw [← sub_div, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  exact h

/-- **Truncated walk convergence** (Theorem 2.11 for a bounded path functional continuous at almost every
limiting path): for a bounded measurable `G` on paths, `E[G(walk) | h, η] → E[G(X^z) | h]` in probability,
provided `G` is continuous at `X^z` for almost every environment and Brownian path. -/
theorem walkFunctional_tendstoInProbability_of_ae_continuous (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (z : ℂ)
    (G : (ℝ≥0 → ℂ) → ℝ) (hGm : Measurable G) (M : ℝ) (hM : ∀ w, |G w| ≤ M)
    (hcont : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion z,
      PathFunctionalContinuousAt G (rescaledLBMPath (S.clock ω) S.m₀ b)) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, G (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z))
      (fun ω => ∫ b, G (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion z) := by
  have : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  set c : ℝ := max M 1 with hc_def
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc0 : c ≠ 0 := hc.ne'
  have hGc : ∀ w, |G w / c| ≤ 1 := by
    intro w
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    exact (hM w).trans (le_max_left _ _)
  have key := tendstoInProbability_of_ae_continuous_pathFunctional S.P
    (Q := fun ε ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) z))
    (fun _ _ => inferInstance)
    (W := fun ε ω x => interpolatedWalk ε (S.η ω) (S.mε ε) x)
    (R := fun _ => planarBrownianMotion z) (fun _ => inferInstance)
    (X := fun ω b => rescaledLBMPath (S.clock ω) S.m₀ b)
    (fun F hF => h211 γ hγ hγ2 Ω S hS ({z} : Set ℂ) isCompact_singleton z rfl F hF)
    (fun w => G w / c) hGc
    (fun ε ω => ((hGm.div_const c).comp
      (measurable_interpolatedWalk ε (S.mε ε) (S.η ω))).aestronglyMeasurable)
    (fun F hF ε ω => (interpolatedWalkMeasurableStep ε (S.mε ε) (S.η ω) (S.mult ε ω)
      (vertexOf ε (S.η ω) z)).1 F hF)
    (fun F hF => (hX γ hγ hγ2 Ω S hS z F hF).1)
    (fun F hF => (hX γ hγ hγ2 Ω S hS z F hF).2)
    (by
      filter_upwards [hcont] with ω hω
      filter_upwards [hω] with b hb
      exact pathFunctionalContinuousAt_div_const hb hc)
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
