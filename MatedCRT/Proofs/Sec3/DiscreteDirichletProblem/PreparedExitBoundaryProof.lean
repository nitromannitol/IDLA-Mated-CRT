import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ConcentricRadii
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitInterior
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitMonotone
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedExitBoundary

/-! Prepared exit-time boundary decay from larger concentric disks. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- The prepared ordinary exit-time barrier follows from Green occupation,
interior compactness, and the exit-time estimates. -/
theorem preparedExitTimeBoundaryDecayStep_of_green_and_estimates
    (𝒮 : SpaceFillingSLEModel) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) :
    PreparedExitTimeBoundaryDecayStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball e he ψ hψ
  let ρ' : ℝ := (1 + ρ) / 2
  have hρρ' : ρ < ρ' := by dsimp [ρ']; linarith
  have hρ'1 : ρ' < 1 := by dsimp [ρ']; linarith
  have hρ'0 : 0 < ρ' := by linarith
  obtain ⟨R, hR, hRlim, Rmax, hmax, hmaxball⟩ :=
    exists_concentric_radii hr hρ hρρ' hball
  have hRball (j : ℕ) : ball z (R j) ⊆ ball 0 ρ' :=
    (ball_subset_ball (hmax j)).trans hmaxball
  let F : ℕ → ℝ → Ω → ℂ → ℝ := fun j ε ω =>
    rescale (S.mε ε) ε (S.η ω) (fun a =>
      (expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z (R j))) a).toReal)
  let g : ℕ → Ω → ℂ → ℝ := fun j ω x => 6 * normalizedExitGreenPotential S (R j) z ω x
  have hconv : ∀ j, TendstoUniformlyOnInProbability S.P (F j) (g j) (closedBall z r) := by
    intro j
    exact expectedExit_uniform_interior_of_prepared 𝒮 h34 h33 h217 h218 hm h31
      hγ hγ2 hρ'0 hρ'1 S hS (lt_trans hr (hR j)) (hR j) (hRball j)
  have heψ : ∀ n, 0 < e (ψ n) ∧ e (ψ n) < (1 / 2 : ℝ) ^ n := by
    intro n
    exact ⟨(he _).1, (he _).2.trans_le
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hψ.id_le n))⟩
  have hpoly := isPolySummableScales_of_lt_half_pow heψ
  obtain ⟨φ, hφ, hφae⟩ := exists_ae_countable_uniform_subsequence S.P (closedBall z r)
    F g hconv (e ∘ ψ) (fun n => (heψ n).1) hpoly.tendsto_zero
  obtain ⟨α, hα, hholder⟩ := normalizedExitGreenPotential_ae_uniform_holder
    𝒮 h217 hγ hγ2 hρ'0 hρ'1 S hS hmaxball
  have hdom : ∀ᵐ ω ∂S.P, ∀ j, ∀ᶠ n in atTop, ∀ x ∈ closedBall z r,
      rescale (S.mε (e (ψ n))) (e (ψ n)) (S.η ω) (fun a =>
        (expectedExitTime (S.mult (e (ψ n)) ω)
          (interiorCellVertices (e (ψ n)) (S.η ω) (ball z r)) a).toReal) x ≤ F j (e (ψ n)) ω x := by
    rw [ae_all_iff]
    intro j
    filter_upwards [ae_eventual_rescale_expectedExitTime_concentric_mono h218 h217
      hγ hγ2 hρ'0 hρ'1 S hS (hR j).le (hRball j) (e ∘ ψ) hpoly hpoly.tendsto_zero] with ω hω
    filter_upwards [hω] with n hn x hx
    exact hn x (closedBall_subset_ball (hR j) hx)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae, hholder, hdom] with ω hφω hholdω hdomω
  obtain ⟨C, hC, hCbound⟩ := hholdω
  have hzero : ∀ j w, w ∈ sphere z (R j) → g j ω w = 0 := by
    intro j w hw
    simp [g, normalizedExitGreenPotential_eq_zero_on_sphere S hw ω]
  have hh : ∀ j, ∀ u ∈ closedBall z (R j), ∀ v ∈ closedBall z (R j),
      |g j ω u - g j ω v| ≤ (6 * C) * ‖u - v‖ ^ α := by
    intro j u hu v hv
    have hb := hCbound (R j) (lt_trans hr (hR j)) (hmax j) u hu v hv
    dsimp [g]
    rw [← mul_sub, abs_mul, abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
    nlinarith
  have hd : ∀ j, ∀ᶠ n in atTop, ∀ x ∈ closedBall z r,
      rescale (S.mε (e (ψ (φ n)))) (e (ψ (φ n))) (S.η ω) (fun a =>
        (expectedExitTime (S.mult (e (ψ (φ n))) ω)
          (interiorCellVertices (e (ψ (φ n))) (S.η ω) (ball z r)) a).toReal) x ≤
      F j (e (ψ (φ n))) ω x := by
    intro j
    exact (hφ.tendsto_atTop.eventually (hdomω j))
  simpa only [rescale, Function.comp_def] using
    boundary_decay_of_concentric_majorants hr (mul_nonneg (by norm_num) hC) hα
      R hR hRlim _ (fun j n => F j (e (ψ (φ n))) ω) (fun j => g j ω)
      hzero hh hd hφω

end MatedCRT

#print axioms MatedCRT.preparedExitTimeBoundaryDecayStep_of_green_and_estimates
