import MatedCRT.FirstPass.Derived.ConeReferenceStoppedHeatBound

/-!
# Stopped heat bound from a ball-mass bound of the dyadic approximants

Let `h` be a family of circle averages whose dyadic approximants
`ε^{γ²/2} e^{γ h_ε(x)} dx`, `ε = 2^{-k}`, of the `γ`-LQG measure give every ball `B(z, r)` with
`‖z‖ ≤ R + 1` and `0 < r ≤ 1` mass at most `C r^β`, uniformly in the level `k`. Then the occupation
integral of the approximant density along planar Brownian motion from `z`, `‖z‖ ≤ R`, stopped at
`t ∧ τ_{B(0, R+1)}`, has expectation at most `C' t^{β'}`, uniformly in the start and the level
(`stoppedHeatBound_of_ballBound`). This is the deterministic half of the stopped heat bound of the
reference cone (`ae_coneRef_stopped_heat_bound`), stated for an arbitrary field.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **Stopped heat bound from a ball-mass bound.** If the dyadic approximants of the `γ`-LQG
measure of `h` give every ball `B(z, r)` with `‖z‖ ≤ R + 1` and `0 < r ≤ 1` mass at most `C r^β`
for every level, then for every start `z` with `‖z‖ ≤ R`, every level `k` and every `t ≥ 0`, the
expected occupation integral of the approximant density along planar Brownian motion from `z`
stopped at `t ∧ τ_{B(0, R+1)}` is at most `C' t^{β'}`, for some `β', C' > 0`. -/
theorem stoppedHeatBound_of_ballBound {γ : ℝ} {h : ℝ → ℂ → ℝ}
    (hmeas : ∀ k : ℕ, Measurable (h (LatticeProb.LQG.dyadicScale k)))
    {R β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ R + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β)) :
    ∃ β' C' : ℝ, 0 < β' ∧ 0 < C' ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
          ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C' * t ^ β') := by
  obtain ⟨N, hN⟩ :=
    LatticeProb.exists_lintegral_Ioc_lintegral_map_prod_gaussianReal_indicator_le (0 : ℂ) (R + 1)
  have hβ' : 0 < min β 1 / 2 := half_pos (lt_min hβ one_pos)
  have hmax : 0 < max C (N * C) := lt_max_of_lt_left hC0
  refine ⟨min β 1 / 2, 1024 / 7 / (2 * Real.pi) * max C (N * C) / (min β 1 / 2), hβ',
    div_pos (mul_pos (by positivity) hmax) hβ', fun z hz k t ht => ?_⟩
  have hρm : Measurable fun x : ℂ => ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) x)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (hmeas k))))
  refine (MatedCRT.KilledOccupation.lintegral_stoppedOccupation_le_lintegral_planarGaussian
    isOpen_ball z hρm t).trans ?_
  refine hN _ hρm C β hC0.le hβ (fun c' hc' r hr hr1 => ?_) z
    (mem_closedBall_zero_iff.2 (by linarith)) t ht
  have h := hball c' (mem_closedBall_zero_iff.1 hc') r hr hr1 k
  rwa [LatticeProb.LQG.lqgApprox, withDensity_apply _ measurableSet_ball] at h

/-- **Stopped heat bound on every disc from ball-mass bounds on every disc.** If for every
`R > 0` the dyadic approximants of the `γ`-LQG measure of `h` satisfy a ball-mass bound `C r^β`
on balls centred in `B̄(0, R)` of radius at most `1`, uniformly in the level, then `h` satisfies the
stopped heat bound on every disc `B(0, R + 1)`. -/
theorem stoppedHeatBound_of_forall_ballBound {γ : ℝ} {h : ℝ → ℂ → ℝ}
    (hmeas : ∀ k : ℕ, Measurable (h (LatticeProb.LQG.dyadicScale k)))
    (hball : ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
          ENNReal.ofReal (C * r ^ β)) :
    ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
          ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β) := by
  intro R hR
  obtain ⟨β, C, hβ, hC0, hb⟩ := hball (R + 1) (by linarith)
  exact stoppedHeatBound_of_ballBound hmeas hβ hC0 hb

/-- **Countable reduction of the ball-mass bound.** A bound `μ(B(q, r)) ≤ C r^β` for the dyadic
approximant `μ = ε^{γ²/2} e^{γ h_ε(x)} dx` on the balls whose centres `q` run through the dense
sequence of `ℂ` with `‖q‖ ≤ R + 1` and whose radii are rational in `(0, 1]` gives the same bound
on every ball `B(z, r)` with `‖z‖ ≤ R` and `0 < r ≤ 1`. -/
theorem lqgApprox_ball_le_of_denseSeq {γ : ℝ} {h : ℝ → ℂ → ℝ} {ε R β C : ℝ} (hβ : 0 ≤ β)
    (hC : 0 ≤ C)
    (hcount : ∀ n : ℕ, ‖TopologicalSpace.denseSeq ℂ n‖ ≤ R + 1 → ∀ r : ℚ, 0 < (r : ℝ) →
      (r : ℝ) ≤ 1 → LatticeProb.LQG.lqgApprox γ h ε (ball (TopologicalSpace.denseSeq ℂ n) r) ≤
        ENNReal.ofReal (C * (r : ℝ) ^ β))
    {z : ℂ} (hz : ‖z‖ ≤ R) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    LatticeProb.LQG.lqgApprox γ h ε (ball z r) ≤ ENNReal.ofReal (C * r ^ β) := by
  have hsmall : ∀ ρ, ρ < r → LatticeProb.LQG.lqgApprox γ h ε (ball z ρ) ≤
      ENNReal.ofReal (C * r ^ β) := by
    intro ρ hρr
    rcases le_or_gt ρ 0 with hρ | hρ
    · rw [ball_eq_empty.2 hρ, measure_empty]
      exact zero_le
    have hδ0 : 0 < (r - ρ) / 2 := by linarith
    obtain ⟨n, hn⟩ :=
      Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z _ hδ0
    obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn (show ρ + (r - ρ) / 2 < r by linarith)
    have hsub : ball z ρ ⊆ ball (TopologicalSpace.denseSeq ℂ n) r' := by
      intro x hx
      rw [mem_ball] at hx ⊢
      calc dist x (TopologicalSpace.denseSeq ℂ n)
          ≤ dist x z + dist z (TopologicalSpace.denseSeq ℂ n) := dist_triangle _ _ _
        _ < ρ + (r - ρ) / 2 := add_lt_add hx hn
        _ < r' := hr'1
    have hq : ‖TopologicalSpace.denseSeq ℂ n‖ ≤ R + 1 := by
      have h1 : ‖TopologicalSpace.denseSeq ℂ n‖ ≤
          ‖z‖ + dist z (TopologicalSpace.denseSeq ℂ n) := by
        rw [dist_comm, dist_eq_norm]
        exact norm_le_insert' _ _
      linarith
    have hr'0 : 0 < (r' : ℝ) := by linarith
    refine (measure_mono hsub).trans ((hcount n hq r' hr'0 (hr'2.le.trans hr1)).trans ?_)
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr'0.le hr'2.le hβ) hC)
  have hmono : Monotone fun n : ℕ => ball z (r - r / ((n : ℝ) + 2)) := by
    intro n m hnm
    refine ball_subset_ball (sub_le_sub_left ?_ r)
    exact div_le_div_of_nonneg_left hr.le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hnm; linarith)
  have hU : (⋃ n : ℕ, ball z (r - r / ((n : ℝ) + 2))) = ball z r := by
    ext x
    simp only [mem_iUnion, mem_ball]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < r / ((n : ℝ) + 2) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - dist x z))
      refine ⟨n, ?_⟩
      have hd : 0 < r - dist x z := by linarith
      have h2 : r / ((n : ℝ) + 2) < r - dist x z := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hd] at hn
        nlinarith
      linarith
  have ht := tendsto_measure_iUnion_atTop (μ := LatticeProb.LQG.lqgApprox γ h ε) hmono
  rw [hU] at ht
  refine le_of_tendsto' ht fun n => hsmall _ ?_
  have : 0 < r / ((n : ℝ) + 2) := by positivity
  linarith

end MatedCRT.FirstPass.Derived
