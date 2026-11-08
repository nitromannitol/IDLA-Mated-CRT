import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseUniform

/-!
# Lemma 3.4 (item 4): locally uniform convergence of the time-changed paths

If the clocks `F i` converge uniformly on compact time intervals to a time-change clock `G`, then for every continuous
path `b` the time-changed paths `t ↦ b (clockInverse (F i) t)` converge uniformly on compact time intervals to
`t ↦ b (clockInverse G t)`: the inverse clocks converge uniformly (`clockInverse_tendsto_uniform`) and `b` is uniformly
continuous on a compact interval. This is the deterministic step of the path convergence in `LBMPathFunctionalMeasurableStep`.
-/

namespace MatedCRT

open Filter Topology Set
open scoped NNReal
open _root_.HarmonicBalls MarkovProcess

/-- Uniform convergence of the time-changed paths `b ∘ clockInverse (F i)` on compact time intervals. -/
theorem liouvilleBrownianPath_tendsto_uniform {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0 → ℝ} {G : ℝ≥0 → ℝ}
    (hG : IsTimeChangeClock G) (hF : ∀ i, StrictMono (F i)) (U : ℝ≥0)
    (hunb : ∀ᶠ i in l, ∀ u : ℝ≥0, u ≤ U → ∃ s : ℝ≥0, (u : ℝ) < F i s)
    (hconv : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ t ≤ T, |F i t - G t| < η)
    (b : ContinuousPath ℂ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ i in l, ∀ t ≤ U, ‖b (clockInverse (F i) t) - b (clockInverse G t)‖ < η := by
  set S : ℝ≥0 := clockInverse G U with hS
  set K : Set ℝ≥0 := Icc 0 (S + 1) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hunif : UniformContinuousOn (fun s : ℝ≥0 => b s) K :=
    hKc.uniformContinuousOn_of_continuous b.continuous.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1 hunif η hη
  have hη' : 0 < min δ 1 := lt_min hδpos one_pos
  filter_upwards [clockInverse_tendsto_uniform hG hF U hunb hconv (min δ 1) hη'] with i hi t ht
  have hiG : |((clockInverse (F i) t : ℝ≥0) : ℝ) - ((clockInverse G t : ℝ≥0) : ℝ)| < min δ 1 := hi t ht
  have hGS : clockInverse G t ≤ S := (IsTimeChangeClock.strictMono_clockInverse hG).monotone ht
  have hGSR : ((clockInverse G t : ℝ≥0) : ℝ) ≤ (S : ℝ) := NNReal.coe_le_coe.2 hGS
  have hmemG : clockInverse G t ∈ K := ⟨by simp, le_trans hGS le_self_add⟩
  have hFle : ((clockInverse (F i) t : ℝ≥0) : ℝ) ≤ ((S + 1 : ℝ≥0) : ℝ) := by
    have h1 := abs_lt.1 hiG
    push_cast
    linarith [h1.2, hGSR, min_le_right δ 1]
  have hmemF : clockInverse (F i) t ∈ K := ⟨by simp, NNReal.coe_le_coe.1 hFle⟩
  have hdist : dist (clockInverse (F i) t) (clockInverse G t) < δ := by
    rw [NNReal.dist_eq]
    exact lt_of_lt_of_le hiG (min_le_left _ _)
  have hb := hδ (clockInverse (F i) t) hmemF (clockInverse G t) hmemG hdist
  rw [← dist_eq_norm]
  exact hb

end MatedCRT
