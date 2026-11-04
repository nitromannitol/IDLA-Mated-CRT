import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialProbability

/-! Small-ball mass is controlled by the largest exit-time quantity. -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls
open scoped ENNReal

/-- On a ball of radius at most one, the logarithmic exit-time kernel is
at least one, including at its pole under Lean's convention for `log 0`. -/
theorem measure_ball_le_largestExitTimeRV (μ : Measure ℂ) {x : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ (ball x δ) ≤ largestExitTimeRV μ (ball x δ) := by
  calc
    μ (ball x δ) = ∫⁻ _ in ball x δ, (1 : ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ w in ball x δ, ENNReal.ofReal (Real.log (1 / ‖x - w‖) + 1) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      have hd : ‖x - w‖ ≤ 1 := by
        have hw' : ‖w - x‖ < δ := by simpa [mem_ball, dist_eq_norm] using hw
        rw [norm_sub_rev]
        exact (le_of_lt hw').trans hδ1
      by_cases hzero : x = w
      · subst w
        simp
      · have hnorm : 0 < ‖x - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
        have hdiv : 1 ≤ 1 / ‖x - w‖ := (one_le_div hnorm).2 hd
        have hlog : 0 ≤ Real.log (1 / ‖x - w‖) := Real.log_nonneg hdiv
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤
          Real.log (1 / ‖x - w‖) + 1 by linarith)
    _ ≤ largestExitTimeRV μ (ball x δ) := by
      unfold largestExitTimeRV
      exact le_iSup_of_le x (le_iSup_of_le (mem_ball_self hδ) le_rfl)

/-- Lemma 2.17 implies polynomial high-probability upper bounds for the
LQG mass of every small ball with centre in the fixed ambient ball. -/
theorem smallBallMass_polyHighProb (h217 : BoundedExitTimeRVStmt)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 0 < q ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      PolyHighProb P fun δ => {ω | ∀ x ∈ ball (0 : ℂ) ρ,
        μ ω (ball x δ) ≤ ENNReal.ofReal (δ ^ q)} := by
  obtain ⟨q, hq, h217q⟩ := h217 γ hγ hγ2
  refine ⟨q, hq, ?_⟩
  intro ρ hρ hρ1 Ω _ P hC hcirc μ hcone
  have hprob := (h217q ρ hρ hρ1 Ω P hC hcirc μ hcone).2
  apply polyHighProb_of_inter_subset hprob (G := Set.univ) (by simp) (show (0 : ℝ) < 1 by norm_num)
  intro δ hδ hδ1 ω hω x hx
  exact (measure_ball_le_largestExitTimeRV (μ ω) hδ hδ1.le).trans (hω.1 x hx)

end MatedCRT
