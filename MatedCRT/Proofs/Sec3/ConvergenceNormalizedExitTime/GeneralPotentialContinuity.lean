import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialContinuous

/-! Boundary continuity of Green potentials on translated balls. -/

namespace MatedCRT

open MeasureTheory Metric Filter Set _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Upper power growth of a locally finite measure gives continuity of its
Green potential up to the boundary of an arbitrary ball. -/
theorem ballGreenPotential_continuousOn_of_upper
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {r r₀ β : ℝ} {z : ℂ}
    (hr : 0 < r) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball z r,
      μ (ball x s) ≤ ENNReal.ofReal (s ^ β)) :
    ContinuousOn (fun x => ∫ y in ball z r, greenFunction (ball z r) x y ∂μ)
      (closedBall z r) := by
  let ν := Measure.map (fun w : ℂ => w - z) μ
  have hmap (a : ℂ) (s : ℝ) : ν (ball a s) = μ (ball (a + z) s) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_const]
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) r,
      ν (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr x hx
    rw [hmap]
    apply hup s hs hsr (x + z)
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
  have hfin : ν (ball (0 : ℂ) r) ≠ ⊤ := by
    rw [hmap]
    simpa using (measure_ball_lt_top.ne : μ (ball z r) ≠ ⊤)
  obtain ⟨_, hholder⟩ := greenPotential_ball_holder_of_upper hr hr₀ hβ hup' hfin
    (f := fun _ => (1 : ℝ)) (M := 1) (by fun_prop) (by norm_num)
    (Eventually.of_forall (fun _ => by simp))
  have hO : (fun w : ℂ => w + z) ⁻¹' ball z r = ball 0 r := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have hint (x : ℂ) :
      (∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) (x - z) y ∂ν) =
        ∫ y in ball z r, greenFunction (ball z r) x y ∂μ := by
    have hf : (fun w : ℂ => w - z) = (Homeomorph.addRight (-z) : ℂ → ℂ) := by
      funext w
      simp [sub_eq_add_neg]
    change (∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) (x - z) y
      ∂Measure.map (fun w : ℂ => w - z) μ) = _
    rw [hf, (Homeomorph.addRight (-z)).isClosedEmbedding.setIntegral_map]
    change (∫ y in (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) r,
      greenFunction (ball 0 r) (x - z) (y - z) ∂μ) = _
    rw [preimage_ball_sub_const, zero_add]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    have hg := greenFunction_translate (ball z r) (x - z) (y - z) z
    simpa only [sub_add_cancel, hO] using hg.symm
  let C : ℝ≥0 := ⟨greenPotentialHolderConstant β r₀ (ν (ball (0 : ℂ) r)).toReal,
    greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg⟩
  let α : ℝ≥0 := ⟨greenPotentialHolderExponent β, (greenPotentialHolderExponent_pos hβ).le⟩
  have hh : HolderOnWith C α
      (fun x => ∫ y in ball z r, greenFunction (ball z r) x y ∂μ) (closedBall z r) := by
    apply holderOnWith_of_dist_le
    intro x hx y hy
    have hx' : x - z ∈ closedBall (0 : ℂ) r := by
      simpa [mem_closedBall, dist_eq_norm] using hx
    have hy' : y - z ∈ closedBall (0 : ℂ) r := by
      simpa [mem_closedBall, dist_eq_norm] using hy
    have hb := hholder (x - z) hx' (y - z) hy'
    simp only [mul_one, hint, sub_sub_sub_cancel_right] at hb
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ w in ball z r, greenFunction (ball z r) x w ∂μ) -
      (∫ w in ball z r, greenFunction (ball z r) y w ∂μ)| ≤
      greenPotentialHolderConstant β r₀ (ν (ball (0 : ℂ) r)).toReal *
        ‖x - y‖ ^ greenPotentialHolderExponent β
    exact hb
  exact hh.continuousOn (greenPotentialHolderExponent_pos hβ)

end MatedCRT
