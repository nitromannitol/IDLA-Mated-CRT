import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredPotentialContinuous
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.HarmonicTranslation

/-! Continuity of the Green potential on an arbitrary ball. -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter
open scoped ENNReal NNReal

/-- Translation transports a ball to the corresponding ball. -/
theorem preimage_ball_sub_const (z a : ℂ) (r : ℝ) :
    (fun w : ℂ => w - z) ⁻¹' ball a r = ball (a + z) r := by
  ext w
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  have h : w - z - a = w - (a + z) := by abel
  rw [h]

/-- Lemma 2.17 implies almost-sure continuity of the normalized exit Green
potential up to the boundary of an arbitrary ball. -/
theorem normalizedExitGreenPotential_ae_continuousOn
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ) :
    ∀ᵐ ω ∂S.P, ContinuousOn (normalizedExitGreenPotential S r z ω) (closedBall z r) := by
  obtain ⟨β, hβ, hmass⟩ := ae_smallBallMass_all_small_radii h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField
  filter_upwards [hmass, hS.isLQGMeasure] with ω hmassω hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨r₀, hr₀, hup⟩ := hmassω
  let ν := Measure.map (fun w : ℂ => w - z) (S.μ ω)
  have hmap (a : ℂ) (s : ℝ) : ν (ball a s) = S.μ ω (ball (a + z) s) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_const]
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ x ∈ ball (0 : ℂ) r,
      ν (ball x s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr x hx
    rw [hmap]
    apply hup s hs hsr (x + z) (hball ?_)
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
  have hfin : ν (ball (0 : ℂ) r) ≠ ⊤ := by
    rw [hmap]
    simpa using (measure_ball_lt_top.ne : S.μ ω (ball z r) ≠ ⊤)
  obtain ⟨_, hholder⟩ := greenPotential_ball_holder_of_upper hr hr₀ hβ hup' hfin
    (f := fun _ => (1 : ℝ)) (M := 1) (by fun_prop) (by norm_num)
    (Eventually.of_forall (fun _ => by simp))
  have hO : (fun w : ℂ => w + z) ⁻¹' ball z r = ball 0 r := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have hint (x : ℂ) :
      (∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) (x - z) y ∂ν) =
        ∫ y in ball z r, greenFunction (ball z r) x y ∂S.μ ω := by
    have hf : (fun w : ℂ => w - z) = (Homeomorph.addRight (-z) : ℂ → ℂ) := by
      funext w
      simp [sub_eq_add_neg]
    change (∫ y in ball (0 : ℂ) r, greenFunction (ball 0 r) (x - z) y
      ∂Measure.map (fun w : ℂ => w - z) (S.μ ω)) = _
    rw [hf]
    rw [(Homeomorph.addRight (-z)).isClosedEmbedding.setIntegral_map]
    change (∫ y in (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) r,
      greenFunction (ball 0 r) (x - z) (y - z) ∂S.μ ω) = _
    rw [preimage_ball_sub_const, zero_add]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    have hg := greenFunction_translate (ball z r) (x - z) (y - z) z
    simpa only [sub_add_cancel, hO] using hg.symm
  let C : ℝ≥0 := ⟨greenPotentialHolderConstant β r₀ (ν (ball (0 : ℂ) r)).toReal,
    greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg⟩
  let α : ℝ≥0 := ⟨greenPotentialHolderExponent β, (greenPotentialHolderExponent_pos hβ).le⟩
  have hh : HolderOnWith C α
      (fun x => ∫ y in ball z r, greenFunction (ball z r) x y ∂S.μ ω)
      (closedBall z r) := by
    apply holderOnWith_of_dist_le
    intro x hx y hy
    have hx' : x - z ∈ closedBall (0 : ℂ) r := by
      simpa [mem_closedBall, dist_eq_norm] using hx
    have hy' : y - z ∈ closedBall (0 : ℂ) r := by
      simpa [mem_closedBall, dist_eq_norm] using hy
    have hb := hholder (x - z) hx' (y - z) hy'
    simp only [mul_one, hint, sub_sub_sub_cancel_right] at hb
    rw [Real.dist_eq, dist_eq_norm]
    change |(∫ w in ball z r, greenFunction (ball z r) x w ∂S.μ ω) -
      (∫ w in ball z r, greenFunction (ball z r) y w ∂S.μ ω)| ≤
      greenPotentialHolderConstant β r₀ (ν (ball (0 : ℂ) r)).toReal *
        ‖x - y‖ ^ greenPotentialHolderExponent β
    exact hb
  have hc := hh.continuousOn (greenPotentialHolderExponent_pos hβ)
  change ContinuousOn (fun x : ℂ => S.c₀ / 6 *
    ∫ y in ball z r, greenFunction (ball z r) x y ∂S.μ ω) (closedBall z r)
  exact hc.const_mul (S.c₀ / 6)

end MatedCRT
