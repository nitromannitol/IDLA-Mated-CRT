import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialContinuous
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundary

/-! Uniform Hölder bounds for Green potentials on concentric disks. -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls Filter
open scoped ENNReal NNReal

/-- The quantitative Green-potential Hölder constant increases with the
mass parameter. -/
theorem greenPotentialHolderConstant_mono_mass {β r₀ a b : ℝ}
    (hβ : 0 < β) (hr₀ : 0 < r₀) (hab : a ≤ b) :
    greenPotentialHolderConstant β r₀ a ≤ greenPotentialHolderConstant β r₀ b := by
  unfold greenPotentialHolderConstant greenPotentialRieszBound volumeGrowthAllScalesConstant
  have hp : 0 ≤ (2 / r₀) ^ β := Real.rpow_nonneg (div_nonneg zero_le_two hr₀.le) _
  have hq : 0 ≤ greenPotentialHolderExponent β / (β - greenPotentialHolderExponent β) :=
    div_nonneg (greenPotentialHolderExponent_pos hβ).le
      (sub_pos.mpr (greenPotentialHolderExponent_lt hβ)).le
  have hc : 0 ≤ 2 * (Real.pi * greenPotentialHolderExponent β)⁻¹ :=
    mul_nonneg zero_le_two (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le
      (greenPotentialHolderExponent_pos hβ).le))
  exact mul_le_mul_of_nonneg_left
    (add_le_add hab (mul_le_mul_of_nonneg_right
      (add_le_add_right (mul_le_mul_of_nonneg_right hab hp) _) hq)) hc

/-- A single random Hölder constant controls the normalized Green potentials
of all concentric subdisks of a fixed disk. -/
theorem normalizedExitGreenPotential_ae_uniform_holder
    (𝒮 : SpaceFillingSLEModel) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {R : ℝ} {z : ℂ} (hball : ball z R ⊆ ball 0 ρ) :
    ∃ α : ℝ, 0 < α ∧ ∀ᵐ ω ∂S.P, ∃ C : ℝ, 0 ≤ C ∧
      ∀ r, 0 < r → r ≤ R → ∀ x ∈ closedBall z r, ∀ y ∈ closedBall z r,
        |normalizedExitGreenPotential S r z ω x - normalizedExitGreenPotential S r z ω y| ≤
          C * ‖x - y‖ ^ α := by
  obtain ⟨β, hβ, hmass⟩ := ae_smallBallMass_all_small_radii h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField
  refine ⟨greenPotentialHolderExponent β, greenPotentialHolderExponent_pos hβ, ?_⟩
  filter_upwards [hmass, hS.isLQGMeasure] with ω hmassω hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨r₀, hr₀, hup⟩ := hmassω
  let ν := Measure.map (fun w : ℂ => w - z) (S.μ ω)
  have hmap (a : ℂ) (s : ℝ) : ν (ball a s) = S.μ ω (ball (a + z) s) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_const]
  have hfin (s : ℝ) : ν (ball (0 : ℂ) s) ≠ ⊤ := by
    rw [hmap]
    simpa using (measure_ball_lt_top.ne : S.μ ω (ball z s) ≠ ⊤)
  let C := S.c₀ / 6 * greenPotentialHolderConstant β r₀ (ν (ball 0 R)).toReal
  refine ⟨C, mul_nonneg (div_nonneg S.c₀_nonneg (by norm_num))
    (greenPotentialHolderConstant_nonneg hβ hr₀ ENNReal.toReal_nonneg), ?_⟩
  intro r hr hrR x hx y hy
  have hup' : ∀ s, 0 < s → s < r₀ → ∀ w ∈ ball (0 : ℂ) r,
      ν (ball w s) ≤ ENNReal.ofReal (s ^ β) := by
    intro s hs hsr w hw
    rw [hmap]
    apply hup s hs hsr (w + z) (hball ?_)
    have hwR := Metric.ball_subset_ball hrR hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hwR
  obtain ⟨_, hholder⟩ := greenPotential_ball_holder_of_upper hr hr₀ hβ hup' (hfin r)
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
    rw [hf, (Homeomorph.addRight (-z)).isClosedEmbedding.setIntegral_map]
    change (∫ y in (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) r,
      greenFunction (ball 0 r) (x - z) (y - z) ∂S.μ ω) = _
    rw [preimage_ball_sub_const, zero_add]
    apply setIntegral_congr_fun measurableSet_ball
    intro w hw
    have hg := greenFunction_translate (ball z r) (x - z) (w - z) z
    simpa only [sub_add_cancel, hO] using hg.symm
  have hx' : x - z ∈ closedBall (0 : ℂ) r := by
    simpa [mem_closedBall, dist_eq_norm] using hx
  have hy' : y - z ∈ closedBall (0 : ℂ) r := by
    simpa [mem_closedBall, dist_eq_norm] using hy
  have hb := hholder (x - z) hx' (y - z) hy'
  simp only [mul_one, hint, sub_sub_sub_cancel_right] at hb
  have hmassle : (ν (ball (0 : ℂ) r)).toReal ≤ (ν (ball (0 : ℂ) R)).toReal :=
    (ENNReal.toReal_le_toReal (hfin r) (hfin R)).2 (measure_mono (ball_subset_ball hrR))
  have hconst := greenPotentialHolderConstant_mono_mass hβ hr₀ hmassle
  have hnorm : 0 ≤ ‖x - y‖ ^ greenPotentialHolderExponent β := Real.rpow_nonneg (norm_nonneg _) _
  change |S.c₀ / 6 * (∫ w in ball z r, greenFunction (ball z r) x w ∂S.μ ω) -
    S.c₀ / 6 * (∫ w in ball z r, greenFunction (ball z r) y w ∂S.μ ω)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg S.c₀_nonneg (by norm_num))]
  calc
    _ ≤ (S.c₀ / 6) * (greenPotentialHolderConstant β r₀ (ν (ball 0 r)).toReal *
        ‖x - y‖ ^ greenPotentialHolderExponent β) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg S.c₀_nonneg (by norm_num))
    _ ≤ C * ‖x - y‖ ^ greenPotentialHolderExponent β := by
      simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hconst hnorm) (div_nonneg S.c₀_nonneg (by norm_num))

end MatedCRT

#print axioms MatedCRT.normalizedExitGreenPotential_ae_uniform_holder
