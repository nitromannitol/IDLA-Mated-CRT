import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialProbability

/-! Integrability of the Green kernel at its pole. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls

/-- Measurability, the logarithmic bound near the pole, and integrability away
from the pole imply integrability on the whole domain. -/
theorem integrableOn_scaledGreen_of_largestExitTimeRV
    (μ : Measure ℂ) {O : Set ℂ} {y : ℂ} {δ C : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hO : O ⊆ closedBall y 2) (hy : y ∈ O)
    (hsm : AEStronglyMeasurable (fun x => C * greenFunction O y x) μ)
    (hM : largestExitTimeRV μ (ball y δ) < ⊤)
    (haway : IntegrableOn (fun x => C * greenFunction O y x) (O \ ball y δ) μ) :
    IntegrableOn (fun x => C * greenFunction O y x) O μ := by
  by_cases hC : C = 0
  · simp [hC]
  have hgreen : AEStronglyMeasurable (greenFunction O y) μ := by
    have h := hsm.const_mul C⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h
  have hnear : IntegrableOn (fun x => C * greenFunction O y x) (ball y δ) μ :=
    (green_integrableOn_small_ball_of_largestExitTimeRV μ hδ hδ1 hO hy
      (hgreen.mono_measure Measure.restrict_le_self) hM).const_mul C
  exact (hnear.union haway).mono_set (by
    intro x hx
    by_cases hxδ : x ∈ ball y δ
    · exact Or.inl hxδ
    · exact Or.inr ⟨hx, hxδ⟩)

/-- Lemmas 3.3 and 2.17 imply integrability of the scaled Green kernel over
the entire ball, including the singularity. -/
theorem greenFunction_ae_integrableOn_ball
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) :
    ∀ᵐ ω ∂S.P, IntegrableOn (fun x => S.c₀ / 6 * greenFunction (ball z r) y x)
      (ball z r) (S.μ ω) := by
  have hyz : dist y z < r := hy
  have hy0 : dist y 0 < ρ := hball hy
  let δ : ℝ := min 1 (min ((1 - ρ) / 4) ((r - dist y z) / 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδρ : δ ≤ (1 - ρ) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ (r - dist y z) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : δ + dist y z < r := by linarith
  have hsub : ball y δ ⊆ ball (0 : ℂ) ((1 + ρ) / 2) := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have h := dist_triangle x y (0 : ℂ)
    linarith
  have hO : ball z r ⊆ closedBall y 2 := by
    intro x hx
    have hx0 : dist x 0 < ρ := hball hx
    rw [mem_closedBall]
    have h := dist_triangle x (0 : ℂ) y
    rw [dist_comm (0 : ℂ) y] at h
    linarith
  have hD : ball z r \ ball y δ ⊆ closedBall z r \ {y} := by
    intro x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    intro hxy
    have : x = y := mem_singleton_iff.mp hxy
    subst x
    exact hx.2 (mem_ball_self hδ)
  have ha := greenFunction_ae_integrableOn_away_from_pole 𝒮 h33 hγ hγ2 hρ hρ1 S hS
    hr hball hy (ball z r \ ball y δ) hD (sdiff_subset.trans hball)
    (infDist_punctured_ball_pos hδ hsmall)
  obtain ⟨_, _, h217ρ⟩ := h217 γ hγ hγ2
  have hM := (h217ρ ((1 + ρ) / 2) (by linarith) (by linarith) Ω S.P S.hC
    S.hcirc S.μ hS.isConeField).1
  filter_upwards [ha, hM, greenFunction_ae_aestronglyMeasurable 𝒮 h33 hγ hγ2 hρ hρ1
    S hS hr hball hy] with ω haway hMω hsm
  apply integrableOn_scaledGreen_of_largestExitTimeRV (S.μ ω) hδ hδ1 hO hy hsm ?_ haway
  have hle : largestExitTimeRV (S.μ ω) (ball y δ) ≤
      (⨆ (D : Set ℂ) (_ : D ⊆ ball (0 : ℂ) ((1 + ρ) / 2)), largestExitTimeRV (S.μ ω) D) :=
    le_iSup_of_le (ball y δ) (le_iSup_of_le hsub le_rfl)
  exact hle.trans_lt hMω

end MatedCRT
