import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenIntegrable
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenTailProbability
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapProbability

/-! Removing the pole from continuum Green integrals. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls

/-- Truncated scaled Green integrals converge in probability to the full
integral as the puncture shrinks. -/
theorem greenIntegral_truncation_tendstoInProbability
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun δ : ℝ => S.P {ω | t < |(∫ x in ball z r \ ball y δ,
      S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) -
      (∫ x in ball z r, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω)|})
      (𝓝[>] 0) (𝓝 0) := by
  have hC : 0 ≤ S.c₀ / 6 := by
    unfold MatedCRTEnv.c₀ MatedCRTEnv.m₀
    exact div_nonneg (div_nonneg (by norm_num) (medianOf_nonneg _)) (by norm_num)
  have hy0 : y ∈ ball (0 : ℂ) ρ := hball hy
  have hO : ball z r ⊆ closedBall y 2 := by
    intro x hx
    have hx0 : dist x 0 < ρ := hball hx
    have hy0' : dist y 0 < ρ := hy0
    rw [mem_closedBall]
    have h := dist_triangle x (0 : ℂ) y
    rw [dist_comm (0 : ℂ) y] at h
    linarith
  let φ : ℝ → ℂ → ℝ := fun δ => (ball z r ∩ ball y δ).indicator (fun _ => 1)
  have hφ0 : ∀ δ w, 0 ≤ φ δ w := by
    intro δ w
    by_cases hw : w ∈ ball z r ∩ ball y δ <;> simp [φ, hw]
  have hφ1 : ∀ δ w, φ δ w ≤ 1 := by
    intro δ w
    by_cases hw : w ∈ ball z r ∩ ball y δ <;> simp [φ, hw]
  have hsupp : ∀ δ w, w ∉ ball y δ → φ δ w = 0 := by
    intro δ w hw
    simp [φ, hw]
  have htail := bumpPotential_tendstoInProbability_zero h217 hγ hγ2 hρ hρ1
    S.P S.hC S.hcirc S.μ hS.isConeField hy0 hO hy hC φ hφ0 hφ1 hsupp t ht
  have hint := greenFunction_ae_integrableOn_ball 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hy
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le) ?_
  intro δ
  apply measure_mono_ae
  filter_upwards [hint] with ω hω
  intro hbad
  have heq : (∫ x in ball z r ∩ ball y δ, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) +
      (∫ x in ball z r \ ball y δ, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) =
      ∫ x in ball z r, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω :=
    integral_inter_add_sdiff measurableSet_ball hω
  have hnonneg : 0 ≤ ∫ x in ball z r ∩ ball y δ,
      S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω := by
    apply integral_nonneg
    intro x
    exact mul_nonneg hC (greenFunction_nonneg isBounded_ball y x)
  have hind : (∫ x, greenFunction (ball z r) y x * φ δ x ∂S.μ ω) =
      ∫ x in ball z r ∩ ball y δ, greenFunction (ball z r) y x ∂S.μ ω := by
    rw [← integral_indicator (measurableSet_ball.inter measurableSet_ball)]
    congr 1
    funext x
    by_cases hx : x ∈ ball z r ∩ ball y δ <;> simp [φ, hx]
  rw [hind, ← integral_const_mul]
  have hdiff : (∫ x in ball z r \ ball y δ, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) -
      (∫ x in ball z r, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) =
      -(∫ x in ball z r ∩ ball y δ, S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω) := by linarith
  rw [hdiff, abs_neg, abs_of_nonneg hnonneg] at hbad
  exact hbad

end MatedCRT
