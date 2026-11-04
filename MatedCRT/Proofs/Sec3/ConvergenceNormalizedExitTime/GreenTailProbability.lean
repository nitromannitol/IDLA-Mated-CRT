import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialProbability

/-! The continuum Green singularity has a small integral in probability. -/

open Set Metric MeasureTheory HarmonicBalls Filter Topology

namespace MatedCRT

/-- The Green integral over a shrinking ball about its pole converges to zero
in probability. This is the continuum tail estimate used when the discrete
Green sum is truncated away from the pole. -/
theorem greenIntegral_near_pole_tendstoInProbability_zero
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) {O : Set ℂ}
    (hO : O ⊆ closedBall x 2) (hxO : x ∈ O) {C : ℝ} (hC0 : 0 ≤ C)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun δ : ℝ => P {ω | t < C * ∫ w in ball x δ, greenFunction O x w ∂μ ω})
      (𝓝[>] 0) (𝓝 0) := by
  let φ : ℝ → ℂ → ℝ := fun δ => (ball x δ).indicator (fun _ => 1)
  have hφ0 : ∀ δ w, 0 ≤ φ δ w := by
    intro δ w
    by_cases hw : w ∈ ball x δ <;> simp [φ, hw]
  have hφ1 : ∀ δ w, φ δ w ≤ 1 := by
    intro δ w
    by_cases hw : w ∈ ball x δ <;> simp [φ, hw]
  have hsupp : ∀ δ w, w ∉ ball x δ → φ δ w = 0 := by
    intro δ w hw
    simp [φ, hw]
  have heq (δ : ℝ) (ω : Ω) :
      (∫ w, greenFunction O x w * φ δ w ∂μ ω) =
        ∫ w in ball x δ, greenFunction O x w ∂μ ω := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext w
    by_cases hw : w ∈ ball x δ <;> simp [φ, hw]
  simpa only [heq] using
    bumpPotential_tendstoInProbability_zero h217 hγ hγ2 hρ hρ1 P hC hcirc μ hcone
      hx hO hxO hC0 φ hφ0 hφ1 hsupp t ht

end MatedCRT
