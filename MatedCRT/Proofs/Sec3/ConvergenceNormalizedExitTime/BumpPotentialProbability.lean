import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialBound
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Draft.Section2

/-! Polynomial smallness of buffered Green potentials from Lemma 2.17. -/

open Set Metric MeasureTheory HarmonicBalls Filter Topology

namespace MatedCRT

/-- Lemma 2.17 controls uniformly the Green potential of every nonnegative
source bounded by one and supported in a small ball around its pole. -/
theorem bumpPotential_polyHighProb (h217 : BoundedExitTimeRVStmt)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 0 < q ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsConeField γ P hC hcirc μ →
      PolyHighProb P fun δ => {ω | ∀ x ∈ ball (0 : ℂ) ρ, ∀ O : Set ℂ,
        O ⊆ closedBall x 2 → x ∈ O → ∀ φ : ℂ → ℝ,
        (∀ w, 0 ≤ φ w) → (∀ w, φ w ≤ 1) → (∀ w ∉ ball x δ, φ w = 0) →
        ENNReal.ofReal (∫ w, greenFunction O x w * φ w ∂μ ω) ≤ ENNReal.ofReal (δ ^ q)} := by
  obtain ⟨q, hq, h217q⟩ := h217 γ hγ hγ2
  refine ⟨q, hq, ?_⟩
  intro ρ hρ hρ1 Ω _ P hC hcirc μ hcone
  have hprob := (h217q ρ hρ hρ1 Ω P hC hcirc μ hcone).2
  apply polyHighProb_of_inter_subset hprob (G := Set.univ) (by simp) (show (0 : ℝ) < 1 by norm_num)
  intro δ hδ hδ1 ω hω x hx O hO hxO φ hφ0 hφ1 hsupp
  exact (ofReal_integral_green_mul_bump_le_largestExitTimeRV (μ ω) φ hδ hδ1.le hO hxO
    hφ0 hφ1 hsupp).trans (hω.1 x hx)

/-- Buffered Green potentials, even multiplied by a fixed nonnegative constant,
converge to zero in probability as their support radius tends to zero. -/
theorem bumpPotential_tendstoInProbability_zero (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) {O : Set ℂ}
    (hO : O ⊆ closedBall x 2) (hxO : x ∈ O) {C : ℝ} (hC0 : 0 ≤ C)
    (φ : ℝ → ℂ → ℝ) (hφ0 : ∀ δ w, 0 ≤ φ δ w) (hφ1 : ∀ δ w, φ δ w ≤ 1)
    (hsupp : ∀ δ w, w ∉ ball x δ → φ δ w = 0) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun δ : ℝ => P {ω | t < C * ∫ w, greenFunction O x w * φ δ w ∂μ ω})
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨q, hq, hprob⟩ := bumpPotential_polyHighProb h217 hγ hγ2
  obtain ⟨p, hp, K, δ₀, hδ₀, hbound⟩ := hprob ρ hρ hρ1 Ω P hC hcirc μ hcone
  have hpow : Tendsto (fun δ : ℝ => δ ^ q) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun δ : ℝ => δ ^ q) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ q)) :=
      ((Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto).mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hq.ne'] using h
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, C * δ ^ q < t := by
    have h := hpow.const_mul C
    simp only [mul_zero] at h
    exact h (Iio_mem_nhds ht)
  have hup : Tendsto (fun δ : ℝ => ENNReal.ofReal (K * δ ^ p)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_ofReal_mul_rpow K 1 p hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₀), hsmall] with δ hδ hδlt hs
  calc
    P {ω | t < C * ∫ w, greenFunction O x w * φ δ w ∂μ ω} ≤
        P {ω | ¬ ∀ x ∈ ball (0 : ℂ) ρ, ∀ O : Set ℂ,
          O ⊆ closedBall x 2 → x ∈ O → ∀ ψ : ℂ → ℝ,
          (∀ w, 0 ≤ ψ w) → (∀ w, ψ w ≤ 1) → (∀ w ∉ ball x δ, ψ w = 0) →
          ENNReal.ofReal (∫ w, greenFunction O x w * ψ w ∂μ ω) ≤ ENNReal.ofReal (δ ^ q)} := by
      apply measure_mono
      intro ω hω hgood
      have h := hgood x hx O hO hxO (φ δ) (hφ0 δ) (hφ1 δ) (hsupp δ)
      have hreal := (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hδ.le _)).mp h
      have hle := mul_le_mul_of_nonneg_left hreal hC0
      change t < C * ∫ w, greenFunction O x w * φ δ w ∂μ ω at hω
      linarith
    _ ≤ ENNReal.ofReal (K * δ ^ p) := hbound δ hδ hδlt

end MatedCRT
