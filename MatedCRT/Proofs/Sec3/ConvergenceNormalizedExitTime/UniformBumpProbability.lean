import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpPotentialProbability

/-! Uniform smallness of the Green potentials of buffered sources. -/

open Set Metric MeasureTheory HarmonicBalls Filter Topology

namespace MatedCRT

/-- Lemma 2.17 bounds the potentials of all admissible small bumps at once. -/
theorem uniformBumpPotential_tendstoInProbability_zero (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) ρ) {O : Set ℂ}
    (hO : O ⊆ closedBall x 2) (hxO : x ∈ O) {C : ℝ} (hC0 : 0 ≤ C)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun δ : ℝ => P {ω | ∃ φ : ℂ → ℝ,
      (∀ w, 0 ≤ φ w) ∧ (∀ w, φ w ≤ 1) ∧ (∀ w ∉ ball x δ, φ w = 0) ∧
      t < C * ∫ w, greenFunction O x w * φ w ∂μ ω}) (𝓝[>] 0) (𝓝 0) := by
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
    P {ω | ∃ φ : ℂ → ℝ, (∀ w, 0 ≤ φ w) ∧ (∀ w, φ w ≤ 1) ∧
        (∀ w ∉ ball x δ, φ w = 0) ∧
        t < C * ∫ w, greenFunction O x w * φ w ∂μ ω} ≤
        P {ω | ¬ ∀ x ∈ ball (0 : ℂ) ρ, ∀ O : Set ℂ,
          O ⊆ closedBall x 2 → x ∈ O → ∀ ψ : ℂ → ℝ,
          (∀ w, 0 ≤ ψ w) → (∀ w, ψ w ≤ 1) → (∀ w ∉ ball x δ, ψ w = 0) →
          ENNReal.ofReal (∫ w, greenFunction O x w * ψ w ∂μ ω) ≤ ENNReal.ofReal (δ ^ q)} := by
      apply measure_mono
      rintro ω ⟨φ, hφ0, hφ1, hsupp, hω⟩ hgood
      have h := hgood x hx O hO hxO φ hφ0 hφ1 hsupp
      have hreal := (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hδ.le _)).mp h
      have hle := mul_le_mul_of_nonneg_left hreal hC0
      linarith
    _ ≤ ENNReal.ofReal (K * δ ^ p) := hbound δ hδ hδlt

end MatedCRT
