import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ConvergingTogether
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.DeterministicNullCircles
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenTruncationProbability

/-! Pointwise convergence from truncation and control of the discrete pole. -/

namespace MatedCRT

open Set Filter Topology MeasureTheory Metric _root_.HarmonicBalls
open scoped ENNReal

/-- Two-parameter convergence in probability with arbitrarily small good
truncation radii. -/
theorem tendstoInProbability_of_small_truncations
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℝ → Ω → ℝ) (G : ℝ → ℝ → Ω → ℝ) (V : ℝ → Ω → ℝ) (U : Ω → ℝ)
    (hconv : ∀ R : ℝ, 0 < R → ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ TendstoInProbability P (G δ) (V δ))
    (hV : ∀ t : ℝ, 0 < t → Tendsto (fun δ : ℝ => P {ω | t < |V δ ω - U ω|})
      (𝓝[>] 0) (𝓝 0))
    (hFG : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ R : ℝ, 0 < R ∧
      ∀ δ : ℝ, 0 < δ → δ < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        P {ω | t < |F ε ω - G δ ε ω|} < e) :
    TendstoInProbability P F U := by
  apply tendstoInProbability_of_approximations P F U
  intro t ht e he
  obtain ⟨R, hR, hRFG⟩ := hFG t ht e he
  have hq : 0 < min e 1 := lt_min he zero_lt_one
  have hqtop : min e 1 ≠ ⊤ := ne_of_lt ((min_le_right e 1).trans_lt ENNReal.one_lt_top)
  have hhalf : 0 < min e 1 / 2 := ENNReal.half_pos hq.ne'
  have hsmall := ENNReal.tendsto_nhds_zero.1 (hV t ht) (min e 1 / 2) hhalf
  obtain ⟨s, hs, hsbound⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hsmall)
  obtain ⟨δ, hδ, hδsmall, hδconv⟩ := hconv (min R s) (lt_min hR hs)
  refine ⟨G δ, V δ, hδconv, hRFG δ hδ (hδsmall.trans_le (min_le_left _ _)), ?_⟩
  have hδs : dist δ 0 < s := by
    simpa [Real.dist_eq, abs_of_pos hδ] using hδsmall.trans_le (min_le_right _ _)
  exact (hsbound hδs hδ).trans_lt
    ((ENNReal.half_lt_self hq.ne' hqtop).trans_le (min_le_left e 1))

/-- The normalized exit time converges pointwise once its near-pole discrete
Green sum is uniformly negligible in probability. -/
theorem pointwise_normalizedExitTime_of_nearPole
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r)
    (hnear : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ R : ℝ, 0 < R ∧
      ∀ δ : ℝ, 0 < δ → δ < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        S.P {ω | t < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y -
          (S.mε ε)⁻¹ * ∑ a ∈ truncatedGreenCells ε (S.η ω) z y r δ,
            greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
              (vertexOf ε (S.η ω) y) a|} < e) :
    TendstoInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y)
      (fun ω => normalizedExitGreenPotential S r z ω y) := by
  let F : ℝ → Ω → ℝ := fun ε ω => rescale (S.mε ε) ε (S.η ω)
    (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) y
  let G : ℝ → ℝ → Ω → ℝ := fun δ ε ω => (S.mε ε)⁻¹ *
    ∑ a ∈ truncatedGreenCells ε (S.η ω) z y r δ,
      greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
        (vertexOf ε (S.η ω) y) a
  let V : ℝ → Ω → ℝ := fun δ ω => ∫ x in ball z r \ ball y δ,
    S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω
  let U : Ω → ℝ := fun ω => ∫ x in ball z r,
    S.c₀ / 6 * greenFunction (ball z r) y x ∂S.μ ω
  have hconv : ∀ R : ℝ, 0 < R → ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      TendstoInProbability S.P (G δ) (V δ) := by
    intro R hR
    obtain ⟨δ, hδ, hδR, _, h⟩ := exists_greenSum_tendstoInProbability_fixed_truncation
      𝒮 h33 hγ hγ2 hρ hρ1 S hS hr hR hball hy
    exact ⟨δ, hδ, hδR, h⟩
  have hV : ∀ t : ℝ, 0 < t → Tendsto (fun δ : ℝ => S.P {ω | t < |V δ ω - U ω|})
      (𝓝[>] 0) (𝓝 0) := greenIntegral_truncation_tendstoInProbability
        𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hy
  have h := tendstoInProbability_of_small_truncations S.P F G V U hconv hV hnear
  simpa only [F, U, normalizedExitGreenPotential, integral_const_mul] using h

end MatedCRT
