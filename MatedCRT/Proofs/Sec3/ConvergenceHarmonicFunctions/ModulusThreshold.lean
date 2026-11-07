import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ProjectedBoundaryModulus
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ModulusApproximation

/-! # Choosing a common threshold for the projected modulus -/

namespace MatedCRT

open Filter Topology Metric MeasureTheory Set _root_.HarmonicBalls
open scoped ENNReal

/-- The boundary and interior terms in the projected extension modulus are
uniformly small when the mesh, cell radius and point separation are small. -/
theorem exists_projected_modulus_threshold {H K χ ξ t : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hχ : 0 < χ) (hξ : 0 < ξ) (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε d s : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ d → d ≤ δ →
      0 ≤ s → s ≤ δ →
      2 * (H * max ε (2 * d) ^ χ) + K * max ε (s + 6 * d) ^ ξ < t := by
  have hg : Tendsto (fun q : ℝ => 2 * (H * (2 * q) ^ χ) + K * (7 * q) ^ ξ)
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun q : ℝ => 2 * (H * (2 * q) ^ χ) + K * (7 * q) ^ ξ :=
      (continuous_const.mul (continuous_const.mul
        ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr hχ.le))).add
        (continuous_const.mul ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr hξ.le))
    simpa [Real.zero_rpow hχ.ne', Real.zero_rpow hξ.ne'] using hc.tendsto 0
  obtain ⟨q, hq, hqg⟩ := Metric.eventually_nhds_iff.1 (hg.eventually (gt_mem_nhds ht))
  let δ := q / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hgδ : 2 * (H * (2 * δ) ^ χ) + K * (7 * δ) ^ ξ < t := by
    apply hqg
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro ε d s hε hεδ hd hdδ hs hsδ
  have hfirst : max ε (2 * d) ≤ 2 * δ := max_le (by linarith) (by linarith)
  have hsecond : max ε (s + 6 * d) ≤ 7 * δ := max_le (by linarith) (by linarith)
  have hpow1 := Real.rpow_le_rpow (le_trans hε (le_max_left _ _)) hfirst hχ.le
  have hpow2 := Real.rpow_le_rpow (le_trans hε (le_max_left _ _)) hsecond hξ.le
  have hterm1 := mul_le_mul_of_nonneg_left hpow1 hH
  have hterm2 := mul_le_mul_of_nonneg_left hpow2 hK
  linarith

/-- A high-probability quantitative modulus and a vanishing cell radius imply
the uniform modulus in probability. No measurability of the displayed events
is needed for monotonicity of the outer measure. -/
theorem modulus_in_probability_of_quantitative_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Set ℂ)
    (F : ℝ → Ω → ℂ → ℝ) (d : ℝ → ℝ) {H K χ ξ t : ℝ} {e : ℝ≥0∞}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hχ : 0 < χ) (hξ : 0 < ξ) (ht : 0 < t)
    (hd : Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hdpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ d ε)
    (hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ A, ∃ y ∈ A,
      |F ε ω x - F ε ω y| > 2 * (H * max ε (2 * d ε) ^ χ) +
        K * max ε (dist x y + 6 * d ε) ^ ξ} ≤ e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P {ω | ∃ x ∈ A, ∃ y ∈ A, dist x y < δ ∧ |F ε ω x - F ε ω y| > t} ≤ e := by
  obtain ⟨δ, hδ, hthreshold⟩ := exists_projected_modulus_threshold hH hK hχ hξ ht
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hgood, hdpos, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hδ), hd.eventually (Iio_mem_nhds hδ)] with ε hg hdε hε hεδ hdδ
  refine (measure_mono ?_).trans hg
  rintro ω ⟨x, hx, y, hy, hxy, hbad⟩
  refine ⟨x, hx, y, hy, ?_⟩
  have hbound := hthreshold ε (d ε) (dist x y) (le_of_lt hε) hεδ.le hdε hdδ.le dist_nonneg hxy.le
  linarith

/-- High-probability quantitative estimate needed for the regular-data
modulus, with deterministic constants and a vanishing cell-radius bound. -/
def CorrectedHarmonicQuantitativeModulusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, IsHolderContinuousOn ψ (closedBall z r) →
  ∀ e : ℝ≥0∞, 0 < e → ∃ H K χ ξ : ℝ, ∃ d : ℝ → ℝ,
    0 ≤ H ∧ 0 ≤ K ∧ 0 < χ ∧ 0 < ξ ∧
    Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ d ε) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ closedBall z r,
      |projectedDiscreteHarmonicExtension S r z ψ ε ω x -
        projectedDiscreteHarmonicExtension S r z ψ ε ω y| >
        2 * (H * max ε (2 * d ε) ^ χ) + K * max ε (dist x y + 6 * d ε) ^ ξ} ≤ e)

/-- The quantitative good-event estimate supplies the Hölder-data modulus. -/
theorem correctedHarmonicHolderModulus_of_quantitative (𝒮 : SpaceFillingSLEModel)
    (hquant : CorrectedHarmonicQuantitativeModulusStep 𝒮) :
    CorrectedHarmonicHolderModulusStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ t ht e he
  obtain ⟨H, K, χ, ξ, d, hH, hK, hχ, hξ, hd, hdpos, hgood⟩ :=
    hquant γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ e he
  exact modulus_in_probability_of_quantitative_bound S.P (closedBall z r)
    (fun ε ω x => projectedDiscreteHarmonicExtension S r z ψ ε ω x)
    d hH hK hχ hξ ht hd hdpos hgood

end MatedCRT
