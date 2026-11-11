import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSUniformDistance
import MatedCRT.Steps.Sec3.ProbabilityTailCutoff

/-! Convert the GMS excursion estimate to the real-valued cutoff tail. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The uniform GMS bound implies the real probability tail in the form used
for Hölder moment estimates, up to any scale with disk margin. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_real_tail_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε a b ρ : ℝ) (z : ℂ)
      (r : ℝ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (v : ℤ) (T : ℝ),
      0 < ε → 0 < r → HolderOnWith H χ ψ (closedBall z r) →
      2 * (100 * ε ^ a + ε ^ b) < T →
      IsLocallyFiniteMult (S.mult ε ω) →
      (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) → 0 < S.mε ε →
      Continuous (S.η ω) → Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) →
      v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
      (∀ j k, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) →
      r + 3 * ε ^ a + dist z 0 + ε ^ a + 2 * T < ρ →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ t : ℝ, ε ^ b ≤ t → t ≤ ρ →
        ball z (2 * t) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z t),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (t / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * t))) y path}) →
      ∀ s ∈ Ioc (2 * (100 * ε ^ a + ε ^ b)) T,
        (srwLaw (S.mult ε ω) v).real
          {path | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
        (2 * (100 * ε ^ a + ε ^ b)) ^ ν * s ^ (-ν) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_sameWalkExitDiscrepancy_le_at_distance_of_uniform_gms
    hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  intro ε a b ρ z r ψ H χ v T hε hr hψ hcut hlf hcons hm hη hproper hv hadj
    hmargin hsize hann s hs
  let d : ℝ := 100 * ε ^ a + ε ^ b
  have hd : 0 < d := by dsimp [d]; positivity
  have hs0 : 0 < s := by dsimp [d] at hd; nlinarith [hs.1]
  have hsmargin : r + 3 * ε ^ a + dist z 0 + ε ^ a + 2 * s < ρ := by linarith [hs.2]
  have he := hbound ε a b ρ z r ψ H χ v s hε hr hψ hs.1.le hlf hcons hm hη hproper hv
    hadj hsmargin hsize hann
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have hnonneg : 0 ≤ (2 : ℝ) ^ ν * (d / s) ^ ν := by positivity
  rw [ENNReal.toReal_ofReal hnonneg] at ht
  have heq : (2 : ℝ) ^ ν * (d / s) ^ ν = (2 * d) ^ ν * s ^ (-ν) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le,
      Real.div_rpow hd.le hs0.le, Real.rpow_neg hs0.le]
    ring
  simpa only [measureReal_def, ← heq, d] using ht

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_real_tail_of_gms
