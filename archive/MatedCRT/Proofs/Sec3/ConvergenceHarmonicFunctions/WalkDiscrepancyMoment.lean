import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkDiscrepancyMeasurable
import MatedCRT.Steps.Sec3.HolderMomentCutoff

/-! Mean walk discrepancy from a cutoff excursion tail. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal

/-- A polynomial discrepancy tail up to a fixed excursion scale yields the
three Hölder mean regimes under the quenched walk law. -/
theorem srwLaw_sameWalkExitDiscrepancy_mean_of_cutoff_tail
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {H χ : ℝ≥0}
    (hH : 0 < H) (hχ : 0 < χ) (hψ : HolderOnWith H χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (v : ℤ)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) (hm : 0 < S.mε ε)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r))
    {ℓ T ν C : ℝ} (hℓ : 0 < ℓ) (hℓT : ℓ < T) (hTr : T ≤ r)
    (hν : 0 < ν) (hC : 0 ≤ C)
    (htail : ∀ s ∈ Ioc ℓ T, (srwLaw (S.mult ε ω) v).real
      {x | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
        C * ℓ ^ ν * s ^ (-ν)) :
    let K := C * (r / T) ^ ν
    let A := (H : ℝ) * (2 : ℝ) ^ (χ : ℝ)
    ((χ : ℝ) < ν → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
      A * (ℓ ^ (χ : ℝ) + (χ : ℝ) * K * (ℓ ^ (χ : ℝ) / (ν - χ)))) ∧
    ((χ : ℝ) = ν → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
      A * (ℓ ^ ν + ν * K * (ℓ ^ ν * Real.log (r / ℓ)))) ∧
    (ν < (χ : ℝ) → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
      A * (ℓ ^ (χ : ℝ) + (χ : ℝ) * K * (ℓ ^ ν * r ^ ((χ : ℝ) - ν) / ((χ : ℝ) - ν)))) := by
  let μ := srwLaw (S.mult ε ω) v
  let D := sameWalkExitDiscrepancy S r z ψ ε ω
  let : IsProbabilityMeasure μ := isProbabilityMeasure_srwLaw _ _
  have hHp : 0 < (H : ℝ) := by exact_mod_cast hH
  have hχp : 0 < (χ : ℝ) := by exact_mod_cast hχ
  have hA : 0 < (H : ℝ) * (2 : ℝ) ^ (χ : ℝ) := by positivity
  have hD := srwLaw_sameWalkExitDiscrepancy_integrable S hr z ψ hψ hε ω v hlf hcons hm hη hp hv
  have hn : 0 ≤ᵐ[μ] D := Filter.Eventually.of_forall fun x => abs_nonneg _
  have hb : ∀ᵐ x ∂μ, D x ≤ ((H : ℝ) * (2 : ℝ) ^ (χ : ℝ)) * r ^ (χ : ℝ) := by
    filter_upwards [srwLaw_ae_sameWalkExitDiscrepancy_le_disk_diameter S hr z ψ hψ hε ω v
      hlf hcons hm hη hp hv] with x hx
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le, mul_assoc] using hx
  have ht : ∀ s ∈ Ioc ℓ T, μ.real
      {x | ((H : ℝ) * (2 : ℝ) ^ (χ : ℝ)) * s ^ (χ : ℝ) < D x} ≤
        C * ℓ ^ ν * s ^ (-ν) := by
    intro s hs
    have hs0 : 0 ≤ s := (hℓ.trans hs.1).le
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs0, mul_assoc] using htail s hs
  exact integral_le_of_holder_probability_tail_cutoff μ D hA hℓ hℓT hTr hχp hν hC
    hD.aemeasurable hn hb ht

end MatedCRT

#print axioms MatedCRT.srwLaw_sameWalkExitDiscrepancy_mean_of_cutoff_tail
