import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCutoffTail
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkDiscrepancyMoment

/-! Quenched Hölder mean bounds from the GMS annulus estimate. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- Under the GMS geometric hypotheses, the same-walk mean discrepancy
satisfies all three Hölder exponent regimes at the microscopic cutoff. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_mean_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε a b ρ : ℝ) (z : ℂ)
      (r : ℝ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (v : ℤ) (T : ℝ),
      0 < H → 0 < χ → T ≤ r → 0 < ε → 0 < r → HolderOnWith H χ ψ (closedBall z r) →
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
      let ℓ := 2 * (100 * ε ^ a + ε ^ b)
      let K := (r / T) ^ ν
      let A := (H : ℝ) * (2 : ℝ) ^ (χ : ℝ)
      ((χ : ℝ) < ν → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
        A * (ℓ ^ (χ : ℝ) + (χ : ℝ) * K * (ℓ ^ (χ : ℝ) / (ν - χ)))) ∧
      ((χ : ℝ) = ν → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
        A * (ℓ ^ ν + ν * K * (ℓ ^ ν * Real.log (r / ℓ)))) ∧
      (ν < (χ : ℝ) → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
        A * (ℓ ^ (χ : ℝ) + (χ : ℝ) * K * (ℓ ^ ν * r ^ ((χ : ℝ) - ν) / ((χ : ℝ) - ν)))) := by
  obtain ⟨ν, hν, htail⟩ := hS.ae_sameWalkExitDiscrepancy_real_tail_of_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [htail] with ω htail
  intro ε a b ρ z r ψ H χ v T hH hχ hTr hε hr hψ hcut hlf hcons hm hη hproper hv hadj
    hmargin hsize hann
  have hℓ : 0 < 2 * (100 * ε ^ a + ε ^ b) := by positivity
  have ht := htail ε a b ρ z r ψ H χ v T hε hr hψ hcut hlf hcons hm hη hproper hv hadj
    hmargin hsize hann
  have ht' : ∀ s ∈ Ioc (2 * (100 * ε ^ a + ε ^ b)) T,
      (srwLaw (S.mult ε ω) v).real
        {x | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
      (1 : ℝ) * (2 * (100 * ε ^ a + ε ^ b)) ^ ν * s ^ (-ν) := by
    simpa only [one_mul] using ht
  simpa only [one_mul] using
    (srwLaw_sameWalkExitDiscrepancy_mean_of_cutoff_tail S hr z ψ hH hχ hψ hε ω v hlf hcons
      hm hη hproper hv hℓ hcut hTr hν (show (0 : ℝ) ≤ 1 by norm_num) ht')

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_mean_of_gms
