import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCutoffMean
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicMeanRates

/-! Mesh-power bounds for the quenched GMS mean discrepancy. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The GMS estimate yields the three mesh-power mean regimes for positive
Hölder constant, under the displayed uniform geometric hypotheses. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_mean_rates_of_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε a b ρ : ℝ) (z : ℂ)
      (r : ℝ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (v : ℤ) (T : ℝ),
      0 < H → 0 < χ → T ≤ r → 0 < ε → ε ≤ 1 → 0 ≤ min a b → 0 < r → HolderOnWith H χ ψ (closedBall z r) →
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
      let K := (r / T) ^ ν
      let A := (H : ℝ) * (2 : ℝ) ^ (χ : ℝ)
      ((χ : ℝ) < ν → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
        A * ((202 : ℝ) ^ (χ : ℝ) * (1 + (χ : ℝ) * K / (ν - χ))) *
          ε ^ (min a b * (χ : ℝ))) ∧
      ((χ : ℝ) = ν → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
        A * ((202 : ℝ) ^ ν * (1 + ν * K * (|Real.log r| + |min a b|))) *
          ε ^ (min a b * ν) * (1 + |Real.log ε|)) ∧
      (ν < (χ : ℝ) → (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
        A * ((202 : ℝ) ^ (χ : ℝ) + (χ : ℝ) * K * (202 : ℝ) ^ ν *
          r ^ ((χ : ℝ) - ν) / ((χ : ℝ) - ν)) * ε ^ (min a b * ν)) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_sameWalkExitDiscrepancy_mean_of_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  intro ε a b ρ z r ψ H χ v T hH hχ hTr hε hε1 hmexp hr hψ hcut hlf hcons hm hη hproper hv hadj
    hmargin hsize hann
  have hmean := hbound ε a b ρ z r ψ H χ v T hH hχ hTr hε hr hψ hcut hlf hcons hm hη hproper hv hadj
    hmargin hsize hann
  have hχp : 0 < (χ : ℝ) := by exact_mod_cast hχ
  have hT : 0 < T := by
    have hp : 0 < 2 * (100 * ε ^ a + ε ^ b) := by positivity
    linarith
  have hK : 0 ≤ (r / T) ^ ν := Real.rpow_nonneg (div_nonneg hr.le hT.le) _
  have hA : 0 ≤ (H : ℝ) * (2 : ℝ) ^ (χ : ℝ) := by positivity
  have hℓr : 2 * (100 * ε ^ a + ε ^ b) ≤ r := hcut.le.trans hTr
  refine ⟨?_, ?_, ?_⟩
  · intro hχv
    have hb := mesoscopic_mean_lt_rate (a := a) (b := b) (K := (r / T) ^ ν) hε hε1 hχp hχv hK
    have hx := (hmean.1 hχv).trans (mul_le_mul_of_nonneg_left hb hA)
    convert hx using 1; ring
  · intro heq
    subst ν
    have hb := mesoscopic_mean_eq_rate (a := a) (b := b) (K := (r / T) ^ (χ : ℝ)) hε hε1 hχp hK hr hℓr
    have hx := (hmean.2.1 rfl).trans (mul_le_mul_of_nonneg_left hb hA)
    convert hx using 1; ring
  · intro hνχ
    have hb := mesoscopic_mean_gt_rate (a := a) (b := b) (K := (r / T) ^ ν) hε hε1 hmexp hν hνχ hK hr
    have hx := (hmean.2.2 hνχ).trans (mul_le_mul_of_nonneg_left hb hA)
    convert hx using 1; ring

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_mean_rates_of_gms
