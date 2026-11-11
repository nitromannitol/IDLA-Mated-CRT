import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSMesoscopicRate
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSUniformGeometry

/-! # Same-walk rate with uniform disk geometry -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A single comparison-disk cell-size event supplies the geometric bounds in
the quenched same-walk tail estimate. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_of_uniform_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε a b ρ q : ℝ) (z : ℂ)
      (r : ℝ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (v : ℤ),
      0 < ε → ε ≤ 1 → 0 < r → 0 < χ →
      HolderOnWith H χ ψ (closedBall z r) →
      4 * (100 * ε ^ a + ε ^ b) ≤ ε ^ (q / (χ : ℝ)) / 2 →
      IsLocallyFiniteMult (S.mult ε ω) →
      (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) → 0 < S.mε ε →
      Continuous (S.η ω) → Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) →
      v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
      (∀ j k, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) →
      r + 3 * ε ^ a + dist z 0 + ε ^ a +
        2 * (ε ^ (q / (χ : ℝ)) / 2) < ρ →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ b ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) →
      srwLaw (S.mult ε ω) v
        {path | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
        ENNReal.ofReal (((2 : ℝ) ^ ν * (202 : ℝ) ^ ν) *
          ε ^ ((min a b - q / (χ : ℝ)) * ν)) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_sameWalkExitDiscrepancy_le_of_gms hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  intro ε a b ρ q z r ψ H χ v hε hε1 hr hχ hψ hscale hlf hcons hm hη hproper hv
    hadj hmargin hsize hgood
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hR : 0 < ε ^ (q / (χ : ℝ)) / 2 := by positivity
  obtain ⟨hsmall, hlarge, hcenters⟩ :=
    gms_uniform_disk_geometry hε.le hη ha hR hmargin hsize
  exact hbound ε a b ρ q z r ψ H χ v hε hε1 hr hχ hψ hscale hlf hcons hm hη
    hproper hv hadj hsmall hlarge hsize hcenters hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_of_uniform_gms
