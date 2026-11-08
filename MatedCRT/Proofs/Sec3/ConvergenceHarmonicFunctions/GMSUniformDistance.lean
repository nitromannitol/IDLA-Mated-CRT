import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSRateAtDistance
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSUniformGeometry

/-! Uniform comparison-disk geometry for the distance-dependent tail. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A comparison-disk cell-size bound supplies the geometry for every
admissible excursion distance. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_at_distance_of_uniform_gms
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε a b ρ : ℝ) (z : ℂ)
      (r : ℝ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (v : ℤ) (s : ℝ),
      0 < ε → 0 < r → HolderOnWith H χ ψ (closedBall z r) →
      2 * (100 * ε ^ a + ε ^ b) ≤ s →
      IsLocallyFiniteMult (S.mult ε ω) →
      (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) → 0 < S.mε ε →
      Continuous (S.η ω) → Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) →
      v ∈ interiorCellVertices ε (S.η ω) (ball z r) →
      (∀ j k, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) →
      r + 3 * ε ^ a + dist z 0 + ε ^ a + 2 * s < ρ →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ t : ℝ, ε ^ b ≤ t → t ≤ ρ →
        ball z (2 * t) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z t),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (t / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * t))) y path}) →
      srwLaw (S.mult ε ω) v
        {path | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
        ENNReal.ofReal ((2 : ℝ) ^ ν * ((100 * ε ^ a + ε ^ b) / s) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_sameWalkExitDiscrepancy_le_at_distance hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  intro ε a b ρ z r ψ H χ v s hε hr hψ hs hlf hcons hm hη hproper hv hadj
    hmargin hsize hgood
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  have hsp : 0 < s := by linarith
  obtain ⟨hsmall, hlarge, hcenters⟩ :=
    gms_uniform_disk_geometry hε.le hη ha hsp hmargin hsize
  exact hbound ε a b ρ z r ψ H χ v s hε hr hψ hs hlf hcons hm hη hproper hv
    hadj hsmall hlarge hsize hcenters hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_at_distance_of_uniform_gms
