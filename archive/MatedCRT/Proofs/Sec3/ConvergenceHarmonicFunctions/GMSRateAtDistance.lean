import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSMesoscopicHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateAtDistance

/-! GMS discrepancy tail at an arbitrary mesoscopic distance. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The GMS boundary-hit estimate controls the discrepancy at each admissible
excursion distance, uniformly over Hölder data. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_at_distance
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
      (∀ j ∈ interiorCellVertices ε (S.η ω) (ball z r) ∪
        cellVertices ε (S.η ω) (sphere z r), diam (cell ε (S.η ω) j) ≤ ε ^ a) →
      (∀ j ∈ cellVertices ε (S.η ω) (sphere z (r + 3 * ε ^ a)),
        diam (cell ε (S.η ω) j) ≤ ε ^ a) →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      (∀ j ∈ cellVertices ε (S.η ω) (sphere z r),
        2 * s + dist (vertexPoint ε (S.η ω) j) 0 ≤ ρ ∧
        vertexPoint ε (S.η ω) j ∈ ball 0 ρ) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ t : ℝ, ε ^ b ≤ t → t ≤ ρ →
        ball z (2 * t) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z t),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (t / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * t))) y path}) →
      srwLaw (S.mult ε ω) v
        {path | (H : ℝ) * (2 * s) ^ (χ : ℝ) < sameWalkExitDiscrepancy S r z ψ ε ω path} ≤
        ENNReal.ofReal ((2 : ℝ) ^ ν * ((100 * ε ^ a + ε ^ b) / s) ^ ν) := by
  obtain ⟨ν, hν, hhit⟩ := hS.ae_boundary_cell_hit_order_le_mesoscopic hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hhit] with ω hhit
  intro ε a b ρ z r ψ H χ v s hε hr hψ hs hlf hcons hm hη hproper hv hadj
    hsmall hlarge hsize hcenters hgood
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  have hds : 2 * ε ^ a ≤ s := by linarith
  apply srwLaw_sameWalkExitDiscrepancy_le_of_boundary_hit S hr z ψ hψ hε ω v
    hlf hcons hm hη hproper hv ha hds _ hadj hsmall hlarge
  intro j hj
  exact hhit ε a b ρ z j r s hε hr hs (hcenters j hj).1 (hcenters j hj).2
    hsize (hsmall j (Or.inr hj)) hj hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_at_distance
