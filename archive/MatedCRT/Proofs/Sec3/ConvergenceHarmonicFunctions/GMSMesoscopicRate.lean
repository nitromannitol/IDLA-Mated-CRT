import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSMesoscopicHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateFromAnnulus

/-! # Same-walk rate on the GMS good event -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The mesoscopic GMS estimate implies the quenched same-walk tail bound
for every disk and Hölder datum satisfying the displayed geometric bounds. -/
theorem MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_of_gms
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
      (∀ j ∈ interiorCellVertices ε (S.η ω) (ball z r) ∪
        cellVertices ε (S.η ω) (sphere z r), diam (cell ε (S.η ω) j) ≤ ε ^ a) →
      (∀ j ∈ cellVertices ε (S.η ω) (sphere z (r + 3 * ε ^ a)),
        diam (cell ε (S.η ω) j) ≤ ε ^ a) →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      (∀ j ∈ cellVertices ε (S.η ω) (sphere z r),
        2 * (ε ^ (q / (χ : ℝ)) / 2) + dist (vertexPoint ε (S.η ω) j) 0 ≤ ρ ∧
        vertexPoint ε (S.η ω) j ∈ ball 0 ρ) →
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
  obtain ⟨ν, hν, hbound⟩ := hS.ae_boundary_cell_hit_order_le_mesoscopic hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  intro ε a b ρ q z r ψ H χ v hε hε1 hr hχ hψ hscale hlf hcons hm hη hproper hv
    hadj hsmall hlarge hsize hcenters hgood
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  have hcut : 2 * (100 * ε ^ a + ε ^ b) ≤ ε ^ (q / (χ : ℝ)) / 2 := by linarith
  have hdR : 2 * ε ^ a ≤ ε ^ (q / (χ : ℝ)) / 2 := by linarith
  apply srwLaw_sameWalkExitDiscrepancy_le_of_annulus_hit_order S hr z ψ hχ hψ hε hε1 ω v
    hlf hcons hm hη hproper hv ha q a b ν ((2 : ℝ) ^ ν) hdR hν.le
    (Real.rpow_nonneg (by norm_num) _) hadj hsmall hlarge
  intro j hj
  exact hbound ε a b ρ z j r (ε ^ (q / (χ : ℝ)) / 2) hε hr hcut
    (hcenters j hj).1 (hcenters j hj).2 hsize (hsmall j (Or.inr hj)) hj hgood

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_sameWalkExitDiscrepancy_le_of_gms
