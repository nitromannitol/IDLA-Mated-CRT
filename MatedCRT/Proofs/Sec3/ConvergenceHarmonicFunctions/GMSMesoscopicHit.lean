import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSBoundaryCellHit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicCutoff

/-! # Mesoscopic boundary-cell hitting bound -/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- The GMS boundary-cell bound at the mesoscopic cutoff, with the constant
from doubling the cutoff made explicit. -/
theorem MatedCRTEnv.IsValid.ae_boundary_cell_hit_order_le_mesoscopic
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ p : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᵐ ω ∂S.P, ∀ (ε a b ρ : ℝ) (z : ℂ)
      (j : ℤ) (r distance : ℝ),
      0 < ε → 0 < r → 2 * (100 * ε ^ a + ε ^ b) ≤ distance →
      2 * distance + dist (vertexPoint ε (S.η ω) j) 0 ≤ ρ →
      vertexPoint ε (S.η ω) j ∈ ball 0 ρ →
      (∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) →
      diam (cell ε (S.η ω) j) ≤ ε ^ a →
      j ∈ cellVertices ε (S.η ω) (sphere z r) →
      (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ b ≤ s → s ≤ ρ →
        ball z (2 * s) ⊆ ball 0 ρ → ∀ v ∈ cellVertices ε (S.η ω) (ball z s),
        ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v
          {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
            walkDisconnectsBeforeHit (S.mult ε ω)
              (cellVertices ε (S.η ω) (sphere z (2 * s))) y path}) →
      srwLaw (S.mult ε ω) j {path |
        vHitTime (cellVertices ε (S.η ω)
          (sphere (vertexPoint ε (S.η ω) j) distance)) path ≤
          vHitTime (cellVertices ε (S.η ω) (sphere z (r + 3 * ε ^ a))) path} ≤
        ENNReal.ofReal ((2 : ℝ) ^ ν * ((100 * ε ^ a + ε ^ b) / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := hS.ae_boundary_cell_hit_order_le_power hγ hγ2 hp hp1
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hbound] with ω hbound
  intro ε a b ρ z j r distance hε hr hscale hcontain hcenter hsize hdiam hj hgood
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  have hcut : 24 * ε ^ a < 2 * (100 * ε ^ a + ε ^ b) := by linarith
  have hmesh : 2 * ε ^ b ≤ 2 * (100 * ε ^ a + ε ^ b) := by linarith
  have h := hbound ε b ρ z j r (ε ^ a) (2 * (100 * ε ^ a + ε ^ b)) distance
    hε hr ha hcut hscale hmesh hcontain hcenter hsize hdiam hj hgood
  have heq : (2 * (100 * ε ^ a + ε ^ b) / distance) ^ ν =
      (2 : ℝ) ^ ν * ((100 * ε ^ a + ε ^ b) / distance) ^ ν := by
    rw [show 2 * (100 * ε ^ a + ε ^ b) / distance =
      2 * ((100 * ε ^ a + ε ^ b) / distance) by ring]
    have hd : 0 < distance := by linarith
    rw [Real.mul_rpow (by norm_num) (div_nonneg (by positivity) hd.le)]
  simpa only [heq] using h

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.ae_boundary_cell_hit_order_le_mesoscopic
