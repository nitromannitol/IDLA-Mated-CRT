import MatedCRT.FirstPass.Derived.AreaCellShiftedFrontierHit
import LatticeProb.Walk.CellConfigExteriorFrontier

/-! # Shifted exterior hitting for area-cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain
open scoped NNReal ENNReal Pointwise

/-- On one full-measure event, every shift visits a cell whose scaled
representative lies outside each bounded set, for every valid representative
selection and every positive scale. -/
theorem ae_hitTime_exterior_ne_top_all_bounded_all_shifts_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (hc : (areaCellConfig h hε m).IsCellConfiguration) (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ K : ℕ, ∀ (p : (areaCellConfig h hε m).cells → Plane),
        (∀ C, p C ∈ (C.1 : Set Plane)) → ∀ (a : ℝ≥0), 0 < a →
        ∀ U : Set Plane, Bornology.IsBounded U →
        hitTime {C : (areaCellConfig h hε m).cells | (a : ℝ) • p C ∉ U}
          (fun n => ξ (K + n)) ≠ ⊤ := by
  filter_upwards [ae_hitTime_frontier_ne_top_all_bounded_open_all_shifts_areaCell
    h hε m hlf H hH hconn x] with ξ hξ
  intro K p hp a ha U hU
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  let A : Set Plane := {z | (a : ℝ) • z ∈ U}
  have hA : Bornology.IsBounded A := by
    apply (hU.smul₀ (a : ℝ)⁻¹).subset
    intro z hz
    change (a : ℝ) • z ∈ U at hz
    refine ⟨(a : ℝ) • z, hz, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  obtain ⟨R, hR, hz, hfront⟩ :=
    LatticeProb.CellConfigBoundary.exists_ball_frontier_representatives_outside
      (areaCellConfig h hε m) hc p hp hA (p (ξ K))
  have hstart : (((ξ K).1 : Set Plane) ∩ Metric.ball (0 : Plane) R).Nonempty :=
    ⟨p (ξ K), hp _, hz⟩
  have hh := hξ (Metric.ball (0 : Plane) R) (Metric.isBounded_ball) isOpen_ball K hstart
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hh
  apply hitTime_ne_top_iff.mpr
  exact ⟨n, hfront _ hn⟩

end MatedCRT
end
