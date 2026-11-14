import MatedCRT.FirstPass.Derived.AreaCellExteriorVisit

/-! # Simultaneous exterior visits for area-parametrized curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Metric ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- Almost every relabelled walk visits the exterior of every bounded set. -/
theorem ae_visit_all_exteriors_areaCellRepresentative
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {s : ℝ} (hs : s ≠ 0) (x : ℤ)
    (Q : Measure (ℕ → (areaCellConfig h hε m).cells))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n))) :
    ∀ᵐ ξ ∂Q, ∀ U : Set ReflectedGMS.Plane, Bornology.IsBounded U →
      ∃ n : ℕ, s • areaCellRepresentative h hε m (ξ n) ∉ U := by
  have hexits : ∀ᵐ ξ ∂Q, ∀ k : ℕ,
      ∃ n : ℕ, s • areaCellRepresentative h hε m (ξ n) ∉
        ball (0 : ReflectedGMS.Plane) (k : ℝ) :=
    ae_all_iff.mpr fun k =>
      ae_visit_exterior_areaCellRepresentative h hε m hlf H hH hconn hs
        isBounded_ball x Q hQ
  filter_upwards [hexits] with ξ hξ U hU
  obtain ⟨r, hr⟩ := hU.subset_ball (0 : ReflectedGMS.Plane)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  obtain ⟨n, hn⟩ := hξ k
  exact ⟨n, fun hmem => hn ((hr.trans (ball_subset_ball (le_of_lt hk))) hmem)⟩

end MatedCRT
end
