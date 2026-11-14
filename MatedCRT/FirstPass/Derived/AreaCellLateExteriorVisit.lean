import MatedCRT.FirstPass.Derived.AreaCellSimultaneousExteriorVisit

/-! # Arbitrarily late exterior visits for area-parametrized curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Metric ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- Almost every relabelled walk visits the exterior of every bounded set
at arbitrarily late times. -/
theorem ae_visit_all_exteriors_late_areaCellRepresentative
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
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        s • areaCellRepresentative h hε m (ξ n) ∉ U := by
  filter_upwards [ae_visit_all_exteriors_areaCellRepresentative h hε m hlf H hH hconn hs x Q hQ]
    with ξ hξ U hU N
  let p : ℕ → ReflectedGMS.Plane := fun n => s • areaCellRepresentative h hε m (ξ n)
  have hfinite : (p '' Set.Iio N).Finite := (Set.finite_Iio N).image p
  obtain ⟨n, hn⟩ := hξ (U ∪ p '' Set.Iio N) (hU.union hfinite.isBounded)
  refine ⟨n, ?_, fun hu => hn (Set.mem_union_left _ hu)⟩
  by_contra h
  have hnlt : n < N := Nat.lt_of_not_ge h
  exact hn (Set.mem_union_right _ (Set.mem_image_of_mem p hnlt))

end MatedCRT
end
