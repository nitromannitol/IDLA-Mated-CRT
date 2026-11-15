import MatedCRT.FirstPass.Derived.ShiftedAreaCellCode
import LatticeProb.Topology.RadialRestrictionGap

/-! # Radial restrictions of shifted area-cell configurations -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- A radial gap in the shifted compact-cell enumeration keeps the actual
shifted area-cell configuration restricted to concentric balls constant. -/
theorem shiftedAreaCellConfig_restrict_ball_eq_of_radial_gap
    {μ : Measure ℂ} {η : C(ℝ, ℂ)} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ) {p q : ℝ}
    (hgap : ∀ k : ℤ, Metric.infDist (0 : ReflectedGMS.Plane)
      (LatticeProb.shiftedCompactCell
        ((⟨Complex.orthonormalBasisOneI.repr,
          Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp η)
        ε θ k : Set ReflectedGMS.Plane) ≤ p ∨
      q ≤ Metric.infDist (0 : ReflectedGMS.Plane)
      (LatticeProb.shiftedCompactCell
        ((⟨Complex.orthonormalBasisOneI.repr,
          Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp η)
        ε θ k : Set ReflectedGMS.Plane)) :
    ∀ r ∈ Ioo p q, ∀ s ∈ Ioo p q,
      (shiftedAreaCellConfig h hε θ m).restrict (Metric.ball 0 r) =
        (shiftedAreaCellConfig h hε θ m).restrict (Metric.ball 0 s) := by
  let C : ℤ → Cell := euclideanCell ε (fun t => η (t + ε * θ))
    (h.1.comp (continuous_id.add continuous_const)) hε
  have hceq (k : ℤ) : (C k : Set ReflectedGMS.Plane) =
      (LatticeProb.shiftedCompactCell
        ((⟨Complex.orthonormalBasisOneI.repr,
          Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp η)
        ε θ k : Set ReflectedGMS.Plane) := by
    change (euclideanCell ε (fun t => η (t + ε * θ))
      (h.1.comp (continuous_id.add continuous_const)) hε k : Set ReflectedGMS.Plane) = _
    rw [coe_euclideanCell, LatticeProb.coe_shiftedCompactCell]
    have ht := shiftedCompactCell_eq_cell_timeShift η hε.le θ k
    rw [LatticeProb.coe_shiftedCompactCell] at ht
    change _ = Set.image (fun t => Complex.orthonormalBasisOneI.repr (η t)) _
    exact (by simpa only [Set.image_image, Function.comp_def] using
      (congrArg (Set.image Complex.orthonormalBasisOneI.repr) ht).symm)
  have hg : ∀ k, Metric.infDist (0 : ReflectedGMS.Plane) (C k : Set ReflectedGMS.Plane) ≤ p ∨
      q ≤ Metric.infDist (0 : ReflectedGMS.Plane) (C k : Set ReflectedGMS.Plane) := by
    intro k
    simpa only [hceq k] using hgap k
  have hs := (LatticeProb.radial_gap_iff_restrictions_constant
    (fun k => (C k : Set ReflectedGMS.Plane)) (fun k => (C k).nonempty) 0).1 hg
  intro r hr s hs'
  ext K
  change (K ∈ Set.range C ∧ ((K : Set ReflectedGMS.Plane) ∩ Metric.ball 0 r).Nonempty) ↔
    (K ∈ Set.range C ∧ ((K : Set ReflectedGMS.Plane) ∩ Metric.ball 0 s).Nonempty)
  constructor <;> rintro ⟨⟨k, rfl⟩, hk⟩
  · exact ⟨⟨k, rfl⟩, (Set.ext_iff.mp (hs r hr s hs') k).mp hk⟩
  · exact ⟨⟨k, rfl⟩, (Set.ext_iff.mp (hs r hr s hs') k).mpr hk⟩

end MatedCRT
end
