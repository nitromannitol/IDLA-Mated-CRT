import MatedCRT.FirstPass.Derived.ContinuousReciprocalSelectedWalk

/-! # Unit-mesh scaling of selected embedded walks -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace MatedCRT

/-- Rescaling time by the positive physical mesh takes the selected walk to
unit mesh, with the marked point and the continuous paths spatially rescaled. -/
theorem shiftedSelectedWalkLaw_unitMesh_rescale
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {R : ℂ} (hR : R ≠ 0) (θ : ℝ)
    (w w' : C(ℝ, ℝ × ℝ))
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m : ℝ≥0) (x : ℂ) :
    shiftedSelectedWalkLaw 1 m θ x η' w' =
      (shiftedSelectedWalkLaw b m (b * θ) (R * x) η w).map
        (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) := by
  have hdiv : b / b = 1 := div_self (ne_of_gt hb)
  have hselect := vertexOf_shiftedPhysical_rescale (ε := b) hb hR θ η η' hη x
  have hlaw := srwLaw_shiftedPhysical_rescale (ε := b) hb hc θ w w' hw
  have hpath := interpolatedWalk_shiftedPhysical_rescale (ε := b) hb θ R η η' hη
  simp only [hdiv, one_mul] at hselect hlaw hpath
  unfold shiftedSelectedWalkLaw
  rw [hselect, hlaw]
  have hscale : Measurable (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hscale (measurable_interpPathCM _ m.coe_nonneg)]
  congr 1
  funext ξ
  ext t
  simpa only [ContinuousMap.mul_apply, ContinuousMap.const_apply, Function.comp_apply,
    interpPathCM_vertexPoint] using hpath m ξ t

end MatedCRT
