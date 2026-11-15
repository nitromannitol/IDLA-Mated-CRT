import MatedCRT.FirstPass.Derived.AreaCellInjectiveRepresentative

/-! # Injective scaled positions for finite cell networks -/

set_option autoImplicit false
noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

/-- For a positive scale, the endpoint positions on any collection of cells
admit arbitrarily close injective positions in the corresponding scaled cells. -/
theorem exists_areaCell_scaled_injective_position
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {a : ℝ≥0} (ha : 0 < a) {t : ℝ} (ht : 0 < t)
    (R : Set (areaCellConfig h hε m).cells) :
    ∃ q : R → Plane, Function.Injective q ∧
      (∀ v : R, ∃ x ∈ (v.1.1 : Set Plane), q v = (a : ℝ) • x) ∧
      ∀ v : R, dist ((a : ℝ) • areaCellRepresentative h hε m v) (q v) < t := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨p, hp, hpcell, hpnear⟩ :=
    exists_areaCell_injective_representative_near_endpoint h hε m (div_pos ht ha')
  refine ⟨fun v => (a : ℝ) • p v, ?_, ?_, ?_⟩
  · exact (smul_right_injective Plane (ne_of_gt ha')).comp (hp.comp Subtype.val_injective)
  · intro v
    exact ⟨p v, hpcell v, rfl⟩
  · intro v
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ha']
    exact (mul_lt_mul_of_pos_left (hpnear v) ha').trans_eq (mul_div_cancel₀ t (ne_of_gt ha'))

end MatedCRT
end
