import MatedCRT.FirstPass.Derived.AreaCellRepresentative

/-! # Scaling endpoint representatives of curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

/-- Rescaling the representative of a labelled cell agrees with taking the
embedded vertex of the time- and space-rescaled curve. -/
theorem repr_vertexPoint_rescale_eq_areaCellRepresentative
    {μ : MeasureTheory.Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (c : ℤ → ℤ → ℕ) (k : ℤ) (δ : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Complex.orthonormalBasisOneI.repr
        (vertexPoint (b * ε) (fun s => (δ : ℂ) * η (s / b)) k) =
      δ • areaCellRepresentative h hε c (euclideanCellEquiv h hε k) := by
  rw [areaCellRepresentative_equiv]
  have heq : (b * ε * (k : ℝ)) / b = ε * k := by field_simp
  simp only [vertexPoint, heq, ← Complex.real_smul, map_smul]

end MatedCRT

end
