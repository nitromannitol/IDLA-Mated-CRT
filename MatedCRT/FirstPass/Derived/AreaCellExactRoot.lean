import MatedCRT.FirstPass.Derived.AreaCellOrigin
import MatedCRT.FirstPass.Derived.ValidCurveFixedTime

/-! # Root cells at a singleton-fibre time -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- If the curve visits the origin only at time zero, exactly the two
integer-labelled cells immediately before and after zero contain the origin. -/
theorem zero_mem_euclideanCell_iff {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ t, η t = η 0 → t = 0) (k : ℤ) :
    (0 : ReflectedGMS.Plane) ∈ (euclideanCell ε η h.1 hε k : Set ReflectedGMS.Plane) ↔
      k = 0 ∨ k = 1 := by
  constructor
  · intro hk
    rw [coe_euclideanCell] at hk
    obtain ⟨z, ⟨t, ht, htz⟩, hz⟩ := hk
    have hz0 : z = 0 := by
      apply Complex.orthonormalBasisOneI.repr.injective
      simpa using hz
    have ht0 : t = 0 := hf t (by rw [htz, hz0, h.2.1])
    subst t
    have hk0 : (0 : ℝ) ≤ k := by
      have := ht.2
      nlinarith
    have hk1 : (k : ℝ) ≤ 1 := by
      have := ht.1
      nlinarith
    have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast hk0
    have hk1' : k ≤ (1 : ℤ) := by exact_mod_cast hk1
    omega
  · rintro (rfl | rfl)
    · exact (zero_mem_euclideanCell_zero_and_one h hε h.2.1).1
    · exact (zero_mem_euclideanCell_zero_and_one h hε h.2.1).2

/-- In a valid environment, the origin belongs to exactly the two cells
adjacent to time zero, simultaneously at every positive mesh. -/
theorem MatedCRTEnv.IsValid.ae_origin_cell_indices
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (h : IsAreaParametrized (S.μ ω) (S.η ω))
      (ε : ℝ) (hε : 0 < ε) (k : ℤ),
      (0 : ReflectedGMS.Plane) ∈
        (euclideanCell ε (S.η ω) h.1 hε k : Set ReflectedGMS.Plane) ↔
          k = 0 ∨ k = 1 := by
  filter_upwards [hS.ae_fixedTime_singleton_fibre 0] with ω hf h ε hε k
  exact zero_mem_euclideanCell_iff h hε hf k

end MatedCRT
