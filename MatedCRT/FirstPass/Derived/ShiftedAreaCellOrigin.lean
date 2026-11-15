import MatedCRT.FirstPass.Derived.AreaCellExactRoot
import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig

/-! # The origin in shifted area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- An interior shift places a singleton-fibre root in exactly cell zero. -/
theorem zero_mem_shiftedEuclideanCell_iff {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c ∧ c < ε) (hf : ∀ t, η t = η 0 → t = 0) (k : ℤ) :
    (0 : ReflectedGMS.Plane) ∈
      (euclideanCell ε (fun t => η (t + c))
        (h.1.comp (continuous_id.add continuous_const)) hε k : Set ReflectedGMS.Plane) ↔
      k = 0 := by
  constructor
  · intro hk
    rw [coe_euclideanCell] at hk
    obtain ⟨z, ⟨t, ht, htz⟩, hz⟩ := hk
    have hz0 : z = 0 := by
      apply Complex.orthonormalBasisOneI.repr.injective
      simpa using hz
    change η (t + c) = z at htz
    have ht0 : t + c = 0 := hf (t + c) (by rw [htz, hz0, h.2.1])
    have hklo : (-1 : ℝ) < k := by
      have := ht.2
      nlinarith
    have hkhi : (k : ℝ) < 1 := by
      have := ht.1
      nlinarith
    have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hkhi' : k < 1 := by exact_mod_cast hkhi
    omega
  · rintro rfl
    rw [coe_euclideanCell]
    refine ⟨0, ?_, by simp⟩
    refine ⟨-c, ?_, ?_⟩
    · simp only [Int.cast_zero, zero_sub, mul_neg, mul_one, mul_zero, Set.mem_Icc]
      constructor <;> linarith
    · simpa only [neg_add_cancel] using h.2.1

/-- A valid environment has the unique shifted root cell at every positive mesh
and every shift strictly inside that mesh, on one event of full measure. -/
theorem MatedCRTEnv.IsValid.ae_shifted_origin_cell_indices
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (h : IsAreaParametrized (S.μ ω) (S.η ω))
      (ε : ℝ) (hε : 0 < ε) (c : ℝ) (_hc : 0 < c ∧ c < ε) (k : ℤ),
      (0 : ReflectedGMS.Plane) ∈
        (euclideanCell ε (fun t => S.η ω (t + c))
          (h.1.comp (continuous_id.add continuous_const)) hε k : Set ReflectedGMS.Plane) ↔
        k = 0 := by
  filter_upwards [hS.ae_fixedTime_singleton_fibre 0] with ω hf h ε hε c hc k
  exact zero_mem_shiftedEuclideanCell_iff h hε hc hf k

end MatedCRT
