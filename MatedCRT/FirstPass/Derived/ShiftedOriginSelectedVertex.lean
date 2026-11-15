import MatedCRT.FirstPass.S5c.HExclusive
import MatedCRT.FirstPass.Derived.ValidCurveFixedTime

/-! # Selected vertex at the origin for shifted cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set

/-- A singleton-fibre root selects vertex zero on an interior shifted grid. -/
theorem vertexOf_shifted_origin_eq_zero {η : ℝ → ℂ} (hzero : η 0 = 0)
    (hf : ∀ t, η t = η 0 → t = 0) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c ∧ c < ε) : vertexOf ε (fun t => η (t + c)) 0 = 0 := by
  apply S5c.vertexOf_eq_of_exclusive
  · refine ⟨-c, ?_, ?_⟩
    · simp only [Int.cast_zero, zero_sub, mul_neg, mul_one, mul_zero, mem_Icc]
      constructor <;> linarith
    · simpa only [neg_add_cancel] using hzero
  · intro k hk
    obtain ⟨t, ht, htz⟩ := hk
    change η (t + c) = 0 at htz
    have ht0 : t + c = 0 := hf (t + c) (by rw [htz, hzero])
    have hklo : (-1 : ℝ) < k := by
      have := ht.2
      nlinarith
    have hkhi : (k : ℝ) < 1 := by
      have := ht.1
      nlinarith
    have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hkhi' : k < 1 := by exact_mod_cast hkhi
    omega

/-- One full-measure event gives the selected origin vertex for every positive
mesh and every shift strictly inside that mesh. -/
theorem MatedCRTEnv.IsValid.ae_vertexOf_shifted_origin
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ), 0 < ε → ∀ (c : ℝ), 0 < c → c < ε →
      vertexOf ε (fun t => S.η ω (t + c)) 0 = 0 := by
  filter_upwards [hS.isAreaParametrized, hS.ae_fixedTime_singleton_fibre 0] with ω harea hf ε hε c hc hcε
  exact vertexOf_shifted_origin_eq_zero harea.2.1 hf hε ⟨hc, hcε⟩

end MatedCRT
