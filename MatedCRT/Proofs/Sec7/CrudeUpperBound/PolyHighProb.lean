import MatedCRT.Defs.Setting

/-!
# Polynomially high probability is preserved under almost sure inclusions

If `E_r` holds with polynomially high probability as `r → 0` and, almost surely, `E_r ⊆ F_r` for all small `r`, then
`F_r` holds with polynomially high probability (`polyHighProb_mono_ae`).
-/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls

theorem polyHighProb_mono_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}
    (hE : PolyHighProb P E) {q : Ω → Prop} (hq : ∀ᵐ ω ∂P, q ω)
    (h : ∀ r : ℝ, 0 < r → ∀ ω, ω ∈ E r → q ω → ω ∈ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  refine ⟨p, hp, C, r₀, hr₀, fun r hr hrr => ?_⟩
  have hq0 : P {ω | ¬ q ω} = 0 := ae_iff.1 hq
  calc P (F r)ᶜ ≤ P ((E r)ᶜ ∪ {ω | ¬ q ω}) := by
        refine measure_mono fun ω hω => ?_
        rw [mem_compl_iff] at hω
        by_contra hc
        simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hc
        exact hω (h r hr ω hc.1 hc.2)
    _ ≤ P (E r)ᶜ + P {ω | ¬ q ω} := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [hq0, add_zero]
    _ ≤ _ := hb r hr hrr

end MatedCRT
