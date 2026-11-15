import MatedCRT.FirstPass.Derived.ExitPointTargetLaw

/-! # Regular exit under invertible linear images -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Invertible linear maps preserve the exit time and regularity of an exit. -/
theorem regularExit_linearImage (L : ℂ ≃L[ℝ] ℂ) (U : Set ℂ) (b : ContinuousPath ℂ)
    (hb : pathExitTime (L ⁻¹' U) ⇑b ≠ ⊤ ∧
      MatedCRT.TruncatedLaws.RegularExit (L ⁻¹' U) ⇑b) :
    pathExitTime U (fun t => L (b t)) ≠ ⊤ ∧
      MatedCRT.TruncatedLaws.RegularExit U (fun t => L (b t)) := by
  have ht : pathExitTime (L ⁻¹' U) ⇑b = pathExitTime U (fun t => L (b t)) := by
    simp only [pathExitTime, mem_preimage]
  have hc : L ⁻¹' closure U = closure (L ⁻¹' U) := L.toHomeomorph.preimage_closure U
  refine ⟨ht ▸ hb.1, Or.inr ?_⟩
  have hf := hb.2.resolve_left hb.1
  rw [ht] at hf
  exact hf.mono fun t h => by
    intro hm
    apply h
    rw [← hc]
    exact hm

/-- A linear image of planar Brownian motion exits every bounded open set with
an exterior normal field regularly, provided the image starts inside the set. -/
theorem ae_regularExit_linearImage_planarBrownian (L : ℂ ≃L[ℝ] ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {v : ℂ → ℂ} (hv : Measurable v)
    (hvU : ∀ p ∈ frontier U, v p ≠ 0 ∧ ∀ q : ℂ,
      0 < inner ℝ (v p) (q - p) → q ∉ closure U)
    {x : ℂ} (hx : L x ∈ U) :
    ∀ᵐ b ∂planarBrownianMotion x,
      pathExitTime U (fun t => L (b t)) ≠ ⊤ ∧
        MatedCRT.TruncatedLaws.RegularExit U (fun t => L (b t)) := by
  filter_upwards [ae_regularExit_planarBrownian_of_exteriorNormal (hU.preimage L.continuous)
    (isBounded_preimage L hUb) (measurable_adjoint_normal L hv)
    (exteriorNormal_preimage L hvU) hx] with b hb
  exact regularExit_linearImage L U b hb

end MatedCRT.StopAtExitCmp
