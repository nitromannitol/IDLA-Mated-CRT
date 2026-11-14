import MatedCRT.FirstPass.Derived.ConeScaledWalkData

/-!
# Scaling of stopped walk laws

A simultaneous rescaling of the boundary-length paths and the embedding curve preserves the
edge multiplicities. The stopped embedded walk laws are related by spatial and time dilation.
-/

set_option autoImplicit false

namespace MatedCRT.ConeScaledWalkData

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRT.ExitCouplingGlue

/-- Rescaling the boundary-length paths preserves the law of the discrete vertex walk. -/
theorem srwLaw_rescale {ε b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (L R L' R' : ℝ → ℝ) (hL : ∀ s, L' s = c * L (b * s))
    (hR : ∀ s, R' s = c * R (b * s)) (x : ℤ) :
    srwLaw (bmEdgeCount (ε / b) L' R') x = srwLaw (bmEdgeCount ε L R) x := by
  have he : bmEdgeCount (ε / b) L' R' = bmEdgeCount ε L R :=
    funext fun j => funext fun k => Sec1.bmEdgeCount_rescale hb hc L R L' R' hL hR j k
  rw [he]

/-- The stopped embedded walk laws agree after the corresponding spatial and time dilations. -/
theorem stoppedInterp_law_rescale {ε b c R : ℝ} (hb : 0 < b) (hc : 0 < c) (hR : 0 < R)
    (L K L' K' : ℝ → ℝ) (hL : ∀ s, L' s = c * L (b * s))
    (hK : ∀ s, K' s = c * K (b * s)) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (ρ : ℝ) (lam m : ℝ≥0) (x : ℤ) :
    (srwLaw (bmEdgeCount ε L K) x).map
      (stoppedInterp (vertexPoint ε η) (lam * m)
        (interiorCellVertices ε η (ball (0 : ℂ) (R * ρ)))) =
    (srwLaw (bmEdgeCount (ε / b) L' K') x).map
      (fun X => (⟨fun t => (R : ℂ) * stoppedInterp (vertexPoint (ε / b) η') m
        (interiorCellVertices (ε / b) η' (ball (0 : ℂ) ρ)) X (lam * t),
        continuous_const.mul ((stoppedInterp (vertexPoint (ε / b) η') m
          (interiorCellVertices (ε / b) η' (ball (0 : ℂ) ρ)) X).continuous.comp
            (continuous_const.mul continuous_id))⟩ : C(ℝ≥0, ℂ))) := by
  rw [srwLaw_rescale hb hc L K L' K' hL hK]
  congr 1
  funext X
  ext t
  exact stoppedInterp_rescale_ball hb hR η η' hη ρ lam m X t

end MatedCRT.ConeScaledWalkData
