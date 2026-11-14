import MatedCRT.FirstPass.Derived.ConeEnvironmentJointLaw
import MatedCRT.FirstPass.Derived.StoppedWalkCarrier

/-! # Joint scaling law for stopped embedded walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open scoped NNReal
open MatedCRT.ExitCouplingGlue

/-- The quenched stopped walk law built from the rescaled curve and boundary pair has the
same distribution as the corresponding law in the original cone environment. -/
theorem MatedCRTEnv.IsValid.map_stoppedWalkLaw_rescaled {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ b : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (m : ℝ≥0) (a : ℤ) :
    S.P.map (fun ω =>
      (srwLaw (bmEdgeCount ε (fun t => (rescaledPair b (S.bm ω) t).1)
          (fun t => (rescaledPair b (S.bm ω) t).2)) a).map
        (stoppedInterp (vertexPoint ε (fun s =>
          ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s))) m
          (interiorCellVertices ε (fun s =>
            ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)) D))) =
    S.P.map (fun ω =>
      (srwLaw (bmEdgeCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)) a).map
        (stoppedInterp (vertexPoint ε (S.η ω)) m (interiorCellVertices ε (S.η ω) D))) := by
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  let F : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) → Measure C(ℝ≥0, ℂ) := fun p =>
    (srwLaw (bmEdgeCount ε (fun t => (p.2 t).1) (fun t => (p.2 t).2)) a).map
      (stoppedInterp (vertexPoint ε p.1) m (interiorCellVertices ε p.1 D))
  let G : MatedCRTHarmonic.MatedCRT.CouplingData → Measure C(ℝ≥0, ℂ) :=
    fun v => F (v.η, v.bm)
  have hG : Measurable G := by
    apply (measurable_stoppedWalkLaw_curve_boundary ε D hD m a).comp
    exact MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.prodMk
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm
  have hmap := congrArg (fun μ => Measure.map G μ) hlaw
  rw [Measure.map_map hG hV', Measure.map_map hG hV] at hmap
  refine (Measure.map_congr ?_).trans (hmap.trans (Measure.map_congr ?_))
  · filter_upwards [hid] with ω hω
    dsimp [G, F]
    rw [hω.1, hω.2.1]
  · filter_upwards [htie] with ω hω
    dsimp [G, F]
    rw [hω.1, hbm ω]

end MatedCRT
