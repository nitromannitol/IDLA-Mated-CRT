import MatedCRT.FirstPass.Derived.ConeStoppedWalkJointLaw

/-! # Joint scaling of stopped walk laws over all starting vertices -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open scoped NNReal
open MatedCRT.ExitCouplingGlue

/-- The positions and stopped walk laws at all vertices jointly have the same law
under cone rescaling. -/
theorem MatedCRTEnv.IsValid.map_stoppedWalkVertexFamily_rescaled
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (m : ℝ≥0) :
    S.P.map (fun ω (a : ℤ) =>
      (vertexPoint ε (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s)) a,
       (srwLaw (bmEdgeCount ε (fun t => (rescaledPair b (S.bm ω) t).1)
          (fun t => (rescaledPair b (S.bm ω) t).2)) a).map
        (stoppedInterp (vertexPoint ε (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ *
          S.η ω (b * s))) m (interiorCellVertices ε (fun s =>
            (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s)) D)))) =
    S.P.map (fun ω (a : ℤ) =>
      (vertexPoint ε (S.η ω) a,
       (srwLaw (bmEdgeCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)) a).map
        (stoppedInterp (vertexPoint ε (S.η ω)) m (interiorCellVertices ε (S.η ω) D)))) := by
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  let F : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) → ℤ → ℂ × Measure C(ℝ≥0, ℂ) := fun p a =>
    (vertexPoint ε p.1 a,
      (srwLaw (bmEdgeCount ε (fun t => (p.2 t).1) (fun t => (p.2 t).2)) a).map
        (stoppedInterp (vertexPoint ε p.1) m (interiorCellVertices ε p.1 D)))
  let G : MatedCRTHarmonic.MatedCRT.CouplingData → ℤ → ℂ × Measure C(ℝ≥0, ℂ) :=
    fun v => F (v.η, v.bm)
  have hF : Measurable F := by
    apply measurable_pi_iff.2
    intro a
    exact ((ContinuousMap.measurable_eval _).comp measurable_fst).prodMk
      (measurable_stoppedWalkLaw_curve_boundary ε D hD m a)
  have hG : Measurable G := hF.comp
    (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.prodMk
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm)
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
