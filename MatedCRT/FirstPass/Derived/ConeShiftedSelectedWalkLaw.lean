import MatedCRT.FirstPass.Derived.ShiftedSelectedWalkFamily
import MatedCRT.FirstPass.Derived.ConeEnvironmentJointLaw
import MatedCRT.FirstPass.Derived.ConeReciprocalSelectedWalk

/-! # Joint cone scaling of shifted selected walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Filter Set Topology
open scoped NNReal

/-- The continuous-path law of the Brownian-edge walk selected at a point on a shifted grid. -/
noncomputable def shiftedSelectedWalkLaw (ε : ℝ) (m : ℝ≥0) (τ : ℝ) (x : ℂ)
    (η : ℝ → ℂ) (w : C(ℝ, ℝ × ℝ)) : Measure C(ℝ≥0, ℂ) :=
  (srwLaw (bmEdgeCount ε (fun t => (w (t + τ)).1) (fun t => (w (t + τ)).2))
    (vertexOf ε (fun t => η (t + τ)) x)).map
      (interpPathCM (vertexPoint ε (fun t => η (t + τ))) m.coe_nonneg)

/-- Cone scaling preserves the joint law of the curve, boundary pair, and the selected walk
law at a fixed marked point on any fixed shifted grid. -/
theorem MatedCRTEnv.IsValid.map_shiftedSelectedWalkLaw_rescaled
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ b ε : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hb : 0 < b) (hε : 0 < ε) (m : ℝ≥0) (τ : ℝ) (x : ℂ) :
    S.P.map (fun ω =>
      let η : ℝ → ℂ := fun t => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * t)
      let w := rescaledPair b (S.bm ω)
      (η, w, shiftedSelectedWalkLaw ε m τ x η w)) =
    S.P.map (fun ω => (S.η ω, S.bm ω, shiftedSelectedWalkLaw ε m τ x (S.η ω) (S.bm ω))) := by
  obtain ⟨F, hF, hFe⟩ := exists_measurable_shifted_selected_walk_law hε m τ
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  let G : MatedCRTHarmonic.MatedCRT.CouplingData →
      (ℝ → ℂ) × C(ℝ, ℝ × ℝ) × Measure C(ℝ≥0, ℂ) :=
    fun v => (⇑v.η, v.bm, F ((v.η, v.bm), x))
  have he : Measurable (fun v : MatedCRTHarmonic.MatedCRT.CouplingData => ⇑v.η) := by
    refine Measurable.of_eval fun t => ?_
    exact (continuous_eval_const t).measurable.comp
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η
  have hw := MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm
  have hf : Measurable (fun v : MatedCRTHarmonic.MatedCRT.CouplingData => F ((v.η, v.bm), x)) :=
    hF.comp ((MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.prodMk hw).prodMk measurable_const)
  have hG : Measurable G := he.prodMk (hw.prodMk hf)
  have hmap := congrArg (fun μ => Measure.map G μ) hlaw
  rw [Measure.map_map hG hV', Measure.map_map hG hV] at hmap
  refine (Measure.map_congr ?_).trans (hmap.trans (Measure.map_congr ?_))
  · filter_upwards [hid, hS.ae_tendsto_cocompact, hS.isAreaParametrized,
        hS.ae_coneScaleRadius_pos_from_coupling hγ hγ2 b] with ω hi hp ha hR
    have hR0 : (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hR.ne'
    let e : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ b hb.ne'
    let f : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ _ (inv_ne_zero hR0)
    have hp' : Tendsto (V' ω).η (cocompact ℝ) (cocompact ℂ) := by
      rw [hi.1]
      exact f.isClosedEmbedding.tendsto_cocompact.comp (hp.comp e.isClosedEmbedding.tendsto_cocompact)
    have hs' : Function.Surjective (V' ω).η := by
      rw [hi.1]
      exact f.surjective.comp (ha.2.2.1.comp e.surjective)
    change (_, _, shiftedSelectedWalkLaw ε m τ x _ _) = (⇑(V' ω).η, (V' ω).bm, F (((V' ω).η, (V' ω).bm), x))
    rw [← hi.1, ← hi.2.1]
    exact congrArg (fun u => (⇑(V' ω).η, (V' ω).bm, u))
      (hFe (V' ω).η (V' ω).bm x hp' hs').symm
  · filter_upwards [htie, hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω ht hp ha
    have hp' : Tendsto (V ω).η (cocompact ℝ) (cocompact ℂ) := by rw [ht.1]; exact hp
    have hs' : Function.Surjective (V ω).η := by rw [ht.1]; exact ha.2.2.1
    have hF' := hFe (V ω).η (V ω).bm x hp' hs'
    dsimp [G, shiftedSelectedWalkLaw] at hF' ⊢
    rw [ht.1, hbm ω] at hF'
    rw [ht.1, hbm ω, hF']

end MatedCRT
