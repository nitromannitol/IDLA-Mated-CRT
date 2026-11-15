import MatedCRT.FirstPass.Derived.JointShiftedSelectedWalkFamily
import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw

/-! # Joint coordinates and representatives for shifted selected walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- The cone lift coordinates and the selected walk representatives agree simultaneously. -/
theorem MatedCRTEnv.IsValid.exists_cone_shifted_walk_coordinates
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ b ε : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hb : 0 < b) (hε : 0 < ε) (m : ℝ≥0) :
    ∃ (V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData)
      (F : ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) × ℝ → Measure C(ℝ≥0, ℂ)),
      Measurable V ∧ Measurable V' ∧ Measurable F ∧ S.P.map V' = S.P.map V ∧
      ∀ᵐ ω ∂S.P,
        ⇑(V ω).η = S.η ω ∧ (V ω).bm = S.bm ω ∧
        ⇑(V' ω).η = (fun t =>
          ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * t)) ∧
        (V' ω).bm = rescaledPair b (S.bm ω) ∧
        ∀ (τ : ℝ) (x : ℂ),
        F ((((V ω).η, (V ω).bm), x), τ) =
          shiftedSelectedWalkLaw ε m τ x (S.η ω) (S.bm ω) ∧
        F ((((V' ω).η, (V' ω).bm), x), τ) =
          shiftedSelectedWalkLaw ε m τ x
            (fun t => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * t))
            (rescaledPair b (S.bm ω)) := by
  obtain ⟨F, hF, hFe⟩ := exists_jointly_measurable_shifted_selected_walk_law hε m
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  refine ⟨V, V', F, hV, hV', hF, hlaw, ?_⟩
  filter_upwards [hid, htie, hS.ae_tendsto_cocompact, hS.isAreaParametrized,
    hS.ae_coneScaleRadius_pos_from_coupling hγ hγ2 b] with ω hi ht hp ha hR
  have hR0 : (((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hR.ne'
  let e : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ b hb.ne'
  let f : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ _ (inv_ne_zero hR0)
  have hpV : Tendsto (V ω).η (cocompact ℝ) (cocompact ℂ) := by
    rw [ht.1]; exact hp
  have hsV : Function.Surjective (V ω).η := by
    rw [ht.1]; exact ha.2.2.1
  have hpV' : Tendsto (V' ω).η (cocompact ℝ) (cocompact ℂ) := by
    rw [hi.1]
    exact f.isClosedEmbedding.tendsto_cocompact.comp (hp.comp e.isClosedEmbedding.tendsto_cocompact)
  have hsV' : Function.Surjective (V' ω).η := by
    rw [hi.1]
    exact f.surjective.comp (ha.2.2.1.comp e.surjective)
  refine ⟨ht.1, hbm ω, hi.1, hi.2.1, ?_⟩
  intro τ x
  constructor
  · simpa only [shiftedSelectedWalkLaw, ht.1, hbm ω] using
      hFe (V ω).η (V ω).bm x τ hpV hsV
  · simpa only [shiftedSelectedWalkLaw, hi.1, hi.2.1] using
      hFe (V' ω).η (V' ω).bm x τ hpV' hsV'

/-- The simultaneous representatives remain valid on an independent product space. -/
theorem MatedCRTEnv.IsValid.exists_cone_shifted_walk_coordinates_prod
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ b ε : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hb : 0 < b) (hε : 0 < ε) (m : ℝ≥0) (Q : Measure ℝ) [SFinite Q] :
    ∃ (V V' : Ω → MatedCRTHarmonic.MatedCRT.CouplingData)
      (F : ((C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) × ℂ) × ℝ → Measure C(ℝ≥0, ℂ)),
      Measurable V ∧ Measurable V' ∧ Measurable F ∧ S.P.map V' = S.P.map V ∧
      ∀ᵐ p ∂Q.prod S.P,
        ⇑(V p.2).η = S.η p.2 ∧ (V p.2).bm = S.bm p.2 ∧
        ⇑(V' p.2).η = (fun t =>
          ((coneScaleRadius γ (S.hcirc p.2) b : ℝ) : ℂ)⁻¹ * S.η p.2 (b * t)) ∧
        (V' p.2).bm = rescaledPair b (S.bm p.2) ∧
        ∀ (τ : ℝ) (x : ℂ),
        F ((((V p.2).η, (V p.2).bm), x), τ) =
          shiftedSelectedWalkLaw ε m τ x (S.η p.2) (S.bm p.2) ∧
        F ((((V' p.2).η, (V' p.2).bm), x), τ) =
          shiftedSelectedWalkLaw ε m τ x
            (fun t => ((coneScaleRadius γ (S.hcirc p.2) b : ℝ) : ℂ)⁻¹ * S.η p.2 (b * t))
            (rescaledPair b (S.bm p.2)) := by
  obtain ⟨V, V', F, hV, hV', hF, hlaw, hae⟩ :=
    hS.exists_cone_shifted_walk_coordinates hγ hγ2 hb hε m
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  exact ⟨V, V', F, hV, hV', hF, hlaw, Measure.quasiMeasurePreserving_snd.ae hae⟩

end MatedCRT
