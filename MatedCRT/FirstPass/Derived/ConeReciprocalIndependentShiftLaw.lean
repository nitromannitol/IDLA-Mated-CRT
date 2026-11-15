import MatedCRT.FirstPass.Derived.ConeShiftedWalkLiftCoordinates
import MatedCRT.FirstPass.Derived.ReciprocalSelectedWalkProduct

/-! # Joint law of reciprocal selected walks with an independent shift -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory
open scoped NNReal

/-- The independent shift, cone coordinates and reciprocal selected walk have the
same joint law as the original coordinates and selected walk at reciprocal mesh. -/
theorem MatedCRTEnv.IsValid.map_reciprocal_selected_walk_prod
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hb1 : b < 1)
    (Q : Measure ℝ) [SFinite Q] (m : ℝ≥0) (x : ℂ) :
    (Q.prod S.P).map (fun p =>
      let q := (⌊b⁻¹⌋₊ : ℝ) * b
      let R : ℂ := (coneScaleRadius γ (S.hcirc p.2) q : ℝ)
      let η : ℝ → ℂ := fun t => R⁻¹ * S.η p.2 (q * t)
      (p.1, (η, rescaledPair q (S.bm p.2),
        (shiftedSelectedWalkLaw b m (b * p.1) (R * x) (S.η p.2) (S.bm p.2)).map
          (fun z : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * z)))) =
    (Q.prod S.P).map (fun p =>
      let δ := (⌊b⁻¹⌋₊ : ℝ)⁻¹
      (p.1, (S.η p.2, S.bm p.2,
        shiftedSelectedWalkLaw δ m (δ * p.1) x (S.η p.2) (S.bm p.2)))) := by
  obtain ⟨hn, _⟩ := LatticeProb.reciprocal_floor_mesh_eq hb hb1
  have hδ : 0 < (⌊b⁻¹⌋₊ : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  have hq : 0 < (⌊b⁻¹⌋₊ : ℝ) * b := by positivity
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨V, V', F, hV, hV', hF, hlaw, hae⟩ :=
    hS.exists_cone_shifted_walk_coordinates_prod hγ hγ2 hq hδ m Q
  let G : ℝ × MatedCRTHarmonic.MatedCRT.CouplingData →
      ℝ × ((ℝ → ℂ) × C(ℝ, ℝ × ℝ) × Measure C(ℝ≥0, ℂ)) :=
    fun p => (p.1, (⇑p.2.η, p.2.bm,
      F (((p.2.η, p.2.bm), x), (⌊b⁻¹⌋₊ : ℝ)⁻¹ * p.1)))
  have he : Measurable (fun v : MatedCRTHarmonic.MatedCRT.CouplingData => ⇑v.η) := by
    refine Measurable.of_eval fun t => ?_
    exact (continuous_eval_const t).measurable.comp
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η
  have hη : Measurable (fun p : ℝ × MatedCRTHarmonic.MatedCRT.CouplingData => p.2.η) :=
    MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.comp measurable_snd
  have hw : Measurable (fun p : ℝ × MatedCRTHarmonic.MatedCRT.CouplingData => p.2.bm) :=
    MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm.comp measurable_snd
  have hwalk : Measurable (fun p : ℝ × MatedCRTHarmonic.MatedCRT.CouplingData =>
      F (((p.2.η, p.2.bm), x), (⌊b⁻¹⌋₊ : ℝ)⁻¹ * p.1)) :=
    hF.comp (((hη.prodMk hw).prodMk measurable_const).prodMk
      (measurable_const.mul measurable_fst))
  have hG : Measurable G := measurable_fst.prodMk
    ((he.comp measurable_snd).prodMk (hw.prodMk hwalk))
  have hprod : (Q.prod S.P).map (Prod.map id V') =
      (Q.prod S.P).map (Prod.map id V) := by
    rw [← Measure.map_prod_map Q S.P measurable_id hV',
      ← Measure.map_prod_map Q S.P measurable_id hV, hlaw]
  have hmap := congrArg (fun μ => μ.map G) hprod
  rw [Measure.map_map hG (measurable_id.prodMap hV'),
    Measure.map_map hG (measurable_id.prodMap hV)] at hmap
  refine (Measure.map_congr ?_).trans (hmap.trans (Measure.map_congr ?_))
  · filter_upwards [hae, hS.ae_prod_shiftedSelectedWalkLaw_reciprocal
      hγ hγ2 hb hb1 Q m x] with p hp hr
    dsimp only [Function.comp_apply, G, Prod.map, id_eq]
    change (p.1, (_, _, _)) = (p.1, (⇑(V' p.2).η, (V' p.2).bm, _))
    rw [(hp.2.2.2.2 _ x).2, hr, hp.2.2.1, hp.2.2.2.1]
  · filter_upwards [hae] with p hp
    dsimp only [Function.comp_apply, G, Prod.map, id_eq]
    change (p.1, (⇑(V p.2).η, (V p.2).bm, _)) = (p.1, (_, _, _))
    rw [(hp.2.2.2.2 _ x).1, hp.1, hp.2.1]

end MatedCRT
