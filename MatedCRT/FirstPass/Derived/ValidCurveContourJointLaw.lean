import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import MatedCRT.FirstPass.Derived.BlockRunningMinTail
import MatedCRT.FirstPass.Derived.MatingFibreNullMeasurable
import LatticeProb.Topology.MeasurableProperSurjectiveCurve

/-! # Joint law of the curve and its contour process -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace MatedCRT.FirstPass.Derived

/-- A valid environment determines a joint probability law of its continuous
curve and boundary-length process. Its curve is proper and surjective almost
surely, its fibres are the mating relation, and its second marginal is the
correlated Brownian law. -/
theorem MatedCRTEnv.IsValid.exists_curve_contour_joint_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∃ ν : Measure (C(ℝ, ℂ) × Path2), IsProbabilityMeasure ν ∧
      ν.map Prod.snd = S.P.map S.bm ∧ IsCorrelatedBM2 γ (ν.map Prod.snd) ∧
      (∀ᵐ p ∂ν, IsProperMap p.1 ∧ Function.Surjective p.1 ∧
        matingRel p.2 = fun s t => p.1 s = p.1 t) := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨η, hη, hgood⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  have hbm := hS.isCorrelatedBM2_map_bm
  let V : Ω → C(ℝ, ℂ) × Path2 := fun ω => (η ω, S.bm ω)
  have hV : Measurable V := hη.prodMk hbm.2
  let ν := S.P.map V
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 inferInstance
  have hmarg : ν.map Prod.snd = S.P.map S.bm := by
    rw [show ν = S.P.map V from rfl, Measure.map_map measurable_snd hV]
    rfl
  have hproper : ∀ᵐ p ∂ν, IsProperMap p.1 ∧ Function.Surjective p.1 := by
    apply (ae_map_iff hV.aemeasurable
      (ContinuousMap.measurableSet_isProperMap_and_surjective_curve.preimage measurable_fst)).2
    filter_upwards [hgood] with ω hω
    exact ⟨hω.2.1, hω.2.2.1⟩
  have hfibre : ∀ᵐ p ∂ν, matingRel p.2 = fun s t => p.1 s = p.1 t := by
    have hn := nullMeasurableSet_matingRel_eq_fibre ν
    rw [ae_iff]
    change (S.P.map V) {p | matingRel p.2 = fun s t => p.1 s = p.1 t}ᶜ = 0
    rw [Measure.map_apply₀ hV.aemeasurable hn.compl]
    apply ae_iff.mp
    filter_upwards [hgood, hS.ae_matingRel_eq_fibre] with ω hv hf
    simpa only [V, hv.1] using hf
  refine ⟨ν, inferInstance, hmarg, ?_, ?_⟩
  · rw [hmarg]
    exact hbm.1
  · filter_upwards [hproper, hfibre] with p hp hf
    exact ⟨hp.1, hp.2, hf⟩

end MatedCRT.FirstPass.Derived
