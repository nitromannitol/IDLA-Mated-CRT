import MatedCRT.FirstPass.Derived.CouplingRadialSplice

/-! # Radial and Brownian witnesses on a mating-of-trees coupling -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- A field-measurable full radial version and the Brownian and conditioned
paths can be chosen on the same coupling, with their joint independence. -/
theorem exists_radial_brownian_conditioned_witnesses_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (R : LQGMetric.DistC → C(ℝ, ℝ)) (W F : Ω → C(ℝ≥0, ℝ)),
      Measurable R ∧
      (∀ t, ∀ᵐ ω ∂P, R (X ω) t = LQGMetric.circleAvg (X ω) (Real.exp (-t)) 0 -
        LQGMetric.circleAvg (X ω) 1 0) ∧
      Measurable W ∧ Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, F ω t = referenceConeConditionedPath γ (fun s => B' s ω) t) ∧
      IsPreBrownianReal (fun t ω => W ω t) P ∧ IndepFun X W P ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) ∧
      IndepFun (fun ω => (X ω, W ω)) F P := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨R, hRm, hR, _, _, _⟩ := MatedCRTHarmonic.GMCFacts.exists_radialProcess
    (LQGMetric.GM.isWholePlaneGFF_id_map D.gff)
  have hRX : ∀ t, ∀ᵐ ω ∂P, R (X ω) t =
      LQGMetric.circleAvg (X ω) (Real.exp (-t)) 0 - LQGMetric.circleAvg (X ω) 1 0 := by
    intro t
    simpa only [id_eq] using MeasureTheory.ae_of_ae_map D.gff.measurable.aemeasurable (hR t)
  obtain ⟨W, F, hWm, hFm, hW, hF, hlaw, hind⟩ :=
    exists_conditionedPath_indep_field_brownian_of_coupling D hγ hγ2
  have hWB : IsPreBrownianReal (fun t ω => W ω t) P :=
    D.bm_B.toIsPreBrownianReal.congr fun t => hW.mono fun ω h => (h t).symm
  obtain ⟨V, hVm, hV⟩ := MatedCRTHarmonic.ConeScaling.exists_continuousMap_version D.bm_B'
  have he : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P]
      fun ω => ((⇑(W ω) : ℝ≥0 → ℝ), (⇑(V ω) : ℝ≥0 → ℝ)) := by
    filter_upwards [hW, hV] with ω hw hv
    exact Prod.ext (funext fun t => (hw t).symm) (funext fun t => (hv t).symm)
  have hXWV : IndepFun X (fun ω => (W ω, V ω)) P :=
    MatedCRTHarmonic.ConeScaling.indepFun_pair_continuousMap_of_coe
      (D.indep_cone.1.congr (ae_eq_refl _) he)
  have hXW : IndepFun X W P := hXWV.comp measurable_id measurable_fst
  exact ⟨R, W, F, hRm, hRX, hWm, hFm, hW, hF, hWB, hXW, hlaw, hind⟩

end MatedCRT.Sec1
