import MatedCRT.FirstPass.Derived.CouplingConditionedPath
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedDefs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

/-! # Independence of a radial splice -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- A continuous exterior radial version can be chosen as a measurable
function of the field. The circle-average identity is for each fixed time. -/
theorem exists_exteriorRadialPath_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ R : LQGMetric.DistC → C(ℝ≥0, ℝ), Measurable R ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        R (X ω) t = LQGMetric.circleAvg (X ω) (Real.exp t) 0 -
          LQGMetric.circleAvg (X ω) 1 0 := by
  have hX := D.gff
  obtain ⟨ρ, hρm, hρ, _, _, _⟩ := MatedCRTHarmonic.GMCFacts.exists_radialProcess
    (LQGMetric.GM.isWholePlaneGFF_id_map hX)
  let R : LQGMetric.DistC → C(ℝ≥0, ℝ) := fun h =>
    ⟨fun t => ρ h (-(t : ℝ)), (ρ h).continuous.comp (by fun_prop)⟩
  have hRm : Measurable R := ContinuousMap.measurable_iff_eval.2 fun t =>
    (ContinuousMap.measurable_eval (-(t : ℝ))).comp hρm
  refine ⟨R, hRm, ?_⟩
  intro t
  have h := MeasureTheory.ae_of_ae_map hX.measurable.aemeasurable (hρ (-(t : ℝ)))
  simpa only [R, ContinuousMap.coe_mk, neg_neg, id_eq] using h

/-- A radial replacement whose exterior path is a measurable function of the
original field is jointly independent with the inner path from the conditioned
outer path. This statement does not assert a law for the replacement field. -/
theorem exists_radialSplice_indep_conditionedPath_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (R : LQGMetric.DistC → C(ℝ≥0, ℝ)) (hR : Measurable R) :
    ∃ W F : Ω → C(ℝ≥0, ℝ), Measurable W ∧ Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, F ω t = referenceConeConditionedPath γ (fun s => B' s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) ∧
      IndepFun (fun ω => (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω, W ω)) F P := by
  obtain ⟨W, F, hWm, hFm, hW, hF, hlaw, hind⟩ :=
    exists_conditionedPath_indep_field_brownian_of_coupling D hγ hγ2
  refine ⟨W, F, hWm, hFm, hW, hF, hlaw, ?_⟩
  have hT : Measurable (fun p : LQGMetric.DistC × C(ℝ≥0, ℝ) =>
      MatedCRTHarmonic.GMCFacts.twoSided p.2 (R p.1)) :=
    MatedCRTHarmonic.GMCFacts.measurable_twoSided.comp
      (measurable_snd.prodMk (hR.comp measurable_fst))
  have hY : Measurable (fun p : LQGMetric.DistC × C(ℝ≥0, ℝ) =>
      MatedCRTHarmonic.GMCFacts.replField Prod.fst
        (fun p => MatedCRTHarmonic.GMCFacts.twoSided p.2 (R p.1)) p) :=
    MatedCRTHarmonic.GMCFacts.measurable_replField measurable_fst hT
  exact hind.comp (hY.prodMk measurable_snd) measurable_id

end MatedCRT.Sec1
