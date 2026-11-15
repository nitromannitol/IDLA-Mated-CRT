import MatedCRT.FirstPass.Derived.CouplingConeSpliceArea
import LatticeProb.LQG.ConeSpliceRestriction

/-! # Local cone field and area on a mating-of-trees coupling -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open MatedCRTHarmonic MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling
open LQGMetric LQGMetric.Blueprint
open scoped NNReal

namespace MatedCRT.Sec1

/-- The same witnesses retain their laws and independence, with the cone pairing
and local field and area identities on one common event. -/
theorem exists_cone_splice_local_field_area_witnesses_of_coupling
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
      LQGMetric.IsNormalizedWPGFF (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
          ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)) P ∧
      IndepFun (fun ω => (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
          ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω, W ω)) F P ∧
      (∀ᵐ ω ∂P, (∀ (φ : LQGMetric.TestC), (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
        MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
          (fun t => B' t ω) φ =
        MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω φ +
          ∫ z, φ z * (γ * (-Real.log ‖z‖))) ∧
        let G := MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
          (fun t => B' t ω)
        let H := MatedCRTHarmonic.GMSCase.addLogSing γ
          (MatedCRTHarmonic.GMCFacts.replField X
            (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
              ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)
        HasAreaLimitS γ H (lqgArea γ H) ∧
          ∀ (V : Opens ℂ), (V : Set ℂ) ⊆ ball 0 1 →
            restrictTo V G = restrictTo V H ∧
            (lqgArea γ G).restrict V = (lqgArea γ H).restrict V) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨R, W, F, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw, hG, hind, harea⟩ :=
    exists_cone_splice_area_witnesses_of_coupling D hγ hγ2
  refine ⟨R, W, F, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw, hG, hind, ?_⟩
  have hfield := LatticeProb.LQG.ae_restrictTo_coneFieldOf_eq_replField_twoSided_addLogSing
    (γ := γ) (X := X) D.bm_B D.bm_B' D.indep_cone.2 W
    (fun ω => ⟨fun t => R (X ω) (-(t : ℝ)),
      (R (X ω)).continuous.comp (by fun_prop)⟩) hW
  filter_upwards [harea, hfield] with ω ha hf
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro V hV
  exact ⟨hf V hV, ha.2.2 V hV⟩

end MatedCRT.Sec1
