import MatedCRT.FirstPass.Derived.CouplingConeSpliceLocalFieldArea
import LatticeProb.LQG.JointSpliceConeObservations

/-! # Joint cone observations on a mating-of-trees coupling -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open MatedCRTHarmonic MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling
open LQGMetric LQGMetric.Blueprint
open scoped NNReal

namespace MatedCRT.Sec1

/-- The same witnesses retain their laws and common local identities, while
the splice and local observations are jointly independent of the conditioned path. -/
theorem exists_cone_splice_joint_observation_witnesses_of_coupling
    {Ω : Type} {ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (V : ι → Opens ℂ) (hV : ∀ i, V i ≤ ballO (0 : ℂ) 1) :
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
      (let G : Ω → LQGMetric.DistC := fun ω =>
        MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)
       let H : Ω → LQGMetric.DistC := fun ω => MatedCRTHarmonic.GMSCase.addLogSing γ
        (MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)
       IndepFun (fun ω => (((H ω, lqgArea γ (H ω)),
        (fun i => (restrictTo (V i) (G ω), (lqgArea γ (G ω)).restrict (V i)))), W ω)) F P) ∧
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
  obtain ⟨R, W, F, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw, hG, hind, hevent⟩ :=
    exists_cone_splice_local_field_area_witnesses_of_coupling D hγ hγ2
  refine ⟨R, W, F, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw, hG, hind, ?_, hevent⟩
  exact (LatticeProb.LQG.joint_splice_and_local_cone_observations
    hγ hγ2 D.gff D.bm_B D.bm_B' D.indep_cone.2 D.indep_cone.1
    hRm hR hWm hWB hXW hW hFm hind V hV).1

end MatedCRT.Sec1
