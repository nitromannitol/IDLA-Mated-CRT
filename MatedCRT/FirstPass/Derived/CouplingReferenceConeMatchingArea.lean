import MatedCRT.FirstPass.Derived.CouplingReferenceConeAllTests
import MatedCRT.FirstPass.Derived.NormalizedFieldReferenceMeasure
import MatedCRT.FirstPass.Derived.CouplingMatchingArea

/-! # Reference cone measure for a mating-of-trees coupling -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

namespace MatedCRT.Sec1

/-- The coupling witnesses also yield a matching reference cone measure and
area parametrization, on a common event with all test pairings. -/
theorem exists_reference_cone_observables_with_matching_area
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (R : LQGMetric.DistC → C(ℝ, ℝ)) (W F : Ω → C(ℝ≥0, ℝ))
      (hC : DistC → (ℂ → ℝ) → ℝ) (c : DistC → ℝ → ℂ → ℝ),
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
      (∀ᵐ ω ∂P, ∀ (φ : LQGMetric.TestC), (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
        MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
          (fun t => B' t ω) φ =
        MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω φ +
          ∫ z, φ z * (γ * (-Real.log ‖z‖))) ∧
      (∀ x (φ : TestC), hC x φ = x φ) ∧
      (∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P,
        c (MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω) r z =
        circleAvg (MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω) r z) ∧
      (∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2) ∧
      IsQuantumCone γ P
        (fun ω => MatedCRT.FirstPass.Derived.coneRefPairing γ
          (hC (MatedCRTHarmonic.GMCFacts.replField X
            (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
              ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω))
          (c (MatedCRTHarmonic.GMCFacts.replField X
            (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
              ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)) (F ω))
        (fun ω => MatedCRT.FirstPass.Derived.coneRefCircle γ
          (c (MatedCRTHarmonic.GMCFacts.replField X
            (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
              ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)) (F ω)) ∧
      (∀ᵐ ω ∂P,
        MatedCRT.radialProcess
          (MatedCRT.FirstPass.Derived.coneRefCircle γ
            (c (MatedCRTHarmonic.GMCFacts.replField X
              (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
                ⟨fun t => R (X ω) (-(t : ℝ)),
                  (R (X ω)).continuous.comp (by fun_prop)⟩) ω)) (F ω)) =
          referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω) ∧
        (∀ φ : LQGMetric.TestC, (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
          MatedCRT.FirstPass.Derived.coneRefPairing γ
            (hC (MatedCRTHarmonic.GMCFacts.replField X
              (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
                ⟨fun t => R (X ω) (-(t : ℝ)),
                  (R (X ω)).continuous.comp (by fun_prop)⟩) ω))
            (c (MatedCRTHarmonic.GMCFacts.replField X
              (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
                ⟨fun t => R (X ω) (-(t : ℝ)),
                  (R (X ω)).continuous.comp (by fun_prop)⟩) ω)) (F ω) φ =
          MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
            (fun t => B' t ω) φ) ∧
        LocallyIntegrable (fun z : ℂ => MatedCRTHarmonic.MatedCRT.coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖)) volume ∧
        LocallyIntegrable (MatedCRTHarmonic.GMCFacts.radialW
          (MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)) volume ∧
        (∀ z : ℂ, MatedCRTHarmonic.MatedCRT.coneRadial γ γ
          (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖) -
          MatedCRTHarmonic.GMCFacts.radialW
            (MatedCRTHarmonic.GMCFacts.twoSided (W ω)
              ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) z =
          γ * (-Real.log ‖z‖) + MatedCRT.FirstPass.Derived.coneRefField
            (c (MatedCRTHarmonic.GMCFacts.replField X
              (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
                ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)) (F ω) z) ∧
        ∀ φ : LQGMetric.TestC,
          MatedCRT.FirstPass.Derived.coneRefPairing γ
            (hC (MatedCRTHarmonic.GMCFacts.replField X
              (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
                ⟨fun t => R (X ω) (-(t : ℝ)),
                  (R (X ω)).continuous.comp (by fun_prop)⟩) ω))
            (c (MatedCRTHarmonic.GMCFacts.replField X
              (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
                ⟨fun t => R (X ω) (-(t : ℝ)),
                  (R (X ω)).continuous.comp (by fun_prop)⟩) ω)) (F ω) φ =
          MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
            (fun t => B' t ω) φ) ∧
      ∃ μ : DistC → Measure ℂ,
        let Y : Ω → DistC := MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)
        let A : Ω → Measure ℂ := fun ω => MatedCRT.FirstPass.Derived.coneRefMeasure γ
          (c (Y ω)) (F ω) (μ (Y ω))
        IsLQGMeasureOfField (P.map Y) γ γ c μ ∧
        IsLQGMeasureOfField P γ γ (fun ω => c (Y ω)) (fun ω => μ (Y ω)) ∧
        IsLQGMeasure P γ (fun ω => MatedCRT.FirstPass.Derived.coneRefCircle γ
          (c (Y ω)) (F ω)) A ∧
        (∀ᵐ ω ∂P,
          (∀ φ : TestC, MatedCRT.FirstPass.Derived.coneRefPairing γ
            (hC (Y ω)) (c (Y ω)) (F ω) φ =
            MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω)
              (fun t => B t ω) (fun t => B' t ω) φ) ∧
          (cellModelOfCoupling D ⟨hγ, hγ2⟩).area ω = A ω ∧
          IsAreaParametrized (A ω) (η ω)) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, hobs⟩ :=
    exists_reference_cone_observables_with_all_test_pairings D hγ hγ2
  obtain ⟨μ, hμmap, hμpull, hμcone⟩ :=
    MatedCRT.FirstPass.Derived.exists_reference_measure_of_normalized_field
      hG hhC hc hcont hmeas hγ hγ2 F
  have hrep := hobs.mono (fun _ ho => ho.2.2.2.2.2)
  have ha := MatedCRT.ae_cellModel_area_eq_of_coupling D ⟨hγ, hγ2⟩ hcone hμcone hrep
  have hp := MatedCRT.ae_isAreaParametrized_of_coupling_matching_area
    D ⟨hγ, hγ2⟩ hcone hμcone hrep
  refine ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, hobs, μ, hμmap, hμpull, hμcone, ?_⟩
  filter_upwards [hrep, ha, hp] with ω hr ha hp
  exact ⟨hr, ha, hp⟩

end MatedCRT.Sec1
