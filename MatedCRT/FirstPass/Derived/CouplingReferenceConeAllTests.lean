import MatedCRT.FirstPass.Derived.CouplingReferenceConeRadialObservables
import MatedCRT.FirstPass.Derived.ReferenceConeAllTestCorrection
import LatticeProb.LQG.ConeSpliceFieldDecomposition

/-! # Coupled reference cone pairings -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric
open scoped NNReal

namespace MatedCRT.Sec1

/-- The reference cone and coupling cone agree on every test for the same
witnesses, on the common event of radial observables and corrections. -/
theorem exists_reference_cone_observables_with_all_test_pairings
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
            (fun t => B' t ω) φ) := by
  obtain ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, hobs⟩ :=
    exists_reference_cone_observables_with_radial_correction D hγ hγ2
  refine ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, ?_⟩
  filter_upwards [hobs] with ω ho
  let V : C(ℝ≥0, ℝ) :=
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  let w : C(ℝ, ℝ) := MatedCRTHarmonic.GMCFacts.twoSided (W ω) V
  let Y : LQGMetric.DistC := MatedCRTHarmonic.GMCFacts.replField X
    (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω
  let g : ℂ → ℝ := fun z => MatedCRTHarmonic.MatedCRT.coneRadial γ γ
    (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖) -
    MatedCRTHarmonic.GMCFacts.radialW w z
  have hdec : MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω)
      (fun t => B t ω) (fun t => B' t ω) =
      Y + MatedCRTHarmonic.MoTPort.ofFunC g := by
    exact LatticeProb.LQG.coneFieldOf_eq_replField_add_radial_difference
      γ (X ω) (fun t => B t ω) (fun t => B' t ω) w ho.2.2.1 ho.2.2.2.1
  have hlocal : LocallyIntegrable g volume := ho.2.2.1.sub ho.2.2.2.1
  have hpoint : g =ᵐ[volume] fun z => γ * (-Real.log ‖z‖) +
      MatedCRT.FirstPass.Derived.coneRefField (c Y) (F ω) z :=
    Filter.Eventually.of_forall ho.2.2.2.2
  have hcircle : ContinuousOn (fun r => c Y r 0) (Ioi 0) :=
    (hcont Y).comp (continuous_id.prodMk continuous_const).continuousOn
      fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hall := MatedCRT.FirstPass.Derived.coneRefPairing_eq_of_field_decomposition
    γ (hC Y) (c Y) (F ω) Y
    (MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω) (fun t => B t ω)
      (fun t => B' t ω)) g hcircle (fun φ => hhC Y φ) hlocal hdec hpoint
  exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, ho.2.2.2.2, hall⟩

end MatedCRT.Sec1
