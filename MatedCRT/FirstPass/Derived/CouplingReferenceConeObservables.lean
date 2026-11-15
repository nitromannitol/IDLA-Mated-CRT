import MatedCRT.FirstPass.Derived.ReferenceConeSupportedPairing
import MatedCRT.FirstPass.Derived.CouplingReferenceRadialLaw
import LatticeProb.LQG.SpliceContinuousRadialReadout
import MatedCRT.FirstPass.Derived.NormalizedFieldReferenceCone

/-! # Coupled reference cone observables -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric
open scoped NNReal

namespace MatedCRT.Sec1

/-- The same reference cone witnesses identify the radial branches and all
unit-disk-supported pairings on a single almost-sure event. -/
theorem exists_reference_cone_observables_of_coupling
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
        ∀ φ : LQGMetric.TestC, (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
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
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone⟩ :=
    exists_reference_cone_witnesses_of_coupling D hγ hγ2
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  let Y : Ω → LQGMetric.DistC := MatedCRTHarmonic.GMCFacts.replField X
    (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (V ω))
  have hread := LatticeProb.LQG.ae_continuous_circleVersion_replField_twoSided
    D.gff D.bm_B W V hW (fun ω => c (Y ω)) (fun ω => hcont (Y ω))
    (fun r hr => hc r hr 0)
  have hrad := MatedCRT.FirstPass.Derived.ae_radialProcess_coneRefCircle_eq_referenceConeRadialPair
    W V F (fun ω => c (Y ω)) hWB hFm hlaw hW hF hread
  have hp := MatedCRT.FirstPass.Derived.ae_referenceCone_pairing_eq_of_supported
    Y (fun ω => MatedCRTHarmonic.CellScaling.coneFieldOf γ (X ω)
      (fun t => B t ω) (fun t => B' t ω)) (fun ω => hC (Y ω))
    (fun ω => c (Y ω)) F (fun ω φ => hhC (Y ω) φ) hpair
  refine ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, ?_⟩
  filter_upwards [hrad, hp] with ω hr hp
  exact ⟨hr, hp⟩

end MatedCRT.Sec1
