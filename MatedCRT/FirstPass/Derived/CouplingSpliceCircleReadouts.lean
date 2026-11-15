import MatedCRT.FirstPass.Derived.CouplingSpliceExteriorCircles
import LatticeProb.LQG.SpliceInnerCircle

/-! # Circle averages in a coupled radial splice -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- The same coupled radial splice has its inner and exterior circle readouts
on almost-sure events for every time in a fixed countable set. -/
theorem exists_normalizedRadialSplice_circle_readouts_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : 0 < γ) (hγ2 : γ < 2) (S : Set ℝ≥0) (hS : S.Countable) :
    ∃ (R : LQGMetric.DistC → C(ℝ≥0, ℝ)) (W F : Ω → C(ℝ≥0, ℝ)),
      Measurable R ∧ Measurable W ∧ Measurable F ∧
      (∀ᵐ ω ∂P, ∀ t ∈ S, R (X ω) t =
        LQGMetric.circleAvg (X ω) (Real.exp t) 0 - LQGMetric.circleAvg (X ω) 1 0) ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, F ω t = referenceConeConditionedPath γ (fun s => B' s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F) ∧
      IndepFun (fun ω => (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω, W ω)) F P ∧
      (∀ᵐ ω ∂P, LQGMetric.circleAvg (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω) 1 0 = 0) ∧
      (∀ᵐ ω ∂P, ∀ t ∈ S,
        LQGMetric.circleAvg (MatedCRTHarmonic.GMCFacts.replField X
          (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω)
          (Real.exp (-(t : ℝ))) 0 = W ω t) := by
  obtain ⟨R, W, F, hRm, hWm, hFm, hR, hW, hF, hlaw, hind, hnorm⟩ :=
    exists_normalizedRadialSplice_exterior_readout_of_coupling D hγ hγ2 S hS
  refine ⟨R, W, F, hRm, hWm, hFm, hR, hW, hF, hlaw, hind, hnorm, ?_⟩
  exact (ae_ball_iff hS).2 fun t _ =>
    LatticeProb.LQG.ae_circleAvg_replField_twoSided_inner D.gff D.bm_B W
      (fun ω => R (X ω)) hW t

end MatedCRT.Sec1
