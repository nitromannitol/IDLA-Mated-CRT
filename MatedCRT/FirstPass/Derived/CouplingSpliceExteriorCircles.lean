import MatedCRT.FirstPass.Derived.CouplingSpliceNormalization

/-! # Exterior circle averages in a radial splice -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- The exterior radial path of the normalized splice is a measurable function
of the original field and agrees with its centered circle averages on one
almost-sure event for any fixed countable set of times. -/
theorem exists_normalizedRadialSplice_exterior_readout_of_coupling
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
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω) 1 0 = 0) := by
  obtain ⟨R, hRm, hR⟩ := exists_exteriorRadialPath_of_coupling D
  obtain ⟨W, F, hWm, hFm, hW, hF, hlaw, hind, hnorm⟩ :=
    exists_normalizedRadialSplice_indep_conditionedPath_of_coupling D hγ hγ2 R hRm
  refine ⟨R, W, F, hRm, hWm, hFm, ?_, hW, hF, hlaw, hind, hnorm⟩
  exact (ae_ball_iff hS).2 fun t _ => hR t

end MatedCRT.Sec1
