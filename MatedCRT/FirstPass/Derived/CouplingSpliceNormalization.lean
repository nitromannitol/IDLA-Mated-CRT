import MatedCRT.FirstPass.Derived.CouplingRadialSplice
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea

/-! # Unit-circle normalization of a radial splice -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- The radial splice and its inner path are independent of the conditioned
outer path, and the splice has zero unit-circle average almost surely. -/
theorem exists_normalizedRadialSplice_indep_conditionedPath_of_coupling
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
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω, W ω)) F P ∧
      (∀ᵐ ω ∂P, LQGMetric.circleAvg (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω) (R (X ω))) ω) 1 0 = 0) := by
  obtain ⟨W, F, hWm, hFm, hW, hF, hlaw, hind⟩ :=
    exists_radialSplice_indep_conditionedPath_of_coupling D hγ hγ2 R hR
  refine ⟨W, F, hWm, hFm, hW, hF, hlaw, hind, ?_⟩
  apply MatedCRTHarmonic.GMCFacts.ae_circleAvg_replField_one D.gff
  intro ω
  simp only [MatedCRTHarmonic.GMCFacts.twoSided_apply, neg_zero, Real.toNNReal_zero,
    sub_self, add_zero]

end MatedCRT.Sec1
