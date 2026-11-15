import MatedCRT.FirstPass.Derived.CouplingRadialWitnesses

/-! # Radial replacement on a mating-of-trees coupling -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MatedCRT.Sec1

/-- The radial version, Brownian path, and conditioned path may be chosen
jointly so that the radial replacement and Brownian path are independent of
the conditioned path. Circle-average identities hold at each fixed time. -/
theorem exists_radial_replacement_witnesses_of_coupling
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
      IndepFun (fun ω => (MatedCRTHarmonic.GMCFacts.replField X
        (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
          ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω, W ω)) F P := by
  obtain ⟨R, W, F, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw, hind⟩ :=
    exists_radial_brownian_conditioned_witnesses_of_coupling D hγ hγ2
  refine ⟨R, W, F, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw, ?_⟩
  let E : LQGMetric.DistC → C(ℝ≥0, ℝ) := fun h =>
    ⟨fun t => R h (-(t : ℝ)), (R h).continuous.comp (by fun_prop)⟩
  have hEm : Measurable E := ContinuousMap.measurable_iff_eval.2 fun t =>
    (ContinuousMap.measurable_eval (-(t : ℝ))).comp hRm
  have hT : Measurable (fun p : LQGMetric.DistC × C(ℝ≥0, ℝ) =>
      MatedCRTHarmonic.GMCFacts.twoSided p.2 (E p.1)) :=
    MatedCRTHarmonic.GMCFacts.measurable_twoSided.comp
      (measurable_snd.prodMk (hEm.comp measurable_fst))
  have hY : Measurable (fun p : LQGMetric.DistC × C(ℝ≥0, ℝ) =>
      MatedCRTHarmonic.GMCFacts.replField Prod.fst
        (fun p => MatedCRTHarmonic.GMCFacts.twoSided p.2 (E p.1)) p) :=
    MatedCRTHarmonic.GMCFacts.measurable_replField measurable_fst hT
  exact hind.comp (hY.prodMk measurable_snd) measurable_id

end MatedCRT.Sec1
