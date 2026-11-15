import MatedCRT.FirstPass.Derived.ConeReferenceLQGSameSpace
import MatedCRT.FirstPass.S2g.SourcePathwise
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-! # Singular-field measure on a common sample space -/

open MeasureTheory Set HarmonicBalls MarkovProcess

namespace MatedCRT.FirstPass.Derived

/-- A logarithmically singular whole-plane field has a measure on the field
sample space, and its pullback yields the reference cone limit for any path on
the original sample space. The circle averages are the given version. -/
theorem exists_singular_measure_and_coneRef_of_map
    {Ω Ω₁ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₁]
    {P : Measure Ω} {U : Ω → Ω₁} (hU : Measurable U)
    {hC : Ω₁ → (ℂ → ℝ) → ℝ} {c : Ω₁ → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF (P.map U) hC c)
    (hc : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∃ μ : Ω₁ → Measure ℂ,
      IsLQGMeasureOfField (P.map U) γ γ c μ ∧
      IsLQGMeasureOfField P γ γ (fun ω => c (U ω)) (fun ω => μ (U ω)) ∧
      IsLQGMeasure P γ (fun ω => coneRefCircle γ (c (U ω)) (w ω))
        (fun ω => coneRefMeasure γ (c (U ω)) (w ω) (μ (U ω))) := by
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived (P.map U) γ γ hC c
    hG hγ hγ2 (MatedCRT.lt_lqgQ_of_mem_Ioo hγ hγ2)
  have hp : IsLQGMeasureOfField P γ γ (fun ω => c (U ω)) (fun ω => μ (U ω)) :=
    ae_of_ae_map hU.aemeasurable hμ
  exact ⟨μ, hμ, hp, isLQGMeasure_coneRef_of_same_space
    (Filter.Eventually.of_forall fun ω => hc (U ω)) hp⟩

end MatedCRT.FirstPass.Derived
