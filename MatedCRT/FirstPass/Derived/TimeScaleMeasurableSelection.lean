import MatedCRT.FirstPass.Derived.TimeScalePathBridge

/-!
# Measurable selection of path-law time scales

A nonzero exit median selects a time scale from a fieldwise scaling identity.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- A fieldwise scaling identity admits a measurable time scale when the two
path-law fields are measurable at one point with nonzero reference exit median. -/
theorem exists_measurable_timeScalePath_of_field
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {Ω Z : Type*} [MeasurableSpace Ω] (U : Set α) (hU : IsOpen U) (z₀ : Z)
    {P : Measure Ω} {K L : Ω → Z → Measure (ContinuousPath α)}
    (hK : Measurable (fun ω => K ω z₀)) (hL : Measurable (fun ω => L ω z₀))
    (hmed : ∀ᵐ ω ∂P, medianOf (exitCdf U (K ω z₀)) ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, L ω z = (K ω z).map (LatticeProb.timeScalePath c)) :
    ∃ c : Ω → ℝ≥0, Measurable c ∧
      ∀ᵐ ω ∂P, c ω ≠ 0 ∧
        ∀ z, L ω z = (K ω z).map (LatticeProb.timeScalePath (c ω)) := by
  let c : Ω → ℝ≥0 := fun ω =>
    (medianOf (exitCdf U (K ω z₀)) / medianOf (exitCdf U (L ω z₀))).toNNReal
  refine ⟨c, measurable_real_toNNReal.comp
    ((measurable_medianOf_exitCdf U hU hK).div (measurable_medianOf_exitCdf U hU hL)), ?_⟩
  filter_upwards [hmed, hlaw] with ω hmed ⟨a, ha, hfield⟩
  have hratio := coe_eq_medianOf_div_of_map_latticeProb_timeScalePath U hU ha
    (K ω z₀) (L ω z₀) (hfield z₀) hmed
  have hc : c ω = a := by
    dsimp [c]
    rw [← hratio]
    exact Real.toNNReal_coe
  simpa only [hc] using ⟨ha, hfield⟩

end MatedCRT
