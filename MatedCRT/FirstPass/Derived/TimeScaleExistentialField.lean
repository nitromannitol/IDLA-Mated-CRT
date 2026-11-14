import MatedCRT.FirstPass.Derived.TimeScaleDeterministicField

/-!
# Deterministic time scaling from fieldwise existence

A common time scale for two independent observations can be chosen
independently of the outcome when it exists simultaneously for both fields.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- Joint existence of a common time scale for two independent law fields
implies the existence of a deterministic common nonzero scale. -/
theorem exists_deterministic_timeScalePath_of_ae_exists_field
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (U : Set α) (hU : IsOpen U) (z₀ : ℂ)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {K : E → ℂ → Measure (ContinuousPath α)}
    (hK : Measurable (fun e => K e z₀))
    {h h' : Ω → E} {P₀ P₀' : Ω → ℂ → Measure (ContinuousPath α)}
    (hh : Measurable h) (hh' : Measurable h')
    (hP₀ : Measurable (fun ω => P₀ ω z₀))
    (hP₀' : Measurable (fun ω => P₀' ω z₀))
    (hind : ProbabilityTheory.IndepFun (fun ω => (h ω, P₀ ω z₀))
      (fun ω => (h' ω, P₀' ω z₀)) P)
    (hexists : ∀ᵐ ω ∂P, ∃ c : ℝ≥0, c ≠ 0 ∧
      (∀ z, P₀ ω z = (K (h ω) z).map (LatticeProb.timeScalePath c)) ∧
      (∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath c)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω) z₀))
    (hprob' : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h' ω) z₀))
    (hpos : ∀ᵐ ω ∂P, K (h ω) z₀ {f | ContinuousPath.exitTime U f = 0} = 0)
    (hpos' : ∀ᵐ ω ∂P, K (h' ω) z₀ {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) z₀ {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hfin' : ∀ᵐ ω ∂P, K (h' ω) z₀ {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    ∃ a : ℝ≥0, a ≠ 0 ∧
      (∀ᵐ ω ∂P, ∀ z, P₀ ω z = (K (h ω) z).map (LatticeProb.timeScalePath a)) ∧
      (∀ᵐ ω ∂P, ∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath a)) := by
  classical
  let Q : Ω → ℝ≥0 → Prop := fun ω c => c ≠ 0 ∧
    (∀ z, P₀ ω z = (K (h ω) z).map (LatticeProb.timeScalePath c)) ∧
    (∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath c))
  let c : Ω → ℝ≥0 := fun ω => if h : ∃ a, Q ω a then Classical.choose h else 0
  have hc : ∀ᵐ ω ∂P, Q ω (c ω) := by
    filter_upwards [hexists] with ω hω
    have hw : ∃ a, Q ω a := hω
    simpa only [c, dite_eq_left hw] using Classical.choose_spec hw
  have hc0 : ∀ᵐ ω ∂P, c ω ≠ 0 := hc.mono fun _ hω => hω.1
  have hlaw : ∀ᵐ ω ∂P, ∀ z, P₀ ω z =
      (K (h ω) z).map (LatticeProb.timeScalePath (c ω)) := hc.mono fun _ hω => hω.2.1
  have hlaw' : ∀ᵐ ω ∂P, ∀ z, P₀' ω z =
      (K (h' ω) z).map (LatticeProb.timeScalePath (c ω)) := hc.mono fun _ hω => hω.2.2
  obtain ⟨a, ha, _, hfield, hfield'⟩ :=
    exists_deterministic_latticeProb_timeScalePath_field U hU z₀ hK hh hh' hP₀ hP₀'
      hind hc0 hlaw hlaw' hprob hprob' hpos hpos' hfin hfin'
  exact ⟨a, ha, hfield, hfield'⟩

end MatedCRT
