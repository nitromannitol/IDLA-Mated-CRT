import MatedCRT.FirstPass.Derived.TimeScaleDeterministicLaw

/-!
# Deterministic time scaling of path-law fields

A common scale identified from independent exit-median observations at one
starting point gives a simultaneous scaling identity for both law fields.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- Independent observations at one starting point determine the time scale
for both fields, simultaneously at all starting points. -/
theorem exists_deterministic_latticeProb_timeScalePath_field
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (U : Set α) (hU : IsOpen U) (z₀ : ℂ)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {K : E → ℂ → Measure (ContinuousPath α)}
    (hK : Measurable (fun e => K e z₀))
    {h h' : Ω → E} {P₀ P₀' : Ω → ℂ → Measure (ContinuousPath α)}
    {c : Ω → ℝ≥0} (hh : Measurable h) (hh' : Measurable h')
    (hP₀ : Measurable (fun ω => P₀ ω z₀))
    (hP₀' : Measurable (fun ω => P₀' ω z₀))
    (hind : ProbabilityTheory.IndepFun (fun ω => (h ω, P₀ ω z₀))
      (fun ω => (h' ω, P₀' ω z₀)) P)
    (hc0 : ∀ᵐ ω ∂P, c ω ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, ∀ z, P₀ ω z = (K (h ω) z).map (LatticeProb.timeScalePath (c ω)))
    (hlaw' : ∀ᵐ ω ∂P, ∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath (c ω)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω) z₀))
    (hprob' : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h' ω) z₀))
    (hpos : ∀ᵐ ω ∂P, K (h ω) z₀ {f | ContinuousPath.exitTime U f = 0} = 0)
    (hpos' : ∀ᵐ ω ∂P, K (h' ω) z₀ {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) z₀ {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hfin' : ∀ᵐ ω ∂P, K (h' ω) z₀ {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    ∃ a : ℝ≥0, a ≠ 0 ∧ (∀ᵐ ω ∂P, c ω = a) ∧
      (∀ᵐ ω ∂P, ∀ z, P₀ ω z = (K (h ω) z).map (LatticeProb.timeScalePath a)) ∧
      (∀ᵐ ω ∂P, ∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath a)) := by
  have h₀ := hlaw.mono fun _ hω => hω z₀
  have h₀' := hlaw'.mono fun _ hω => hω z₀
  obtain ⟨a, ha, heq, _, _⟩ := exists_deterministic_latticeProb_timeScalePath
    U hU hK hh hh' hP₀ hP₀' hind hc0 h₀ h₀' hprob hprob' hpos hpos' hfin hfin'
  refine ⟨a, ha, heq, ?_, ?_⟩
  · filter_upwards [hlaw, heq] with ω hω hscale
    intro z
    simpa only [hscale] using hω z
  · filter_upwards [hlaw', heq] with ω hω hscale
    intro z
    simpa only [hscale] using hω z

end MatedCRT
