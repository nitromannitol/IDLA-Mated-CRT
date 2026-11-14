import MatedCRT.FirstPass.Derived.TimeScaleMedianIndependence

/-!
# Deterministic time scaling of path laws

Independent observations determine a common nonzero time scale, which can be
chosen deterministically in both path-law identities.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- If two independent observations determine a common time scale through exit
medians, both path laws have the same deterministic nonzero time scale. -/
theorem exists_deterministic_latticeProb_timeScalePath
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (U : Set α) (hU : IsOpen U) {P : Measure Ω} [IsProbabilityMeasure P]
    {K : E → Measure (ContinuousPath α)} (hK : Measurable K)
    {h h' : Ω → E} {P₀ P₀' : Ω → Measure (ContinuousPath α)}
    {c : Ω → ℝ≥0} (hh : Measurable h) (hh' : Measurable h')
    (hP₀ : Measurable P₀) (hP₀' : Measurable P₀')
    (hind : ProbabilityTheory.IndepFun (fun ω => (h ω, P₀ ω)) (fun ω => (h' ω, P₀' ω)) P)
    (hc0 : ∀ᵐ ω ∂P, c ω ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, P₀ ω = (K (h ω)).map (LatticeProb.timeScalePath (c ω)))
    (hlaw' : ∀ᵐ ω ∂P, P₀' ω = (K (h' ω)).map (LatticeProb.timeScalePath (c ω)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω)))
    (hprob' : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h' ω)))
    (hpos : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = 0} = 0)
    (hpos' : ∀ᵐ ω ∂P, K (h' ω) {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hfin' : ∀ᵐ ω ∂P, K (h' ω) {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    ∃ a : ℝ≥0, a ≠ 0 ∧ (∀ᵐ ω ∂P, c ω = a) ∧
      (∀ᵐ ω ∂P, P₀ ω = (K (h ω)).map (LatticeProb.timeScalePath a)) ∧
      (∀ᵐ ω ∂P, P₀' ω = (K (h' ω)).map (LatticeProb.timeScalePath a)) := by
  obtain ⟨k, hk⟩ := exists_ae_eq_const_coe_of_latticeProb_timeScalePath U hU hK hh hh'
    hP₀ hP₀' hind hc0 hlaw hlaw' hprob hprob' hpos hpos' hfin hfin'
  obtain ⟨ω₀, hω₀, hk₀⟩ := (hc0.and hk).exists
  have heq : ∀ᵐ ω ∂P, c ω = c ω₀ := by
    filter_upwards [hk] with ω hω
    exact NNReal.coe_injective (hω.trans hk₀.symm)
  refine ⟨c ω₀, hω₀, heq, ?_, ?_⟩
  · filter_upwards [hlaw, heq] with ω hω hscale
    simpa only [hscale] using hω
  · filter_upwards [hlaw', heq] with ω hω hscale
    simpa only [hscale] using hω

end MatedCRT
