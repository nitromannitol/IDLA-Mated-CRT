import MatedCRT.FirstPass.Derived.TimeScalePathBridge

/-!
# Exit medians and independent time scales

The exit-median argument applies equally to the library path-scaling map.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
variable {Ω E : Type*} [MeasurableSpace Ω]

/-- A nonzero library time scale is almost surely the ratio of exit-time medians. -/
theorem ae_coe_eq_exitMedianRatio_of_latticeProb_timeScalePath
    (U : Set α) (hU : IsOpen U) {P : Measure Ω}
    {K : E → Measure (ContinuousPath α)} {h : Ω → E} {P₀ : Ω → Measure (ContinuousPath α)}
    {c : Ω → ℝ≥0} (hc0 : ∀ᵐ ω ∂P, c ω ≠ 0)
    (hlaw : ∀ᵐ ω ∂P, P₀ ω = (K (h ω)).map (LatticeProb.timeScalePath (c ω)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω)))
    (hpos : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) {f | ContinuousPath.exitTime U f = ⊤} = 0) :
    ∀ᵐ ω ∂P, (c ω : ℝ) = exitMedianRatio U K (h ω, P₀ ω) := by
  apply ae_coe_eq_exitMedianRatio U hU hc0 ?_ hprob hpos hfin
  simpa only [timeScalePath_eq_latticeProb] using hlaw

/-- A common library time scale determined by two independent observations is deterministic. -/
theorem exists_ae_eq_const_coe_of_latticeProb_timeScalePath
    [MeasurableSpace E] (U : Set α) (hU : IsOpen U)
    {P : Measure Ω} [IsProbabilityMeasure P] {K : E → Measure (ContinuousPath α)}
    (hK : Measurable K) {h h' : Ω → E} {P₀ P₀' : Ω → Measure (ContinuousPath α)}
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
    ∃ k : ℝ, ∀ᵐ ω ∂P, (c ω : ℝ) = k := by
  apply exists_ae_eq_const_coe_of_time_change U hU hK hh hh' hP₀ hP₀' hind hc0 ?_ ?_
    hprob hprob' hpos hpos' hfin hfin'
  · simpa only [timeScalePath_eq_latticeProb] using hlaw
  · simpa only [timeScalePath_eq_latticeProb] using hlaw'

end MatedCRT
