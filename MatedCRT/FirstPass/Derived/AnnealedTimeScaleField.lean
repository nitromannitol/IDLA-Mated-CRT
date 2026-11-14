import MatedCRT.FirstPass.Derived.TimeScaleExistentialField
import MatedCRT.FirstPass.Derived.AnnealedExitTimeScaling

/-!
# Annealed normalization of fieldwise time scaling

Independent observations determine a common time scale, which is identified by
an annealed exit-time median.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- A jointly existing scale for two independent law fields is deterministic
and, under unit annealed exit median, equals the reference annealed median. -/
theorem exists_deterministic_timeScalePath_field_of_annealed_median
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
    (hfin' : ∀ᵐ ω ∂P, K (h' ω) z₀ {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hunit : medianOf (fun x => ∫⁻ ω, exitCdf U (P₀ ω z₀) x ∂P) = 1) :
    ∃ a : ℝ≥0, a ≠ 0 ∧
      (a : ℝ) = medianOf (fun x => ∫⁻ ω, exitCdf U (K (h ω) z₀) x ∂P) ∧
      (∀ᵐ ω ∂P, ∀ z, P₀ ω z = (K (h ω) z).map (LatticeProb.timeScalePath a)) ∧
      (∀ᵐ ω ∂P, ∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath a)) := by
  obtain ⟨a, ha, hfield, hfield'⟩ :=
    exists_deterministic_timeScalePath_of_ae_exists_field U hU z₀ hK hh hh' hP₀ hP₀'
      hind hexists hprob hprob' hpos hpos' hfin hfin'
  have hlaw : ∀ᵐ ω ∂P, P₀ ω z₀ =
      (K (h ω) z₀).map (LatticeProb.timeScalePath a) := by
    filter_upwards [hfield] with ω hω
    exact hω z₀
  exact ⟨a, ha, coe_eq_medianOf_lintegral_exitCdf_of_ae_timeScalePath U hU P ha hlaw hunit,
    hfield, hfield'⟩

end MatedCRT
