import MatedCRT.FirstPass.Derived.AnnealedTimeScaleField
import MatedCRT.FirstPass.Derived.OriginMixtureTimeScale

/-!
# Normalization of a fieldwise time scale by an origin mixture

The unit exit median of the origin mixture identifies the common deterministic
scale of two independent observations of a path-law field.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The origin-mixture median determines the common scale of two independent
field observations when that scale exists simultaneously at every start. -/
theorem exists_deterministic_timeScalePath_field_of_origin_median
    {Ω E Data : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    (U : Set ℂ) (hU : IsOpen U)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Ω → Data} (hD : Measurable D)
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : Measurable Λ)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hν : ν = P.map fun ω => (D ω, Λ (D ω)))
    {K : E → ℂ → Measure (ContinuousPath ℂ)}
    (hK : Measurable (fun e => K e 0))
    {h h' : Ω → E} {P₀' : Ω → ℂ → Measure (ContinuousPath ℂ)}
    (hh : Measurable h) (hh' : Measurable h')
    (hP₀' : Measurable (fun ω => P₀' ω 0))
    (hind : ProbabilityTheory.IndepFun
      (fun ω => (h ω, (Λ (D ω) 0 : Measure (ContinuousPath ℂ))))
      (fun ω => (h' ω, P₀' ω 0)) P)
    (hexists : ∀ᵐ ω ∂P, ∃ c : ℝ≥0, c ≠ 0 ∧
      (∀ z, (Λ (D ω) z : Measure (ContinuousPath ℂ)) =
        (K (h ω) z).map (LatticeProb.timeScalePath c)) ∧
      (∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath c)))
    (hprob : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h ω) 0))
    (hprob' : ∀ᵐ ω ∂P, IsProbabilityMeasure (K (h' ω) 0))
    (hpos : ∀ᵐ ω ∂P, K (h ω) 0 {f | ContinuousPath.exitTime U f = 0} = 0)
    (hpos' : ∀ᵐ ω ∂P, K (h' ω) 0 {f | ContinuousPath.exitTime U f = 0} = 0)
    (hfin : ∀ᵐ ω ∂P, K (h ω) 0 {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hfin' : ∀ᵐ ω ∂P, K (h' ω) 0 {f | ContinuousPath.exitTime U f = ⊤} = 0)
    (hunit : medianOf (exitCdf U (originPathLaw ν)) = 1) :
    ∃ a : ℝ≥0, a ≠ 0 ∧
      (a : ℝ) = medianOf (fun x => ∫⁻ ω, exitCdf U (K (h ω) 0) x ∂P) ∧
      (∀ᵐ ω ∂P, ∀ z, (Λ (D ω) z : Measure (ContinuousPath ℂ)) =
        (K (h ω) z).map (LatticeProb.timeScalePath a)) ∧
      (∀ᵐ ω ∂P, ∀ z, P₀' ω z = (K (h' ω) z).map (LatticeProb.timeScalePath a)) := by
  have hprobLaw : Measurable (fun ω => (Λ (D ω) 0 : ProbabilityMeasure (ContinuousPath ℂ))) :=
    (continuous_eval_const (0 : ℂ)).measurable.comp (hΛ.comp hD)
  have hP₀ : Measurable (fun ω => (Λ (D ω) 0 : Measure (ContinuousPath ℂ))) :=
    measurable_subtype_coe.comp hprobLaw
  have hunit' : medianOf (fun x =>
      ∫⁻ ω, exitCdf U (Λ (D ω) 0 : Measure (ContinuousPath ℂ)) x ∂P) = 1 := by
    rw [← funext (exitCdf_originPathLaw_eq_lintegral hD hΛ hν U hU)]
    exact hunit
  exact exists_deterministic_timeScalePath_field_of_annealed_median U hU 0 hK hh hh'
    hP₀ hP₀' hind hexists hprob hprob' hpos hpos' hfin hfin' hunit'

end MatedCRT.FirstPass.Derived
