import MatedCRT.FirstPass.Derived.AnnealedLawConvergence
import MatedCRT.FirstPass.Derived.AnnealedExitTimeScaling

/-!
# Exit-time normalization of a mixture of path laws

The exit distribution of an origin mixture is the annealed exit distribution
of its constituent path laws. Its median identifies a deterministic time scale.
-/

open MeasureTheory MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The origin mixture has the annealed exit distribution of its path-law field. -/
theorem exitCdf_originPathLaw_eq_lintegral {Ω Data : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {P : Measure Ω} {D : Ω → Data} (hD : Measurable D)
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : Measurable Λ)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hν : ν = P.map fun ω => (D ω, Λ (D ω)))
    (U : Set ℂ) (hU : IsOpen U) (x : ℝ) :
    exitCdf U (originPathLaw ν) x =
      ∫⁻ ω, exitCdf U (Λ (D ω) 0 : Measure (ContinuousPath ℂ)) x ∂P := by
  let E : Set (ContinuousPath ℂ) :=
    {f | ContinuousPath.exitTime U f ≤ ENNReal.ofReal x}
  have hE : MeasurableSet E :=
    measurableSet_le (ContinuousPath.measurable_exitTime U hU) measurable_const
  have hκ : Measurable fun p : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
      ((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) E :=
    (Measure.measurable_coe hE).comp measurable_originPathLawKernel
  have hmap : Measurable fun ω => (D ω, Λ (D ω)) := hD.prodMk (hΛ.comp hD)
  change originPathLaw ν E = ∫⁻ ω, (Λ (D ω) 0 : Measure (ContinuousPath ℂ)) E ∂P
  rw [hν, originPathLaw, Measure.bind_apply hE measurable_originPathLawKernel.aemeasurable]
  exact lintegral_map hκ hmap

/-- A unit median of the origin mixture determines the scale of the reference law. -/
theorem coe_eq_annealed_median_of_originPathLaw
    {Ω Data : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {P : Measure Ω} {D : Ω → Data} (hD : Measurable D)
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛ : Measurable Λ)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hν : ν = P.map fun ω => (D ω, Λ (D ω)))
    (U : Set ℂ) (hU : IsOpen U) {c : ℝ≥0} (hc : c ≠ 0)
    {K : Ω → Measure (ContinuousPath ℂ)}
    (hlaw : ∀ᵐ ω ∂P, (Λ (D ω) 0 : Measure (ContinuousPath ℂ)) =
      (K ω).map (LatticeProb.timeScalePath c))
    (hunit : medianOf (exitCdf U (originPathLaw ν)) = 1) :
    (c : ℝ) = medianOf (fun x => ∫⁻ ω, exitCdf U (K ω) x ∂P) := by
  apply coe_eq_medianOf_lintegral_exitCdf_of_ae_timeScalePath U hU P hc hlaw
  rw [← funext (exitCdf_originPathLaw_eq_lintegral hD hΛ hν U hU)]
  exact hunit

end MatedCRT.FirstPass.Derived
