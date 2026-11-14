import MatedCRT.FirstPass.Derived.MarkovTimeChangePathLaw
import MatedCRT.FirstPass.Derived.TimeScaleMeasurableSelection

/-!
# Measurable time scales for Markovian time changes

A common invariant measure determines a measurable time scale for random
families of Markovian time-changed Brownian path laws.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- A common invariant measure gives a common time scale for each sample. -/
theorem ae_exists_timeScale_of_isMarkovTCBM
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) (K L : Ω → PathLawFamily)
    (hcommon : ∀ᵐ ω ∂P, IsMarkovTCBM (K ω) ∧ IsMarkovTCBM (L ω) ∧
      ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
        IsInvariantFor (K ω) μ ∧ IsInvariantFor (L ω) μ) :
    ∀ᵐ ω ∂P, ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z,
      (L ω z : Measure (ContinuousPath ℂ)) =
        (K ω z : Measure (ContinuousPath ℂ)).map (LatticeProb.timeScalePath c) := by
  filter_upwards [hcommon] with ω ⟨hKM, hLM, μ, hμlocal, hμ, hKinv, hLinv⟩
  let : IsLocallyFiniteMeasure μ := hμlocal
  obtain ⟨c, hc, hfield⟩ :=
    exists_pathLaw_time_scale_of_isMarkovTCBM hRU hRI hTU hLM hKM hμ hLinv hKinv
  refine ⟨c, hc, fun z => ?_⟩
  have he := congrArg (fun p : ProbabilityMeasure (ContinuousPath ℂ) =>
    (p : Measure (ContinuousPath ℂ))) (hfield z)
  simpa only [LatticeProb.timeScalePathKernel, ProbabilityMeasure.toMeasure_map] using he

/-- A nonzero exit median selects a measurable time scale simultaneously for all starts. -/
theorem exists_measurable_timeScale_of_isMarkovTCBM
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput)
    (K L : Ω → PathLawFamily) (U : Set ℂ) (hU : IsOpen U) (z₀ : ℂ)
    (hK : Measurable (fun ω => (K ω z₀ : Measure (ContinuousPath ℂ))))
    (hL : Measurable (fun ω => (L ω z₀ : Measure (ContinuousPath ℂ))))
    (hmed : ∀ᵐ ω ∂P, medianOf (exitCdf U (K ω z₀ : Measure (ContinuousPath ℂ))) ≠ 0)
    (hcommon : ∀ᵐ ω ∂P, IsMarkovTCBM (K ω) ∧ IsMarkovTCBM (L ω) ∧
      ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
        IsInvariantFor (K ω) μ ∧ IsInvariantFor (L ω) μ) :
    ∃ c : Ω → ℝ≥0, Measurable c ∧
      ∀ᵐ ω ∂P, c ω ≠ 0 ∧ ∀ z, L ω z = LatticeProb.timeScalePathKernel (c ω) (K ω) z := by
  have hlaw := ae_exists_timeScale_of_isMarkovTCBM hRU hRI hTU K L hcommon
  obtain ⟨c, hc, hfield⟩ := exists_measurable_timeScalePath_of_field
    (P := P) (K := fun ω z => (K ω z : Measure (ContinuousPath ℂ)))
    (L := fun ω z => (L ω z : Measure (ContinuousPath ℂ))) U hU z₀ hK hL hmed hlaw
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfield] with ω ⟨hcω, hω⟩
  refine ⟨hcω, fun z => ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa only [LatticeProb.timeScalePathKernel, ProbabilityMeasure.toMeasure_map] using hω z

end MatedCRT
