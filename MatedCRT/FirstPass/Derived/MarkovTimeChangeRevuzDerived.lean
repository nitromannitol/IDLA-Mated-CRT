import MatedCRT.FirstPass.Derived.MarkovTimeChangeMeasurableScaleDerived
import MatedCRT.FirstPass.Derived.TimeChangeInvariantUnique

/-!
# Markovian time changes with the Revuz invariance and the uniqueness of invariant measures proved

Derived forms of the path-law and measurable time-scale identifications of Markovian time-changed planar
Brownian motions, in which both `RevuzInvariantInput` (supplied by `revuzInvariantInput_derived`) and
`TimeChangeInvariantUniqueInput` (every `σ`-finite invariant measure of the time change of planar Brownian
motion by a positive continuous additive functional with a good clock is a finite multiple of the Revuz
measure; supplied by `timeChangeInvariantUniqueInput_derived`) are proved. The input
`RevuzUniquenessInput` remains a hypothesis.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- `exists_pathLaw_time_scale_of_isMarkovTCBM` with `RevuzInvariantInput` and
`TimeChangeInvariantUniqueInput` supplied. -/
theorem exists_pathLaw_time_scale_of_isMarkovTCBM_revuz_derived
    (hRU : RevuzUniquenessInput) {P₁ P₂ : PathLawFamily}
    (hP₁ : IsMarkovTCBM P₁) (hP₂ : IsMarkovTCBM P₂)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, P₁ z = LatticeProb.timeScalePathKernel c P₂ z :=
  exists_pathLaw_time_scale_of_isMarkovTCBM_derived hRU timeChangeInvariantUniqueInput_derived
    hP₁ hP₂ hμ h₁ h₂

/-- `exists_measurable_timeScale_of_isMarkovTCBM` with `RevuzInvariantInput` and
`TimeChangeInvariantUniqueInput` supplied. -/
theorem exists_measurable_timeScale_of_isMarkovTCBM_revuz_derived
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hRU : RevuzUniquenessInput)
    (K L : Ω → PathLawFamily) (U : Set ℂ) (hU : IsOpen U) (z₀ : ℂ)
    (hK : Measurable (fun ω => (K ω z₀ : Measure (ContinuousPath ℂ))))
    (hL : Measurable (fun ω => (L ω z₀ : Measure (ContinuousPath ℂ))))
    (hmed : ∀ᵐ ω ∂P, medianOf (exitCdf U (K ω z₀ : Measure (ContinuousPath ℂ))) ≠ 0)
    (hcommon : ∀ᵐ ω ∂P, IsMarkovTCBM (K ω) ∧ IsMarkovTCBM (L ω) ∧
      ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
        IsInvariantFor (K ω) μ ∧ IsInvariantFor (L ω) μ) :
    ∃ c : Ω → ℝ≥0, Measurable c ∧
      ∀ᵐ ω ∂P, c ω ≠ 0 ∧ ∀ z, L ω z = LatticeProb.timeScalePathKernel (c ω) (K ω) z :=
  exists_measurable_timeScale_of_isMarkovTCBM_derived hRU timeChangeInvariantUniqueInput_derived
    K L U hU z₀ hK hL hmed hcommon

end MatedCRT
