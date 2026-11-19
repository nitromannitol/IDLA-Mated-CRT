import MatedCRT.FirstPass.Derived.MarkovTimeChangeRevuzDerived
import MatedCRT.FirstPass.Derived.RevuzUniqueness

/-!
# Markovian time changes with all three Revuz inputs proved

Derived forms of the path-law and measurable time-scale identifications of Markovian time-changed planar
Brownian motions in which `RevuzInvariantInput` (`revuzInvariantInput_derived`), `TimeChangeInvariantUniqueInput`
(`timeChangeInvariantUniqueInput_derived`) and `RevuzUniquenessInput` (uniqueness of a positive continuous additive
functional with a given `σ`-finite Revuz measure, `revuzUniquenessInput_derived`) are all proved, so that no Revuz
correspondence input remains a hypothesis.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- `exists_pathLaw_time_scale_of_isMarkovTCBM` with `RevuzInvariantInput`, `TimeChangeInvariantUniqueInput` and
`RevuzUniquenessInput` supplied. -/
theorem exists_pathLaw_time_scale_of_isMarkovTCBM_revuzUnique_derived {P₁ P₂ : PathLawFamily}
    (hP₁ : IsMarkovTCBM P₁) (hP₂ : IsMarkovTCBM P₂)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, P₁ z = LatticeProb.timeScalePathKernel c P₂ z :=
  exists_pathLaw_time_scale_of_isMarkovTCBM_revuz_derived revuzUniquenessInput_derived hP₁ hP₂ hμ h₁ h₂

/-- `exists_measurable_timeScale_of_isMarkovTCBM` with `RevuzInvariantInput`, `TimeChangeInvariantUniqueInput`
and `RevuzUniquenessInput` supplied. -/
theorem exists_measurable_timeScale_of_isMarkovTCBM_revuzUnique_derived
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K L : Ω → PathLawFamily) (U : Set ℂ) (hU : IsOpen U) (z₀ : ℂ)
    (hK : Measurable (fun ω => (K ω z₀ : Measure (ContinuousPath ℂ))))
    (hL : Measurable (fun ω => (L ω z₀ : Measure (ContinuousPath ℂ))))
    (hmed : ∀ᵐ ω ∂P, medianOf (exitCdf U (K ω z₀ : Measure (ContinuousPath ℂ))) ≠ 0)
    (hcommon : ∀ᵐ ω ∂P, IsMarkovTCBM (K ω) ∧ IsMarkovTCBM (L ω) ∧
      ∃ μ : Measure ℂ, IsLocallyFiniteMeasure μ ∧ μ ≠ 0 ∧
        IsInvariantFor (K ω) μ ∧ IsInvariantFor (L ω) μ) :
    ∃ c : Ω → ℝ≥0, Measurable c ∧
      ∀ᵐ ω ∂P, c ω ≠ 0 ∧ ∀ z, L ω z = LatticeProb.timeScalePathKernel (c ω) (K ω) z :=
  exists_measurable_timeScale_of_isMarkovTCBM_revuz_derived (P := P) revuzUniquenessInput_derived
    K L U hU z₀ hK hL hmed hcommon

end MatedCRT
