import MatedCRT.FirstPass.Derived.MarkovTimeChangeMarginal
import LatticeProb.Prob.MarkovScaledPathLaw

/-!
# Path laws of Markovian time-changed Brownian motions

A common nonzero locally finite invariant measure determines the path law of a
Markovian time-changed planar Brownian motion up to deterministic time scaling.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- A common invariant measure determines the path laws up to a nonzero time scale. -/
theorem exists_pathLaw_time_scale_of_isMarkovTCBM
    (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {P₁ P₂ : PathLawFamily}
    (hP₁ : IsMarkovTCBM P₁) (hP₂ : IsMarkovTCBM P₂)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, P₁ z = LatticeProb.timeScalePathKernel c P₂ z := by
  obtain ⟨c, hc, hm⟩ := exists_marginal_time_scale_of_isMarkovTCBM hRU hRI hTU
    hP₁ hP₂ hμ h₁ h₂
  refine ⟨c⁻¹, inv_ne_zero hc, fun z => ?_⟩
  apply LatticeProb.markov_pathLaw_eq_timeScale_of_marginals c⁻¹ P₁.continuous P₂.continuous
    hP₁.2 hP₂.2 ?_ z
  intro y t
  ext S hS
  rw [Measure.map_apply (continuous_eval_const t).measurable hS,
    Measure.map_apply (continuous_eval_const (c⁻¹ * t)).measurable hS]
  simpa only [Set.preimage, div_eq_mul_inv, mul_comm] using hm y t S hS

end MatedCRT
