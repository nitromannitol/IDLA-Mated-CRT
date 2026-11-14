import MatedCRT.FirstPass.Derived.MarkovTimeChangeConstMul

/-!
# One-time laws of Markovian time-changed Brownian motions

The proportional-clock construction gives one common deterministic time scale for
all starting points and all one-time marginal distributions.
-/

open MeasureTheory MarkovProcess
open scoped NNReal

namespace MatedCRT

/-- Two Markovian time-changed planar Brownian motions with a common nonzero locally finite
invariant measure have the same one-time laws after a deterministic time scaling. -/
theorem exists_marginal_time_scale_of_isMarkovTCBM
    (hRU : RevuzUniquenessInput) (hRI : RevuzInvariantInput)
    (hTU : TimeChangeInvariantUniqueInput) {P₁ P₂ : PathLawFamily}
    (hP₁ : IsMarkovTCBM P₁) (hP₂ : IsMarkovTCBM P₂)
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (h₁ : IsInvariantFor P₁ μ) (h₂ : IsInvariantFor P₂ μ) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (z : ℂ) (t : ℝ≥0) (S : Set ℂ), MeasurableSet S →
      (P₁ z : Measure (ContinuousPath ℂ)) {x | x t ∈ S} =
        (P₂ z : Measure (ContinuousPath ℂ)) {x | x (t / c) ∈ S} := by
  obtain ⟨m₁, m₂, F₁, F₂, h⟩ :=
    ae_eval_clockInverse_eq_of_isMarkovTCBM hRU hRI hTU hP₁ hP₂ hμ h₁ h₂
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm₁, hm₂, c, hc, he⟩
  refine ⟨c, hc, fun z t S hS => ?_⟩
  rw [hm₁ z t S hS, hm₂ z (t / c) S hS]
  apply measure_congr
  filter_upwards [he z] with ω hω
  exact congrArg (fun x => x ∈ S) (hω t)

end MatedCRT
