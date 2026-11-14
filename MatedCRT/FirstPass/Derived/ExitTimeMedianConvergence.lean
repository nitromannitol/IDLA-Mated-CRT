import MatedCRT.FirstPass.Derived.ExitTimeCdfConvergence
import MatedCRT.FirstPass.Derived.MedianConvergence
import MatedCRT.FirstPass.Derived.ExitTimeScaling

/-!
# Convergence of the median exit time under weak convergence of path laws

Let `μₙ → μ` weakly on the path space `ContinuousPath ℂ`, let `U ⊆ ℂ` be open, and write
`MatedCRT.exitCdf U μ s = μ (exitTime U ≤ s)` for the distribution function of the exit time from `U`.
If `μ`-almost every path exits `U` regularly, then `exitCdf U μₙ s → exitCdf U μ s` at every `s` where the exit
time of `μ` has no atom, and these are the points of a set meeting every open subinterval of `(0, ∞)`
(`MatedCRT.ExitTimeCdf.exists_mem_Ioo_measure_pathExitTime_eq_zero`).  The stability of lower medians
(`MatedCRT.tendsto_medianOf_of_tendsto_cdf`) then gives `medianOf (exitCdf U μₙ) → medianOf (exitCdf U μ)`
as soon as `exitCdf U μ` is strictly above `1/2` to the right of its lower median.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.ExitTimeCdf

open MatedCRT.TruncatedLaws (RegularExit)

/-- **Convergence of the median exit time.** Under weak convergence `μₙ → μ` of path laws with `μ`-almost sure
regular exit from the open set `U`, the lower medians of the exit-time distribution functions converge, provided
the limit distribution function is strictly above `1/2` to the right of its lower median. -/
theorem tendsto_medianOf_exitCdf {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure (ContinuousPath ℂ)} {μ : ProbabilityMeasure (ContinuousPath ℂ)}
    (hlim : Tendsto μs L (𝓝 μ)) {U : Set ℂ} (hU : IsOpen U)
    (hreg : ∀ᵐ g : ContinuousPath ℂ ∂(μ : Measure (ContinuousPath ℂ)), RegularExit U ⇑g)
    (hstrict : ∀ s, MatedCRT.medianOf (exitCdf U μ) < s → (1 / 2 : ℝ≥0∞) < exitCdf U μ s) :
    Tendsto (fun i => MatedCRT.medianOf (exitCdf U (μs i))) L
      (𝓝 (MatedCRT.medianOf (exitCdf U μ))) := by
  refine MatedCRT.tendsto_medianOf_of_tendsto_cdf (fun i => exitCdf_mono U (μs i))
    (D := {s : ℝ | (μ : Measure (ContinuousPath ℂ))
      {g : ContinuousPath ℂ | pathExitTime U ⇑g = ENNReal.ofReal s} = 0}) ?_ ?_ hstrict
  · intro a b ha hab
    obtain ⟨s, h1, h2, h3⟩ :=
      exists_mem_Ioo_measure_pathExitTime_eq_zero hU (μ : Measure (ContinuousPath ℂ)) ha hab
    exact ⟨s, h3, h1, h2⟩
  · intro s hs
    exact tendsto_measure_pathExitTime_le hlim hU hreg (s := s.toNNReal) hs

end MatedCRT.ExitTimeCdf
