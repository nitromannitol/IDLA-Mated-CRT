import MatedCRT.Defs.Notation
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Weak convergence in probability of finite random measures -/

namespace MatedCRT

open MeasureTheory Filter Topology

/-- A family of random finite measures converges weakly in probability when
its Lévy–Prokhorov distance from the limiting random measure tends to zero in
probability. The intended state spaces are separable Euclidean domains, where
the Lévy–Prokhorov topology is the weak topology. The finiteness clauses
prevent the extended distance from being used on infinite measures. -/
def TendstoWeaklyInProbability {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] (P : Measure Ω) (μ : ℝ → Ω → Measure E)
    (ν : Ω → Measure E) : Prop :=
  (∀ᵐ ω ∂P, IsFiniteMeasure (ν ω)) ∧
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, IsFiniteMeasure (μ ε ω)) ∧
  ∀ δ : ℝ, 0 < δ → Tendsto
    (fun ε => P {ω | δ < levyProkhorovDist (μ ε ω) (ν ω)}) (𝓝[>] 0) (𝓝 0)

end MatedCRT
