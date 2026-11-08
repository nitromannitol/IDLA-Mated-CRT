import MatedCRT.Defs.QuantumCone

/-!
# The first component of the quantum cone's radial law

The radial law of the γ-quantum cone (Definition 2.1, corrected draft line 431; `quantumConeRadialLaw`) is a product
of the law `B + γ t` of a standard Brownian motion with a law `ν` of the conditioned process. Its first component is
therefore the law of `t ↦ B_t + γ t` (`B` standard Brownian motion from `0`). This is the component that the radii
`e^{-t} ≤ 1` of the good annulus events see (`radialProcess`, Defs/QuantumCone.lean).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped NNReal

/-- The first component of `quantumConeRadialLaw γ ν` is the law of `t ↦ B_t + γ t`, with `B` a standard Brownian
motion from `0` (`brownianMotion 0`). -/
theorem map_fst_quantumConeRadialLaw (γ : ℝ) (ν : Measure (ContinuousPath ℝ)) [IsProbabilityMeasure ν] :
    (quantumConeRadialLaw γ ν).map Prod.fst = (brownianMotion 0).map (fun w (t : ℝ≥0) => w t + γ * t) := by
  unfold quantumConeRadialLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]

end MatedCRT

