import MatedCRT.Defs.Setting

/-!
# Literature input: scale invariance of the quantum cone

`QuantumConeScalingInput`: DMS14 Proposition 4.13(i), eq:quantum-cone-scaling (line 458), `h(R_b ·) + Q log R_b - γ⁻¹ log b =d h` for the cone scale radius `R_b` (eq:cone-scale-radius, line 454). Used in the proofs of Lemmas 2.5 and 2.6 of the paper. The field enters through its circle average process (`circleProcess`), which is pathwise, so the random radius `R_b` is evaluated pathwise.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Scale invariance of the `γ`-quantum cone** (DMS14 Proposition 4.13(i); eq:quantum-cone-scaling, line 458): for
each `b > 0`, `h(R_b ·) + Q log R_b - γ⁻¹ log b =d h`, through the circle average processes. -/
def QuantumConeScalingInput : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc → ∀ b : ℝ, 0 < b →
    P.map (fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      P.map (fun ω => circleProcess (hcirc ω))

end MatedCRT
