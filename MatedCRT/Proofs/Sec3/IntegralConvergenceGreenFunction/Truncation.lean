import MatedCRT.Steps.Sec3.IntegralConvergenceGreenFunction
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ConvergingTogether

/-!
# Truncation reduction for Lemma 3.4

Separate the fixed-time convergence and the discrete and continuum tail
bounds from the identification of the limiting occupation integral.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls Filter Topology
open scoped ENNReal

/-- The rescaled discrete occupation sum, truncated at `N` steps. -/
noncomputable def truncatedDiscreteOccupation {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (D : Set ℂ) (y : ℂ) (f : Ω → ℂ → ℝ)
    (N : ℕ) (ε : ℝ) (ω : Ω) : ℝ :=
  (S.mε ε)⁻¹ * ∫ x, ∑ n ∈ Finset.range N,
    if (n : ℕ∞) < vExitTime (interiorCellVertices ε (S.η ω) D) x then
      f ω (vertexPoint ε (S.η ω) (x n)) else 0
    ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)

/-- The rescaled continuum occupation integral, truncated at time `T`. -/
noncomputable def truncatedLBMOccupation {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (D : Set ℂ) (y : ℂ) (f : Ω → ℂ → ℝ)
    (T : ℝ) (ω : Ω) : ℝ :=
  ∫ b, (∫ t in Ioc (0 : ℝ)
      (min T (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
    f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal))
    ∂planarBrownianMotion y

/-- The convergence-together reduction for the Green occupation sum. The
hypotheses are fixed-time convergence, discrete tail control in probability,
and continuum tail control after identifying the limit. -/
theorem integralConvergenceGreenFunction_of_truncation
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (D : Set ℂ) (y : ℂ) (f : Ω → ℂ → ℝ)
    (hfixed : ∀ T : ℝ, 0 < T →
      TendstoInProbability S.P
        (fun ε ω => truncatedDiscreteOccupation S D y f ⌊T * S.mε ε⌋₊ ε ω)
        (truncatedLBMOccupation S D y f T))
    (htails : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e →
      ∃ T : ℝ, 0 < T ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | t < |(S.mε ε)⁻¹ * (∑' x : cellVertices ε (S.η ω) D,
            greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)
              (vertexOf ε (S.η ω) y) x * f ω (vertexPoint ε (S.η ω) x)) -
          truncatedDiscreteOccupation S D y f ⌊T * S.mε ε⌋₊ ε ω|} < e) ∧
        S.P {ω | t < |truncatedLBMOccupation S D y f T ω -
          S.c₀ * ∫ x in D, greenFunction D y x * f ω x ∂S.μ ω|} < e) :
    TendstoInProbability S.P
      (fun ε ω => (S.mε ε)⁻¹ * ∑' x : cellVertices ε (S.η ω) D,
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)
          (vertexOf ε (S.η ω) y) x * f ω (vertexPoint ε (S.η ω) x))
      (fun ω => S.c₀ * ∫ x in D, greenFunction D y x * f ω x ∂S.μ ω) := by
  apply tendstoInProbability_of_approximations
  intro t ht e he
  obtain ⟨T, hT, hdisc, hcont⟩ := htails t ht e he
  exact ⟨_, _, hfixed T hT, hdisc, hcont⟩

end MatedCRT
