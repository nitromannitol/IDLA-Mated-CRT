import MatedCRT.Defs.Setting

/-! # Uniform ball-mass estimates for the quantum cone

Staged literature input for independent source audit; this is a proposition,
not an axiom or a proof of the published theorem.
-/

namespace MatedCRT

open HarmonicBalls MeasureTheory Set Metric
open scoped ENNReal

/-- Berestycki and Gwynne, *Random walks on mated-CRT planar maps and
Liouville Brownian motion*, arXiv:2003.10320v2, Lemma A.1, equation (A.1),
p. 66.
For a circle-average embedded `γ`-quantum cone and its LQG measure, the
two mass estimates hold simultaneously at every center in `B_{1-δ}(0)`,
with polynomially high probability as `δ` tends to zero. -/
def BerestyckiGwynneConeBallMassStmt : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ),
    0 < γ → γ < 2 → IsConeField γ P hC hcirc μ →
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      PolyHighProb P (fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ (((2 + γ) ^ (2 : ℕ)) / 2 + ζ)) ≤ μ ω (ball z δ) ∧
        μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (((2 - γ) ^ (2 : ℕ)) / 2 - ζ))})

end MatedCRT
