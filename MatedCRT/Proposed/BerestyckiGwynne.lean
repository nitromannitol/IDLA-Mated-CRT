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
with polynomially high probability as `δ` tends to zero. Definition 2.2 on
p. 15 has an unspecified drift parameter in its displayed formula; the
standard cone used here has inward drift `+γ`, as in the following paragraph
and the proof of Lemma A.1. -/
def BerestyckiGwynneConeBallMassStmt : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ),
    0 < γ → γ < 2 → IsConeField γ P hC hcirc μ →
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      PolyHighProb P (fun δ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
        ENNReal.ofReal (δ ^ (((2 + γ) ^ (2 : ℕ)) / 2 + ζ)) ≤ μ ω (ball z δ) ∧
        μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (((2 - γ) ^ (2 : ℕ)) / 2 - ζ))})

/-- Berestycki and Gwynne, arXiv:2003.10320v2, Lemma 2.4, (2.8),
p. 17: the two-sided cell-diameter estimate for the canonical circle-average
embedded quantum cone and its independent space-filling SLE, parameterized
by quantum area. `P` and `η` here denote that fixed canonical realization;
this proposition does not assert the estimate for arbitrary model laws or a
representation-uniform exponent. -/
def BerestyckiGwynneCellDiameterStmt {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (η : Ω → ℝ → ℂ) (γ : ℝ) : Prop :=
  0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    PolyHighProb P (fun ε => {ω | ∀ i : ℤ,
      (cell ε (η ω) i ∩ ball 0 ρ).Nonempty →
        ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (η ω) i) ∧
        diam (cell ε (η ω) i) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)})

/-- Berestycki and Gwynne, arXiv:2003.10320v2, Remark 1.3, (1.8),
p. 10, for the annealed median of the canonical whole-plane model. The
argument `m` denotes that fixed canonical median scale, rather than an
arbitrary raw environment law. -/
def BerestyckiGwynneMedianScaleStmt (γ : ℝ) (m : ℝ → ℝ) : Prop :=
  0 < γ → γ < 2 → ∃ C : ℝ, 1 < C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → C⁻¹ * ε⁻¹ ≤ m ε ∧ m ε ≤ C * ε⁻¹

end MatedCRT
