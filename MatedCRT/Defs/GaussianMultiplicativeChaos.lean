import HarmonicBalls.Defs.LQG

/-!
# Gaussian multiplicative chaos approximations

Vocabulary for Berestycki, *An elementary approach to Gaussian multiplicative
chaos*, arXiv:1506.09113v2, equations (1.3)–(1.5), pp. 2–3. The
normalization here uses the variance of the regularized field, rather than
the circle-average normalization in `HarmonicBalls.lqgApprox`.
-/

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- The Riesz kernel `|x-y|^(-s)` with its singular value `∞` on the diagonal
when `s > 0`. -/
noncomputable def rieszEnergyKernel {E : Type*} [PseudoMetricSpace E]
    (s : ℝ) (x y : E) : ℝ≥0∞ :=
  if dist x y = 0 ∧ 0 < s then ⊤ else ENNReal.ofReal (dist x y ^ (-s))

/-- The reference measure has dimension at least `d` in the energy sense of
Berestycki (1.3): its `(d - δ)`-energy is finite for every `δ > 0`. -/
def HasFiniteDimensionalEnergy {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (σ : Measure E) (d : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∫⁻ x, ∫⁻ y, rieszEnergyKernel (d - δ) x y ∂σ ∂σ) < ⊤

/-- Variance-normalized Gaussian multiplicative chaos approximation with
reference measure `σ`. The argument `hε` is the regularized field at one
fixed scale; no convergence or Gaussian hypothesis is built into this
definition. This is equation (1.5) of Berestycki, integrated over sets. -/
noncomputable def gmcApprox {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (σ : Measure E) (γ : ℝ) (hε : Ω → E → ℝ) (ω : Ω) : Measure E :=
  σ.withDensity fun x => ENNReal.ofReal (Real.exp
    (γ * hε ω x - (γ ^ 2 / 2) * ∫ ω', (hε ω' x) ^ 2 ∂P))

/-- At zero coupling the chaos approximation is its reference measure. -/
theorem gmcApprox_zero {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (σ : Measure E) (hε : Ω → E → ℝ) (ω : Ω) :
    gmcApprox P σ 0 hε ω = σ := by
  simp [gmcApprox]

end MatedCRT
