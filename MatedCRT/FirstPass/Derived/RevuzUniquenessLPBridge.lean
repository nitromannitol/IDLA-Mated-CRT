import MatedCRT.FirstPass.Derived.RevuzUniquenessTaylorBounds
import MatedCRT.FirstPass.Derived.RevuzUniquenessLocalizer
import LatticeProb.Analysis.LogOnePlusSqDyadicTaylor
import LatticeProb.MeasureTheory.SigmaFiniteLocalizer

/-!
# Bridge to the Lattice-Probability copies of the Revuz-uniqueness calculus lemmas

The deterministic ingredients of the Taylor argument for the uniqueness of the Revuz correspondence
(Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4; Revuz–Yor (1999), Chapter X, Theorem 2.6) are general
real analysis and measure theory, and also live in Lattice-Probability:
`LatticeProb.Analysis.LogOnePlusSqDyadicTaylor` (the function `φ(y) = log(1 + y²)`, its second-order Taylor bound and
the dyadic Taylor remainders along a difference of nondecreasing continuous functions) and
`LatticeProb.MeasureTheory.SigmaFiniteLocalizer` (localizers of a σ-finite measure).

This file identifies the paper-side definitions with the library ones (definitionally) and derives the paper-side
statements from the library theorems.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

/-- `φ(y) = log(1 + y²)`: the paper-side function is the library one. -/
theorem logOnePlusSq_eq_latticeProb : logOnePlusSq = LatticeProb.logOnePlusSq := rfl

/-- `φ'(y) = 2y / (1 + y²)`: the paper-side derivative is the library one. -/
theorem logOnePlusSqDeriv_eq_latticeProb : logOnePlusSqDeriv = LatticeProb.logOnePlusSqDeriv := rfl

/-- The dyadic Taylor remainders of `φ` agree with the library ones. -/
theorem dyadicTaylorRemainder_eq_latticeProb :
    dyadicTaylorRemainder = LatticeProb.dyadicTaylorRemainder := rfl

/-- The second-order Taylor bound for `φ`, from the library. -/
theorem abs_logOnePlusSq_sub_sub_le_of_latticeProb (a b : ℝ) :
    |logOnePlusSq b - logOnePlusSq a - logOnePlusSqDeriv a * (b - a)| ≤ 2 * |b - a| * min |b - a| 1 :=
  LatticeProb.abs_logOnePlusSq_sub_sub_le a b

/-- Uniformly small dyadic increments of a function continuous on `[0, T]`, from the library. -/
theorem eventually_forall_abs_dyadic_increment_lt_of_latticeProb {F : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hF : ContinuousOn F (Icc 0 T)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k < 2 ^ n,
      |F (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - F ((k : ℝ) * T / 2 ^ n)| < ε :=
  LatticeProb.eventually_forall_abs_dyadic_increment_lt hT hF hε

/-- The dyadic Taylor expansion of `φ(N_T)` for `N_0 = 0`, from the library. -/
theorem logOnePlusSq_eq_sum_add_dyadicTaylorRemainder_of_latticeProb {N : ℝ → ℝ} (h0 : N 0 = 0) (T : ℝ)
    (n : ℕ) :
    logOnePlusSq (N T) = ∑ k ∈ Finset.range (2 ^ n), logOnePlusSqDeriv (N ((k : ℝ) * T / 2 ^ n)) *
        (N (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ((k : ℝ) * T / 2 ^ n)) + dyadicTaylorRemainder N T n :=
  LatticeProb.logOnePlusSq_eq_sum_add_dyadicTaylorRemainder h0 T n

/-- The dyadic Taylor remainders of `φ` along a difference of nondecreasing functions continuous on `[0, T]`
tend to `0`, from the library. -/
theorem tendsto_dyadicTaylorRemainder_of_latticeProb {N α β : ℝ → ℝ} (hN : ∀ r, N r = α r - β r) {T : ℝ}
    (hT : 0 ≤ T) (hα : MonotoneOn α (Icc 0 T)) (hβ : MonotoneOn β (Icc 0 T))
    (hαc : ContinuousOn α (Icc 0 T)) (hβc : ContinuousOn β (Icc 0 T)) :
    Tendsto (dyadicTaylorRemainder N T) atTop (𝓝 0) :=
  LatticeProb.tendsto_dyadicTaylorRemainder hN hT hα hβ hαc hβc

/-- Localizers of a σ-finite measure, from the library. -/
theorem exists_localizer_of_sigmaFinite_of_latticeProb {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] :
    ∃ h : ℕ → α → ℝ≥0∞, (∀ j, Measurable (h j)) ∧ (∀ j x, h j x ≤ 1) ∧
      (∀ j, ∫⁻ x, h j x ∂μ < ∞) ∧ (∀ x, Monotone fun j => h j x) ∧ ∀ x, ∀ᶠ j in atTop, h j x = 1 :=
  LatticeProb.exists_localizer_of_sigmaFinite μ

end MatedCRT
