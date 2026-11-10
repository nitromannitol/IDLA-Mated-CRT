import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The distributional Laplacian of a function on the plane

For an open set `U ⊆ ℂ`, `IsTestFunction U φ` says that `φ : ℂ → ℝ` is a smooth function with compact support
contained in `U`. `DistribLaplacianLE f μ U` says that `Δf ≤ μ` on `U` in the sense of distributions, that is,
`f` is locally integrable on `U` and `∫ f Δφ ≤ ∫ φ dμ` for every nonnegative test function `φ` on `U`
(Armitage and Gardiner, *Classical Potential Theory*, Springer 2001, §3.3 (distributional superharmonicity);
Hörmander, *The Analysis of Linear Partial Differential Operators I*, §4.5). For `μ = 0` this says that `f`
is distributionally superharmonic on `U`.
-/

open MeasureTheory Laplacian
open scoped ContDiff

namespace LatticeProb

/-- `φ : ℂ → ℝ` is a *test function on `U`*: it is smooth, has compact support, and its support is contained
in `U`. -/
def IsTestFunction (U : Set ℂ) (φ : ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- `Δf ≤ μ` *on `U`* in the sense of distributions: `f` is locally integrable on `U` and
`∫ f Δφ ≤ ∫ φ dμ` for every nonnegative test function `φ` on `U` that is `μ`-integrable.
For `μ = 0` this says that `f` is distributionally superharmonic on `U`
(Armitage and Gardiner, *Classical Potential Theory*, §3.3). -/
def DistribLaplacianLE (f : ℂ → ℝ) (μ : Measure ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn f U ∧
    ∀ φ : ℂ → ℝ, IsTestFunction U φ → 0 ≤ φ → Integrable φ μ →
      ∫ x, f x * Δ φ x ≤ ∫ x, φ x ∂μ

end LatticeProb
