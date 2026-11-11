import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLocalIntegrability
import MatedCRT.LPStaging.Analysis.AngularIntegralMeasurable
import MatedCRT.LPStaging.Analysis.AngularLogIntegrability

/-!
# Angular integrability of logarithmic radial singularities on circles through zero

Deterministic component of the angular assertion:
"Angular integrals remain finite for circles through zero, since a logarithmic singularity is
integrable in the angle."  The lateral observable `ℓ(r,z)` integrates
the radial function over the circle `θ ↦ z + r e^{iθ}`; that circle passes through `0` exactly when
`‖z‖ = r`.

* `norm_add_mul_exp_eq`: the standard circle parametrization.  If `‖z‖ = r`, then
  `‖z + r e^{iθ}‖ = r · 2 |sin((θ - arg(-z))/2)|`; the circle vanishes at `θ = arg(-z)`.
* `abs_log_norm_add_mul_exp_le`: the logarithmic singularity comparison
  `|log ‖z + r e^{iθ}‖| ≤ |log (2r)| + |log |sin((θ - arg(-z))/2)||` for every `θ`.
* `intervalIntegrable_abs_log_abs_sin_shift`: `θ ↦ |log |sin((θ - c)/2)||` is interval integrable on
  `[0, 2π]`, from Mathlib's `intervalIntegrable_log_sin` by an affine change of variable.
* `intervalIntegrable_abs_log_norm_add_mul_exp`: `θ ↦ |log ‖z + r e^{iθ}‖|` is interval integrable
  on `[0, 2π]` along every circle through zero.
* `intervalIntegrable_radial_circle`: for `g` continuous on `(0, ∞)` with the majorant
  `|g t| ≤ C (1 + |log t|)` on `(0, δ]`, `2r ≤ δ`, the radial function `θ ↦ g ‖z + r e^{iθ}‖` is
  interval integrable on `[0, 2π]` (the finiteness of the angular integral).
* `locallyIntegrable_radial_and_circle`: the planar statement `locallyIntegrable_radial` of
  `RadialLocalIntegrability` together with the circle statement, under the same hypotheses.

A locally finite spatial integral does not control a single circle: a circle is Lebesgue-null, so
`LocallyIntegrable (fun z ↦ g ‖z‖)` carries no information on `θ ↦ g ‖z + r e^{iθ}‖`.  The circle
statement uses the pointwise majorant along the circle itself.

The five circle lemmas are the declarations of `LatticeProb.AngularIntegralMeasurable`, and the last
one is `LatticeProb.AngularLogIntegrability.locallyIntegrable_radial_and_circle`; the declarations
below have the same statements and cite them.

Not proved here: the measurable-in-`ω` version for random radial families (a later component), and
the identification of the circle integral with the lateral observable `ℓ(r,z)`.
-/

open MeasureTheory Set Filter Topology Complex

namespace MatedCRT.Sec1

/-- Standard circle parametrization through zero.  If `‖z‖ = r`, the circle `θ ↦ z + r e^{iθ}` has
`‖z + r e^{iθ}‖ = r · 2 |sin((θ - arg (-z))/2)|`, and it vanishes at `θ = arg (-z)`. -/
lemma norm_add_mul_exp_eq {z : ℂ} {r : ℝ} (hz : ‖z‖ = r) (θ : ℝ) :
    ‖z + (r : ℂ) * exp (I * θ)‖ = r * (2 * |Real.sin ((θ - arg (-z)) / 2)|) :=
  LatticeProb.AngularIntegralMeasurable.norm_add_mul_exp_eq hz θ

/-- Logarithmic singularity comparison on a circle through zero: for every `θ`,
`|log ‖z + r e^{iθ}‖| ≤ |log (2r)| + |log |sin((θ - arg (-z))/2)||`.  In Lean `log 0 = 0`, so the
zero of the circle is covered by the same inequality. -/
lemma abs_log_norm_add_mul_exp_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (θ : ℝ) :
    |Real.log ‖z + (r : ℂ) * exp (I * θ)‖| ≤
      |Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| :=
  LatticeProb.AngularIntegralMeasurable.abs_log_norm_add_mul_exp_le hr hz θ

/-- For every shift `c`, `θ ↦ |log |sin((θ - c)/2)||` is interval integrable on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_abs_sin_shift (c : ℝ) :
    IntervalIntegrable (fun θ : ℝ => |Real.log (|Real.sin ((θ - c) / 2)|)|) volume 0
      (2 * Real.pi) :=
  LatticeProb.AngularIntegralMeasurable.intervalIntegrable_abs_log_abs_sin_shift c

/-- Angular integrability of the absolute logarithmic singularity: for `r > 0` and `‖z‖ = r`,
`θ ↦ |log ‖z + r e^{iθ}‖|` is interval integrable on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_norm_add_mul_exp {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    IntervalIntegrable (fun θ : ℝ => |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) volume 0
      (2 * Real.pi) :=
  LatticeProb.AngularIntegralMeasurable.intervalIntegrable_abs_log_norm_add_mul_exp hr hz

/-- Finiteness of the angular integral of a radial function with logarithmic majorant.  Let
`g` be continuous on `(0, ∞)` with `|g t| ≤ C (1 + |log t|)` for `0 < t ≤ δ`, and let the circle
`θ ↦ z + r e^{iθ}` pass through zero (`‖z‖ = r > 0`) with `2r ≤ δ`.  Then `θ ↦ g ‖z + r e^{iθ}‖`
is interval integrable on `[0, 2π]`.  The circle is Lebesgue-null, so the majorant is used along
the circle itself; the zeros of `θ ↦ sin((θ - arg(-z))/2)` form a countable set. -/
theorem intervalIntegrable_radial_circle {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (hδ : 2 * r ≤ δ)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ δ → |g t| ≤ C * (1 + |Real.log t|)) :
    IntervalIntegrable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * θ)‖) volume 0 (2 * Real.pi) :=
  LatticeProb.AngularIntegralMeasurable.intervalIntegrable_radial_circle hg hr hz hδ hbound

/-- Planar and angular statements together, for the radial function `z ↦ g ‖z‖` under the
hypotheses of `locallyIntegrable_radial`: the function is locally integrable on `ℂ`, and its
restriction to every circle through zero is interval integrable.  The second conjunct does not
follow from the first (a circle is Lebesgue-null). -/
theorem locallyIntegrable_radial_and_circle {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    (hδ : 0 < δ) (hbound : ∀ t : ℝ, 0 < t → t ≤ δ → |g t| ≤ C * (1 + |Real.log t|)) :
    LocallyIntegrable (fun z : ℂ => g ‖z‖) volume ∧
      ∀ (z : ℂ) (r : ℝ), 0 < r → ‖z‖ = r → 2 * r ≤ δ →
        IntervalIntegrable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * θ)‖) volume 0
          (2 * Real.pi) :=
  LatticeProb.AngularLogIntegrability.locallyIntegrable_radial_and_circle hg hδ hbound

end MatedCRT.Sec1
