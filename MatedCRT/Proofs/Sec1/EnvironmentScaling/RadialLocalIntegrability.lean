import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import MatedCRT.LPStaging.Analysis.RadialLocalIntegrability

/-!
# Local integrability of radial functions with logarithmic growth at zero

The
paper's claim has two parts.  On the inward branch Brownian growth is `o(t)`
as `t → ∞` (with `t = -log |z|`), which bounds the radial function by
`C (1 + |log |z||)` near zero; on a bounded annulus the radial function is
continuous.  This file proves the deterministic implications and keeps the
Brownian inputs as explicit hypotheses:

* `integrableOn_one_add_abs_log_norm_closedBall`: the majorant
  `1 + |log ‖z‖|` is integrable on every closed disc of `ℂ`, by the polar
  coordinate criterion `MeasureTheory.integrable_fun_norm_addHaar`.
* `locallyIntegrable_of_continuousOn_compl_zero`: a function continuous on
  `ℂ \ {0}` and dominated near `0` by a multiple of the majorant is locally
  integrable (domination on compact sets).
* `locallyIntegrable_radial`: the radial form `z ↦ g ‖z‖`.
* `exists_abs_le_mul_one_add_of_sublinear`: a continuous path with
  `h t / t → 0` satisfies a linear envelope `|h t| ≤ C (1 + t)` on `[0, ∞)`.
* `locallyIntegrable_radial_of_sublinear` and
  `ae_locallyIntegrable_radial_brownian`: `z ↦ h (-log ‖z‖)` is locally
  integrable; almost surely for a random radial path whose a.s. continuity and
  a.s. sublinear growth are hypotheses (`hcont`, `hsub`).

Not proved here: the Gaussian tail bound, the reflection bound and the
Borel–Cantelli argument that the paper sketches for Brownian sublinear growth
(`hsub` carries that statement), and the measurability of the radial integrals
(a later component).  Nothing here identifies the conditioned radial path or
the represented circle of the canonical cone.
-/

open MeasureTheory Set Filter Topology Metric

namespace MatedCRT.Sec1

/-- On `(0, R]` the radial majorant satisfies `y (1 + |log y|) ≤ 2 + R + R ^ 2`.
For `y ≤ 1` this uses `|log y * y| < 1` (`Real.abs_log_mul_self_lt`); for
`1 < y ≤ R` it uses `log y ≤ y - 1`. -/
lemma mul_one_add_abs_log_le_of_mem_Ioc {y R : ℝ} (hy : y ∈ Ioc 0 R) :
    y * (1 + |Real.log y|) ≤ 2 + R + R ^ 2 :=
  LatticeProb.RadialLocalIntegrability.mul_one_add_abs_log_le_of_mem_Ioc hy

/-- The radial majorant `y ↦ y (1 + |log y|)` is Lebesgue integrable on `(0, R]`,
since it is bounded there. -/
lemma integrableOn_mul_one_add_abs_log_Ioc (R : ℝ) :
    IntegrableOn (fun y : ℝ => y * (1 + |Real.log y|)) (Ioc 0 R) :=
  LatticeProb.RadialLocalIntegrability.integrableOn_mul_one_add_abs_log_Ioc R

/-- The majorant `1 + |log ‖z‖|` is integrable on every closed disc of `ℂ`.
Polar coordinates (`MeasureTheory.integrable_fun_norm_addHaar`) reduce this to
the one-dimensional integrability of `y ↦ y (1 + |log y|)` on `(0, R]`, where
the radial Jacobian in the plane is `y ^ (2 - 1) = y`. -/
lemma integrableOn_one_add_abs_log_norm_closedBall (R : ℝ) :
    IntegrableOn (fun z : ℂ => 1 + |Real.log ‖z‖|) (closedBall 0 R) :=
  LatticeProb.RadialLocalIntegrability.integrableOn_one_add_abs_log_norm_closedBall R

/-- Domination: a function continuous on `ℂ \ {0}` and bounded near the origin by
`C (1 + |log ‖z‖|)` is locally integrable on `ℂ`.  On a closed disc `|z| ≤ R` the
annulus `δ ≤ |z| ≤ R` is compact and avoids the origin, so `f` is bounded there;
on the punctured disc `0 < |z| ≤ δ` the logarithmic majorant dominates. -/
theorem locallyIntegrable_of_continuousOn_compl_zero {f : ℂ → ℝ}
    (hf : ContinuousOn f {z : ℂ | z ≠ 0}) {C δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ δ → |f z| ≤ C * (1 + |Real.log ‖z‖|)) :
    LocallyIntegrable f volume :=
  LatticeProb.RadialLocalIntegrability.locallyIntegrable_of_continuousOn_compl_zero hf hδ hbound

/-- Radial form: for `g` continuous on `(0, ∞)` and bounded near zero by
`C (1 + |log r|)` on `(0, δ]`, the function `z ↦ g ‖z‖` is locally integrable on `ℂ`.
This is the statement for a radial function; radiality is
the form `g ∘ norm`. -/
theorem locallyIntegrable_radial {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    (hδ : 0 < δ) (hbound : ∀ r : ℝ, 0 < r → r ≤ δ → |g r| ≤ C * (1 + |Real.log r|)) :
    LocallyIntegrable (fun z : ℂ => g ‖z‖) volume :=
  LatticeProb.RadialLocalIntegrability.locallyIntegrable_radial hg hδ hbound

/-- Sublinear growth gives a linear envelope in the radial time variable.
If `h` is continuous and `h t / t → 0` as `t → ∞`, then `|h t| ≤ C (1 + t)` for
all `t ≥ 0`, with `C ≥ 0`.  This is the deterministic step from "Brownian growth is
`o(t)`" to the logarithmic bound `O(1 + |log |z||)` near zero. -/
lemma exists_abs_le_mul_one_add_of_sublinear {h : ℝ → ℝ} (hcont : Continuous h)
    (hsub : Tendsto (fun t : ℝ => h t / t) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |h t| ≤ C * (1 + t) :=
  LatticeProb.RadialLocalIntegrability.exists_abs_le_mul_one_add_of_sublinear hcont hsub

/-- Radial path with sublinear growth.  If `h` is continuous on `ℝ` and
`h t / t → 0` as `t → ∞`, then `z ↦ h (-log ‖z‖)` is locally integrable on `ℂ`.
The inward branch `t = -log ‖z‖ → ∞` corresponds to `z → 0`; continuity of `h`
on bounded intervals corresponds to continuity on bounded annuli. -/
theorem locallyIntegrable_radial_of_sublinear {h : ℝ → ℝ} (hcont : Continuous h)
    (hsub : Tendsto (fun t : ℝ => h t / t) atTop (𝓝 0)) :
    LocallyIntegrable (fun z : ℂ => h (-Real.log ‖z‖)) volume :=
  LatticeProb.RadialLocalIntegrability.locallyIntegrable_radial_of_sublinear hcont hsub

/-- Almost sure form, with the two Brownian premises explicit.  Almost surely the
radial path `t ↦ B t ω` is continuous (equivalently, continuous on every bounded
annulus `{r₁ ≤ |z| ≤ r₂}` of the paper) and it grows sublinearly,
`B t ω / t → 0` as `t → ∞` (the inward branch).  Neither premise is derived here;
the paper's Gaussian tail and Borel–Cantelli argument for `hsub` is not formalized. -/
theorem ae_locallyIntegrable_radial_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ → Ω → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : ℝ => B t ω)
    (hsub : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t ω / t) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, LocallyIntegrable (fun z : ℂ => B (-Real.log ‖z‖) ω) volume := by
  filter_upwards [hcont, hsub] with ω h1 h2
  exact locallyIntegrable_radial_of_sublinear h1 h2

end MatedCRT.Sec1
