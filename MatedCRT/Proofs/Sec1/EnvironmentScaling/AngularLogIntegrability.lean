import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLocalIntegrability

/-!
# Angular integrability of logarithmic radial singularities on circles through zero

Deterministic component of the angular assertion in `notes/env-steps/env-steps.tex:250-251`:
"Angular integrals remain finite for circles through zero, since a logarithmic singularity is
integrable in the angle."  The lateral observable `ℓ(r,z)` of `env-steps.tex:128-135` integrates
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

Not proved here: the measurable-in-`ω` version for random radial families (a later component), and
the identification of the circle integral with the lateral observable `ℓ(r,z)`.
-/

open MeasureTheory Set Filter Topology Complex

namespace MatedCRT.Sec1

/-- Standard circle parametrization through zero.  If `‖z‖ = r`, the circle `θ ↦ z + r e^{iθ}` has
`‖z + r e^{iθ}‖ = r · 2 |sin((θ - arg (-z))/2)|`, and it vanishes at `θ = arg (-z)`. -/
lemma norm_add_mul_exp_eq {z : ℂ} {r : ℝ} (hz : ‖z‖ = r) (θ : ℝ) :
    ‖z + (r : ℂ) * exp (I * θ)‖ = r * (2 * |Real.sin ((θ - arg (-z)) / 2)|) := by
  have ha : (r : ℂ) * exp (I * (arg (-z) : ℂ)) = -z := by
    have h := norm_mul_exp_arg_mul_I (-z)
    rw [norm_neg, hz, mul_comm ((arg (-z) : ℝ) : ℂ) I] at h
    exact h
  have hE : exp (I * (θ : ℂ)) =
      exp (I * (arg (-z) : ℂ)) * exp (I * ((θ - arg (-z) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have key : z + (r : ℂ) * exp (I * (θ : ℂ)) =
      -z * (exp (I * ((θ - arg (-z) : ℝ) : ℂ)) - 1) := by
    linear_combination (r : ℂ) * hE + exp (I * ((θ - arg (-z) : ℝ) : ℂ)) * ha
  rw [key, norm_mul, norm_neg, hz, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_two]

/-- Logarithmic singularity comparison on a circle through zero: for every `θ`,
`|log ‖z + r e^{iθ}‖| ≤ |log (2r)| + |log |sin((θ - arg (-z))/2)||`.  In Lean `log 0 = 0`, so the
zero of the circle is covered by the same inequality. -/
lemma abs_log_norm_add_mul_exp_le {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (θ : ℝ) :
    |Real.log ‖z + (r : ℂ) * exp (I * θ)‖| ≤
      |Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| := by
  rw [norm_add_mul_exp_eq hz]
  by_cases hS : Real.sin ((θ - arg (-z)) / 2) = 0
  · simp [hS]
  · have hpos : 0 < |Real.sin ((θ - arg (-z)) / 2)| := abs_pos.2 hS
    have hfac : r * (2 * |Real.sin ((θ - arg (-z)) / 2)|) =
        2 * r * |Real.sin ((θ - arg (-z)) / 2)| := by ring
    have h2r : 2 * r ≠ 0 := ne_of_gt (by linarith)
    rw [hfac, Real.log_mul h2r hpos.ne']
    exact abs_add_le _ _

/-- For every shift `c`, `θ ↦ |log |sin((θ - c)/2)||` is interval integrable on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_abs_sin_shift (c : ℝ) :
    IntervalIntegrable (fun θ : ℝ => |Real.log (|Real.sin ((θ - c) / 2)|)|) volume 0
      (2 * Real.pi) := by
  have hF : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin x)) volume (-c / 2)
      ((2 * Real.pi - c) / 2) := intervalIntegrable_log_sin
  have hG : IntervalIntegrable (fun x : ℝ => Real.log (Real.sin (1 / 2 * (x - c)))) volume
      ((-c / 2) / (1 / 2) + c) (((2 * Real.pi - c) / 2) / (1 / 2) + c) :=
    (hF.comp_mul_left (c := 1 / 2)).comp_sub_right c
  rw [show (-c / 2) / (1 / 2) + c = 0 by ring,
    show ((2 * Real.pi - c) / 2) / (1 / 2) + c = 2 * Real.pi by ring] at hG
  have hfun : (fun θ : ℝ => |Real.log (|Real.sin ((θ - c) / 2)|)|) =
      (fun θ : ℝ => |Real.log (Real.sin (1 / 2 * (θ - c)))|) := by
    funext θ
    have h2 : (θ - c) / 2 = 1 / 2 * (θ - c) := by ring
    rw [Real.log_abs, h2]
  rw [hfun]
  exact hG.abs

/-- Angular integrability of the absolute logarithmic singularity: for `r > 0` and `‖z‖ = r`,
`θ ↦ |log ‖z + r e^{iθ}‖|` is interval integrable on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_norm_add_mul_exp {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) :
    IntervalIntegrable (fun θ : ℝ => |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) volume 0
      (2 * Real.pi) := by
  have hcont : Continuous fun θ : ℝ => ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by fun_prop
  have hmeas : Measurable fun θ : ℝ => |Real.log ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp hcont.measurable)
  refine IntervalIntegrable.mono_fun' (g := fun θ : ℝ =>
      |Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)|) ?_
    hmeas.aestronglyMeasurable ?_
  · exact intervalIntegrable_const.add (intervalIntegrable_abs_log_abs_sin_shift (arg (-z)))
  · refine ae_of_all _ fun θ => ?_
    dsimp only
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_log_norm_add_mul_exp_le hr hz θ

/-- Finiteness of the angular integral of a radial function with logarithmic majorant.  Let
`g` be continuous on `(0, ∞)` with `|g t| ≤ C (1 + |log t|)` for `0 < t ≤ δ`, and let the circle
`θ ↦ z + r e^{iθ}` pass through zero (`‖z‖ = r > 0`) with `2r ≤ δ`.  Then `θ ↦ g ‖z + r e^{iθ}‖`
is interval integrable on `[0, 2π]`.  The circle is Lebesgue-null, so the majorant is used along
the circle itself; the zeros of `θ ↦ sin((θ - arg(-z))/2)` form a countable set. -/
theorem intervalIntegrable_radial_circle {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (hδ : 2 * r ≤ δ)
    (hbound : ∀ t : ℝ, 0 < t → t ≤ δ → |g t| ≤ C * (1 + |Real.log t|)) :
    IntervalIntegrable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * θ)‖) volume 0 (2 * Real.pi) := by
  classical
  have hZc : Set.Countable {θ : ℝ | Real.sin ((θ - arg (-z)) / 2) = 0} := by
    refine (Set.countable_range (fun n : ℤ => arg (-z) + 2 * Real.pi * n)).mono ?_
    intro θ hθ
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 (show Real.sin ((θ - arg (-z)) / 2) = 0 from hθ)
    exact ⟨n, by show arg (-z) + 2 * Real.pi * (n : ℝ) = θ; linear_combination 2 * hn⟩
  have hae : ∀ᵐ (θ : ℝ) ∂(volume : Measure ℝ), θ ∉ {θ : ℝ | Real.sin ((θ - arg (-z)) / 2) = 0} :=
    hZc.ae_notMem volume
  have hae' := ae_restrict_of_ae (s := Set.uIoc 0 (2 * Real.pi)) hae
  have hpos : ∀ θ : ℝ, Real.sin ((θ - arg (-z)) / 2) ≠ 0 → 0 < ‖z + (r : ℂ) * exp (I * θ)‖ := by
    intro θ hS
    rw [norm_add_mul_exp_eq hz]
    exact mul_pos hr (mul_pos two_pos (abs_pos.2 hS))
  have hle2 : ∀ θ : ℝ, ‖z + (r : ℂ) * exp (I * θ)‖ ≤ 2 * r := by
    intro θ
    rw [norm_add_mul_exp_eq hz]
    have hS1 : |Real.sin ((θ - arg (-z)) / 2)| ≤ 1 :=
      abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    nlinarith
  have hcont : Continuous fun θ : ℝ => ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by fun_prop
  have hGm : Measurable ((Ioi (0 : ℝ)).piecewise g (fun _ => (0 : ℝ))) :=
    ContinuousOn.measurable_piecewise hg continuousOn_const measurableSet_Ioi
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * θ)‖)
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    refine (hGm.comp hcont.measurable).aestronglyMeasurable.congr ?_
    filter_upwards [hae'] with θ hθ
    exact Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ioi.2 (hpos θ hθ))
  have hbd : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))),
      ‖g (‖z + (r : ℂ) * exp (I * θ)‖)‖ ≤ |C| * (1 + |Real.log (2 * r)|) +
        |C| * |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| := by
    filter_upwards [hae'] with θ hθ
    have hp := hpos θ hθ
    have hd : ‖z + (r : ℂ) * exp (I * θ)‖ ≤ δ := (hle2 θ).trans hδ
    have h1 := hbound _ hp hd
    have h2 := abs_log_norm_add_mul_exp_le hr hz θ
    rw [Real.norm_eq_abs]
    calc |g ‖z + (r : ℂ) * exp (I * θ)‖|
        ≤ C * (1 + |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) := h1
      _ ≤ |C| * (1 + |Real.log ‖z + (r : ℂ) * exp (I * θ)‖|) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (1 + (|Real.log (2 * r)| + |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)|)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
      _ = |C| * (1 + |Real.log (2 * r)|) + |C| * |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)| := by
          ring
  have hint : IntervalIntegrable (fun θ : ℝ => |C| * (1 + |Real.log (2 * r)|) +
      |C| * |Real.log (|Real.sin ((θ - arg (-z)) / 2)|)|) volume 0 (2 * Real.pi) :=
    intervalIntegrable_const.add
      ((intervalIntegrable_abs_log_abs_sin_shift (arg (-z))).const_mul |C|)
  exact IntervalIntegrable.mono_fun' hint hmeas hbd

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
  ⟨locallyIntegrable_radial hg hδ hbound, fun _ _ hr hz hr2 =>
    intervalIntegrable_radial_circle hg hr hz hr2 hbound⟩

end MatedCRT.Sec1
