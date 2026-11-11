import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionCoordinate
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionDyadicDecoder

/-!
# Complex-affine transport of the insertion circle array

Internal module; it cites no literature input. It formalizes one written component of "Identification for the fixed
affine map": for a complex-affine map `z ↦ a z + b`, `a ≠ 0`,
the insertion circle array `(r, z) ↦ H(|a| r, a z + b) + Q log |a|` is the normalized
array `H^a(r, z + b/a)` up to the random constant `h(|a|, 0)` and a deterministic
constant.

* `circleAverage_log_complexAffine`, `affineCircleArray_eq_normalized`: the deterministic circle-average identity.
  For every realization `h`, every radius `s > 0` and every centre `v`, with `H = fieldCircleAverage α` and
  `H^a = fieldCircleAverage α (normalizedCircleProc a h)`,
  `H(|a| s, a v + b) + Q log |a| = H^a(s, v + b/a) + h(|a|, 0) + (Q - α) log |a|`.
  It uses no regularity and no almost-sure qualification.
* `measurable_circleProc_affineCircleArray`: `ω ↦ circleProc (affineCircleArray α Q a b (hcirc ω))` is measurable into
  the product space `Set.Ioi 0 × ℂ → ℝ`, for a whole-plane GFF.
* `continuousOn_affineCircleArray`, `ae_forall_continuous_circleProc_affineCircleArray`: the transported positive-radius
  process is continuous on `(0,∞) × ℂ` for all `a ≠ 0` and all `b` on one full-probability event, namely the event of
  `IsWholePlaneGFF.ae_continuousOn_circle`.
* `exists_measurable_contCircle_affineCircleArray`: for fixed `a ≠ 0` and `b`, a measurable random element of the
  continuous domain `ContCircle` of `InsertionDyadicDecoder` that agrees almost surely with the transported process.
* `normalized_circle_law_ofReal`: the real case `a = R > 0`, `b = 0` of the random law, read off from
  `circleProc_affine_law`.

Not proved here (exact residual of the random law equality for complex `a`): for `u ∈ ℂ` with `‖u‖ = 1`, the rotated field `hcirc' ω r z := hcirc ω r (u * z)` is a
whole-plane GFF for the rotated pairings `hC' ω φ := hC ω (fun y ↦ φ (u⁻¹ * y))`. Granting this residual,
`IsWholePlaneGFF P hC' hcirc'`, the random law `P.map (circleProc ∘ normalizedCircleProc a ∘ hcirc)
= P.map (circleProc ∘ hcirc)` follows for `a = |a| u`, since `normalizedCircleProc a (hcirc ω)
= normalizedCircleProc |a| (hcirc' ω)`, `circleProc_affine_law` applies to `hcirc'`, and
`Field.wholePlane_circle_law` identifies `hcirc'` with `hcirc` in law. The measure-level identity
`M^a_r = C_a⁻¹ (x ↦ x / a)_* M_{|a| r}` is not part of this file.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- The normalized complex-affine circle process:
`h^a(r, z) = h(|a| r, a z) - h(|a|, 0)`. For `a = R > 0` real it is `Field.affHcirc R 0` (`normalized_circle_law_ofReal`). -/
noncomputable def normalizedCircleProc (a : ℂ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => h (‖a‖ * r) (a * z) - h ‖a‖ 0

/-- The insertion circle array of the target, `(r, z) ↦ H(|a| r, a z + b) + Q log |a|` with `H = fieldCircleAverage α`. -/
noncomputable def affineCircleArray (α Q : ℝ) (a b : ℂ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => fieldCircleAverage α h (‖a‖ * r) (a * z + b) + Q * Real.log ‖a‖

/-- Closed form of the logarithmic circle average at a positive radius: `cavg(log|·|)(c, r) = log r + log⁺(|c| / r)`
(Jensen's formula). -/
theorem circleAverage_log_closed {c : ℂ} {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun x => Real.log ‖x‖) c r = Real.log r + Real.posLog (r⁻¹ * ‖c‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := c) (R := r) hr.ne'
  simpa only [sub_zero] using h

/-- Jensen's identity under a complex-affine change of centre: for `a ≠ 0`, `s > 0` and `v ∈ ℂ`,
`cavg(log|·|)(a v + b, |a| s) = log |a| + cavg(log|·|)(v + b / a, s)`. -/
theorem circleAverage_log_complexAffine {a b : ℂ} (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) (v : ℂ) :
    Real.circleAverage (fun x => Real.log ‖x‖) (a * v + b) (‖a‖ * s)
      = Real.log ‖a‖ + Real.circleAverage (fun x => Real.log ‖x‖) (v + b / a) s := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hs0 : s ≠ 0 := hs.ne'
  have hc : a * v + b = a * (v + b / a) := by field_simp
  have hn : ‖a * v + b‖ = ‖a‖ * ‖v + b / a‖ := by rw [hc, norm_mul]
  rw [circleAverage_log_closed (mul_pos (norm_pos_iff.2 ha) hs), circleAverage_log_closed hs, hn,
    Real.log_mul hna hs0]
  have key : (‖a‖ * s)⁻¹ * (‖a‖ * ‖v + b / a‖) = s⁻¹ * ‖v + b / a‖ := by
    field_simp
  rw [key]
  ring

/-- **Deterministic circle-average identity**. For `a ≠ 0`, every realization `h`, every `s > 0` and
`v ∈ ℂ`:
`affineCircleArray α Q a b h s v = fieldCircleAverage α (normalizedCircleProc a h) s (v + b / a) + h |a| 0 + (Q - α) log |a|`.
The identity holds pointwise in `h`, for all positive radii and all centres at once, with no regularity assumption. -/
theorem affineCircleArray_eq_normalized {α Q : ℝ} {a b : ℂ} (ha : a ≠ 0) (h : ℝ → ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    (v : ℂ) :
    affineCircleArray α Q a b h s v
      = fieldCircleAverage α (normalizedCircleProc a h) s (v + b / a) + h ‖a‖ 0 + (Q - α) * Real.log ‖a‖ := by
  have hc : a * (v + b / a) = a * v + b := by field_simp
  simp only [affineCircleArray, fieldCircleAverage, normalizedCircleProc]
  rw [hc, circleAverage_log_complexAffine ha hs v]
  ring

/-- **Measurable circle-array transport** (measurable part). For a whole-plane GFF `(hC, hcirc)`,
`a ≠ 0` and `b ∈ ℂ`, the transported positive-radius process `ω ↦ circleProc (affineCircleArray α Q a b (hcirc ω))` is a
random variable into the product space `Set.Ioi 0 × ℂ → ℝ`. -/
theorem measurable_circleProc_affineCircleArray {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α Q : ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    Measurable fun ω => circleProc (affineCircleArray α Q a b (hcirc ω)) := by
  refine Measurable.of_eval fun p => ?_
  have hm := hGFF.measurable_circle (‖a‖ * p.1.1) (a * p.2 + b) (mul_pos (norm_pos_iff.2 ha) p.1.2)
  unfold circleProc affineCircleArray fieldCircleAverage
  exact (hm.sub_const _).add_const _

/-- Joint continuity of the transported array on the positive-radius domain (continuity part): if `h` is
continuous on `(0,∞) × ℂ`, so is `(r, z) ↦ affineCircleArray α Q a b h r z`. -/
theorem continuousOn_affineCircleArray {α Q : ℝ} {a b : ℂ} (ha : a ≠ 0) {h : ℝ → ℂ → ℝ}
    (hh : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × ℂ => affineCircleArray α Q a b h p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hmapsto : MapsTo (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun p hp => ⟨mul_pos hna hp.1, mem_univ _⟩
  have hcont : ContinuousOn (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) (Ioi 0 ×ˢ univ) :=
    ((continuous_const.mul continuous_fst).prodMk
      ((continuous_const.mul continuous_snd).add continuous_const)).continuousOn
  have hcomp : ContinuousOn (fun p : ℝ × ℂ => h (‖a‖ * p.1) (a * p.2 + b)) (Ioi 0 ×ˢ univ) :=
    hh.comp hcont hmapsto
  have hlog : ContinuousOn (fun p : ℝ × ℂ => Real.log (‖a‖ * p.1)) (Ioi 0 ×ˢ univ) := by
    refine ContinuousOn.log (continuous_const.mul continuous_fst).continuousOn ?_
    intro p hp
    exact (mul_pos hna hp.1).ne'
  have hpos : ContinuousOn (fun p : ℝ × ℂ => Real.posLog ((‖a‖ * p.1)⁻¹ * ‖a * p.2 + b‖)) (Ioi 0 ×ˢ univ) := by
    refine Real.continuous_posLog.comp_continuousOn (ContinuousOn.mul ?_ ?_)
    · refine ContinuousOn.inv₀ (continuous_const.mul continuous_fst).continuousOn ?_
      intro p hp
      exact (mul_pos hna hp.1).ne'
    · exact (continuous_norm.comp ((continuous_const.mul continuous_snd).add continuous_const)).continuousOn
  have hform : ContinuousOn (fun p : ℝ × ℂ => h (‖a‖ * p.1) (a * p.2 + b)
      - α * (Real.log (‖a‖ * p.1) + Real.posLog ((‖a‖ * p.1)⁻¹ * ‖a * p.2 + b‖)) + Q * Real.log ‖a‖)
      (Ioi 0 ×ˢ univ) :=
    (hcomp.sub (continuousOn_const.mul (hlog.add hpos))).add continuousOn_const
  refine hform.congr ?_
  rintro ⟨r, z⟩ hrz
  have hr : 0 < r := hrz.1
  simp only [affineCircleArray, fieldCircleAverage]
  rw [circleAverage_log_closed (mul_pos hna hr)]

/-- Almost-sure continuity of the transported circle process, simultaneously in `a ≠ 0` and `b ∈ ℂ`.
The exceptional event is that of `IsWholePlaneGFF.ae_continuousOn_circle`, so it does not depend on `(a, b)`. -/
theorem ae_forall_continuous_circleProc_affineCircleArray {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (α Q : ℝ) :
    ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      Continuous (circleProc (affineCircleArray α Q a b (hcirc ω))) := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
  intro a ha b
  exact continuous_circleProc_of_continuousOn (continuousOn_affineCircleArray ha hω)

/-- The real case of the random law (with `a = R > 0`, `b = 0`): the normalized circle process of `R`
has the law of the circle process. This is `circleProc_affine_law` read through `normalizedCircleProc`. The complex
case is the residual described in the module docstring. -/
theorem normalized_circle_law_ofReal {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 0 < R) :
    P.map (fun ω => circleProc (normalizedCircleProc (R : ℂ) (hcirc ω)))
      = P.map (fun ω => circleProc (hcirc ω)) := by
  have e : (fun ω => circleProc (normalizedCircleProc (R : ℂ) (hcirc ω)))
      = fun ω => circleProc (Field.affHcirc R 0 hcirc ω) := by
    funext ω
    funext p
    simp only [circleProc, normalizedCircleProc, Field.affHcirc, Complex.norm_real, Real.norm_of_nonneg hR.le,
      add_zero]
  rw [e]
  exact circleProc_affine_law hGFF hR

/-- **Measurable continuous-domain transport** (the random element consumed by the decoder). For fixed
`a ≠ 0` and `b ∈ ℂ` there is a measurable map `X : Ω → ContCircle` into the continuous positive-radius processes of
`InsertionDyadicDecoder` that agrees almost surely with `circleProc (affineCircleArray α Q a b (hcirc ω))`. The
modification on a measurable null superset of the exceptional event is the constant `0`. -/
theorem exists_measurable_contCircle_affineCircleArray {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α Q : ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ∃ X : Ω → ContCircle, Measurable X ∧
      ∀ᵐ ω ∂P, (X ω : Set.Ioi (0 : ℝ) × ℂ → ℝ) = circleProc (affineCircleArray α Q a b (hcirc ω)) := by
  classical
  have hae : ∀ᵐ ω ∂P, Continuous (circleProc (affineCircleArray α Q a b (hcirc ω))) :=
    (ae_forall_continuous_circleProc_affineCircleArray hGFF α Q).mono fun ω hω => hω a ha b
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hYm : Measurable (N.piecewise (fun _ : Ω => (0 : Set.Ioi (0 : ℝ) × ℂ → ℝ))
      (fun ω => circleProc (affineCircleArray α Q a b (hcirc ω)))) :=
    Measurable.piecewise hN measurable_const (measurable_circleProc_affineCircleArray hGFF α Q ha b)
  have hYc : ∀ ω, Continuous (N.piecewise (fun _ : Ω => (0 : Set.Ioi (0 : ℝ) × ℂ → ℝ))
      (fun ω => circleProc (affineCircleArray α Q a b (hcirc ω))) ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [Set.piecewise, hω, ↓reduceIte]
      exact continuous_const
    · simp only [Set.piecewise, hω, ↓reduceIte]
      by_contra hnc
      exact hω (hsub hnc)
  refine ⟨fun ω => ⟨N.piecewise (fun _ : Ω => (0 : Set.Ioi (0 : ℝ) × ℂ → ℝ))
      (fun ω => circleProc (affineCircleArray α Q a b (hcirc ω))) ω, hYc ω⟩, ?_, ?_⟩
  · exact Measurable.subtype_mk hYm
  · filter_upwards [compl_mem_ae_iff.2 hN0] with ω hω
    have hω' : ω ∉ N := hω
    simp only [Set.piecewise, hω', ↓reduceIte]

end MatedCRT
