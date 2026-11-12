import MatedCRT.FirstPass.Derived.ConeWholePlaneFieldLaw
import MatedCRT.FirstPass.Derived.ConeGFFCoupling2

/-!
# Two-sided radial read-out of a field with continuous circle averages

For a sample `(hC, hcirc)` whose circle average process is continuous on `(0, ∞) × ℂ`, the radial profile
`x ↦ h_{|x|}(0)` is recovered from the two-sided radial path `(t ↦ h_{e^{-t}}(0), s ↦ h_{e^s}(0))` at rational times:
inside the closed unit disk from the inner path at time `-log |x|`, outside it from the outer path at time `log |x|`.
Consequently every admissible observable is its lateral part plus a measurable functional of the two rational-time
paths.

* `limVal2`: the value at `x` of a two-sided rational-time path (a `limsup` along rational times, hence measurable).
* `radOf2`: the radial part `o.smear (limVal2 F)` of an observable `o`, read from a two-sided rational-time path `F`.
* `limVal2_radRat2`: for a continuous circle average process, `limVal2 (radRat2 hcirc) x = h_{|x|}(0)` for `x ≠ 0`.
* `eval_eq_lateralProcess_add_radOf2`: `o(h) = lateral part of o(h) + radOf2 (radRat2 hcirc) o`.
* `measurable_radOf2`: the radial read-out of a fixed admissible observable is measurable in the path.
* `radRat2_coneGFFCircle`, `eval_coneGFF_eq_lateralProcess_add_radOf2`: the two-sided radial path of the field
  coupled to a quantum cone, `(t ↦ h_{e^{-t}}(0) - γ t, s ↦ h_1(0) + w(s) - w(0))`, and the resulting read-out.
-/

open MeasureTheory Filter Topology Set HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

open MatedCRT.ConeMeanZeroRestriction

/-- The outer radial path `s ↦ h_{e^s}(0)` at rational times. -/
noncomputable def outerRat (hcirc : ℝ → ℂ → ℝ) (q : ℚ≥0) : ℝ := (radialProcess hcirc).2 (q : ℝ≥0)

/-- The two-sided radial path `(t ↦ h_{e^{-t}}(0), s ↦ h_{e^s}(0))` at rational times. -/
noncomputable def radRat2 (hcirc : ℝ → ℂ → ℝ) : (ℚ≥0 → ℝ) × (ℚ≥0 → ℝ) := (radRat hcirc, outerRat hcirc)

/-- The value at `x` of a two-sided rational-time path `F = (f, g)`: `f` read at time `-log |x|` when `|x| ≤ 1`, and
`g` read at time `log |x|` (the inner time of `x⁻¹`) when `|x| > 1`. -/
noncomputable def limVal2 (F : (ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) (x : ℂ) : ℝ :=
  if ‖x‖ ≤ 1 then limVal F.1 x else limVal F.2 x⁻¹

/-- The radial part of an observable, read from a two-sided rational-time path. -/
noncomputable def radOf2 (F : (ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) (o : GFFObservable) : ℝ :=
  o.smear (limVal2 F)

theorem lateralEval_eq_sub_smear (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (o : GFFObservable) :
    lateralEval hC hcirc o = o.eval hC hcirc - o.smear (fun x => hcirc ‖x‖ 0) := by
  cases o <;> rfl

theorem continuous_outerCircle {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Continuous (fun t : ℝ => hcirc (Real.exp t) 0) := by
  have h1 : Continuous (fun t : ℝ => ((Real.exp t, (0 : ℂ)) : ℝ × ℂ)) := by fun_prop
  exact hc.comp_continuous h1 (fun t => ⟨Real.exp_pos _, mem_univ _⟩)

theorem limVal_outerRat {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (x : ℂ) :
    limVal (outerRat hcirc) x = hcirc (Real.exp (radTime x)) 0 := by
  apply limVal_eq_of_tendsto
  have hT := ((continuous_outerCircle hc).tendsto (radTime x)).comp (tendsto_ratApprox x)
  refine hT.congr (fun n => ?_)
  simp [outerRat, radialProcess]
  norm_cast

/-- For a continuous circle average process, the two-sided rational-time radial path recovers `h_{|x|}(0)`. -/
theorem limVal2_radRat2 {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {x : ℂ} (hx : x ≠ 0) :
    limVal2 (radRat2 hcirc) x = hcirc ‖x‖ 0 := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  simp only [limVal2, radRat2]
  split_ifs with h
  · rw [limVal_radRat hc]
    have ht : radTime x = -Real.log ‖x‖ :=
      max_eq_left (by linarith [Real.log_nonpos hpos.le h])
    rw [ht, neg_neg, Real.exp_log hpos]
  · rw [limVal_outerRat hc]
    have ht : radTime x⁻¹ = Real.log ‖x‖ := by
      unfold radTime
      rw [norm_inv, Real.log_inv, neg_neg]
      exact max_eq_left (Real.log_nonneg (by linarith [not_le.1 h]))
    rw [ht, Real.exp_log hpos]

theorem smear_limVal2_radRat2 {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) {o : GFFObservable}
    (ho : o.IsAdmissible) :
    o.smear (limVal2 (radRat2 hcirc)) = o.smear (fun x => hcirc ‖x‖ 0) := by
  cases o with
  | pairing φ =>
    simp only [GFFObservable.smear]
    refine integral_congr_ae ?_
    have h0 : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ 0 := by
      have := measure_eq_zero_iff_ae_notMem.1
        (measure_singleton (0 : ℂ) : (volume : Measure ℂ) {0} = 0)
      simpa using this
    filter_upwards [h0] with x hx
    rw [limVal2_radRat2 hc hx]
  | circle r z =>
    have hr : 0 < r := ho
    simp only [GFFObservable.smear]
    exact MatedCRT.ConeWholePlaneFieldLaw.circleAverage_congr_ne_zero hr
      (fun x _ hx => limVal2_radRat2 hc hx)

/-- **Read-out of an observable.** For a continuous circle average process, every admissible observable is its lateral
part plus the radial read-out of the two-sided rational-time radial path. -/
theorem eval_eq_lateralProcess_add_radOf2 (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (o : GFFObservable.Admissible) :
    o.1.eval hC hcirc = lateralProcess hC hcirc o + radOf2 (radRat2 hcirc) o.1 := by
  simp only [lateralProcess, lateralEval_eq_sub_smear, radOf2, smear_limVal2_radRat2 hc o.2]
  ring

/-- Composition form of the measurability of `limVal` (elaborated without expected type to avoid unfolding the
`limsup`). -/
theorem measurable_limVal_comp {α : Type*} [MeasurableSpace α] {F : α → ℚ≥0 → ℝ} {X : α → ℂ}
    (hF : Measurable F) (hX : Measurable X) : Measurable (fun a => limVal (F a) (X a)) := by
  have h := measurable_limVal_pair.comp (hF.prodMk hX)
  exact h

theorem measurable_limVal2_pair :
    Measurable (fun p : ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) × ℂ => limVal2 p.1 p.2) := by
  have hs : MeasurableSet {p : ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) × ℂ | ‖p.2‖ ≤ 1} :=
    measurableSet_le (measurable_norm.comp measurable_snd) measurable_const
  have hinv : Measurable (fun x : ℂ => x⁻¹) := measurable_inv
  have h1 : Measurable (fun p : ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) × ℂ => limVal p.1.1 p.2) :=
    measurable_limVal_comp measurable_fst.fst measurable_snd
  have h2 : Measurable (fun p : ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) × ℂ => limVal p.1.2 p.2⁻¹) :=
    measurable_limVal_comp measurable_fst.snd (hinv.comp measurable_snd)
  exact Measurable.ite hs h1 h2

/-- The radial read-out of a fixed admissible observable is a measurable function of the two-sided path. -/
theorem measurable_radOf2 {o : GFFObservable} (ho : o.IsAdmissible) :
    Measurable (fun F : (ℚ≥0 → ℝ) × (ℚ≥0 → ℝ) => radOf2 F o) := by
  cases o with
  | pairing φ =>
    have hφ' : IsTestFunction Set.univ φ := ho
    have hφ : Measurable φ := hφ'.1.continuous.measurable
    simp only [radOf2, GFFObservable.smear]
    have hf : StronglyMeasurable
        (fun p : ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) × ℂ => φ p.2 * limVal2 p.1 p.2) :=
      ((hφ.comp measurable_snd).mul measurable_limVal2_pair).stronglyMeasurable
    exact (hf.integral_prod_right' (ν := volume)).measurable
  | circle r z =>
    simp only [radOf2, GFFObservable.smear]
    unfold Real.circleAverage
    simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by linarith [Real.pi_pos])]
    have hf : StronglyMeasurable
        (fun p : ((ℚ≥0 → ℝ) × (ℚ≥0 → ℝ)) × ℝ => limVal2 p.1 (circleMap z r p.2)) :=
      (measurable_limVal2_pair.comp (measurable_fst.prodMk
        ((continuous_circleMap z r).measurable.comp measurable_snd))).stronglyMeasurable
    exact (hf.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * Real.pi)))).measurable.const_smul
      ((2 * Real.pi)⁻¹ : ℝ)

theorem measurable_outerRat {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (hm : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable (fun ω => outerRat (hcirc ω)) :=
  Measurable.of_eval fun _ => hm _ _ (Real.exp_pos _)

theorem measurable_radRat2 {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (hm : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable (fun ω => radRat2 (hcirc ω)) :=
  (measurable_radRat hm).prodMk (measurable_outerRat hm)

/-- The two-sided rational-time radial path of the coupled field: `(t ↦ h_{e^{-t}}(0) - γ t, s ↦ h_1(0) + w(s) - w(0))`. -/
theorem radRat2_coneGFFCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    radRat2 (coneGFFCircle γ hcirc w) =
      (driftRat γ (radRat hcirc), fun q : ℚ≥0 => hcirc 1 0 + (w q - w 0)) := by
  have h := radialProcess_coneGFFCircle γ hcirc w
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · simp only [radRat2, radRat, driftRat, h]
    norm_cast
  · simp only [radRat2, outerRat, h]

/-- **Read-out of the coupled field.** When the cone's circle averages are continuous and `w` is continuous, every
admissible observable of the coupled field is its lateral part plus the radial read-out of
`(t ↦ h_{e^{-t}}(0) - γ t, s ↦ h_1(0) + w(s) - w(0))`. -/
theorem eval_coneGFF_eq_lateralProcess_add_radOf2 (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    {w : ℝ≥0 → ℝ} (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ))
    (hw : Continuous w) (o : GFFObservable.Admissible) :
    o.1.eval (coneCouplingPairing γ hC hcirc w) (coneGFFCircle γ hcirc w) =
      lateralProcess (coneCouplingPairing γ hC hcirc w) (coneGFFCircle γ hcirc w) o +
        radOf2 (driftRat γ (radRat hcirc), fun q : ℚ≥0 => hcirc 1 0 + (w q - w 0)) o.1 := by
  rw [← radRat2_coneGFFCircle γ hcirc w]
  exact eval_eq_lateralProcess_add_radOf2 _ (continuousOn_coneGFFCircle γ hcont hw) o

end MatedCRT.FirstPass.Derived
