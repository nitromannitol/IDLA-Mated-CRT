import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import MatedCRT.LPStaging.Bonanno.CirclePairing

/-!
# Circle averages of the whole-plane GFF are limits of pairings

For a whole-plane GFF `h` (`HarmonicBalls.IsWholePlaneGFF`, covariance kernel
`log (max |x| 1 · max |y| 1 / |x - y|)`), the circle average `h_r(z)` is the almost sure limit of the pairings
`(h, φ_k)` with the mollified uniform measures `φ_k = σ_{z,r} * ψ_k` on `∂B_r(z)` (Bonanno's `circBump k z r`):
`E[(h_r(z) - (h, φ_k))²] ≤ 3 · 2^{-k} / r` (`integral_sq_circle_sub_circBump_le`).

The computation: with `a(x) = log max(|x|, 1)` and `L = ∫ -log|· - y| φ_k(y) dy` the logarithmic potential of `φ_k`,
the terms of `a` cancel and `E[(h_r(z) - (h, φ_k))²] = -log r - 2 ⨍_{∂B_r(z)} L + ∫ φ_k L`; the potential `L` is within
`2^{-k}/r` of minus the logarithmic potential `g_{z,r}(x) = log r + log⁺(|x - z|/r)` of `σ_{z,r}` (Bonanno's
`abs_integral_bump_circLog_sub_le`), which equals `log r` on `∂B_r(z)` and is at least `log r` everywhere.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal

namespace MatedCRT
namespace CirclePairing

open LQGMetric LQGMetric.CircleAvg

/-- `a(x) = log max(|x|, 1)`, the normalization term of the covariance of the whole-plane GFF. -/
def logMaxOne (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)

lemma continuous_logMaxOne : Continuous logMaxOne :=
  (continuous_norm.max continuous_const).log fun _ => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

lemma wholePlaneCov_eq {x y : ℂ} (h : x ≠ y) :
    HarmonicBalls.wholePlaneCov x y = logMaxOne x + logMaxOne y - Real.log ‖x - y‖ := by
  have h1 : (0 : ℝ) < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2 : (0 : ℝ) < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h3 : (0 : ℝ) < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
  rw [HarmonicBalls.wholePlaneCov, Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
  rfl

lemma circleIntegrable_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (R : ℝ) : CircleIntegrable f c R :=
  LatticeProb.CirclePairing.circleIntegrable_of_continuous hf c R

/-- A circle average of a function which is constant on the circle. -/
lemma circleAverage_eq_of_eqOn_sphere {f : ℂ → ℝ} {c : ℂ} {R v : ℝ} (hf : CircleIntegrable f c R)
    (h : ∀ x ∈ sphere c |R|, f x = v) : Real.circleAverage f c R = v :=
  LatticeProb.CirclePairing.circleAverage_eq_of_eqOn_sphere hf h

/-- Two functions which agree off one point agree codiscretely on any set. -/
lemma eventuallyEq_codiscreteWithin_of_ne {f g : ℂ → ℝ} (S : Set ℂ) (x : ℂ) (h : ∀ y, y ≠ x → f y = g y) :
    f =ᶠ[codiscreteWithin S] g :=
  LatticeProb.CirclePairing.eventuallyEq_codiscreteWithin_of_ne S x h

/-- The logarithmic potential of `circBump k z r` is within `2^{-k}/r` of `-g_{z,r}`. -/
lemma abs_logPot_circBump_add_circLog_le {r : ℝ} (hr : 0 < r) (k : ℕ) (z x : ℂ) :
    |logPot (circBump k z r) x + circLog z r x| ≤ (2 : ℝ)⁻¹ ^ k / r :=
  LatticeProb.CirclePairing.abs_logPot_circBump_add_circLog_le hr k z x

lemma abs_logPot_circBump_sub_le {r : ℝ} (hr : 0 < r) (k : ℕ) (z x y : ℂ) :
    |logPot (circBump k z r) x - logPot (circBump k z r) y| ≤ ‖x - y‖ / r :=
  LatticeProb.CirclePairing.abs_logPot_circBump_sub_le hr k z x y

lemma continuous_logPot_circBump {r : ℝ} (hr : 0 < r) (k : ℕ) (z : ℂ) :
    Continuous (logPot (circBump k z r)) :=
  LatticeProb.CirclePairing.continuous_logPot_circBump hr k z

/-- `circBump k z r` is a test function in the sense of the harmonic-balls formalization. -/
lemma isTestFunction_circBump (k : ℕ) (z : ℂ) (r : ℝ) :
    HarmonicBalls.IsTestFunction univ (circBump k z r) :=
  ⟨(circBump k z r).contDiff, (circBump k z r).hasCompactSupport, subset_univ _⟩

section Covariance

variable {k : ℕ} {z : ℂ} {r : ℝ}

/-- `∫ φ_k(y) K(x, y) dy = a(x) + ∫ φ_k a + L(x)`. -/
lemma integral_circBump_mul_wholePlaneCov (x : ℂ) :
    ∫ y, circBump k z r y * HarmonicBalls.wholePlaneCov x y =
      logMaxOne x + (∫ y, circBump k z r y * logMaxOne y) + logPot (circBump k z r) x := by
  have hae : (fun y => circBump k z r y * HarmonicBalls.wholePlaneCov x y) =ᵐ[volume]
      fun y => circBump k z r y * logMaxOne x + circBump k z r y * logMaxOne y +
        -Real.log ‖x - y‖ * circBump k z r y := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton x)] with y hy
    have hxy : x ≠ y := fun h => hy (by rw [h]; rfl)
    rw [wholePlaneCov_eq hxy]
    ring
  have h1 : Integrable fun y => circBump k z r y * logMaxOne x := (integrable_testC _).mul_const _
  have h2 : Integrable fun y => circBump k z r y * logMaxOne y :=
    ((circBump k z r).continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport
      (circBump k z r).hasCompactSupport.mul_right
  have h12 : Integrable fun y => circBump k z r y * logMaxOne x + circBump k z r y * logMaxOne y := h1.add h2
  rw [integral_congr_ae hae, integral_add h12 (integrable_log_mul_test _ x), integral_add h1 h2,
    integral_mul_const, integral_circBump, one_mul]
  rfl

lemma integrable_circBump_mul_logPot (hr : 0 < r) :
    Integrable fun x => circBump k z r x * logPot (circBump k z r) x :=
  LatticeProb.CirclePairing.integrable_circBump_mul_logPot hr

lemma wholePlaneGFFCov_circle_pairing (hr : 0 < r) :
    HarmonicBalls.wholePlaneGFFCov (.circle r z) (.pairing (circBump k z r)) =
      Real.circleAverage logMaxOne z r + (∫ y, circBump k z r y * logMaxOne y) +
        Real.circleAverage (logPot (circBump k z r)) z r := by
  simp only [HarmonicBalls.wholePlaneGFFCov, HarmonicBalls.GFFObservable.smear]
  simp_rw [integral_circBump_mul_wholePlaneCov]
  rw [show (fun x => logMaxOne x + (∫ y, circBump k z r y * logMaxOne y) + logPot (circBump k z r) x) =
      (logMaxOne + fun _ => ∫ y, circBump k z r y * logMaxOne y) + logPot (circBump k z r) from rfl,
    Real.circleAverage_add ((circleIntegrable_of_continuous continuous_logMaxOne z r).add
      (circleIntegrable_of_continuous continuous_const z r))
      (circleIntegrable_of_continuous (continuous_logPot_circBump hr k z) z r),
    Real.circleAverage_add (circleIntegrable_of_continuous continuous_logMaxOne z r)
      (circleIntegrable_of_continuous continuous_const z r), Real.circleAverage_const]

lemma wholePlaneGFFCov_pairing_pairing (hr : 0 < r) :
    HarmonicBalls.wholePlaneGFFCov (.pairing (circBump k z r)) (.pairing (circBump k z r)) =
      2 * (∫ y, circBump k z r y * logMaxOne y) + ∫ x, circBump k z r x * logPot (circBump k z r) x := by
  simp only [HarmonicBalls.wholePlaneGFFCov, HarmonicBalls.GFFObservable.smear]
  simp_rw [integral_circBump_mul_wholePlaneCov, mul_add]
  have h2 : Integrable fun y => circBump k z r y * logMaxOne y :=
    ((circBump k z r).continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport
      (circBump k z r).hasCompactSupport.mul_right
  have h1 : Integrable fun y => circBump k z r y * (∫ y, circBump k z r y * logMaxOne y) :=
    (integrable_testC _).mul_const _
  have h21 : Integrable fun y => circBump k z r y * logMaxOne y +
      circBump k z r y * (∫ y, circBump k z r y * logMaxOne y) := h2.add h1
  rw [integral_add h21 (integrable_circBump_mul_logPot hr), integral_add h2 h1, integral_mul_const,
    integral_circBump, one_mul]
  ring

lemma wholePlaneGFFCov_circle_circle (hr : 0 < r) :
    HarmonicBalls.wholePlaneGFFCov (.circle r z) (.circle r z) = 2 * Real.circleAverage logMaxOne z r - Real.log r := by
  simp only [HarmonicBalls.wholePlaneGFFCov, HarmonicBalls.GFFObservable.smear]
  have hin : ∀ x, Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) z r =
      logMaxOne x + Real.circleAverage logMaxOne z r - circLog z r x := by
    intro x
    rw [Real.circleAverage_congr_codiscreteWithin (f₂ := (fun _ => logMaxOne x) + logMaxOne -
        fun y => Real.log ‖y - x‖) ?_ hr.ne']
    · rw [Real.circleAverage_sub ((circleIntegrable_of_continuous continuous_const z r).add
          (circleIntegrable_of_continuous continuous_logMaxOne z r)) (circleIntegrable_log_norm_sub_const r),
        Real.circleAverage_add (circleIntegrable_of_continuous continuous_const z r)
          (circleIntegrable_of_continuous continuous_logMaxOne z r), Real.circleAverage_const]
      rfl
    · refine eventuallyEq_codiscreteWithin_of_ne _ x fun y hy => ?_
      rw [wholePlaneCov_eq (Ne.symm hy), norm_sub_rev]
      rfl
  simp_rw [hin]
  rw [show (fun x => logMaxOne x + Real.circleAverage logMaxOne z r - circLog z r x) =
      (logMaxOne + fun _ => Real.circleAverage logMaxOne z r) - circLog z r from rfl,
    Real.circleAverage_sub ((circleIntegrable_of_continuous continuous_logMaxOne z r).add
      (circleIntegrable_of_continuous continuous_const z r))
      (circleIntegrable_of_continuous (continuous_circLog hr.ne' z) z r),
    Real.circleAverage_add (circleIntegrable_of_continuous continuous_logMaxOne z r)
      (circleIntegrable_of_continuous continuous_const z r), Real.circleAverage_const,
    circleAverage_eq_of_eqOn_sphere (circleIntegrable_of_continuous (continuous_circLog hr.ne' z) z r)
      (v := Real.log r) fun x hx => ?_]
  · ring
  · rw [circLog_eq hr.ne', mem_sphere, abs_of_pos hr] at *
    rw [← dist_eq_norm, dist_comm, hx, inv_mul_cancel₀ hr.ne', Real.posLog_one, add_zero]

/-- `g_{z,r} ≥ log r`. -/
lemma log_le_circLog (hr : 0 < r) (x : ℂ) : Real.log r ≤ circLog z r x :=
  LatticeProb.CirclePairing.log_le_circLog hr x

end Covariance

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

omit [IsProbabilityMeasure P] in
lemma memLp_eval (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) {o : HarmonicBalls.GFFObservable}
    (ho : o.IsAdmissible) : MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
  (hG.isGaussianProcess.hasGaussianLaw_eval ⟨o, ho⟩).memLp_two

lemma covariance_eval_eq_integral (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    {o o' : HarmonicBalls.GFFObservable} (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    ∫ ω, o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω) ∂P = HarmonicBalls.wholePlaneGFFCov o o' := by
  rw [← hG.covariance_eq o o' ho ho', covariance_eq_sub (memLp_eval hG ho) (memLp_eval hG ho'),
    hG.integral_eq_zero o ho, zero_mul, sub_zero]
  rfl

/-- `E[(X_o - X_{o'})²] = C(o, o) - 2 C(o, o') + C(o', o')` for admissible observables of the whole-plane GFF. -/
lemma integral_sq_eval_sub (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    {o o' : HarmonicBalls.GFFObservable} (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    ∫ ω, (o.eval (hC ω) (hcirc ω) - o'.eval (hC ω) (hcirc ω)) ^ 2 ∂P =
      HarmonicBalls.wholePlaneGFFCov o o - 2 * HarmonicBalls.wholePlaneGFFCov o o' +
        HarmonicBalls.wholePlaneGFFCov o' o' := by
  have hX := memLp_eval hG ho
  have hY := memLp_eval hG ho'
  have hXX : Integrable (fun ω => o.eval (hC ω) (hcirc ω) * o.eval (hC ω) (hcirc ω)) P := hX.integrable_mul hX
  have hXY : Integrable (fun ω => o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω)) P := hX.integrable_mul hY
  have hYY : Integrable (fun ω => o'.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω)) P := hY.integrable_mul hY
  have e : (fun ω => (o.eval (hC ω) (hcirc ω) - o'.eval (hC ω) (hcirc ω)) ^ 2) = fun ω =>
      o.eval (hC ω) (hcirc ω) * o.eval (hC ω) (hcirc ω) -
        2 * (o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω)) +
          o'.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω) := funext fun ω => by ring
  have hXY2 : Integrable (fun ω => 2 * (o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω))) P := hXY.const_mul 2
  have hsub : Integrable (fun ω => o.eval (hC ω) (hcirc ω) * o.eval (hC ω) (hcirc ω) -
      2 * (o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω))) P := hXX.sub hXY2
  rw [e, integral_add hsub hYY, integral_sub hXX hXY2, integral_const_mul,
    covariance_eval_eq_integral hG ho ho, covariance_eval_eq_integral hG ho ho',
    covariance_eval_eq_integral hG ho' ho']

/-- **The circle average is the `L²` limit of the pairings with `circBump`, with rate**:
`E[(h_r(z) - (h, φ_k))²] ≤ 3 · 2^{-k} / r`. -/
theorem integral_sq_circle_sub_circBump_le (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (z : ℂ) :
    ∫ ω, (hcirc ω r z - hC ω (circBump k z r)) ^ 2 ∂P ≤ 3 * ((2 : ℝ)⁻¹ ^ k / r) := by
  have h := integral_sq_eval_sub hG (o := .circle r z) (o' := .pairing (circBump k z r)) hr
    (isTestFunction_circBump k z r)
  simp only [HarmonicBalls.GFFObservable.eval] at h
  rw [h, wholePlaneGFFCov_circle_circle hr, wholePlaneGFFCov_circle_pairing hr, wholePlaneGFFCov_pairing_pairing hr]
  set δ := (2 : ℝ)⁻¹ ^ k / r with hδ
  have hCA : -Real.log r - δ ≤ Real.circleAverage (logPot (circBump k z r)) z r := by
    calc -Real.log r - δ = Real.circleAverage (fun _ => -Real.log r - δ) z r := (Real.circleAverage_const _ z r).symm
      _ ≤ _ := by
        refine Real.circleAverage_mono (circleIntegrable_of_continuous continuous_const z r)
          (circleIntegrable_of_continuous (continuous_logPot_circBump hr k z) z r) fun x hx => ?_
        have h1 := abs_logPot_circBump_add_circLog_le hr k z x
        have h2 : circLog z r x = Real.log r := by
          rw [mem_sphere, abs_of_pos hr] at hx
          rw [circLog_eq hr.ne', ← dist_eq_norm, dist_comm, hx, inv_mul_cancel₀ hr.ne', Real.posLog_one, add_zero]
        rw [h2, ← hδ] at h1
        linarith [(abs_le.1 h1).1]
  have hint : ∫ x, circBump k z r x * logPot (circBump k z r) x ≤ -Real.log r + δ := by
    calc ∫ x, circBump k z r x * logPot (circBump k z r) x ≤ ∫ x, circBump k z r x * (-Real.log r + δ) := by
          refine integral_mono (integrable_circBump_mul_logPot hr) ((integrable_testC _).mul_const _) fun x => ?_
          refine mul_le_mul_of_nonneg_left ?_ (circBump_nonneg k z r x)
          have h1 := abs_logPot_circBump_add_circLog_le hr k z x
          rw [← hδ] at h1
          linarith [(abs_le.1 h1).2, log_le_circLog (z := z) hr x]
      _ = -Real.log r + δ := by rw [integral_mul_const, integral_circBump, one_mul]
  linarith

/-- **Almost surely `(h, φ_k) → h_r(z)`** for the whole-plane GFF (`φ_k = circBump k z r`, `r > 0`). -/
theorem ae_tendsto_circBump (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, Tendsto (fun k => hC ω (circBump k z r)) atTop (𝓝 (hcirc ω r z)) := by
  set D : ℕ → Ω → ℝ := fun k ω => (hcirc ω r z - hC ω (circBump k z r)) ^ 2
  have hDint : ∀ k, Integrable (D k) P := fun k =>
    ((memLp_eval hG (o := .circle r z) hr).sub
      (memLp_eval hG (o := .pairing (circBump k z r)) (isTestFunction_circBump k z r))).integrable_sq
  have hDnn : ∀ k ω, 0 ≤ D k ω := fun k ω => sq_nonneg _
  have hmeas : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal (D k ω)) P := fun k =>
    (hDint k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hsum : Summable fun k : ℕ => 3 * ((2 : ℝ)⁻¹ ^ k / r) := by
    have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_left (3 / r)
    refine this.congr fun k => ?_
    ring
  have hlint : ∫⁻ ω, ∑' k, ENNReal.ofReal (D k ω) ∂P ≠ ∞ := by
    rw [lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal (3 * ((2 : ℝ)⁻¹ ^ k / r))) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
      exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun k => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hDint k) (Eventually.of_forall (hDnn k))]
      exact ENNReal.ofReal_le_ofReal (integral_sq_circle_sub_circBump_le hG hr k z)
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hlint] with ω hω
  have h0 : Tendsto (fun k => ENNReal.ofReal (D k ω)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h1 : Tendsto (fun k => D k ω) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hDnn _ ω)] using this
  have h2 : Tendsto (fun k => Real.sqrt (D k ω)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine h2.congr fun k => ?_
  simp only [D, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
  exact abs_sub_comm _ _

end Gaussian

end CirclePairing
end MatedCRT
