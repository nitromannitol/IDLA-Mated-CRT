import MatedCRT.Proofs.Field.Translation
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Inversion of test functions and the whole-plane GFF modulo constants

For a function `φ` on `ℂ`, `invPull φ x = φ (x⁻¹) / |x| ^ 4` is its pullback by the inversion
`x ↦ 1 / x` together with the Jacobian `|x| ^ (-4)` of the inversion (the value at `0` is the junk
value `0`, in accordance with `0⁻¹ = 0` in `ℂ`).

Used for the reduction of the tail at infinity of the whole-plane GFF to its germ at `0` (the proof
of `WholePlaneGFFExteriorTailTrivial`, in `ZeroConeLemmaA1GFFTail`):

* `integral_invPull_mul`: change of variables, `∫ invPull φ · H = ∫ φ · H (⁻¹)`;
* `isTestFunction_invPull`, `tsupport_invPull_subset`, `integral_invPull`: if `φ` is a test function
  whose support avoids `0` and lies in `{|w| > k}`, then `invPull φ` is a test function with support
  in the closed disc of radius `1 / k` and the same integral;
* `wholePlaneCov_inv`: the covariance kernel `G(x, y) = log (max(|x|, 1) max(|y|, 1) / |x - y|)` is
  invariant under `(x, y) ↦ (x⁻¹, y⁻¹)`; `wholePlaneGFFCov_invPull` is the resulting invariance of
  the covariance of pairings;
* `IsWholePlaneGFF.map_pairing_inv`: the families `s ↦ (h, φ_s)` and `s ↦ (h, invPull φ_s)` of
  pairings of a whole-plane GFF with test functions supported away from `0` have the same law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open HarmonicBalls (IsTestFunction IsWholePlaneGFF GFFObservable wholePlaneGFFCov wholePlaneCov)

namespace MatedCRT

/-- The pullback `x ↦ φ (x⁻¹) / |x| ^ 4` of `φ` by the inversion, with its Jacobian. -/
def invPull (φ : ℂ → ℝ) (x : ℂ) : ℝ := φ x⁻¹ * (‖x‖ ^ 4)⁻¹

/-- The real derivative `h ↦ -h / x ^ 2` of the inversion `x ↦ x⁻¹` at `x`. -/
abbrev invDeriv (x : ℂ) : ℂ →L[ℝ] ℂ :=
  ((1 : ℂ →L[ℂ] ℂ).smulRight (-(x ^ 2)⁻¹)).restrictScalars ℝ

/-- The absolute value of the real Jacobian of the inversion `x ↦ x⁻¹` at `x` is `|x| ^ (-4)`. -/
lemma abs_det_invDeriv (x : ℂ) : |(invDeriv x).det| = (‖x‖ ^ 4)⁻¹ := by
  have hdet : (invDeriv x).det = Complex.normSq (-(x ^ 2)⁻¹) := by
    have h : ((invDeriv x : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
        (LinearMap.mulLeft ℂ (-(x ^ 2)⁻¹)).restrictScalars ℝ := by
      ext z
      simp [mul_comm]
    rw [ContinuousLinearMap.det, h, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
    simp
  rw [hdet, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _), norm_neg, norm_inv, norm_pow]
  ring

/-- **Change of variables for the inversion** `y = x⁻¹` of the plane (Jacobian `|x| ^ (-4)`). -/
theorem integral_inv_comp (g : ℂ → ℝ) : ∫ x, (‖x‖ ^ 4)⁻¹ * g x⁻¹ = ∫ y, g y := by
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hf' : ∀ x ∈ ({0}ᶜ : Set ℂ), HasFDerivWithinAt (fun x : ℂ => x⁻¹) (invDeriv x) {0}ᶜ x :=
    fun x hx =>
    ((hasDerivAt_inv hx).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : InjOn (fun x : ℂ => x⁻¹) {0}ᶜ := inv_injective.injOn
  have himg : (fun x : ℂ => x⁻¹) '' {0}ᶜ = {0}ᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y⁻¹, by simpa using hy, inv_inv y⟩
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' hinj g
  rw [himg] at h
  have hR : ∫ x in ({0}ᶜ : Set ℂ), |(invDeriv x).det| • g x⁻¹ =
      ∫ x in ({0}ᶜ : Set ℂ), (‖x‖ ^ 4)⁻¹ * g x⁻¹ :=
    setIntegral_congr_fun hs fun x _ => by rw [abs_det_invDeriv x, smul_eq_mul]
  rw [hR, restrict_compl_singleton] at h
  exact h.symm

/-- **Change of variables for `invPull`**: `∫ invPull φ · H = ∫ φ · H (⁻¹)`. -/
theorem integral_invPull_mul (φ H : ℂ → ℝ) :
    ∫ x, invPull φ x * H x = ∫ y, φ y * H y⁻¹ := by
  rw [← integral_inv_comp fun y => φ y * H y⁻¹]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [invPull, inv_inv]
  ring

/-- `∫ invPull φ = ∫ φ`. -/
theorem integral_invPull (φ : ℂ → ℝ) : ∫ x, invPull φ x = ∫ y, φ y := by
  simpa using integral_invPull_mul φ fun _ => 1

/-- A function whose support avoids `0` vanishes on a disc around `0`. -/
lemma exists_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} (h0 : (0 : ℂ) ∉ tsupport φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℂ, ‖x‖ < δ → φ x = 0 := by
  have h := notMem_tsupport_iff_eventuallyEq.1 h0
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨δ, hδ, fun x hx => hball (by simpa using hx)⟩

/-- `invPull φ` vanishes at the points `x` for which `φ x⁻¹ = 0`. -/
lemma invPull_eq_zero {φ : ℂ → ℝ} {x : ℂ} (h : φ x⁻¹ = 0) : invPull φ x = 0 := by
  simp [invPull, h]

/-- **The inversion of a test function supported away from `0` is a test function.** -/
theorem isTestFunction_invPull {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (h0 : (0 : ℂ) ∉ tsupport φ) : IsTestFunction univ (invPull φ) := by
  obtain ⟨δ, hδ, hzero⟩ := exists_eq_zero_of_notMem_tsupport h0
  obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hsmall : ∀ x : ℂ, x ≠ 0 → ‖x‖ < (max R 0 + 1)⁻¹ → invPull φ x = 0 := by
    intro x hx hxs
    refine invPull_eq_zero ?_
    by_contra hne
    have hmem : x⁻¹ ∈ closedBall (0 : ℂ) R :=
      hR (subset_tsupport φ (Function.mem_support.2 hne))
    rw [mem_closedBall, dist_zero_right, norm_inv] at hmem
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 : (max R 0 + 1)⁻¹ ≤ ‖x‖ := by
      rw [inv_le_comm₀ (by positivity) hpos]
      exact lt_of_le_of_lt ((le_max_left R 0).trans' hmem) (by linarith) |>.le
    exact absurd hxs (not_lt.2 h1)
  refine ⟨?_, ?_, subset_univ _⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x = 0
    · subst hx
      have hev : invPull φ =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
        have hnhds : Metric.ball (0 : ℂ) (max R 0 + 1)⁻¹ ∈ 𝓝 (0 : ℂ) :=
          Metric.ball_mem_nhds _ (by positivity)
        filter_upwards [hnhds] with y hy
        by_cases hy0 : y = 0
        · subst hy0
          simp [invPull]
        · exact hsmall y hy0 (by simpa using hy)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => φ y⁻¹) x :=
        (hφ.1.contDiffAt (x := x⁻¹)).comp x (contDiffAt_inv ℝ hx)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => (‖y‖ ^ 4)⁻¹) x :=
        ((contDiffAt_norm ℝ hx).pow 4).inv
          (pow_ne_zero 4 (norm_ne_zero_iff.2 hx))
      exact h1.mul h2
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ⁻¹) fun x hx => ?_
    refine invPull_eq_zero (hzero _ ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    rw [norm_inv]
    exact inv_lt_of_inv_lt₀ hδ hx

/-- If `tsupport φ ⊆ {|w| > k}`, then `tsupport (invPull φ)` lies in the closed disc of radius
`1 / k`. -/
theorem tsupport_invPull_subset {φ : ℂ → ℝ} {k : ℝ} (hk : 0 < k)
    (hφ : tsupport φ ⊆ {w : ℂ | k < ‖w‖}) :
    tsupport (invPull φ) ⊆ closedBall 0 k⁻¹ := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  have hne : φ x⁻¹ ≠ 0 := fun h => hx (invPull_eq_zero h)
  have hlt : k < ‖x⁻¹‖ := hφ (subset_tsupport φ (Function.mem_support.2 hne))
  have hx0 : x ≠ 0 := fun h => by simp [h] at hlt; linarith
  rw [mem_closedBall, dist_zero_right]
  rw [norm_inv] at hlt
  exact (lt_inv_comm₀ hk (norm_pos_iff.2 hx0)).1 hlt |>.le

/-- The covariance kernel `G(x, y) = log (max(|x|, 1) max(|y|, 1) / |x - y|)` is inversion
invariant. -/
theorem wholePlaneCov_inv {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    wholePlaneCov u⁻¹ v⁻¹ = wholePlaneCov u v := by
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hmax : ∀ w : ℂ, w ≠ 0 → max ‖w⁻¹‖ 1 = max ‖w‖ 1 / ‖w‖ := by
    intro w hw
    have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
    rw [norm_inv]
    rcases le_total ‖w‖ 1 with h | h
    · rw [max_eq_left (one_le_inv₀ hw' |>.2 h), max_eq_right h, one_div]
    · rw [max_eq_right (inv_le_one_of_one_le₀ h), max_eq_left h, div_self hw'.ne']
  have hdiff : ‖u⁻¹ - v⁻¹‖ = ‖u - v‖ / (‖u‖ * ‖v‖) := by
    rw [inv_sub_inv hu hv, norm_div, norm_mul, norm_sub_rev]
  unfold wholePlaneCov
  rw [hmax u hu, hmax v hv, hdiff]
  congr 1
  by_cases hD : ‖u - v‖ = 0
  · simp [hD]
  · field_simp

/-- **Inversion invariance of the covariance of pairings**: for test functions supported away from
`0`, the covariance of the pairings with `invPull φ` and `invPull ψ` is that of the pairings with
`φ` and `ψ`. -/
theorem wholePlaneGFFCov_invPull {φ ψ : ℂ → ℝ} (hφ : (0 : ℂ) ∉ tsupport φ)
    (hψ : (0 : ℂ) ∉ tsupport ψ) :
    wholePlaneGFFCov (.pairing (invPull φ)) (.pairing (invPull ψ)) =
      wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
  have hφ0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport hφ
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport hψ
  show ∫ x, invPull φ x * ∫ y, invPull ψ y * wholePlaneCov x y =
    ∫ x, φ x * ∫ y, ψ y * wholePlaneCov x y
  have hin : ∀ x, ∫ y, invPull ψ y * wholePlaneCov x y =
      ∫ v, ψ v * wholePlaneCov x v⁻¹ := fun x => integral_invPull_mul ψ (wholePlaneCov x)
  simp_rw [hin]
  rw [integral_invPull_mul φ fun x => ∫ v, ψ v * wholePlaneCov x v⁻¹]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : u = 0
  · simp [hu, hφ0]
  · have hinner : ∫ v, ψ v * wholePlaneCov u⁻¹ v⁻¹ = ∫ y, ψ y * wholePlaneCov u y := by
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      by_cases hv : v = 0
      · simp [hv, hψ0]
      · simp only [wholePlaneCov_inv hu hv]
    rw [hinner]

/-- **Inversion invariance of the whole-plane GFF modulo additive constants.** For any family
`φ : S → (ℂ → ℝ)` of test functions supported away from `0`, the processes `s ↦ (h, φ_s)` and
`s ↦ (h, invPull φ_s)` have the same law. -/
theorem IsWholePlaneGFF.map_pairing_inv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsWholePlaneGFF P hC hcirc)
    {S : Type*} (φ : S → ℂ → ℝ) (hφ : ∀ s, IsTestFunction univ (φ s))
    (h0 : ∀ s, (0 : ℂ) ∉ tsupport (φ s)) :
    P.map (fun ω s => hC ω (φ s)) = P.map (fun ω s => hC ω (invPull (φ s))) := by
  have : IsProbabilityMeasure P := hP.isProbabilityMeasure
  have hφi : ∀ s, IsTestFunction univ (invPull (φ s)) := fun s =>
    isTestFunction_invPull (hφ s) (h0 s)
  let f : S → GFFObservable.Admissible := fun s => ⟨.pairing (φ s), hφ s⟩
  let g : S → GFFObservable.Admissible := fun s => ⟨.pairing (invPull (φ s)), hφi s⟩
  have hX : IsGaussianProcess (fun s ω => hC ω (φ s)) P := hP.isGaussianProcess.comp_right f
  have hY : IsGaussianProcess (fun s ω => hC ω (invPull (φ s))) P :=
    hP.isGaussianProcess.comp_right g
  refine MatedCRT.Field.map_eq_of_covariance hX hY (fun s => hP.measurable_pairing _ (hφ s))
    (fun s => hP.measurable_pairing _ (hφi s))
    (fun s => hP.integral_eq_zero (.pairing (φ s)) (hφ s))
    (fun s => hP.integral_eq_zero (.pairing (invPull (φ s))) (hφi s)) fun s t => ?_
  have h1 : covariance (fun ω => hC ω (φ s)) (fun ω => hC ω (φ t)) P =
      wholePlaneGFFCov (.pairing (φ s)) (.pairing (φ t)) :=
    hP.covariance_eq (.pairing (φ s)) (.pairing (φ t)) (hφ s) (hφ t)
  have h2 : covariance (fun ω => hC ω (invPull (φ s))) (fun ω => hC ω (invPull (φ t))) P =
      wholePlaneGFFCov (.pairing (invPull (φ s))) (.pairing (invPull (φ t))) :=
    hP.covariance_eq (.pairing (invPull (φ s))) (.pairing (invPull (φ t))) (hφi s) (hφi t)
  rw [h1, h2]
  exact (wholePlaneGFFCov_invPull (h0 s) (h0 t)).symm

end MatedCRT
