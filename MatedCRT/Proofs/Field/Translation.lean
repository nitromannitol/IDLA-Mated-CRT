import HarmonicBalls.Defs.GFF
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl2Pot
import MatedCRT.Proofs.Field.GaussianLaw

/-!
# Translation invariance of the whole-plane GFF modulo additive constant (eq:gff-scaling)

For a whole-plane GFF `h^ℂ` (`HarmonicBalls.IsWholePlaneGFF`) and `z ∈ ℂ`, the translated field `h^ℂ(· + z)` agrees in
law with `h^ℂ` modulo additive constant: the family of pairings `(h^ℂ, φ(· + z))`, `φ` ranging over test functions with
`∫ φ = 0`, has the law of the family `(h^ℂ, φ)` (`IsWholePlaneGFF.map_pairing_translate`).

Proof. Both families are centred Gaussian processes (`IsWholePlaneGFF.isGaussianProcess`), so by
`MatedCRT.Field.map_eq_of_covariance` it suffices to compare covariances. The covariance kernel
`G(x, y) = log (max(|x|, 1) max(|y|, 1) / |x - y|)` satisfies `G(x - z, y - z) = G(x, y) + a(x) + a'(y)` off the diagonal,
and the terms `a(x)`, `a'(y)` integrate to `0` against test functions of mean zero (`wholePlaneGFFCov_translate`). The
integrability of `y ↦ ψ(y) log |x - y|` is Leonardo Bonanno's `LQGMetric.MarkovWeyl2.integrable_logConv`.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Set
open HarmonicBalls (IsTestFunction IsWholePlaneGFF GFFObservable wholePlaneGFFCov wholePlaneCov)

/-- `ℓ(u) = log max(|u|, 1)`, the normalization part of the whole-plane covariance kernel. -/
noncomputable def logMaxOne (u : ℂ) : ℝ := Real.log (max ‖u‖ 1)

lemma continuous_logMaxOne : Continuous logMaxOne :=
  Real.continuousOn_log.comp_continuous (continuous_norm.max continuous_const)
    fun _ => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

/-- Off the diagonal, `G(x, y) = ℓ(x) + ℓ(y) - log |x - y|`. -/
lemma wholePlaneCov_eq {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = logMaxOne x + logMaxOne y - Real.log ‖x - y‖ := by
  have h1 : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have h2 : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have h3 : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
  unfold wholePlaneCov logMaxOne
  rw [Real.log_div (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2]

/-- Lebesgue-a.e. `y ∈ ℂ` differs from a given point. -/
lemma ae_ne (x : ℂ) : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x :=
  compl_mem_ae_iff.2 (measure_singleton x)

lemma integrable_of_isTestFunction {U : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) : Integrable φ :=
  hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1

/-- `y ↦ ψ(y) log |x - y|` is integrable (Leonardo Bonanno, `LQGMetric.MarkovWeyl2.integrable_logConv`). -/
lemma integrable_mul_log_norm_sub {U : Set ℂ} {ψ : ℂ → ℝ} (hψ : IsTestFunction U ψ) (x : ℂ) :
    Integrable fun y => ψ y * Real.log ‖x - y‖ := by
  have h := (LQGMetric.MarkovWeyl2.integrable_logConv hψ.1.continuous hψ.2.1 x).comp_sub_left x
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]
  ring

/-- `y ↦ ψ(y) G(x, y)` is integrable. -/
lemma integrable_mul_wholePlaneCov {U : Set ℂ} {ψ : ℂ → ℝ} (hψ : IsTestFunction U ψ) (x : ℂ) :
    Integrable fun y => ψ y * wholePlaneCov x y := by
  have hc : Integrable fun y => ψ y * (logMaxOne x + logMaxOne y) := by
    have h1 : Integrable fun y => ψ y * logMaxOne x := (integrable_of_isTestFunction hψ).mul_const _
    have h2 : Integrable fun y => ψ y * logMaxOne y :=
      (hψ.1.continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport (hψ.2.1.mul_right)
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)
  refine (hc.sub (integrable_mul_log_norm_sub hψ x)).congr ?_
  filter_upwards [ae_ne x] with y hy
  rw [wholePlaneCov_eq (Ne.symm hy)]
  simp only [Pi.sub_apply]
  ring

/-- Translation of the inner integral: for `∫ ψ = 0`,
`∫ ψ(y) G(x - z, y - z) dy = ∫ ψ(y) G(x, y) dy + b(ψ, z)` with `b` independent of `x`. -/
lemma integral_mul_wholePlaneCov_sub {U : Set ℂ} {ψ : ℂ → ℝ} (hψ : IsTestFunction U ψ) (hψ0 : ∫ y, ψ y = 0)
    (z x : ℂ) :
    ∫ y, ψ y * wholePlaneCov (x - z) (y - z) =
      (∫ y, ψ y * wholePlaneCov x y) + ∫ y, ψ y * (logMaxOne (y - z) - logMaxOne y) := by
  have hb : Integrable fun y => ψ y * (logMaxOne (y - z) - logMaxOne y) :=
    (hψ.1.continuous.mul ((continuous_logMaxOne.comp (continuous_id.sub continuous_const)).sub
      continuous_logMaxOne)).integrable_of_hasCompactSupport hψ.2.1.mul_right
  have ha : Integrable fun y => ψ y * (logMaxOne (x - z) - logMaxOne x) :=
    (integrable_of_isTestFunction hψ).mul_const _
  have hab : Integrable fun y => ψ y * (logMaxOne (x - z) - logMaxOne x) +
      ψ y * (logMaxOne (y - z) - logMaxOne y) := ha.add hb
  have hcongr : (fun y => ψ y * wholePlaneCov (x - z) (y - z)) =ᵐ[volume]
      fun y => ψ y * wholePlaneCov x y + (ψ y * (logMaxOne (x - z) - logMaxOne x) +
        ψ y * (logMaxOne (y - z) - logMaxOne y)) := by
    filter_upwards [ae_ne x] with y hy
    have hy' : x - z ≠ y - z := fun h => hy (sub_left_injective h).symm
    rw [wholePlaneCov_eq hy', wholePlaneCov_eq (Ne.symm hy)]
    have : x - z - (y - z) = x - y := by ring
    rw [this]
    ring
  rw [integral_congr_ae hcongr, integral_add (integrable_mul_wholePlaneCov hψ x) hab,
    integral_add ha hb, integral_mul_const, hψ0, zero_mul, zero_add]

/-- If `∫ φ = 0`, adding a constant to `g` does not change `∫ φ g` (also when `φ g` is not integrable). -/
lemma integral_mul_add_const {φ g : ℂ → ℝ} (hφ : Integrable φ) (hφ0 : ∫ x, φ x = 0) (b : ℝ) :
    ∫ x, φ x * (g x + b) = ∫ x, φ x * g x := by
  have hφb : Integrable fun x => φ x * b := hφ.mul_const b
  have heq : (fun x => φ x * (g x + b)) = fun x => φ x * g x + φ x * b := by
    funext x
    ring
  by_cases hint : Integrable fun x => φ x * g x
  · rw [heq, integral_add hint hφb, integral_mul_const, hφ0, zero_mul, add_zero]
  · have hint' : ¬ Integrable fun x => φ x * (g x + b) := by
      intro h
      refine hint ((h.sub hφb).congr (Filter.Eventually.of_forall fun x => ?_))
      simp only [Pi.sub_apply]
      ring
    rw [integral_undef hint, integral_undef hint']

/-- **Translation invariance of the covariance of mean-zero pairings.** For test functions `φ, ψ` with
`∫ φ = ∫ ψ = 0`, `Cov((h, φ(· + z)), (h, ψ(· + z))) = Cov((h, φ), (h, ψ))`. -/
theorem wholePlaneGFFCov_translate {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hφ0 : ∫ x, φ x = 0) (hψ0 : ∫ y, ψ y = 0) (z : ℂ) :
    wholePlaneGFFCov (.pairing fun x => φ (x + z)) (.pairing fun y => ψ (y + z)) =
      wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
  show ∫ x, φ (x + z) * ∫ y, ψ (y + z) * wholePlaneCov x y =
    ∫ x, φ x * ∫ y, ψ y * wholePlaneCov x y
  have hin : ∀ x, ∫ y, ψ (y + z) * wholePlaneCov x y = ∫ y, ψ y * wholePlaneCov x (y - z) := by
    intro x
    have h := integral_add_right_eq_self (μ := volume) (fun y => ψ y * wholePlaneCov x (y - z)) z
    simp only [add_sub_cancel_right] at h
    exact h
  simp_rw [hin]
  have hout := integral_add_right_eq_self (μ := volume)
    (fun x => φ x * ∫ y, ψ y * wholePlaneCov (x - z) (y - z)) z
  simp only [add_sub_cancel_right] at hout
  rw [hout]
  simp_rw [integral_mul_wholePlaneCov_sub hψ hψ0 z]
  exact integral_mul_add_const (g := fun x => ∫ y, ψ y * wholePlaneCov x y)
    (integrable_of_isTestFunction hφ) hφ0 _

/-- The translate `φ(· + z)` of a test function. -/
lemma isTestFunction_translate {U : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (z : ℂ) :
    IsTestFunction ((fun x => x + z) ⁻¹' U) fun x => φ (x + z) := by
  refine ⟨hφ.1.comp (contDiff_id.add contDiff_const), ?_, ?_⟩
  · exact hφ.2.1.comp_homeomorph (Homeomorph.addRight z)
  · have h : tsupport (fun x => φ (x + z)) = (Homeomorph.addRight z) ⁻¹' tsupport φ :=
      tsupport_comp_eq_preimage φ (Homeomorph.addRight z)
    rw [h]
    exact preimage_mono hφ.2.2

lemma integral_translate (φ : ℂ → ℝ) (z : ℂ) : ∫ x, φ (x + z) = ∫ x, φ x :=
  integral_add_right_eq_self φ z

/-- **Translation invariance of the whole-plane GFF modulo additive constant** (eq:gff-scaling). For any family
`φ : S → (ℂ → ℝ)` of test functions with `∫ φ_s = 0`, the processes `s ↦ (h, φ_s)` and `s ↦ (h, φ_s(· + z))` have the same
law. -/
theorem IsWholePlaneGFF.map_pairing_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsWholePlaneGFF P hC hcirc) (z : ℂ) {S : Type*}
    (φ : S → ℂ → ℝ) (hφ : ∀ s, IsTestFunction univ (φ s)) (hφ0 : ∀ s, ∫ x, φ s x = 0) :
    P.map (fun ω s => hC ω (φ s)) = P.map (fun ω s => hC ω fun x => φ s (x + z)) := by
  have : IsProbabilityMeasure P := hP.isProbabilityMeasure
  have hφz : ∀ s, IsTestFunction univ fun x => φ s (x + z) := fun s => by
    simpa using isTestFunction_translate (hφ s) z
  let f : S → GFFObservable.Admissible := fun s => ⟨.pairing (φ s), hφ s⟩
  let g : S → GFFObservable.Admissible := fun s => ⟨.pairing fun x => φ s (x + z), hφz s⟩
  have hX : IsGaussianProcess (fun s ω => hC ω (φ s)) P := hP.isGaussianProcess.comp_right f
  have hY : IsGaussianProcess (fun s ω => hC ω fun x => φ s (x + z)) P := hP.isGaussianProcess.comp_right g
  have hX0 : ∀ s, ∫ ω, hC ω (φ s) ∂P = 0 := fun s => hP.integral_eq_zero (.pairing (φ s)) (hφ s)
  have hY0 : ∀ s, ∫ ω, hC ω (fun x => φ s (x + z)) ∂P = 0 :=
    fun s => hP.integral_eq_zero (.pairing fun x => φ s (x + z)) (hφz s)
  refine map_eq_of_covariance hX hY (fun s => hP.measurable_pairing _ (hφ s))
    (fun s => hP.measurable_pairing _ (hφz s)) hX0 hY0 fun s t => ?_
  have h1 : covariance (fun ω => hC ω (φ s)) (fun ω => hC ω (φ t)) P =
      wholePlaneGFFCov (.pairing (φ s)) (.pairing (φ t)) :=
    hP.covariance_eq (.pairing (φ s)) (.pairing (φ t)) (hφ s) (hφ t)
  have h2 : covariance (fun ω => hC ω fun x => φ s (x + z)) (fun ω => hC ω fun x => φ t (x + z)) P =
      wholePlaneGFFCov (.pairing fun x => φ s (x + z)) (.pairing fun x => φ t (x + z)) :=
    hP.covariance_eq (.pairing fun x => φ s (x + z)) (.pairing fun x => φ t (x + z)) (hφz s) (hφz t)
  rw [h1, h2]
  exact (wholePlaneGFFCov_translate (hφ s) (hφ t) (hφ0 s) (hφ0 t) z).symm

end MatedCRT.Field
