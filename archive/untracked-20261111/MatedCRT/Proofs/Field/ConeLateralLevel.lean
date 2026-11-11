import MatedCRT.Proofs.Field.ConeLevelIntegrable
import MatedCRT.Proofs.Field.ConeRadialCov

/-!
# The lateral observables of the whole-plane GFF as level integrals (eq:gff)

Every admissible observable `o` (a pairing with a test function, or a circle average) smears a radially symmetric
function `x ↦ F(|x|)` as a level integral of the path `u ↦ F(e^{-u})` along `s(x) = -log |x|` (`HasLevelDatum`,
`hasLevelDatum`). For the whole-plane GFF `h^ℂ` this writes the radial part `o.smear (x ↦ h^ℂ_{|x|}(0))` of `o` as a
level integral of the radial process `V_u = h^ℂ_{e^{-u}}(0)`, a centred Gaussian process with almost surely continuous
paths and `Var V_u = |u|` (`covariance_radial`). By `levelIntegral_versions` it has a version which can be adjoined to
the Gaussian span of `h^ℂ`, with `Cov(V_t, ·) = o.smear (x ↦ K(e^{-t}, |x|))` (`lateral_versions`).
-/

namespace MatedCRT.Field.ConeRadial

open MeasureTheory ProbabilityTheory Set Filter Topology MatedCRT.Field.GaussClosure MatedCRT.Field.Level
open HarmonicBalls (IsTestFunction IsWholePlaneGFF GFFObservable wholePlaneGFFCov wholePlaneCov)
open scoped ENNReal NNReal

/-- `o` smears radially symmetric functions as level integrals along `s` with weight `g` against `ν`. -/
def HasLevelDatum (o : GFFObservable) : Prop :=
  ∃ (α : Type) (_ : MeasurableSpace α) (ν : Measure α) (_ : SFinite ν) (g s : α → ℝ), Measurable g ∧
    Measurable s ∧ Integrable g ν ∧ Integrable (fun x => g x * (1 + |s x|)) ν ∧
    ∀ F : ℝ → ℝ, o.smear (fun x => F ‖x‖) = levelIntegral ν g s fun u => F (Real.exp (-u))

lemma measurable_neg_log_norm : Measurable fun x : ℂ => -Real.log ‖x‖ :=
  (Real.measurable_log.comp measurable_norm).neg

lemma hasLevelDatum_pairing {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) : HasLevelDatum (.pairing φ) := by
  have hφi := integrable_of_isTestFunction hφ
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have hlog : Integrable (fun x => φ x * Real.log ‖x‖) :=
    (integrable_mul_log_norm_sub hφ 0).congr (Eventually.of_forall fun x => by simp)
  refine ⟨ℂ, inferInstance, volume, inferInstance, φ, fun x => -Real.log ‖x‖, hφm, measurable_neg_log_norm, hφi,
    ?_, fun F => ?_⟩
  · refine (hφi.abs.add hlog.abs).mono' (hφm.mul (measurable_const.add
      measurable_neg_log_norm.abs)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |Real.log ‖x‖|)]
    simp only [Pi.add_apply, abs_mul]
    nlinarith [abs_nonneg (φ x), abs_nonneg (Real.log ‖x‖)]
  · show ∫ x, φ x * F ‖x‖ = ∫ x, φ x * F (Real.exp (-(-Real.log ‖x‖)))
    refine integral_congr_ae ((ae_ne 0).mono fun x hx => ?_)
    simp only [neg_neg, Real.exp_log (norm_pos_iff.2 hx)]

lemma circleMap_eq_zero_subset (z : ℂ) (ρ : ℝ) :
    {θ : ℝ | circleMap z ρ θ = 0} ⊆ {θ : ℝ | circleMap 0 ρ θ = -z} := fun θ hθ => by
  change circleMap z ρ θ = 0 at hθ
  change circleMap 0 ρ θ = -z
  simp only [circleMap, zero_add] at hθ ⊢
  linear_combination hθ

lemma hasLevelDatum_circle {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : HasLevelDatum (.circle ρ z) := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hcm : Continuous fun θ => circleMap z ρ θ := continuous_circleMap z ρ
  have hsm : Measurable fun θ : ℝ => -Real.log ‖circleMap z ρ θ‖ :=
    measurable_neg_log_norm.comp hcm.measurable
  have hlogi : IntegrableOn (fun θ => Real.log ‖circleMap z ρ θ - 0‖) (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 (circleIntegrable_log_norm_sub_const (a := 0) (c := z) ρ)
  refine ⟨ℝ, inferInstance, volume.restrict (Ioc 0 (2 * Real.pi)), inferInstance, fun _ => (2 * Real.pi)⁻¹,
    fun θ => -Real.log ‖circleMap z ρ θ‖, measurable_const, hsm, integrable_const _, ?_, fun F => ?_⟩
  · refine (((integrable_const (1 : ℝ)).add hlogi.abs).const_mul (2 * Real.pi)⁻¹).congr
      (Eventually.of_forall fun θ => ?_)
    simp [abs_neg]
  · show Real.circleAverage (fun x => F ‖x‖) z ρ = ∫ θ in Ioc 0 (2 * Real.pi),
      (2 * Real.pi)⁻¹ * F (Real.exp (-(-Real.log ‖circleMap z ρ θ‖)))
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le h2π, smul_eq_mul, ← integral_const_mul]
    have hnull := ((countable_circleMap_eq hρ.ne' (-z)).mono (circleMap_eq_zero_subset z ρ)).measure_zero
      (volume : Measure ℝ)
    refine integral_congr_ae (ae_restrict_of_ae ((measure_eq_zero_iff_ae_notMem.1 hnull).mono fun θ hθ => ?_))
    simp only [neg_neg, Real.exp_log (norm_pos_iff.2 hθ)]

lemma hasLevelDatum {o : GFFObservable} (ho : o.IsAdmissible) : HasLevelDatum o := by
  cases o with
  | pairing φ => exact hasLevelDatum_pairing ho
  | circle r z => exact hasLevelDatum_circle ho z

/-! ## Bounds on the radial covariance -/

lemma log_max_one_exp_neg (u : ℝ) : Real.log (max (Real.exp (-u)) 1) = max (-u) 0 := by
  rcases le_total u 0 with h | h
  · rw [max_eq_left (Real.one_le_exp_iff.2 (by linarith)), Real.log_exp, max_eq_left (by linarith)]
  · rw [max_eq_right (Real.exp_le_one_iff.2 (by linarith)), Real.log_one, max_eq_right (by linarith)]

lemma radialCov_self_exp_neg (u : ℝ) : radialCov (Real.exp (-u)) (Real.exp (-u)) = |u| := by
  rw [radialCov, max_self, Real.log_exp, log_max_one_exp_neg]
  rcases le_total u 0 with h | h
  · rw [max_eq_left (by linarith), abs_of_nonpos h]
    ring
  · rw [max_eq_right (by linarith), abs_of_nonneg h]
    ring

lemma abs_radialCov_exp_neg_le (r u : ℝ) :
    |radialCov r (Real.exp (-u))| ≤ (2 + 2 * |Real.log r|) * (1 + |u|) := by
  have h1 : |Real.log (max (Real.exp (-u)) 1)| ≤ |u| := by
    rw [log_max_one_exp_neg]
    rcases le_total u 0 with h | h
    · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos h]
    · rw [max_eq_right (by linarith), abs_zero]
      exact abs_nonneg u
  have h2 : |Real.log (max r 1)| ≤ |Real.log r| := by
    rcases le_total r 1 with h | h
    · rw [max_eq_right h, Real.log_one, abs_zero]
      exact abs_nonneg _
    · rw [max_eq_left h]
  have h3 : |Real.log (max r (Real.exp (-u)))| ≤ |Real.log r| + |u| := by
    rcases le_total r (Real.exp (-u)) with h | h
    · rw [max_eq_right h, Real.log_exp, abs_neg]
      linarith [abs_nonneg (Real.log r)]
    · rw [max_eq_left h]
      linarith [abs_nonneg u]
  rw [radialCov]
  calc |Real.log (max (Real.exp (-u)) 1) + Real.log (max r 1) - Real.log (max r (Real.exp (-u)))|
      ≤ |Real.log (max (Real.exp (-u)) 1)| + |Real.log (max r 1)| + |Real.log (max r (Real.exp (-u)))| :=
        (abs_sub _ _).trans (by linarith [abs_add_le (Real.log (max (Real.exp (-u)) 1)) (Real.log (max r 1))])
    _ ≤ (2 + 2 * |Real.log r|) * (1 + |u|) := by
        nlinarith [abs_nonneg u, abs_nonneg (Real.log r), mul_nonneg (abs_nonneg u) (abs_nonneg (Real.log r))]

end MatedCRT.Field.ConeRadial
