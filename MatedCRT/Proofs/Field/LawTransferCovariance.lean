import MatedCRT.Proofs.Field.Translation
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# Covariance of the whole-plane GFF modulo constants

We compare the covariance kernel in Harmonic Balls with Leonardo Bonanno's `logCov`.
The normalization terms vanish against test functions of integral zero. The logarithmic
integrability used here is supplied by Bonanno's `LQGMetric.MarkovWeyl2.integrable_logConv`.
-/

namespace MatedCRT.Field

open MeasureTheory ProbabilityTheory Set HarmonicBalls

/-- The Harmonic Balls covariance agrees with the logarithmic covariance on mean-zero
test functions, which is the covariance used by Leonardo Bonanno's GFF. -/
theorem wholePlaneGFFCov_eq_logCov {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (hψ : IsTestFunction univ ψ) (hφ0 : ∫ x, φ x = 0) (hψ0 : ∫ y, ψ y = 0) :
    wholePlaneGFFCov (.pairing φ) (.pairing ψ) = LQGMetric.logCov φ ψ := by
  have hψl : Integrable (fun y => ψ y * logMaxOne y) :=
    (hψ.1.continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport hψ.2.1.mul_right
  have inner (x : ℂ) : (∫ y, ψ y * wholePlaneCov x y) =
      (∫ y, ψ y * (-Real.log ‖x - y‖)) + ∫ y, ψ y * logMaxOne y := by
    have ha : Integrable (fun y => ψ y * logMaxOne x) := (integrable_of_isTestFunction hψ).mul_const _
    have hb : Integrable (fun y => ψ y * (-Real.log ‖x - y‖)) := by
      refine (integrable_mul_log_norm_sub hψ x).neg.congr ?_
      filter_upwards with y
      simp
    have hc : (fun y => ψ y * wholePlaneCov x y) =ᵐ[volume]
        fun y => (ψ y * logMaxOne x + ψ y * logMaxOne y) + ψ y * (-Real.log ‖x - y‖) := by
      filter_upwards [ae_ne x] with y hy
      rw [wholePlaneCov_eq (Ne.symm hy)]
      ring
    rw [integral_congr_ae hc]
    calc
      _ = ((∫ y, ψ y * logMaxOne x) + ∫ y, ψ y * logMaxOne y) +
          ∫ y, ψ y * (-Real.log ‖x - y‖) := by
            have hi := integral_add (ha.add hψl) hb
            change (∫ y, ψ y * logMaxOne x + ψ y * logMaxOne y + ψ y * (-Real.log ‖x - y‖)) = _ at hi
            rw [hi]
            congr 1
            exact integral_add ha hψl
      _ = _ := by rw [integral_mul_const, hψ0]; simp [add_comm]
  change (∫ x, φ x * ∫ y, ψ y * wholePlaneCov x y) =
    ∫ x, ∫ y, φ x * (-Real.log ‖x - y‖) * ψ y
  simp_rw [inner]
  rw [integral_mul_add_const (integrable_of_isTestFunction hφ) hφ0]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- A distribution-valued test function is a Harmonic Balls test function. -/
lemma isTestFunction_of_TestC (φ : LQGMetric.TestC) : IsTestFunction univ φ :=
  ⟨φ.contDiff, φ.hasCompactSupport, subset_univ _⟩

/-- The mean-zero pairings of the two GFF interfaces have the same joint law. -/
theorem map_pairings_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (h : Ω' → LQGMetric.DistC)
    (hwp : IsWholePlaneGFF P hC hcirc) (hwp' : LQGMetric.IsWholePlaneGFF h P') :
    P.map (fun ω (φ : LQGMetric.TestC0) => hC ω φ.1) =
      P'.map (fun ω (φ : LQGMetric.TestC0) => h ω φ.1) := by
  let : IsProbabilityMeasure P := hwp.isProbabilityMeasure
  let : IsProbabilityMeasure P' := hwp'.gaussian.isProbabilityMeasure
  let f : LQGMetric.TestC0 → GFFObservable.Admissible :=
    fun φ => ⟨.pairing φ.1, isTestFunction_of_TestC φ.1⟩
  have hX : IsGaussianProcess (fun (φ : LQGMetric.TestC0) ω => hC ω φ.1) P :=
    hwp.isGaussianProcess.comp_right f
  refine map_eq_of_covariance hX hwp'.gaussian
    (fun φ => hwp.measurable_pairing φ.1 (isTestFunction_of_TestC φ.1))
    (fun φ => (LQGMetric.GFFInv.measurable_pair φ.1).comp hwp'.measurable)
    (fun φ => hwp.integral_eq_zero (.pairing φ.1) (isTestFunction_of_TestC φ.1))
    hwp'.centered ?_
  intro φ ψ
  have hc : covariance (fun ω => hC ω φ.1) (fun ω => hC ω ψ.1) P =
      wholePlaneGFFCov (.pairing φ.1) (.pairing ψ.1) :=
    hwp.covariance_eq (.pairing φ.1) (.pairing ψ.1)
      (isTestFunction_of_TestC φ.1) (isTestFunction_of_TestC ψ.1)
  rw [hc, hwp'.covariance_eq]
  exact wholePlaneGFFCov_eq_logCov (isTestFunction_of_TestC φ.1)
    (isTestFunction_of_TestC ψ.1) φ.2 ψ.2


end MatedCRT.Field
