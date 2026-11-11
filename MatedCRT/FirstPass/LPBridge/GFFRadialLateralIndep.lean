import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.FirstPass.LPBridge.WholePlaneGFFLateral
import MatedCRT.FirstPass.LPBridge.LateralGaussian
import MatedCRT.Proofs.Field.ConeGaussianClosure

/-!
# The radial and lateral parts of a whole-plane GFF are independent

Statement: `MatedCRT.ConeMeanZeroRestriction.GFFRadialLateralIndep` (the whole-plane analogue of the independence
in Definition 2.1 of the paper; Duplantier-Sheffield, Berestycki-Powell). The proof is in Lean only.

Strategy. Write `X_s = h_s(0)` for the radial circle averages and `G(x) = h_{|x|}(0)`. A lateral observable is
`L_o = o - Rad_o`, with `Rad_o = ∫ φ(x) G(x) dx` (pairings) or `Rad_o = avg_{∂B_r(z)} G` (circles). The radial
family and the lateral family are jointly Gaussian (each `Rad_o` lies in the `L²`-closure of the Gaussian space of
observables) and uncorrelated, hence independent (`IsGaussianProcess.indepFun_of_covariance_eq_zero`).
The covariances are computed from Newton's identity `circleAverage_wholePlaneCov`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open HarmonicBalls MatedCRT.WholePlaneGFFLateral

namespace MatedCRT.ConeMeanZeroRestriction

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The covariance `Cov(h(x), h_s(0))` of the whole-plane GFF averaged over the circle `∂B_s(0)`:
`log max(|x|,1) + log max(s,1) - log max(s,|x|)` (Newton's identity for the logarithm). -/
def cW (x : ℂ) (s : ℝ) : ℝ := Real.log (max ‖x‖ 1) + Real.log (max s 1) - Real.log (max s ‖x‖)

lemma circleAverage_wholePlaneCov' {s : ℝ} (hs : 0 < s) (x : ℂ) :
    Real.circleAverage (fun w : ℂ => wholePlaneCov x w) 0 s = cW x s :=
  circleAverage_wholePlaneCov hs x

lemma wholePlaneGFFCov_circle_circle_eq {t s : ℝ} (hs : 0 < s) :
    wholePlaneGFFCov (.circle t 0) (.circle s 0) = Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  congr 1
  funext x
  exact circleAverage_wholePlaneCov' hs x

lemma wholePlaneGFFCov_pairing_circle_eq (φ : ℂ → ℝ) {s : ℝ} (hs : 0 < s) :
    wholePlaneGFFCov (.pairing φ) (.circle s 0) = ∫ x, φ x * cW x s := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  congr 1
  funext x
  rw [circleAverage_wholePlaneCov' hs x]

lemma wholePlaneGFFCov_circle_circle_centre_eq (z : ℂ) {r s : ℝ} (hs : 0 < s) :
    wholePlaneGFFCov (.circle r z) (.circle s 0) = Real.circleAverage (fun x : ℂ => cW x s) z r := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  congr 1
  funext x
  rw [circleAverage_wholePlaneCov' hs x]

/-- `cW` depends only on the modulus of its first argument. -/
lemma circleAverage_cW_sphere {t : ℝ} (ht : 0 < t) (x : ℂ) (s : ℝ) (hx : ‖x‖ = t) :
    Real.circleAverage (fun y : ℂ => cW y s) 0 t = cW x s := by
  have hf : Set.EqOn (fun y : ℂ => cW y s) (fun _ => cW x s) (Metric.sphere (0 : ℂ) |t|) := by
    intro y hy
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos ht] at hy
    show cW y s = cW x s
    unfold cW
    rw [hy, hx]
  rw [Real.circleAverage_congr_sphere hf, Real.circleAverage_const]

/-- Radial covariances: `Cov(h_t(0), h_s(0)) = avg_{∂B_t(0)} cW · s`. -/
lemma covariance_radial_radial (h : IsWholePlaneGFF P hC hcirc) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    covariance (fun ω => hcirc ω t 0) (fun ω => hcirc ω s 0) P =
      Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
  have := h.covariance_eq (.circle t 0) (.circle s 0) ht hs
  rw [← wholePlaneGFFCov_circle_circle_eq hs]
  exact this

end

end MatedCRT.ConeMeanZeroRestriction

namespace MatedCRT.ConeMeanZeroRestriction

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

lemma covariance_symm' (X Y : Ω → ℝ) (P : Measure Ω) :
    covariance X Y P = covariance Y X P := by
  simp only [covariance, mul_comm]

/-- Expectation of a product with a centred circle average: `E[h_s(0) h_t(0)] = avg_{∂B_t(0)} cW · s`. -/
lemma integral_circle_mul_circle_centred (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * hcirc ω t 0 ∂P = Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
  have hX : MemLp (fun ω => hcirc ω s 0) 2 P := memLp_two_circle h hs 0
  have hY : MemLp (fun ω => hcirc ω t 0) 2 P := memLp_two_circle h ht 0
  have hYc : ∫ ω, hcirc ω t 0 ∂P = 0 := h.integral_eq_zero (.circle t 0) ht
  have hcov : covariance (fun ω => hcirc ω s 0) (fun ω => hcirc ω t 0) P =
      ∫ ω, hcirc ω s 0 * hcirc ω t 0 ∂P :=
    covariance_eq_integral_of_mean_zero hYc (hY.integrable one_le_two) (hX.integrable_mul hY)
  rw [← hcov, covariance_symm', covariance_radial_radial h ht hs]
