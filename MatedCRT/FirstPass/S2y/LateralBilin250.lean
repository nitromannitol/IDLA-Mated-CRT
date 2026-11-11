import MatedCRT.FirstPass.S2y.LateralCov250
import MatedCRT.Proofs.Field.WholePlaneLateralCov
import MatedCRT.Proofs.Field.ConeRadialCov

/-!
# GFF facts for the lateral pairing

For a whole-plane GFF `(hC, hcirc)`: the jointly measurable radial version `radialVersion` agrees almost surely with the
circle average `h_r(0)` at each radius `r > 0`; circle averages at `0` are square integrable with variance
`radialCov r r`; the pairings have covariance `wholePlaneCov`; and `E|h_r(0)| ≤ 1 + 3|log r|`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The radial version agrees a.s. with the circle average `h_r(0)` at each radius `r > 0`. -/
lemma radialVersion_ae_eq (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, MatedCRT.CirclePairing.radialVersion hcirc ω r = hcirc ω r 0 := by
  filter_upwards [h.ae_continuousOn_circle] with ω hω
  exact MatedCRT.CirclePairing.radialVersion_eq (MatedCRT.CirclePairing.continuousOn_radial hω) hr

/-- A circle average at the origin of positive radius is square integrable. -/
lemma memLp_circle_zero (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    MemLp (fun ω => hcirc ω r 0) 2 P :=
  (MatedCRT.Field.wpSpace_gaussian h).memLp (Submodule.subset_span ⟨⟨GFFObservable.circle r 0, hr⟩, rfl⟩)

/-- The circle averages at the origin are centred. -/
lemma integral_circle_zero (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∫ ω, hcirc ω r 0 ∂P = 0 :=
  h.integral_eq_zero (.circle r 0) hr

/-- The second moment of a circle average at the origin is `radialCov r r` (the variance, Duplantier-Sheffield,
Section 3.1). -/
lemma integral_sq_circle_zero [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∫ ω, (hcirc ω r 0) ^ 2 ∂P = MatedCRT.Field.ConeRadial.radialCov r r := by
  have hc : cov[fun ω => hcirc ω r 0, fun ω => hcirc ω r 0; P] = MatedCRT.Field.ConeRadial.radialCov r r :=
    MatedCRT.Field.ConeRadial.covariance_radial h hr hr
  have h0 := integral_circle_zero h hr
  rw [← hc]
  simp only [covariance, h0, sub_zero, sq]

/-- The covariance of two pairings with test functions is the double integral of `wholePlaneCov`. -/
lemma integral_mul_pairing [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {f g : ℂ → ℝ}
    (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
    ∫ ω, hC ω f * hC ω g ∂P = ∫ x, f x * ∫ y, g y * wholePlaneCov x y := by
  have hc : cov[fun ω => hC ω f, fun ω => hC ω g; P] = ∫ x, f x * ∫ y, g y * wholePlaneCov x y :=
    h.covariance_eq (.pairing f) (.pairing g) hf hg
  have h0f : ∫ ω, hC ω f ∂P = 0 := h.integral_eq_zero (.pairing f) hf
  have h0g : ∫ ω, hC ω g ∂P = 0 := h.integral_eq_zero (.pairing g) hg
  rw [← hc]
  simp only [covariance, h0f, h0g, sub_zero]

/-- `E|h_r(0)| ≤ 1 + 3|log r|` (from `E h_r(0)² = radialCov r r` and `|radialCov r r| ≤ 3|log r|`). -/
lemma integral_abs_circle_zero_le [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∫ ω, |hcirc ω r 0| ∂P ≤ 1 + 3 * |Real.log r| := by
  have hL2 := memLp_circle_zero h hr
  have hi1 : Integrable (fun ω => |hcirc ω r 0|) P := by
    simpa [Real.norm_eq_abs] using (MemLp.integrable one_le_two hL2).norm
  have hi2 : Integrable (fun ω => (hcirc ω r 0) ^ 2) P := hL2.integrable_sq
  have hpt : ∀ ω, |hcirc ω r 0| ≤ 1 + (hcirc ω r 0) ^ 2 := fun ω => by
    nlinarith [sq_abs (hcirc ω r 0), abs_nonneg (hcirc ω r 0), sq_nonneg (|hcirc ω r 0| - 1)]
  have hmono : ∫ ω, |hcirc ω r 0| ∂P ≤ ∫ ω, (1 + (hcirc ω r 0) ^ 2) ∂P :=
    integral_mono hi1 ((integrable_const _).add hi2) hpt
  simp only [integral_add (integrable_const _) hi2, integral_const, probReal_univ, smul_eq_mul, mul_one,
    integral_sq_circle_zero h hr] at hmono
  have hK : |MatedCRT.Field.ConeRadial.radialCov r r| ≤ 3 * |Real.log r| := by
    have hm : |Real.log (max r 1)| ≤ |Real.log r| := by
      have := abs_log_max_le r 1
      rwa [Real.log_one, abs_zero, add_zero] at this
    have e : MatedCRT.Field.ConeRadial.radialCov r r =
        Real.log (max r 1) + Real.log (max r 1) - Real.log r := by
      unfold MatedCRT.Field.ConeRadial.radialCov; rw [max_self]
    rw [e]
    calc |Real.log (max r 1) + Real.log (max r 1) - Real.log r|
        ≤ |Real.log (max r 1) + Real.log (max r 1)| + |Real.log r| := abs_sub _ _
      _ ≤ (|Real.log (max r 1)| + |Real.log (max r 1)|) + |Real.log r| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 3 * |Real.log r| := by linarith
  have : MatedCRT.Field.ConeRadial.radialCov r r ≤ 3 * |Real.log r| := le_trans (le_abs_self _) hK
  linarith

end MatedCRT.LQGMeasure
