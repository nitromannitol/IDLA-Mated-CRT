import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.LPStaging.Bonanno.WholePlaneLateral
import MatedCRT.LPStaging.Bonanno.RadialPointIntegrals
import MatedCRT.FirstPass.LPBridge.WholePlaneGFFLateral
import MatedCRT.FirstPass.LPBridge.LateralGaussian
import MatedCRT.Proofs.Field.ConeGaussianClosure
import MatedCRT.Proofs.Field.ConeLevelIntegrable

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

open MeasureTheory ProbabilityTheory Filter Topology Set Real
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
  calc ∫ ω, hcirc ω s 0 * hcirc ω t 0 ∂P = ∫ ω, hcirc ω t 0 * hcirc ω s 0 ∂P := by
        congr 1
        funext ω
        exact mul_comm _ _
    _ = Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 s) 0 t :=
        MatedCRT.WholePlaneGFFLateral.integral_circle_mul_circle h ht hs
    _ = Real.circleAverage (fun x : ℂ => cW x s) 0 t := by
        congr 1
        funext x
        exact circleAverage_wholePlaneCov' hs x

lemma radialPoint_fst_of_ne {x : ℂ} (hx : x ≠ 0) : ((radialPoint x).1 : ℝ) = ‖x‖ :=
  LatticeProb.radialPoint_fst_of_ne hx

lemma radialPoint_snd (x : ℂ) : (radialPoint x).2 = 0 :=
  LatticeProb.radialPoint_snd x

/-- Pointwise covariance of a radial circle average with the radial part at `x ≠ 0`. -/
lemma integral_mul_radialPoint (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {x : ℂ} (hx : x ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) ∂P = cW x s :=
  LatticeProb.RadialPointIntegrals.integral_mul_radialPoint hFae
    (fun _ ht => integral_circle_mul_circle_centred h ht hs) hx

/-- Fubini for the radial pairing: `E[h_s(0) ∫ φ(x) h_{|x|}(0) dx] = ∫ φ(x) cW x s dx`. -/
lemma integral_circle_mul_radialIntegral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P = ∫ x, φ x * cW x s := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P := memLp_two_circle h hs 0
  have hint := MatedCRT.WholePlaneGFFLateral.integrable_radial_mul h hF hFae hφ hZm hZ rfl
  exact LatticeProb.RadialPointIntegrals.integral_circle_mul_radialIntegral (Z := fun ω => hcirc ω s 0)
    (s := s) hFae hint (fun _ hx => integral_mul_radialPoint h hFae hx hs)

lemma two_log_max_sub_log {u : ℝ} (hu : 0 < u) :
    2 * Real.log (max u 1) - Real.log u = |Real.log u| :=
  LatticeProb.RadialPointIntegrals.two_log_max_sub_log hu

/-- The second moment of a radial circle average: `E[h_{|x|}(0)²] = |log |x||` for `x ≠ 0`. -/
lemma integral_sq_radialPoint (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {x : ℂ} (hx : x ≠ 0) :
    ∫ ω, F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) ^ 2 ∂P = |Real.log ‖x‖| := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [MatedCRT.WholePlaneGFFLateral.integral_sq_radialPoint h hFae hx]
  exact two_log_max_sub_log hpos

/-- The zero set of `θ ↦ z + r e^{iθ}` is countable, hence null for Lebesgue measure. -/
lemma circleMap_ne_zero_ae {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))), circleMap z r θ ≠ 0 :=
  LatticeProb.RadialPointIntegrals.circleMap_ne_zero_ae hr

/-- The logarithm of the modulus of a circle has integrable absolute value (Mathlib's circle integrability). -/
lemma integrable_abs_log_circleMap (z : ℂ) (r : ℝ) :
    Integrable (fun θ : ℝ => |Real.log ‖circleMap z r θ‖|)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
  LatticeProb.RadialPointIntegrals.integrable_abs_log_circleMap z r

lemma abs_mul_le_sq_add_sq_div_two (a b : ℝ) : ‖a * b‖ ≤ (a ^ 2 + b ^ 2) / 2 :=
  LatticeProb.RadialPointIntegrals.abs_mul_le_sq_add_sq_div_two a b

/-- Integrability of `(ω, θ) ↦ Z(ω) · F(ω, radial point of e^{iθ}-circle)` against `P ⊗ dθ` on `(0, 2π]`
for an `L²` variable `Z`: the radial factor has `E[F²] = |log|z+re^{iθ}||`, which is circle integrable. -/
lemma integrable_mul_radialPoint_circle (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : MemLp Z 2 P) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : Ω × ℝ =>
        Z q.1 * F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2)))
      (P.prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))) := by
  have hFL2 : ∀ x : ℂ, x ≠ 0 →
      MemLp (fun ω => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) 2 P := by
    intro x hx
    refine (memLp_two_circle h (norm_pos_iff.2 hx) 0).ae_eq ?_
    filter_upwards [hFae] with ω hω
    rw [hω, radialPoint_fst_of_ne hx, radialPoint_snd]
  exact LatticeProb.RadialPointIntegrals.integrable_mul_radialPoint_circle hF hZm hZ hFL2
    (fun _ hx => integral_sq_radialPoint h hFae hx) z hr

/-- Fubini for the radial circle average: `E[h_s(0) · avg_{∂B_r(z)} h_{|·|}(0)] = avg_{∂B_r(z)} cW · s`. -/
lemma integral_circle_mul_circleAverage (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hcirc ω s 0 * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r ∂P =
      Real.circleAverage (fun x : ℂ => cW x s) z r := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P := memLp_two_circle h hs 0
  have hint := integrable_mul_radialPoint_circle h hF hFae hZm hZ z hr
  exact LatticeProb.RadialPointIntegrals.integral_circle_mul_circleAverage (Z := fun ω => hcirc ω s 0)
    (s := s) hr hFae hint (fun _ hx => integral_mul_radialPoint h hFae hx hs)

end

/-! ## Covariances of the radial circle averages with the lateral observables -/

section RadialLateralCov

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Admissible observables of a whole-plane GFF are square integrable. -/
lemma memLp_two_observable (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    (o : GFFObservable) (ho : o.IsAdmissible) :
    MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨o, ho⟩).memLp_two

/-- The covariance of two admissible observables, as the expectation of their product. -/
lemma integral_mul_observable (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    (o o' : GFFObservable) (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    ∫ ω, o.eval (hC ω) (hcirc ω) * o'.eval (hC ω) (hcirc ω) ∂P = wholePlaneGFFCov o o' := by
  have hX := memLp_two_observable h o ho
  have hY := memLp_two_observable h o' ho'
  rw [← h.covariance_eq o o' ho ho']
  exact (covariance_eq_integral_of_mean_zero (h.integral_eq_zero o' ho') (hY.integrable one_le_two)
    (hX.integrable_mul hY)).symm

lemma integral_pairing_mul_circle_cW (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, hC ω φ * hcirc ω s 0 ∂P = ∫ x, φ x * cW x s := by
  rw [MatedCRT.WholePlaneGFFLateral.integral_pairing_mul_circle h hφ hs]
  congr 1
  funext x
  rw [circleAverage_wholePlaneCov' hs x]

lemma integral_circle_mul_circle_centre (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    ∫ ω, hcirc ω r z * hcirc ω s 0 ∂P = Real.circleAverage (fun x : ℂ => cW x s) z r :=
  (integral_mul_observable h (GFFObservable.circle r z) (GFFObservable.circle s 0) hr hs).trans
    (wholePlaneGFFCov_circle_circle_centre_eq z hs)

lemma integrable_circle_mul_radialIntegral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun ω => hcirc ω s 0 * ∫ x, φ x * hcirc ω ‖x‖ 0) P := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hint := MatedCRT.WholePlaneGFFLateral.integrable_radial_mul h hF hFae hφ hZm hZ rfl
  refine hint.integral_prod_left.congr ?_
  filter_upwards [MatedCRT.WholePlaneGFFLateral.ae_radialIntegral_eq hFae φ] with ω hω
  rw [integral_mul_const, ← hω]
  ring

lemma integrable_circle_mul_circleAverage (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    Integrable (fun ω => hcirc ω s 0 * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) P := by
  have hZm : Measurable (fun ω => hcirc ω s 0) := h.measurable_circle s 0 hs
  have hZ : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hint := integrable_mul_radialPoint_circle h hF hFae hZm hZ z hr
  refine (hint.integral_prod_left.const_mul (2 * π)⁻¹).congr ?_
  filter_upwards [hFae] with ω hω
  have step1 : ∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0 =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
        F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) := by
    apply integral_congr_ae
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
  simp only [Real.circleAverage, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [integral_const_mul, ← step1]
  ring

lemma covariance_circle_pairing_lateral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {s : ℝ} (hs : 0 < s) :
    covariance (fun ω => hcirc ω s 0) (fun ω => hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) P = 0 := by
  have hX : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hmean : ∫ ω, hcirc ω s 0 ∂P = 0 := h.integral_eq_zero (GFFObservable.circle s 0) hs
  have hA : MemLp (fun ω => hC ω φ) 2 P := memLp_two_observable h (GFFObservable.pairing φ) hφ
  have hB := integrable_circle_mul_radialIntegral h hF hFae hφ hs
  have hAX : Integrable (fun ω => hC ω φ * hcirc ω s 0) P := hA.integrable_mul hX
  have hfun : (fun ω => (hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω s 0) =
      fun ω => hC ω φ * hcirc ω s 0 - hcirc ω s 0 * ∫ x, φ x * hcirc ω ‖x‖ 0 := by
    funext ω
    ring
  have hint : Integrable (fun ω => (hC ω φ - ∫ x, φ x * hcirc ω ‖x‖ 0) * hcirc ω s 0) P := by
    rw [hfun]
    exact hAX.sub hB
  rw [covariance_symm', covariance_eq_integral_of_mean_zero hmean (hX.integrable one_le_two) hint,
    hfun, integral_sub hAX hB, integral_pairing_mul_circle_cW h hφ hs,
    integral_circle_mul_radialIntegral h hF hFae hφ hs, sub_self]

lemma covariance_circle_circle_lateral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) (z : ℂ) :
    covariance (fun ω => hcirc ω s 0)
      (fun ω => hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) P = 0 := by
  have hX : MemLp (fun ω => hcirc ω s 0) 2 P :=
    memLp_two_observable h (GFFObservable.circle s 0) hs
  have hmean : ∫ ω, hcirc ω s 0 ∂P = 0 := h.integral_eq_zero (GFFObservable.circle s 0) hs
  have hC' : MemLp (fun ω => hcirc ω r z) 2 P :=
    memLp_two_observable h (GFFObservable.circle r z) hr
  have hCX : Integrable (fun ω => hcirc ω r z * hcirc ω s 0) P := hC'.integrable_mul hX
  have hAX := integrable_circle_mul_circleAverage h hF hFae hr hs (z := z)
  have hfun : (fun ω => (hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) *
      hcirc ω s 0) = fun ω => hcirc ω r z * hcirc ω s 0 -
        hcirc ω s 0 * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r := by
    funext ω
    ring
  have hint : Integrable (fun ω => (hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) *
      hcirc ω s 0) P := by
    rw [hfun]
    exact hCX.sub hAX
  rw [covariance_symm', covariance_eq_integral_of_mean_zero hmean (hX.integrable one_le_two) hint,
    hfun, integral_sub hCX hAX, integral_circle_mul_circle_centre h hr hs z,
    integral_circle_mul_circleAverage h hF hFae hr hs, sub_self]

/-- The covariance of a radial circle average `h_s(0)` with every admissible lateral observable vanishes:
the radial and lateral parts of a whole-plane GFF are uncorrelated (Duplantier-Sheffield, Section 3). -/
lemma covariance_circle_lateralEval (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {s : ℝ} (hs : 0 < s) (o : GFFObservable.Admissible) :
    covariance (fun ω => hcirc ω s 0) (fun ω => lateralEval (hC ω) (hcirc ω) o.1) P = 0 := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact covariance_circle_pairing_lateral h hF hFae ho hs
  | circle r z => exact covariance_circle_circle_lateral h hF hFae ho hs z

end RadialLateralCov

/-! ## Gaussian closure: an orthogonality criterion in `L²(P)` -/

section HilbertClosure

open MatedCRT.Field.GaussClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Orthogonal projection criterion.** Let `G i` and `g` be square integrable. If `E[Z g] = 0` for every
square integrable `Z` with `E[Z G i] = 0` for all `i`, then `g` is an almost sure limit of elements of the linear
span of the family `G` (projection in the Hilbert space `L²(P)` onto the closed span of `G`). -/
lemma isAeLimitOf_span_of_orthogonal [IsProbabilityMeasure P] {ι : Type*} (G : ι → Ω → ℝ)
    (hG : ∀ i, MemLp (G i) 2 P) (g : Ω → ℝ) (hg : MemLp g 2 P)
    (horth : ∀ Z : Ω → ℝ, MemLp Z 2 P → (∀ i, ∫ ω, Z ω * G i ω ∂P = 0) → ∫ ω, Z ω * g ω ∂P = 0) :
    IsAeLimitOf P (Submodule.span ℝ (Set.range G) : Set (Ω → ℝ)) g := by
  classical
  let V : Submodule ℝ (Lp ℝ 2 P) := Submodule.span ℝ (Set.range fun i => (hG i).toLp (G i))
  have hgen : ∀ i, (hG i).toLp (G i) ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  -- representatives of the elements of `V` by genuine functions in the span
  have hrep : ∀ u ∈ V, ∃ w ∈ Submodule.span ℝ (Set.range G), w =ᵐ[P] (u : Ω → ℝ) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨G i, Submodule.subset_span ⟨i, rfl⟩, (hG i).coeFn_toLp.symm⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by filter_upwards with ω; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w₁, hw₁, e₁⟩ := hx
      obtain ⟨w₂, hw₂, e₂⟩ := hy
      exact ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, by
        filter_upwards [e₁, e₂, Lp.coeFn_add x y] with ω h1 h2 h3
        simp only [Pi.add_apply, h1, h2, h3]⟩
    | smul c x _ hx =>
      obtain ⟨w, hw, e⟩ := hx
      exact ⟨c • w, Submodule.smul_mem _ c hw, by
        filter_upwards [e, Lp.coeFn_smul c x] with ω h1 h2
        simp only [Pi.smul_apply, smul_eq_mul, h1, h2]⟩
  -- a test element `u` of `V^⊥` annihilates `g`
  have hperp : ∀ u ∈ Vᗮ, ∫ ω, (u : Ω → ℝ) ω * g ω ∂P = 0 := by
    intro u hu
    refine horth u (Lp.memLp u) fun i => ?_
    have h1 := (Submodule.mem_orthogonal _ _).1 hu _ (hgen i)
    rw [MeasureTheory.L2.inner_def] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [(hG i).coeFn_toLp] with ω hω
    simp [hω, mul_comm]
  -- `g` lies in the double orthogonal complement, that is in the closure of `V`
  have hgL : hg.toLp g ∈ Vᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [MeasureTheory.L2.inner_def]
    have hE : ∫ a, inner ℝ (u a) (hg.toLp g a) ∂P = ∫ ω, (u : Ω → ℝ) ω * g ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp] with ω hω
      simp [hω, mul_comm]
    rw [hE]
    exact hperp u hu
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hgL
  have hcl : hg.toLp g ∈ closure (V : Set (Lp ℝ 2 P)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hgL
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  choose w hw he using fun n => hrep (u n) (hu n)
  refine ⟨fun i => w (ns i), fun i => hw (ns i), ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, w (ns i) ω = (u (ns i) : Ω → ℝ) ω := ae_all_iff.2 fun i => he (ns i)
  filter_upwards [hae, hall, hg.coeFn_toLp] with ω h1 h2 h3
  have hfun : (fun n => w (ns n) ω) = fun n => (u (ns n) : Ω → ℝ) ω := funext fun n => h2 n
  rw [hfun, ← h3]
  exact h1

end HilbertClosure

/-! ## The radial integrals `∫ φ(x) h_{|x|}(0) dx` are Gaussian limits -/

section RadialIntegralGaussian

open MatedCRT.Field.GaussClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The radial integral `ω ↦ ∫ φ(x) h_{|x|}(0) dx` of a test function is square integrable. -/
lemma memLp_two_radialIntegral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    MemLp (fun ω => ∫ x, φ x * hcirc ω ‖x‖ 0) 2 P := by
  have htr := MatedCRT.WholePlaneGFFLateral.integrable_radial_triple h hF hFae hφ hφ
  have hsq : ∀ ω, ∫ p : ℂ × ℂ, φ p.1 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint p.1) *
      (φ p.2 * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint p.2)) ∂(volume.prod volume) =
      (∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) ^ 2 := by
    intro ω
    rw [sq]
    exact integral_prod_mul (fun x => φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x))
      (fun y => φ y * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint y))
  have hQ : Integrable (fun ω => (∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) ^ 2) P :=
    htr.integral_prod_left.congr (ae_of_all _ fun ω => hsq ω)
  have hjoint : Measurable (fun q : Ω × ℂ => F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint q.2)) :=
    (measurable_circle_version_joint hF).comp
      (measurable_fst.prodMk (MatedCRT.WholePlaneGFFLateral.measurable_radialPoint.comp measurable_snd))
  have hmeas : Measurable (fun q : Ω × ℂ => φ q.2 * F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint q.2)) :=
    (hφ.1.continuous.measurable.comp measurable_snd).mul hjoint
  have hRadm : AEStronglyMeasurable (fun ω => ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) P :=
    (hmeas.stronglyMeasurable.integral_prod_right (f := fun ω x =>
      φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x))).aestronglyMeasurable
  have hmem : MemLp (fun ω => ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) 2 P := by
    rw [memLp_two_iff_integrable_sq hRadm]
    exact hQ
  have hae : (fun ω => ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) =ᵐ[P]
      (fun ω => ∫ x, φ x * hcirc ω ‖x‖ 0) := by
    filter_upwards [MatedCRT.WholePlaneGFFLateral.ae_radialIntegral_eq hFae φ] with ω hω
    exact hω.symm
  exact hmem.ae_eq hae

/-- Orthogonality of the radial integral: if `Z ∈ L²(P)` is orthogonal to the circle averages
`h_{|x|}(0)` for `x ≠ 0`, then `E[Z ∫ φ(x) h_{|x|}(0) dx] = 0`. -/
lemma integral_mul_radialIntegral_eq_zero (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (horth : ∀ x : ℂ, x ≠ 0 → ∫ ω, Z ω * hcirc ω ‖x‖ 0 ∂P = 0) :
    ∫ ω, Z ω * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P = 0 := by
  obtain ⟨Z', hZ'm, hZZ'⟩ : ∃ Z' : Ω → ℝ, Measurable Z' ∧ Z =ᵐ[P] Z' :=
    ⟨hZ.aestronglyMeasurable.mk Z, hZ.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hZ.aestronglyMeasurable.ae_eq_mk⟩
  have hZ' : MemLp Z' 2 P := hZ.ae_eq hZZ'
  have horth' : ∀ x : ℂ, x ≠ 0 → ∫ ω, Z' ω * hcirc ω ‖x‖ 0 ∂P = 0 := fun x hx => by
    rw [← horth x hx]
    refine integral_congr_ae ?_
    filter_upwards [hZZ'] with ω hω
    rw [hω]
  have hint := MatedCRT.WholePlaneGFFLateral.integrable_radial_mul h hF hFae hφ hZ'm hZ' rfl
  have step1 : (fun ω => Z' ω * ∫ x, φ x * hcirc ω ‖x‖ 0) =ᵐ[P]
      (fun ω => ∫ x, Z' ω * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x))) := by
    filter_upwards [MatedCRT.WholePlaneGFFLateral.ae_radialIntegral_eq hFae φ] with ω hω
    rw [hω, integral_const_mul]
  have hI : Integrable (Function.uncurry fun (ω : Ω) (x : ℂ) =>
      Z' ω * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x))) (P.prod volume) := by
    refine hint.congr (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry]
    ring
  have hae0 : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) :=
    compl_mem_ae_iff.2 (measure_singleton 0)
  have hzero : ∀ᵐ x ∂(volume : Measure ℂ),
      ∫ ω, Z' ω * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) ∂P = 0 := by
    filter_upwards [hae0] with x hx
    have hx0 : x ≠ 0 := Set.mem_compl_singleton_iff.1 hx
    calc ∫ ω, Z' ω * (φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) ∂P
        = ∫ ω, φ x * (Z' ω * hcirc ω ‖x‖ 0) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hFae] with ω hω
          rw [hω, radialPoint_fst_of_ne hx0, radialPoint_snd]
          ring
      _ = 0 := by rw [integral_const_mul, horth' x hx0, mul_zero]
  have main : ∫ ω, Z' ω * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P = 0 := by
    rw [integral_congr_ae step1, integral_integral_swap hI, integral_congr_ae hzero]
    simp
  calc ∫ ω, Z ω * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P
      = ∫ ω, Z' ω * (∫ x, φ x * hcirc ω ‖x‖ 0) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hZZ'] with ω hω
        rw [hω]
    _ = 0 := main

/-- The radial integral is an almost sure limit of elements of the span of the admissible observables
(Hilbert projection criterion of `isAeLimitOf_span_of_orthogonal`). -/
lemma isAeLimitOf_radialIntegral (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    IsAeLimitOf P (Submodule.span ℝ (Set.range fun o : GFFObservable.Admissible =>
      fun ω => o.1.eval (hC ω) (hcirc ω)) : Set (Ω → ℝ))
      (fun ω => ∫ x, φ x * hcirc ω ‖x‖ 0) := by
  refine isAeLimitOf_span_of_orthogonal (fun o : GFFObservable.Admissible =>
      fun ω => o.1.eval (hC ω) (hcirc ω)) (fun o => memLp_two_observable h o.1 o.2) _
    (memLp_two_radialIntegral h hF hFae hφ) fun Z hZ hperp => ?_
  exact integral_mul_radialIntegral_eq_zero h hF hFae hφ hZ fun x hx =>
    hperp ⟨GFFObservable.circle ‖x‖ 0, norm_pos_iff.2 hx⟩

end RadialIntegralGaussian

/-! ## The circle averages `avg_{∂B_r(z)} h_{|·|}(0)` are square integrable Gaussian limits -/

section CircleAverageL2

open MatedCRT.Field.GaussClosure

/-- Cauchy-Schwarz for a finite measure: `(∫ f)² ≤ μ(T) ∫ f²`. -/
lemma sq_integral_le_measureReal_mul_integral_sq {T : Type*} [MeasurableSpace T] (μ : Measure T)
    [IsFiniteMeasure μ] {f : T → ℝ} (hf1 : Integrable f μ) (hf2 : Integrable (fun t => f t ^ 2) μ) :
    (∫ t, f t ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ t, f t ^ 2 ∂μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have hm : 0 < μ.real Set.univ := by
    have hu : μ Set.univ ≠ 0 := by rwa [Ne, Measure.measure_univ_eq_zero]
    rw [Measure.real]
    exact ENNReal.toReal_pos hu (measure_ne_top _ _)
  set m := μ.real Set.univ with hmdef
  set a := ∫ t, f t ∂μ with ha
  set S := ∫ t, f t ^ 2 ∂μ with hS
  set c := a / m with hc
  have hcm : c * m = a := by rw [hc, div_mul_cancel₀ a hm.ne']
  have hnonneg : 0 ≤ ∫ t, (f t - c) ^ 2 ∂μ := integral_nonneg fun t => sq_nonneg _
  have hA : Integrable (fun t => f t ^ 2 - 2 * c * f t) μ := hf2.sub (hf1.const_mul (2 * c))
  have hC2 : Integrable (fun _ : T => c ^ 2) μ := integrable_const _
  have hexp : ∫ t, (f t - c) ^ 2 ∂μ = S - 2 * c * a + c ^ 2 * m := by
    have e : (fun t => (f t - c) ^ 2) = fun t => (f t ^ 2 - 2 * c * f t) + c ^ 2 := by
      funext t
      ring
    rw [e, integral_add hA hC2, integral_sub hf2 (hf1.const_mul (2 * c)), integral_const_mul,
      integral_const, smul_eq_mul]
    ring
  have hc2 : c ^ 2 * m = c * a := by linear_combination c * hcm
  have h1 : 0 ≤ S - c * a := by linarith [hnonneg, hexp, hc2]
  have key : a ^ 2 = m * (c * a) := by linear_combination (-a) * hcm
  nlinarith [mul_nonneg hm.le h1, key]

/-- A jointly measurable family whose squares are jointly integrable: the integral against a finite measure is
square integrable (Cauchy-Schwarz and Fubini). -/
lemma memLp_two_integral_of_sq {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {P : Measure Ω}
    [IsProbabilityMeasure P] (μ : Measure T) [IsFiniteMeasure μ] {G : Ω → T → ℝ}
    (hG : Measurable (fun q : Ω × T => G q.1 q.2))
    (hsq : Integrable (fun q : Ω × T => G q.1 q.2 ^ 2) (P.prod μ)) :
    MemLp (fun ω => ∫ t, G ω t ∂μ) 2 P := by
  have hfm : AEStronglyMeasurable (fun ω => ∫ t, G ω t ∂μ) P :=
    (hG.stronglyMeasurable.integral_prod_right (ν := μ) (f := fun ω t => G ω t)).aestronglyMeasurable
  have hint2 : Integrable (fun ω => ∫ t, G ω t ^ 2 ∂μ) P := hsq.integral_prod_left
  rw [memLp_two_iff_integrable_sq hfm]
  refine Integrable.mono' (hint2.const_mul (μ.real Set.univ)) (hfm.pow 2) ?_
  filter_upwards [hsq.prod_right_ae] with ω hω
  have hG1 : Integrable (G ω) μ := by
    have hmeas : AEStronglyMeasurable (G ω) μ :=
      (hG.comp measurable_prodMk_left).aestronglyMeasurable
    exact ((memLp_two_iff_integrable_sq hmeas).2 hω).integrable one_le_two
  show ‖(∫ t, G ω t ∂μ) ^ 2‖ ≤ μ.real Set.univ * ∫ t, G ω t ^ 2 ∂μ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_integral_le_measureReal_mul_integral_sq μ (f := G ω) hG1 hω

end CircleAverageL2

section CircleAverageGaussian

open MatedCRT.Field.GaussClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The circle average `avg_{∂B_r(z)} h_{|·|}(0)` of the radial process is square integrable. -/
lemma memLp_two_circleAverage (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) :
    MemLp (fun ω => Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) 2 P := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)) with hμ
  have hjoint : Measurable (fun q : Ω × ℝ =>
      F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2))) :=
    (measurable_circle_version_joint hF).comp (measurable_fst.prodMk
      (MatedCRT.WholePlaneGFFLateral.measurable_radialPoint.comp
        ((continuous_circleMap z r).measurable.comp measurable_snd)))
  have hsq : Integrable (fun q : Ω × ℝ =>
      F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2)) ^ 2) (P.prod μ) := by
    refine (integrable_prod_iff' (hjoint.pow_const 2).aestronglyMeasurable).2 ⟨ae_of_all _ fun θ => ?_, ?_⟩
    · exact (MatedCRT.WholePlaneGFFLateral.memLp_two_radialPoint h hFae (circleMap z r θ)).integrable_sq
    · refine (integrable_abs_log_circleMap z r).congr ?_
      filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
      rw [← integral_sq_radialPoint h hFae hθ]
      congr 1
      funext ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have key := memLp_two_integral_of_sq (P := P) μ (G := fun ω θ =>
    F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))) hjoint hsq
  refine (key.const_mul (2 * π)⁻¹).ae_eq ?_
  filter_upwards [hFae] with ω hω
  simp only [Real.circleAverage, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
  rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]

/-- Orthogonality of the circle average: if `Z ∈ L²(P)` is orthogonal to `h_{|x|}(0)` for `x ≠ 0`, then
`E[Z avg_{∂B_r(z)} h_{|·|}(0)] = 0`. -/
lemma integral_mul_circleAverage_eq_zero (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (horth : ∀ x : ℂ, x ≠ 0 → ∫ ω, Z ω * hcirc ω ‖x‖ 0 ∂P = 0) :
    ∫ ω, Z ω * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r ∂P = 0 := by
  obtain ⟨Z', hZ'm, hZZ'⟩ : ∃ Z' : Ω → ℝ, Measurable Z' ∧ Z =ᵐ[P] Z' :=
    ⟨hZ.aestronglyMeasurable.mk Z, hZ.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hZ.aestronglyMeasurable.ae_eq_mk⟩
  have hZ' : MemLp Z' 2 P := hZ.ae_eq hZZ'
  have horth' : ∀ x : ℂ, x ≠ 0 → ∫ ω, Z' ω * hcirc ω ‖x‖ 0 ∂P = 0 := fun x hx => by
    rw [← horth x hx]
    refine integral_congr_ae ?_
    filter_upwards [hZZ'] with ω hω
    rw [hω]
  have hint := integrable_mul_radialPoint_circle h hF hFae hZ'm hZ' z hr
  have hae0 : ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π))),
      ∫ ω, Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) ∂P = 0 := by
    filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
    calc ∫ ω, Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) ∂P
        = ∫ ω, Z' ω * hcirc ω ‖circleMap z r θ‖ 0 ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hFae] with ω hω
          rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
      _ = 0 := horth' _ hθ
  have hswap := integral_integral_swap (μ := P) (ν := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))
    (f := fun ω θ => Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))) hint
  have step1 : ∀ᵐ ω ∂P, Z' ω * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r =
      (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
        Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) := by
    filter_upwards [hFae] with ω hω
    have e2 : ∫ θ in Set.Ioc (0 : ℝ) (2 * π), F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))
        = ∫ θ in Set.Ioc (0 : ℝ) (2 * π), hcirc ω ‖circleMap z r θ‖ 0 := by
      refine integral_congr_ae ?_
      filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
      rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]
    simp only [Real.circleAverage, smul_eq_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π), integral_const_mul]
    rw [e2]
    ring
  calc ∫ ω, Z ω * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r ∂P
      = ∫ ω, Z' ω * Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r ∂P :=
        integral_congr_ae (hZZ'.mono fun ω hω => by simp only [hω])
    _ = ∫ ω, ((2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))) ∂P :=
        integral_congr_ae step1
    _ = (2 * π)⁻¹ * ∫ ω, (∫ θ in Set.Ioc (0 : ℝ) (2 * π),
          Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ))) ∂P := by
        rw [integral_const_mul]
    _ = (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π), ∫ ω,
          Z' ω * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) ∂P := by
        rw [hswap]
    _ = 0 := by
        rw [integral_congr_ae hae0]
        simp

/-- The circle average `avg_{∂B_r(z)} h_{|·|}(0)` is an almost sure limit of observables. -/
lemma isAeLimitOf_circleAverage (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {z : ℂ} {r : ℝ} (hr : 0 < r) :
    IsAeLimitOf P (Submodule.span ℝ (Set.range fun o : GFFObservable.Admissible =>
      fun ω => o.1.eval (hC ω) (hcirc ω)) : Set (Ω → ℝ))
      (fun ω => Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r) :=
  isAeLimitOf_span_of_orthogonal (fun o : GFFObservable.Admissible =>
      fun ω => o.1.eval (hC ω) (hcirc ω)) (fun o => memLp_two_observable h o.1 o.2) _
    (memLp_two_circleAverage h hF hFae hr) fun _ hZ hperp =>
      integral_mul_circleAverage_eq_zero h hF hFae hr hZ fun x hx =>
        hperp ⟨GFFObservable.circle ‖x‖ 0, norm_pos_iff.2 hx⟩

end CircleAverageGaussian

/-! ## Assembly: the radial and lateral parts of a whole-plane GFF are independent -/

section Assembly

open MatedCRT.Field.GaussClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The lateral observables computed from a jointly measurable version `F` of the circle averages of the radial
part `x ↦ h_{|x|}(0)`: `(h, φ) - ∫ φ(x) h_{|x|}(0) dx` and `h_r(z) - avg_{∂B_r(z)} h_{|·|}(0)`. -/
noncomputable def lateralEvalF (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (F : Ω → C(CircleParameter, ℝ)) : GFFObservable → Ω → ℝ
  | .pairing φ => fun ω => hC ω φ -
      ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)
  | .circle r z => fun ω => hcirc ω r z -
      Real.circleAverage (fun x => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) z r

omit [MeasurableSpace Ω] in
/-- On the good set where `F` is the circle average version, the circle averages of `F` and of `h_{|·|}(0)` agree. -/
lemma circleAverage_eq_of_good {F : Ω → C(CircleParameter, ℝ)} {ω : Ω}
    (hω : ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2) {z : ℂ} {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r =
      Real.circleAverage (fun x => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) z r := by
  simp only [Real.circleAverage, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [circleMap_ne_zero_ae hr] with θ hθ
  rw [hω, radialPoint_fst_of_ne hθ, radialPoint_snd]

omit [MeasurableSpace Ω] in
lemma lateralEvalF_eq {F : Ω → C(CircleParameter, ℝ)} {ω : Ω}
    (hω : ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2) (o : GFFObservable.Admissible) :
    lateralEvalF hC hcirc F o.1 ω = lateralEval (hC ω) (hcirc ω) o.1 := by
  obtain ⟨o, ho⟩ := o
  have hae0 : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx
    exact Set.mem_compl_singleton_iff.1 hx
  cases o with
  | pairing φ =>
    have e : ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x) =
        ∫ x, φ x * hcirc ω ‖x‖ 0 := by
      refine integral_congr_ae (μ := (volume : Measure ℂ)) ?_
      filter_upwards [hae0] with x hx
      rw [hω, radialPoint_fst_of_ne hx, radialPoint_snd]
    simp only [lateralEvalF, lateralEval, e]
  | circle r z =>
    have hr : 0 < r := ho
    simp only [lateralEvalF, lateralEval, circleAverage_eq_of_good hω hr]

lemma measurable_radialIntegralF {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Measurable (fun ω => ∫ x, φ x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) :=
  MatedCRT.WholePlaneGFFLateral.measurable_radialIntegral_version hF hφ.1.continuous.measurable

lemma measurable_circleAverageF {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F) (z : ℂ) (r : ℝ) :
    Measurable (fun ω => Real.circleAverage (fun x => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) z r) := by
  have hjoint : Measurable (fun q : Ω × ℝ =>
      F q.1 (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r q.2))) :=
    (measurable_circle_version_joint hF).comp (measurable_fst.prodMk
      (MatedCRT.WholePlaneGFFLateral.measurable_radialPoint.comp
        ((continuous_circleMap z r).measurable.comp measurable_snd)))
  have hint := (hjoint.stronglyMeasurable.integral_prod_right
    (ν := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (2 * π)))
    (f := fun ω θ => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)))).measurable
  have e : (fun ω => Real.circleAverage (fun x => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) z r) =
      fun ω => (2 * π)⁻¹ * ∫ θ in Set.Ioc (0 : ℝ) (2 * π),
        F ω (MatedCRT.WholePlaneGFFLateral.radialPoint (circleMap z r θ)) := by
    funext ω
    simp only [Real.circleAverage, smul_eq_mul, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [e]
  exact hint.const_mul _

lemma lateralEvalF_ae_eq {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2) :
    (fun ω (o : GFFObservable.Admissible) => lateralEvalF hC hcirc F o.1 ω) =ᵐ[P]
      (fun ω => lateralProcess (hC ω) (hcirc ω)) := by
  filter_upwards [hFae] with ω hω
  funext o
  exact lateralEvalF_eq hω o

lemma isAeLimitOf_congr_ae' {M : Set (Ω → ℝ)} {Z Z' : Ω → ℝ} (hZ : IsAeLimitOf P M Z)
    (hZZ' : Z =ᵐ[P] Z') : IsAeLimitOf P M Z' := by
  obtain ⟨Y, hY, hlim⟩ := hZ
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hlim, hZZ'] with ω h1 h2
  rw [← h2]
  exact h1

lemma measurable_observable' (h : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible) :
    Measurable (fun ω => o.1.eval (hC ω) (hcirc ω)) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

lemma measurable_lateralEvalF (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F) (o : GFFObservable.Admissible) :
    Measurable (lateralEvalF hC hcirc F o.1) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact (h.measurable_pairing φ ho).sub (measurable_radialIntegralF hF ho)
  | circle r z => exact (h.measurable_circle r z ho).sub (measurable_circleAverageF hF z r)

end Assembly

/-! ## The independence theorem -/

section Final

open MatedCRT.Field.GaussClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Each radial circle average is uncorrelated with the lateral observables computed from `F`. -/
lemma covariance_radial_lateralF (h : IsWholePlaneGFF P hC hcirc) [IsProbabilityMeasure P]
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω (p.1 : ℝ) p.2)
    {s : ℝ} (hs : 0 < s) (o : GFFObservable.Admissible) :
    covariance (fun ω => hcirc ω s 0) (lateralEvalF hC hcirc F o.1) P = 0 := by
  have hae : (fun ω => lateralEvalF hC hcirc F o.1 ω) =ᵐ[P]
      (fun ω => lateralEval (hC ω) (hcirc ω) o.1) := by
    filter_upwards [hFae] with ω hω
    exact lateralEvalF_eq hω o
  exact (covariance_congr_ae (Filter.EventuallyEq.refl _ _) hae).trans
    (covariance_circle_lateralEval h hF hFae hs o)

/-- **Radial-lateral independence for whole-plane GFFs** (the content of `GFFRadialLateralIndep`). -/
theorem gffRadialLateralIndep_aux [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) :
    IndepFun (fun ω => radialProcess (hcirc ω)) (fun ω => lateralProcess (hC ω) (hcirc ω)) P := by
  obtain ⟨F, hF, hFae⟩ := exists_ae_circle_version h
  let X : ℝ≥0 ⊕ ℝ≥0 → Ω → ℝ := Sum.elim (fun t ω => hcirc ω (Real.exp (-(t : ℝ))) 0)
    (fun s ω => hcirc ω (Real.exp (s : ℝ)) 0)
  let M0 : Submodule ℝ (Ω → ℝ) :=
    Submodule.span ℝ (Set.range fun o : GFFObservable.Admissible => fun ω => o.1.eval (hC ω) (hcirc ω))
  have hM0 : IsCentredGaussianSpace P (M0 : Set (Ω → ℝ)) :=
    isCentredGaussianSpace_span h.isGaussianProcess (measurable_observable' h)
      (fun o => h.integral_eq_zero o.1 o.2)
  let RadF : {φ : ℂ → ℝ // IsTestFunction Set.univ φ} → Ω → ℝ :=
    fun φ ω => ∫ x, φ.1 x * F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)
  let AvgF : {p : ℝ × ℂ // 0 < p.1} → Ω → ℝ :=
    fun p ω => Real.circleAverage (fun x => F ω (MatedCRT.WholePlaneGFFLateral.radialPoint x)) p.1.2 p.1.1
  have hRadm : ∀ φ, Measurable (RadF φ) := fun φ => measurable_radialIntegralF hF φ.2
  have hAvgm : ∀ p, Measurable (AvgF p) := fun p => measurable_circleAverageF hF p.1.2 p.1.1
  have hRadA : ∀ φ, IsAeLimitOf P (M0 : Set (Ω → ℝ)) (RadF φ) := by
    intro φ
    refine isAeLimitOf_congr_ae' (isAeLimitOf_radialIntegral h hF hFae φ.2) ?_
    filter_upwards [ae_radialIntegral_eq hFae φ.1] with ω hω
    exact hω
  have hAvgA : ∀ p, IsAeLimitOf P (M0 : Set (Ω → ℝ)) (AvgF p) := by
    intro p
    refine isAeLimitOf_congr_ae' (isAeLimitOf_circleAverage h hF hFae (z := p.1.2) (r := p.1.1) p.2) ?_
    filter_upwards [hFae] with ω hω
    exact circleAverage_eq_of_good (z := p.1.2) hω p.2
  let Mone : Submodule ℝ (Ω → ℝ) := M0 ⊔ Submodule.span ℝ (Set.range RadF)
  have hM1 : IsCentredGaussianSpace P (Mone : Set (Ω → ℝ)) :=
    isCentredGaussianSpace_sup_span_range hM0 RadF hRadm hRadA
  have hAvgA' : ∀ p, IsAeLimitOf P (Mone : Set (Ω → ℝ)) (AvgF p) := fun p =>
    IsAeLimitOf.mono (SetLike.coe_subset_coe.2 le_sup_left) (hAvgA p)
  let Mall : Submodule ℝ (Ω → ℝ) := Mone ⊔ Submodule.span ℝ (Set.range AvgF)
  have hMall : IsCentredGaussianSpace P (Mall : Set (Ω → ℝ)) :=
    isCentredGaussianSpace_sup_span_range hM1 AvgF hAvgm hAvgA'
  have hM0_le : M0 ≤ Mall := (le_sup_left : M0 ≤ Mone).trans (le_sup_left : Mone ≤ Mall)
  have hmemM0 : ∀ o : GFFObservable.Admissible,
      (fun ω => o.1.eval (hC ω) (hcirc ω)) ∈ Mall :=
    fun o => hM0_le (Submodule.subset_span ⟨o, rfl⟩)
  have hmemRad : ∀ φ, RadF φ ∈ Mall := fun φ =>
    (le_sup_right : Submodule.span ℝ (Set.range RadF) ≤ Mone).trans le_sup_left
      (Submodule.subset_span ⟨φ, rfl⟩)
  have hmemAvg : ∀ p, AvgF p ∈ Mall := fun p =>
    (le_sup_right : Submodule.span ℝ (Set.range AvgF) ≤ Mall) (Submodule.subset_span ⟨p, rfl⟩)
  have hYmem : ∀ o : GFFObservable.Admissible, lateralEvalF hC hcirc F o.1 ∈ Mall := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ =>
      have e : lateralEvalF hC hcirc F (GFFObservable.pairing φ) =
          (fun ω => (GFFObservable.pairing φ).eval (hC ω) (hcirc ω)) - RadF ⟨φ, ho⟩ := by
        funext ω
        rfl
      rw [e]
      exact Submodule.sub_mem _ (hmemM0 ⟨GFFObservable.pairing φ, ho⟩) (hmemRad ⟨φ, ho⟩)
    | circle r z =>
      have hr : 0 < r := ho
      have e : lateralEvalF hC hcirc F (GFFObservable.circle r z) =
          (fun ω => (GFFObservable.circle r z).eval (hC ω) (hcirc ω)) - AvgF ⟨(r, z), hr⟩ := by
        funext ω
        rfl
      rw [e]
      exact Submodule.sub_mem _ (hmemM0 ⟨GFFObservable.circle r z, hr⟩) (hmemAvg ⟨(r, z), hr⟩)
  have hW : ∀ t, Sum.elim X (fun o : GFFObservable.Admissible => lateralEvalF hC hcirc F o.1) t ∈ Mall := by
    rintro ((t | s) | o)
    · exact hmemM0 ⟨GFFObservable.circle (Real.exp (-(t : ℝ))) 0, Real.exp_pos _⟩
    · exact hmemM0 ⟨GFFObservable.circle (Real.exp (s : ℝ)) 0, Real.exp_pos _⟩
    · exact hYmem o
  have hG : IsGaussianProcess
      (Sum.elim X (fun o : GFFObservable.Admissible => lateralEvalF hC hcirc F o.1)) P :=
    isGaussianProcess_of_isCentredGaussianSpace hMall hW
  have hXm : ∀ t : ℝ≥0 ⊕ ℝ≥0, Measurable (X t) := by
    rintro (t | s)
    · exact h.measurable_circle _ 0 (Real.exp_pos _)
    · exact h.measurable_circle _ 0 (Real.exp_pos _)
  have hcov : ∀ (t : ℝ≥0 ⊕ ℝ≥0) (o : GFFObservable.Admissible),
      covariance (X t) (lateralEvalF hC hcirc F o.1) P = 0 := by
    rintro (t | s) o
    · exact covariance_radial_lateralF h hF hFae (Real.exp_pos (-(t : ℝ))) o
    · exact covariance_radial_lateralF h hF hFae (Real.exp_pos (s : ℝ)) o
  have hI := IsGaussianProcess.indepFun_of_covariance_eq_zero hG (fun t => (hXm t).aemeasurable)
    (fun o => (measurable_lateralEvalF h hF o).aemeasurable) hcov
  let A : (ℝ≥0 ⊕ ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
    fun f => (fun t => f (Sum.inl t), fun s => f (Sum.inr s))
  have hA : Measurable A :=
    Measurable.prodMk (measurable_pi_iff.mpr fun t => measurable_pi_apply (Sum.inl t))
      (measurable_pi_iff.mpr fun s => measurable_pi_apply (Sum.inr s))
  have hI2 := hI.comp hA measurable_id
  exact hI2.congr (ae_of_all _ fun ω => rfl) (lateralEvalF_ae_eq hFae)

end Final

theorem gffRadialLateralIndep_holds : GFFRadialLateralIndep := by
  intro Ω _ P hC hcirc hP h
  exact gffRadialLateralIndep_aux h

end MatedCRT.ConeMeanZeroRestriction
