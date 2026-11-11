import MatedCRT.Proofs.Measurability.ConePairing
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVerPot
import LatticeProb.Bonanno.LQGMetric.Field.CircleBumpRadial

/-!
# Circle-average differences of the quantum cone are determined by the field modulo additive constant

`circleAverageModConstStep : CircleAverageModConstStep` (the field input, Lemma 6.4): for the `γ`-quantum
cone `h`, an open `U ⊆ B_1` and circles whose closed discs lie in `U`, the difference `h_ε(x) - h_s(y)` is a.s. equal to
a random variable measurable for `σ(h|_U)` modulo additive constant (`modConstSigma hC U`).

Route (DS11 Section 3.1; Definition 2.1 of the quantum cone):
* whole-plane GFF: the pairings are a.s. linear, `(h, a - b) = (h, a) - (h, b)` (`ae_pairing_sub`), since
  `E[((h, a - b) - (h, a) + (h, b))²] = 0` by the bilinearity of the covariance `∫ a(x) ∫ b(y) K(x, y) dy dx`
  (`covPot`, written with Bonanno's logarithmic potential);
* quantum cone: the same for test functions vanishing near `0`, through the lateral law (`ae_pairing_sub_of_isQuantumCone`);
* with the mollified circle measures `φ_k = circBump k z r` (Bonanno) and `CirclePairing.ae_tendsto_circBump_of_isQuantumCone`,
  `(h, φ_k(x, ε) - φ_k(y, s)) → h_ε(x) - h_s(y)` a.s. when `|x| ≠ ε`, `|y| ≠ s`; the test function `φ_k(x, ε) - φ_k(y, s)`
  has mean zero and support in `U` for large `k`, hence its pairing is `modConstSigma hC U`-measurable;
* general radii: `ε_n ↑ ε`, `s_n ↑ s` avoiding `|x|`, `|y|`, and the a.s. continuity of the circle averages.
-/

namespace MatedCRT
namespace Field
namespace ConeCircle

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped Real ENNReal
open _root_.HarmonicBalls
open LQGMetric LQGMetric.CircleAvg MatedCRT.CirclePairing

/-! ## Test functions -/

lemma coe_sub_apply (a b : TestC) (y : ℂ) : (a - b : TestC) y = a y - b y :=
  LatticeProb.CirclePairing.coe_sub_apply a b y

lemma coe_sub_fun (a b : TestC) : ((a - b : TestC) : ℂ → ℝ) = ⇑a - ⇑b :=
  LatticeProb.CirclePairing.coe_sub_fun a b

lemma isTestFunction_testC (a : TestC) : HarmonicBalls.IsTestFunction univ ⇑a :=
  ⟨a.contDiff, a.hasCompactSupport, subset_univ _⟩

/-! ## The covariance of two pairings -/

/-- `∫ b(y) K(x, y) dy = (∫ b) a(x) + ∫ b a + L_b(x)` for a test function `b`. -/
lemma integral_test_mul_wholePlaneCov (b : TestC) (x : ℂ) :
    ∫ y, b y * HarmonicBalls.wholePlaneCov x y =
      (∫ y, b y) * logMaxOne x + (∫ y, b y * logMaxOne y) + logPot b x := by
  have hae : (fun y => b y * HarmonicBalls.wholePlaneCov x y) =ᵐ[volume]
      fun y => b y * logMaxOne x + b y * logMaxOne y + -Real.log ‖x - y‖ * b y := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton x)] with y hy
    have hxy : x ≠ y := fun h => hy (by rw [h]; rfl)
    rw [wholePlaneCov_eq hxy]
    ring
  have h1 : Integrable fun y => b y * logMaxOne x := (integrable_testC _).mul_const _
  have h2 : Integrable fun y => b y * logMaxOne y :=
    (b.continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  have h12 : Integrable fun y => b y * logMaxOne x + b y * logMaxOne y := h1.add h2
  rw [integral_congr_ae hae, integral_add h12 (integrable_log_mul_test _ x), integral_add h1 h2,
    integral_mul_const]
  rfl

/-- The covariance potential `F_b(x) = ∫ b(y) K(x, y) dy` of a test function `b`, in closed form. -/
noncomputable def covPot (b : TestC) (x : ℂ) : ℝ :=
  (∫ y, b y) * logMaxOne x + (∫ y, b y * logMaxOne y) + logPot b x

lemma continuous_covPot (b : TestC) : Continuous (covPot b) := by
  have hL : Continuous (logPot b) := (MarkovGermVer.contDiff_logPot b).continuous
  exact ((continuous_const.mul continuous_logMaxOne).add continuous_const).add hL

lemma integrable_mul_covPot (a b : TestC) : Integrable fun x => a x * covPot b x :=
  (a.continuous.mul (continuous_covPot b)).integrable_of_hasCompactSupport a.hasCompactSupport.mul_right

lemma covPot_sub (a b : TestC) : covPot (a - b) = covPot a - covPot b := by
  funext x
  have ha := integrable_testC a
  have hb := integrable_testC b
  have ha' : Integrable fun y => a y * logMaxOne y :=
    (a.continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport a.hasCompactSupport.mul_right
  have hb' : Integrable fun y => b y * logMaxOne y :=
    (b.continuous.mul continuous_logMaxOne).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  have h1 : ∫ y, (a - b : TestC) y = (∫ y, a y) - ∫ y, b y := by
    simp only [coe_sub_apply]
    exact integral_sub ha hb
  have h2 : ∫ y, (a - b : TestC) y * logMaxOne y = (∫ y, a y * logMaxOne y) - ∫ y, b y * logMaxOne y := by
    rw [← integral_sub ha' hb']
    congr 1
    funext y
    rw [coe_sub_apply]
    ring
  have h3 : logPot (a - b : TestC) x = logPot a x - logPot b x := by
    simp only [logPot]
    rw [← integral_sub (integrable_log_mul_test a x) (integrable_log_mul_test b x)]
    congr 1
    funext y
    rw [coe_sub_apply]
    ring
  simp only [covPot, Pi.sub_apply]
  rw [h1, h2, h3]
  ring

lemma wholePlaneGFFCov_pairing_eq (a b : TestC) :
    HarmonicBalls.wholePlaneGFFCov (.pairing a) (.pairing b) = ∫ x, a x * covPot b x := by
  simp only [HarmonicBalls.wholePlaneGFFCov, HarmonicBalls.GFFObservable.smear]
  simp_rw [integral_test_mul_wholePlaneCov]
  rfl

lemma cov_sub_left (a b c : TestC) :
    HarmonicBalls.wholePlaneGFFCov (.pairing ⇑(a - b)) (.pairing c) =
      HarmonicBalls.wholePlaneGFFCov (.pairing a) (.pairing c) -
        HarmonicBalls.wholePlaneGFFCov (.pairing b) (.pairing c) := by
  rw [wholePlaneGFFCov_pairing_eq, wholePlaneGFFCov_pairing_eq, wholePlaneGFFCov_pairing_eq,
    ← integral_sub (integrable_mul_covPot a c) (integrable_mul_covPot b c)]
  congr 1
  funext x
  rw [coe_sub_apply]
  ring

lemma cov_sub_right (a b c : TestC) :
    HarmonicBalls.wholePlaneGFFCov (.pairing c) (.pairing ⇑(a - b)) =
      HarmonicBalls.wholePlaneGFFCov (.pairing c) (.pairing a) -
        HarmonicBalls.wholePlaneGFFCov (.pairing c) (.pairing b) := by
  rw [wholePlaneGFFCov_pairing_eq, wholePlaneGFFCov_pairing_eq, wholePlaneGFFCov_pairing_eq,
    ← integral_sub (integrable_mul_covPot c a) (integrable_mul_covPot c b), covPot_sub]
  congr 1
  funext x
  simp only [Pi.sub_apply]
  ring

/-! ## Almost-sure linearity of the pairings of the whole-plane GFF -/

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

lemma integral_pairing_mul (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (a b : TestC) :
    ∫ ω, hC ω a * hC ω b ∂P = HarmonicBalls.wholePlaneGFFCov (.pairing a) (.pairing b) :=
  covariance_eval_eq_integral hG (o := .pairing a) (o' := .pairing b) (isTestFunction_testC a)
    (isTestFunction_testC b)

omit [IsProbabilityMeasure P] in
lemma integrable_pairing_mul (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (a b : TestC) :
    Integrable (fun ω => hC ω a * hC ω b) P :=
  (memLp_eval hG (o := .pairing a) (isTestFunction_testC a)).integrable_mul
    (memLp_eval hG (o := .pairing b) (isTestFunction_testC b))

lemma cov_symm (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (a b : TestC) :
    HarmonicBalls.wholePlaneGFFCov (.pairing b) (.pairing a) =
      HarmonicBalls.wholePlaneGFFCov (.pairing a) (.pairing b) := by
  rw [← integral_pairing_mul hG, ← integral_pairing_mul hG]
  congr 1
  funext ω
  ring

/-- **The pairings of the whole-plane GFF are a.s. linear**: `(h, a - b) = (h, a) - (h, b)` a.s. -/
theorem ae_pairing_sub (hG : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (a b : TestC) :
    ∀ᵐ ω ∂P, hC ω ⇑(a - b) = hC ω a - hC ω b := by
  set c := a - b with hc
  have iXX := integrable_pairing_mul hG c c
  have iYY := integrable_pairing_mul hG a a
  have iZZ := integrable_pairing_mul hG b b
  have iXY := (integrable_pairing_mul hG c a).const_mul 2
  have iXZ := (integrable_pairing_mul hG c b).const_mul 2
  have iYZ := (integrable_pairing_mul hG a b).const_mul 2
  have i1 : Integrable (fun ω => hC ω c * hC ω c + hC ω a * hC ω a) P := iXX.add iYY
  have i2 : Integrable (fun ω => hC ω c * hC ω c + hC ω a * hC ω a + hC ω b * hC ω b) P := i1.add iZZ
  have i3 : Integrable (fun ω => hC ω c * hC ω c + hC ω a * hC ω a + hC ω b * hC ω b -
      2 * (hC ω c * hC ω a)) P := i2.sub iXY
  have i4 : Integrable (fun ω => hC ω c * hC ω c + hC ω a * hC ω a + hC ω b * hC ω b -
      2 * (hC ω c * hC ω a) + 2 * (hC ω c * hC ω b)) P := i3.add iXZ
  have e : (fun ω => (hC ω c - hC ω a + hC ω b) ^ 2) = fun ω => hC ω c * hC ω c + hC ω a * hC ω a +
      hC ω b * hC ω b - 2 * (hC ω c * hC ω a) + 2 * (hC ω c * hC ω b) - 2 * (hC ω a * hC ω b) :=
    funext fun ω => by ring
  have hW : Integrable (fun ω => (hC ω c - hC ω a + hC ω b) ^ 2) P := by
    rw [e]
    exact i4.sub iYZ
  have hint : ∫ ω, (hC ω c - hC ω a + hC ω b) ^ 2 ∂P = 0 := by
    rw [e, integral_sub i4 iYZ, integral_add i3 iXZ, integral_sub i2 iXY, integral_add i1 iZZ,
      integral_add iXX iYY, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_pairing_mul hG, integral_pairing_mul hG, integral_pairing_mul hG, integral_pairing_mul hG,
      integral_pairing_mul hG, integral_pairing_mul hG, hc]
    simp only [cov_sub_left, cov_sub_right]
    rw [cov_symm hG a b]
    ring
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hW).1 hint
  filter_upwards [h0] with ω hω
  have h2 : (hC ω c - hC ω a + hC ω b) ^ 2 = 0 := hω
  have h3 : hC ω c - hC ω a + hC ω b = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
  linarith

end Gaussian

/-! ## Transfer to the quantum cone -/

lemma continuousOn_radial_ne {f : ℝ → ℂ → ℝ} (h : ContinuousOn (fun p : ℝ × ℂ => f p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun x : ℂ => f ‖x‖ 0) {x | x ≠ 0} :=
  LatticeProb.CirclePairing.continuousOn_radial_ne h

lemma integrable_mul_radial {R : ℂ → ℝ} (hR : ContinuousOn R {x | x ≠ 0}) (a : TestC)
    (ha : (a : ℂ → ℝ) =ᶠ[𝓝 0] 0) : Integrable fun x => a x * R x :=
  LatticeProb.CirclePairing.integrable_mul_radial hR a ha

lemma integral_sub_mul_radial {R : ℂ → ℝ} (hR : ContinuousOn R {x | x ≠ 0}) {a b : TestC}
    (ha : (a : ℂ → ℝ) =ᶠ[𝓝 0] 0) (hb : (b : ℂ → ℝ) =ᶠ[𝓝 0] 0) :
    ∫ x, (a - b : TestC) x * R x = (∫ x, a x * R x) - ∫ x, b x * R x :=
  LatticeProb.CirclePairing.integral_sub_mul_radial hR ha hb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **The pairings of the quantum cone are a.s. linear** on test functions vanishing near `0`, through the lateral law
of Definition 2.1. -/
theorem ae_pairing_sub_of_isQuantumCone {γ : ℝ} (hQ : IsQuantumCone γ P hC hcirc) {a b : TestC}
    (ha : (a : ℂ → ℝ) =ᶠ[𝓝 0] 0) (hb : (b : ℂ → ℝ) =ᶠ[𝓝 0] 0) :
    ∀ᵐ ω ∂P, hC ω ⇑(a - b) = hC ω a - hC ω b := by
  obtain ⟨Ω', _, P', hC', hcirc', hP', hG, hlaw⟩ := hQ.lateral_law
  have := hP'
  let pa : GFFObservable.Admissible := ⟨.pairing a, isTestFunction_testC a⟩
  let pb : GFFObservable.Admissible := ⟨.pairing b, isTestFunction_testC b⟩
  let pab : GFFObservable.Admissible := ⟨.pairing ⇑(a - b), isTestFunction_testC (a - b)⟩
  let E : Set (GFFObservable.Admissible → ℝ) := {f | f pab = f pa - f pb}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (measurable_pi_apply pab) ((measurable_pi_apply pa).sub (measurable_pi_apply pb))
  have hlat' := aemeasurable_lateralProcess (P := P') hG.measurable_pairing hG.measurable_circle
    hG.ae_continuousOn_circle
  have hlat := aemeasurable_lateralProcess (P := P) hQ.measurable_pairing hQ.measurable_circle
    hQ.ae_continuousOn_circle
  have hgff : ∀ᵐ ω' ∂P', lateralProcess (hC' ω') (hcirc' ω') ∈ E := by
    filter_upwards [ae_pairing_sub hG a b, hG.ae_continuousOn_circle] with ω' h1 h2
    show hC' ω' ⇑(a - b) - ∫ x, (a - b : TestC) x * hcirc' ω' ‖x‖ 0 =
      (hC' ω' a - ∫ x, a x * hcirc' ω' ‖x‖ 0) - (hC' ω' b - ∫ x, b x * hcirc' ω' ‖x‖ 0)
    rw [h1, integral_sub_mul_radial (continuousOn_radial_ne h2) ha hb]
    ring
  have hcone : ∀ᵐ ω ∂P, lateralProcess (hC ω) (hcirc ω) ∈ E := by
    have h := (ae_map_iff hlat' hE).2 hgff
    rw [← hlaw] at h
    exact (ae_map_iff hlat hE).1 h
  filter_upwards [hcone, hQ.ae_continuousOn_circle] with ω h1 h2
  have h1' : hC ω ⇑(a - b) - ∫ x, (a - b : TestC) x * hcirc ω ‖x‖ 0 =
      (hC ω a - ∫ x, a x * hcirc ω ‖x‖ 0) - (hC ω b - ∫ x, b x * hcirc ω ‖x‖ 0) := h1
  rw [integral_sub_mul_radial (continuousOn_radial_ne h2) ha hb] at h1'
  linarith

/-! ## Mollified circle measures -/

lemma circBump_eventuallyEq_zero {k : ℕ} {z : ℂ} {r : ℝ} (hr : 0 < r) (hk : (2 : ℝ)⁻¹ ^ k < |‖z‖ - r|) :
    (circBump k z r : ℂ → ℝ) =ᶠ[𝓝 0] 0 :=
  LatticeProb.CirclePairing.circBump_eventuallyEq_zero hr hk

lemma tsupport_circBump_subset_closedBall {k : ℕ} {z : ℂ} {r : ℝ} (hr : 0 < r) :
    tsupport (circBump k z r : ℂ → ℝ) ⊆ closedBall z (r + (2 : ℝ)⁻¹ ^ k) :=
  LatticeProb.CirclePairing.tsupport_circBump_subset_closedBall hr

/-- `(h, φ_k(x, ε) - φ_k(y, s)) → h_ε(x) - h_s(y)` a.s. for the quantum cone (`|x| ≠ ε`, `|y| ≠ s`). -/
theorem ae_tendsto_circBump_sub {γ : ℝ} (hQ : IsQuantumCone γ P hC hcirc) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    {x y : ℂ} (hx : ‖x‖ ≠ ε) (hy : ‖y‖ ≠ s) :
    ∀ᵐ ω ∂P, Tendsto (fun k => hC ω ⇑(circBump k x ε - circBump k y s)) atTop
      (𝓝 (hcirc ω ε x - hcirc ω s y)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (2 : ℝ)⁻¹ ^ K < min |‖x‖ - ε| |‖y‖ - s| :=
    exists_pow_lt_of_lt_one (lt_min (abs_pos.2 (sub_ne_zero.2 hx)) (abs_pos.2 (sub_ne_zero.2 hy))) (by norm_num)
  have hle : ∀ k : ℕ, (2 : ℝ)⁻¹ ^ (k + K) ≤ (2 : ℝ)⁻¹ ^ K := fun k =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hlin : ∀ k : ℕ, ∀ᵐ ω ∂P, hC ω ⇑(circBump (k + K) x ε - circBump (k + K) y s) =
      hC ω (circBump (k + K) x ε) - hC ω (circBump (k + K) y s) := fun k =>
    ae_pairing_sub_of_isQuantumCone hQ
      (circBump_eventuallyEq_zero hε ((hle k).trans_lt (hK.trans_le (min_le_left _ _))))
      (circBump_eventuallyEq_zero hs ((hle k).trans_lt (hK.trans_le (min_le_right _ _))))
  filter_upwards [ae_tendsto_circBump_of_isQuantumCone hQ hε hx, ae_tendsto_circBump_of_isQuantumCone hQ hs hy,
    ae_all_iff.2 hlin] with ω h1 h2 h3
  refine (tendsto_add_atTop_iff_nat K).1 ?_
  have h4 := ((tendsto_add_atTop_iff_nat K).2 h1).sub ((tendsto_add_atTop_iff_nat K).2 h2)
  exact h4.congr fun k => (h3 k).symm

/-! ## Measurability modulo additive constant -/

omit [MeasurableSpace Ω] in
lemma measurable_modConstSigma {U : Set ℂ} {φ : ℂ → ℝ} (hφ : HarmonicBalls.IsTestFunction U φ)
    (h0 : ∫ x, φ x = 0) : Measurable[modConstSigma hC U] fun ω => hC ω φ := by
  refine Measurable.of_comap_le ?_
  unfold modConstSigma
  exact le_iSup₂_of_le (f := fun (ψ : ℂ → ℝ) (_ : HarmonicBalls.IsTestFunction U ψ ∧ ∫ x, ψ x = 0) =>
    MeasurableSpace.comap (fun ω => hC ω ψ) inferInstance) φ ⟨hφ, h0⟩ le_rfl

/-- An a.s. limit of `m`-measurable real random variables is a.s. equal to an `m`-measurable one. -/
lemma exists_measurable_ae_eq_of_ae_tendsto (m : MeasurableSpace Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ k, Measurable[m] (f k)) (hfg : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (g ω))) :
    ∃ D : Ω → ℝ, Measurable[m] D ∧ g =ᵐ[P] D :=
  LatticeProb.CirclePairing.exists_measurable_ae_eq_of_ae_tendsto m hf hfg

lemma integral_circBump_sub (k : ℕ) (x y : ℂ) (ε s : ℝ) :
    ∫ w, (circBump k x ε - circBump k y s : TestC) w = 0 :=
  LatticeProb.CirclePairing.integral_circBump_sub k x y ε s

/-- The step at radii `ε' < ε`, `s' < s` avoiding `|x|`, `|y|`. -/
theorem exists_modConst_ae_eq_of_ne {γ : ℝ} (hQ : IsQuantumCone γ P hC hcirc) {U : Set ℂ} {ε s ε' s' : ℝ}
    {x y : ℂ} (hε' : 0 < ε') (hs' : 0 < s') (hεε : ε' < ε) (hss : s' < s) (hx : ‖x‖ ≠ ε') (hy : ‖y‖ ≠ s')
    (hxU : closedBall x ε ⊆ U) (hyU : closedBall y s ⊆ U) :
    ∃ D : Ω → ℝ, Measurable[modConstSigma hC U] D ∧ (fun ω => hcirc ω ε' x - hcirc ω s' y) =ᵐ[P] D := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (2 : ℝ)⁻¹ ^ K < min (ε - ε') (s - s') :=
    exists_pow_lt_of_lt_one (lt_min (by linarith) (by linarith)) (by norm_num)
  have hle : ∀ k : ℕ, (2 : ℝ)⁻¹ ^ (k + K) ≤ (2 : ℝ)⁻¹ ^ K := fun k =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  refine exists_measurable_ae_eq_of_ae_tendsto (modConstSigma hC U)
    (f := fun k ω => hC ω ⇑(circBump (k + K) x ε' - circBump (k + K) y s')) (fun k => ?_) ?_
  · refine measurable_modConstSigma ⟨(circBump (k + K) x ε' - circBump (k + K) y s').contDiff,
      (circBump (k + K) x ε' - circBump (k + K) y s').hasCompactSupport, ?_⟩ (integral_circBump_sub _ _ _ _ _)
    rw [coe_sub_fun]
    refine (tsupport_sub _ _).trans (union_subset ?_ ?_)
    · refine (tsupport_circBump_subset_closedBall hε').trans ((closedBall_subset_closedBall ?_).trans hxU)
      linarith [hle k, hK.trans_le (min_le_left _ _)]
    · refine (tsupport_circBump_subset_closedBall hs').trans ((closedBall_subset_closedBall ?_).trans hyU)
      linarith [hle k, hK.trans_le (min_le_right _ _)]
  · filter_upwards [ae_tendsto_circBump_sub hQ hε' hs' hx hy] with ω h
    exact (tendsto_add_atTop_iff_nat K).2 h

lemma tendsto_radius (ρ : ℝ) : Tendsto (fun n : ℕ => ρ * (1 - (2 : ℝ)⁻¹ ^ (n + 1))) atTop (𝓝 ρ) :=
  LatticeProb.CirclePairing.tendsto_radius ρ

lemma radius_pos_lt {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    0 < ρ * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ∧ ρ * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) < ρ :=
  LatticeProb.CirclePairing.radius_pos_lt hρ n

/-- **`CircleAverageModConstStep`** (the field input, Lemma 6.4): for the quantum cone, circle-average
differences over circles whose closed discs lie in an open `U ⊆ B_1` are a.s. `σ(h|_U)`-measurable modulo additive
constant. -/
theorem circleAverageModConstStep : CircleAverageModConstStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc hP hQ U hU hUB ε s x y hε hs hxU hyU
  have hne : ∀ᶠ n in atTop, ε * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ≠ ‖x‖ ∧ s * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ≠ ‖y‖ := by
    have h1 : ∀ᶠ n in atTop, ε * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ≠ ‖x‖ := by
      by_cases hx : ε = ‖x‖
      · exact Eventually.of_forall fun n => ((radius_pos_lt hε n).2.trans_eq hx).ne
      · exact (tendsto_radius ε).eventually_ne hx
    have h2 : ∀ᶠ n in atTop, s * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) ≠ ‖y‖ := by
      by_cases hy : s = ‖y‖
      · exact Eventually.of_forall fun n => ((radius_pos_lt hs n).2.trans_eq hy).ne
      · exact (tendsto_radius s).eventually_ne hy
    exact h1.and h2
  obtain ⟨N, hN⟩ := eventually_atTop.1 hne
  have hD : ∀ n : ℕ, ∃ D : Ω → ℝ, Measurable[modConstSigma hC U] D ∧
      (fun ω => hcirc ω (ε * (1 - (2 : ℝ)⁻¹ ^ (n + N + 1))) x -
        hcirc ω (s * (1 - (2 : ℝ)⁻¹ ^ (n + N + 1))) y) =ᵐ[P] D := fun n =>
    exists_modConst_ae_eq_of_ne hQ (radius_pos_lt hε _).1 (radius_pos_lt hs _).1 (radius_pos_lt hε _).2
      (radius_pos_lt hs _).2 (hN (n + N) (by omega)).1.symm (hN (n + N) (by omega)).2.symm hxU hyU
  choose D hDm hDae using hD
  refine exists_measurable_ae_eq_of_ae_tendsto (modConstSigma hC U) hDm ?_
  filter_upwards [ae_all_iff.2 hDae, hQ.ae_continuousOn_circle] with ω h1 h2
  have hc : ∀ (r : ℕ → ℝ) (ρ : ℝ) (z : ℂ), 0 < ρ → Tendsto r atTop (𝓝 ρ) →
      Tendsto (fun n => hcirc ω (r n) z) atTop (𝓝 (hcirc ω ρ z)) := by
    intro r ρ z hρ hr
    have hcont : ContinuousAt (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (ρ, z) :=
      h2.continuousAt (prod_mem_nhds (Ioi_mem_nhds hρ) univ_mem)
    exact hcont.tendsto.comp (hr.prodMk_nhds tendsto_const_nhds)
  have h3 := (hc _ ε x hε ((tendsto_radius ε).comp (tendsto_add_atTop_nat N))).sub
    (hc _ s y hs ((tendsto_radius s).comp (tendsto_add_atTop_nat N)))
  exact h3.congr fun n => h1 n

end ConeCircle
end Field
end MatedCRT
