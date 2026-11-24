import MatedCRT.FirstPass.Derived.WindowInverseChart
import MatedCRT.FirstPass.Derived.TestFunctionBorel

/-!
# Measurability of the chart fields of the windows

For the normalized inverse chart `windowChart a u b η` of the window `(a, u, b)` of the curve of a joint-limit sample
`q`, the chart field `windowChartField γ a u b (windowChart a u b q.1.2) q` (the field `h ∘ φ + Q log |φ'|` on the
unit disc, as its pairings with test functions) is a measurable function of `q`
(`measurable_windowChartField_windowChart`). For a test function `f` on the disc:

* on the samples whose window has an inverse chart and whose curve segment lies in the closed disc of radius `R`,
  the transported test function `(f ∘ ψ) |ψ'|²` is a measurable `𝓓_{K_R}`-valued function of the sample
  (`measurable_windowChartTestK`): its values are measurable, membership in the window being read off the
  normalized conformal map `φ` and its extended inverse `ψ` (`mem_windowDomain_iff`), and the derivative `ψ'` being
  jointly measurable (mathlib `measurable_deriv_with_param`);
* its pairing with the field is then measurable by the joint measurability of the pairing on `𝓓_K × 𝒟'(ℂ)`
  (`measurable_distC_apply_testK`);
* the term `Q ∫ log |φ'| f` is measurable (Fubini, the integrand being jointly measurable): on the open disc the
  conformal map `chartMap` of the chart is the normalized conformal map (`chartMap_eq_of_isDiscMap`).

`BG20NormalizedChartKernelInput` is `BG20NormalizedChartInput` without the measurability of the chart fields, and
implies it (`bg20NormalizedChartInput_of_kernelInput`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-! ### Window geometry -/

theorem windowDomain_subset_image (η : C(ℝ, ℂ)) (a u b : ℝ) : windowDomain η a u b ⊆ η '' Icc a b := by
  unfold windowDomain
  exact (connectedComponentIn_subset _ _).trans interior_subset

theorem isBounded_windowDomain (η : C(ℝ, ℂ)) (a u b : ℝ) : Bornology.IsBounded (windowDomain η a u b) :=
  (isCompact_Icc.image η.continuous).isBounded.subset (windowDomain_subset_image η a u b)

/-- On the open disc, the conformal map `chartMap U ψ = ψ⁻¹` of an inverse chart `ψ` which inverts a conformal map
`φ` of the closed disc onto the closure of `U` is `φ`. -/
theorem chartMap_eq_of_isDiscMap {U : Set ℂ} {z : ℂ} {φ : ℂ → ℂ} {ψ : C(ℂ, ℂ)} (hφ : IsDiscMap U φ)
    (hψ : IsInverseChart U z ψ) (hψφ : ∀ v ∈ closedBall (0 : ℂ) 1, ψ (φ v) = v) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) : chartMap U ψ w = φ w := by
  have hφU : φ w ∈ U := by
    rw [← hφ.image_ball]
    exact mem_image_of_mem φ hw
  have hex : ∃ x ∈ U, ψ x = w := ⟨φ w, hφU, hψφ w (ball_subset_closedBall hw)⟩
  exact hψ.injOn (subset_closure (Function.invFunOn_mem hex)) (subset_closure hφU)
    ((Function.invFunOn_eq hex).trans (hψφ w (ball_subset_closedBall hw)).symm)

theorem deriv_chartMap_eq_of_isDiscMap {U : Set ℂ} {z : ℂ} {φ : ℂ → ℂ} {ψ : C(ℂ, ℂ)} (hφ : IsDiscMap U φ)
    (hψ : IsInverseChart U z ψ) (hψφ : ∀ v ∈ closedBall (0 : ℂ) 1, ψ (φ v) = v) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) : deriv (chartMap U ψ) w = deriv φ w :=
  Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    exact chartMap_eq_of_isDiscMap hφ hψ hψφ hw')

/-! ### The samples whose window has an inverse chart -/

theorem measurable_jointSample_curve : Measurable fun q : JointSample => q.1.2 :=
  measurable_snd.comp measurable_fst

theorem measurable_jointSample_field : Measurable fun q : JointSample => LQGMetric.pairJInv ⊤ q.1.1.1 :=
  (LQGMetric.measurable_pairJInv ⊤).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))

/-- The samples whose window `(a, u, b)` has an inverse chart at the curve point. -/
def windowChartSet (a u b : ℝ) : Set JointSample :=
  {q | ∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ}

theorem measurableSet_windowChartSet (a u b : ℝ) : MeasurableSet (windowChartSet a u b) :=
  measurable_jointSample_curve (measurableSet_setOf_exists_isInverseChart a u b)

theorem isInverseChart_of_mem_windowChartSet {a u b : ℝ} {q : JointSample} (hq : q ∈ windowChartSet a u b) :
    IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (windowChart a u b q.1.2) := by
  obtain ⟨ψ, hψ⟩ := hq
  exact isInverseChart_windowChart hψ

theorem isNormalizedDiscMap_of_mem_windowChartSet {a u b : ℝ} {q : JointSample}
    (hq : q ∈ windowChartSet a u b) :
    IsNormalizedDiscMap (windowDomain q.1.2 a u b) (q.1.2 u) (windowDiscMap a u b q.1.2) := by
  obtain ⟨ψ, hψ⟩ := hq
  exact isNormalizedDiscMap_windowDiscMap hψ

theorem windowChart_apply_windowDiscMap {a u b : ℝ} {q : JointSample} (hq : q ∈ windowChartSet a u b) {v : ℂ}
    (hv : v ∈ closedBall (0 : ℂ) 1) : windowChart a u b q.1.2 (windowDiscMap a u b q.1.2 v) = v :=
  discInverseExt_apply_image (isNormalizedDiscMap_of_mem_windowChartSet hq).isDiscMap.injOn hv

/-- **Membership in the window, read off the conformal map and its extended inverse.** -/
theorem mem_windowDomain_iff {a u b : ℝ} {q : JointSample} (hq : q ∈ windowChartSet a u b) (x : ℂ) :
    x ∈ windowDomain q.1.2 a u b ↔
      x ∈ windowDiscMap a u b q.1.2 '' closedBall 0 1 ∧ ‖windowChart a u b q.1.2 x‖ < 1 := by
  have hφ := (isNormalizedDiscMap_of_mem_windowChartSet hq).isDiscMap
  constructor
  · intro hx
    rw [← hφ.image_ball] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨mem_image_of_mem _ (ball_subset_closedBall hv), ?_⟩
    rw [windowChart_apply_windowDiscMap hq (ball_subset_closedBall hv)]
    exact mem_ball_zero_iff.1 hv
  · rintro ⟨⟨v, hv, rfl⟩, h1⟩
    rw [windowChart_apply_windowDiscMap hq hv] at h1
    rw [← hφ.image_ball]
    exact mem_image_of_mem _ (mem_ball_zero_iff.2 h1)

/-- The closed disc of radius `R`, as a compact set. -/
def closedBallCompacts (R : ℕ) : TopologicalSpace.Compacts ℂ :=
  ⟨closedBall 0 R, isCompact_closedBall 0 R⟩

/-- The samples whose window `(a, u, b)` has an inverse chart and whose curve segment `η([a, b])` lies in the
closed disc of radius `R`. -/
def windowChartSetR (a u b : ℝ) (R : ℕ) : Set JointSample :=
  windowChartSet a u b ∩ {q | ∀ t ∈ Icc a b, q.1.2 t ∈ closedBall (0 : ℂ) R}

theorem measurableSet_windowChartSetR (a u b : ℝ) (R : ℕ) : MeasurableSet (windowChartSetR a u b R) := by
  refine (measurableSet_windowChartSet a u b).inter ?_
  have hc : IsClosed {η : C(ℝ, ℂ) | ∀ t ∈ Icc a b, η t ∈ closedBall (0 : ℂ) R} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_closedBall.preimage (continuous_eval_const t)
  exact measurable_jointSample_curve hc.measurableSet

/-! ### The transported test function -/

open Classical in
/-- The transported test function `x ↦ f(ψ x) |ψ'(x)|²` of the window `(a, u, b)` of `q`, with membership in the
window read off the normalized conformal map and its extended inverse. -/
noncomputable def windowTestValue (a u b : ℝ) (f : ℂ → ℝ) (q : JointSample) (x : ℂ) : ℝ :=
  if x ∈ windowDiscMap a u b q.1.2 '' closedBall 0 1 ∧ ‖windowChart a u b q.1.2 x‖ < 1 then
    f (windowChart a u b q.1.2 x) * ‖deriv (windowChart a u b q.1.2) x‖ ^ 2
  else 0

theorem chartTestFun_eq_windowTestValue {a u b : ℝ} {q : JointSample} (hq : q ∈ windowChartSet a u b)
    (f : ℂ → ℝ) (x : ℂ) :
    chartTestFun (windowDomain q.1.2 a u b) (windowChart a u b q.1.2) f x = windowTestValue a u b f q x := by
  unfold chartTestFun windowTestValue
  by_cases hx : x ∈ windowDomain q.1.2 a u b
  · rw [indicator_of_mem hx, ite_eq_left ((mem_windowDomain_iff hq x).1 hx)]
  · rw [indicator_of_notMem hx, ite_eq_right fun h => hx ((mem_windowDomain_iff hq x).2 h)]

theorem measurable_windowTestValue (a u b : ℝ) {f : ℂ → ℝ} (hf : Continuous f) (x : ℂ) :
    Measurable fun q : JointSample => windowTestValue a u b f q x := by
  have hφ : Measurable fun q : JointSample => windowDiscMap a u b q.1.2 :=
    (measurable_windowDiscMap a u b).comp measurable_jointSample_curve
  have hψ : Measurable fun q : JointSample => windowChart a u b q.1.2 :=
    (measurable_windowChart a u b).comp measurable_jointSample_curve
  have hψx : Measurable fun q : JointSample => windowChart a u b q.1.2 x :=
    (continuous_eval_const x).measurable.comp hψ
  have h1 : MeasurableSet ((fun q : JointSample => windowDiscMap a u b q.1.2) ⁻¹'
      {φ : C(ℂ, ℂ) | ∃ v ∈ closedBall (0 : ℂ) 1, φ v = x}) :=
    hφ (isClosed_setOf_exists_mem_of_isCompact (isCompact_closedBall (0 : ℂ) 1)
      (P := fun (φ : C(ℂ, ℂ)) (v : ℂ) => φ v = x) (isClosed_eq continuous_eval continuous_const)).measurableSet
  have h2 : MeasurableSet {q : JointSample | ‖windowChart a u b q.1.2 x‖ < 1} :=
    measurableSet_lt hψx.norm measurable_const
  have hS : MeasurableSet {q : JointSample | x ∈ windowDiscMap a u b q.1.2 '' closedBall 0 1 ∧
      ‖windowChart a u b q.1.2 x‖ < 1} := h1.inter h2
  have hd : Measurable fun q : JointSample => deriv (windowChart a u b q.1.2) x :=
    (measurable_deriv_with_param (f := fun (ψ : C(ℂ, ℂ)) (z : ℂ) => ψ z) continuous_eval).comp
      (hψ.prodMk measurable_const)
  unfold windowTestValue
  exact Measurable.ite hS ((hf.measurable.comp hψx).mul (hd.norm.pow_const 2)) measurable_const

theorem windowChartTestFun_eq_zero {a u b : ℝ} {R : ℕ} {q : JointSample} (hq : q ∈ windowChartSetR a u b R)
    (f : ℂ → ℝ) {x : ℂ} (hx : x ∉ (closedBallCompacts R : Set ℂ)) :
    chartTestFun (windowDomain q.1.2 a u b) (windowChart a u b q.1.2) f x = 0 := by
  unfold chartTestFun
  refine indicator_of_notMem (fun hxU => hx ?_) _
  obtain ⟨t, ht, rfl⟩ := windowDomain_subset_image q.1.2 a u b hxU
  exact hq.2 t ht

open Classical in
/-- **The transported test function `(f ∘ ψ) |ψ'|²` of the window `(a, u, b)` of `q`** for its normalized inverse
chart `ψ`, as an element of `𝓓_{K_R}` when the window has an inverse chart and the curve segment lies in the closed
disc of radius `R` (and `0` otherwise). -/
noncomputable def windowChartTestK (a u b : ℝ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) (q : JointSample) :
    𝓓^{⊤}_{closedBallCompacts R}(ℂ, ℝ) :=
  if hq : q ∈ windowChartSetR a u b R then
    { toFun := chartTestFun (windowDomain q.1.2 a u b) (windowChart a u b q.1.2) f
      contDiff' := contDiff_chartTestFun (isInverseChart_of_mem_windowChartSet hq.1)
        (isOpen_windowDomain _ _ _ _) (isBounded_windowDomain _ _ _ _) f
      zero_on_compl' := fun _ hx => windowChartTestFun_eq_zero hq f hx }
  else 0

open Classical in
theorem windowChartTestK_apply (a u b : ℝ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) (q : JointSample) (x : ℂ) :
    windowChartTestK a u b f R q x =
      if q ∈ windowChartSetR a u b R then windowTestValue a u b f q x else 0 := by
  by_cases hq : q ∈ windowChartSetR a u b R
  · rw [ite_eq_left hq, ← chartTestFun_eq_windowTestValue hq.1]
    unfold windowChartTestK
    rw [dite_eq_left hq]
    rfl
  · rw [ite_eq_right hq]
    unfold windowChartTestK
    rw [dite_eq_right hq]
    rfl

/-- **The transported test function is a measurable `𝓓_{K_R}`-valued function of the sample.** -/
theorem measurable_windowChartTestK (a u b : ℝ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) :
    Measurable (windowChartTestK a u b f R) := by
  classical
  refine (measurable_testK_iff (closedBallCompacts R)).2 fun x => ?_
  have heq : (fun q => windowChartTestK a u b f R q x) =
      fun q => if q ∈ windowChartSetR a u b R then windowTestValue a u b f q x else 0 :=
    funext fun q => windowChartTestK_apply a u b f R q x
  rw [heq]
  exact Measurable.ite (measurableSet_windowChartSetR a u b R)
    (measurable_windowTestValue a u b f.contDiff.continuous x) measurable_const

/-- The pairing of the field of the sample with the transported test function in `𝓓_{K_R}` is measurable. -/
theorem measurable_windowChartPairingK (a u b : ℝ) (f : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) :
    Measurable fun q : JointSample =>
      LQGMetric.pairJInv ⊤ q.1.1.1 (testKToTestC (closedBallCompacts R) (windowChartTestK a u b f R q)) :=
  (measurable_distC_apply_testK (closedBallCompacts R)).comp
    ((measurable_windowChartTestK a u b f R).prodMk measurable_jointSample_field)

/-- The term `∫ log |φ'| f` of the chart field is a measurable function of the sample. -/
theorem measurable_windowLogDerivIntegral (a u b : ℝ) (f : 𝓓(unitDiscOpens, ℝ)) :
    Measurable fun q : JointSample => ∫ w, Real.log ‖deriv (windowDiscMap a u b q.1.2) w‖ * f w := by
  have hφ : Measurable fun q : JointSample => windowDiscMap a u b q.1.2 :=
    (measurable_windowDiscMap a u b).comp measurable_jointSample_curve
  have hd : Measurable fun p : JointSample × ℂ => deriv (windowDiscMap a u b p.1.1.2) p.2 :=
    (measurable_deriv_with_param (f := fun (φ : C(ℂ, ℂ)) (z : ℂ) => φ z) continuous_eval).comp
      ((hφ.comp measurable_fst).prodMk measurable_snd)
  have hj : Measurable fun p : JointSample × ℂ =>
      Real.log ‖deriv (windowDiscMap a u b p.1.1.2) p.2‖ * f p.2 :=
    (Real.measurable_log.comp hd.norm).mul (f.contDiff.continuous.measurable.comp measurable_snd)
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-! ### The chart field -/

/-- On the samples of `windowChartSetR a u b R`, the chart field of the window for the normalized inverse chart is the
pairing of the field with the transported test function in `𝓓_{K_R}`, plus `Q ∫ log |φ'| f`. -/
theorem windowChartField_eq {γ a u b : ℝ} {R : ℕ} {q : JointSample} (hq : q ∈ windowChartSetR a u b R)
    (f : 𝓓(unitDiscOpens, ℝ)) :
    windowChartField γ a u b (windowChart a u b q.1.2) q f =
      LQGMetric.pairJInv ⊤ q.1.1.1 (testKToTestC (closedBallCompacts R) (windowChartTestK a u b f R q)) +
        MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (windowDiscMap a u b q.1.2) w‖ * f w := by
  have hψ := isInverseChart_of_mem_windowChartSet hq.1
  have hc : IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (windowChart a u b q.1.2) ∧
      IsOpen (windowDomain q.1.2 a u b) ∧ Bornology.IsBounded (windowDomain q.1.2 a u b) :=
    ⟨hψ, isOpen_windowDomain _ _ _ _, isBounded_windowDomain _ _ _ _⟩
  have htest : chartTest hc.1 hc.2.1 hc.2.2 f =
      testKToTestC (closedBallCompacts R) (windowChartTestK a u b f R q) := by
    ext x
    rw [chartTest_apply, testKToTestC_apply]
    unfold windowChartTestK
    rw [dite_eq_left hq]
    rfl
  have hint : ∀ w, Real.log ‖deriv (chartMap (windowDomain q.1.2 a u b) (windowChart a u b q.1.2)) w‖ * f w =
      Real.log ‖deriv (windowDiscMap a u b q.1.2) w‖ * f w := by
    intro w
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · rw [deriv_chartMap_eq_of_isDiscMap (isNormalizedDiscMap_of_mem_windowChartSet hq.1).isDiscMap hψ
        (fun v hv => windowChart_apply_windowDiscMap hq.1 hv) hw]
    · have hf0 : f w = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (f.tsupport_subset h)
      rw [hf0, mul_zero, mul_zero]
  unfold windowChartField chartFieldPairing
  rw [dite_eq_left hc]
  simp only [htest, integral_congr_ae (Eventually.of_forall hint)]

/-- **The chart field of a window is measurable, tested against a test function on the disc.** -/
theorem measurable_windowChartField_apply (γ a u b : ℝ) (f : 𝓓(unitDiscOpens, ℝ)) :
    Measurable fun q : JointSample => windowChartField γ a u b (windowChart a u b q.1.2) q f := by
  classical
  refine measurable_of_tendsto_metrizable (f := fun (R : ℕ) (q : JointSample) =>
      if q ∈ windowChartSetR a u b R then
        LQGMetric.pairJInv ⊤ q.1.1.1 (testKToTestC (closedBallCompacts R) (windowChartTestK a u b f R q)) +
          MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (windowDiscMap a u b q.1.2) w‖ * f w
      else 0)
    (fun R => Measurable.ite (measurableSet_windowChartSetR a u b R)
      ((measurable_windowChartPairingK a u b f R).add
        ((measurable_windowLogDerivIntegral a u b f).const_mul _)) measurable_const)
    (tendsto_pi_nhds.2 fun q => ?_)
  by_cases hq : q ∈ windowChartSet a u b
  · obtain ⟨r, hr⟩ := (isCompact_Icc.image q.1.2.continuous).isBounded.subset_closedBall (0 : ℂ)
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈r⌉₊) fun R hR => ?_
    have hqR : q ∈ windowChartSetR a u b R := ⟨hq, fun t ht =>
      closedBall_subset_closedBall ((Nat.le_ceil r).trans (Nat.cast_le.2 hR)) (hr (mem_image_of_mem _ ht))⟩
    rw [ite_eq_left hqR]
    exact (windowChartField_eq hqR f).symm
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun R _ => ?_
    have hc : ¬ (IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (windowChart a u b q.1.2) ∧
        IsOpen (windowDomain q.1.2 a u b) ∧ Bornology.IsBounded (windowDomain q.1.2 a u b)) :=
      fun h => hq ⟨_, h.1⟩
    rw [ite_eq_right fun h => hq h.1]
    unfold windowChartField chartFieldPairing
    rw [dite_eq_right hc]

/-- **The chart field of a window for its normalized inverse chart is a measurable function of the sample.** -/
theorem measurable_windowChartField_windowChart (γ a u b : ℝ) :
    Measurable fun q : JointSample => windowChartField γ a u b (windowChart a u b q.1.2) q :=
  measurable_pi_iff.2 fun f => measurable_windowChartField_apply γ a u b f

/-! ### The chart input with measurable chart fields -/

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit, with the normalized inverse charts).** As `BG20NormalizedChartInput`, without the measurability of the chart
fields of the two windows (`measurable_windowChartField_windowChart`). For times `a < u < b < a' < u' < b'`:

* almost surely the two windows have inverse charts at the curve points;
* the kernel `K` and the window chart laws depend measurably on the sample;
* (Lemma 7.20 without the time change; Berestycki (2015), Theorem 1.3) almost surely the chart image of the
  Liouville Brownian law of the field from `η(u)` is `K` of the chart field, and likewise for the second window;
* (Lemma 7.21) the pairs (chart field, window chart law) of the two windows are independent. -/
def BG20NormalizedChartKernelInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure JointSample, IsProbabilityMeasure ν'' →
    (∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∀ a u b a' u' b' : ℝ, a < u → u < b → b < a' → a' < u' → u' < b' →
    ∃ K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ),
      (∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) ∧
      (∀ᵐ q ∂ν'', ∃ ψ, IsInverseChart (windowDomain q.1.2 a' u' b') (q.1.2 u') ψ) ∧
      Measurable K ∧
      Measurable (fun q : JointSample => windowChartLaw a u b (windowChart a u b q.1.2) q) ∧
      Measurable (fun q : JointSample => windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
        K (windowChartField γ a u b (windowChart a u b q.1.2) q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (windowChart a' u' b' q.1.2) q =
        K (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q)) ∧
      IndepFun (fun q : JointSample => (windowChartField γ a u b (windowChart a u b q.1.2) q,
          windowChartLaw a u b (windowChart a u b q.1.2) q))
        (fun q : JointSample => (windowChartField γ a' u' b' (windowChart a' u' b' q.1.2) q,
          windowChartLaw a' u' b' (windowChart a' u' b' q.1.2) q)) ν''

/-- The input without the measurability of the chart fields implies `BG20NormalizedChartInput`. -/
theorem bg20NormalizedChartInput_of_kernelInput {𝒮 : SpaceFillingSLEModel}
    (hC : BG20NormalizedChartKernelInput 𝒮) : BG20NormalizedChartInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  obtain ⟨K, hψ, hψ', hK, hm, hm', hb, hb', hind⟩ :=
    hC γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'
  exact ⟨K, hψ, hψ', hK, measurable_windowChartField_windowChart γ a u b,
    measurable_windowChartField_windowChart γ a' u' b', hm, hm', hb, hb', hind⟩

/-- The input without the measurability of the chart fields implies `BG20ChartFieldInput`. -/
theorem bg20ChartFieldInput_of_kernelInput {𝒮 : SpaceFillingSLEModel}
    (hC : BG20NormalizedChartKernelInput 𝒮) : BG20ChartFieldInput 𝒮 :=
  bg20ChartFieldInput_of_normalizedChart (bg20NormalizedChartInput_of_kernelInput hC)

end MatedCRT
