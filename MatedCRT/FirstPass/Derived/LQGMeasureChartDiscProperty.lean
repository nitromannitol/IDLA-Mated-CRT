import MatedCRT.FirstPass.Derived.LQGMeasureChartMarkov
import MatedCRT.FirstPass.Derived.LQGMeasureChartPerturb
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward

/-!
# The coordinate change of the LQG measure on a disc, for a field with a Markov remainder

Let `D = B(c, r)` be a disc. A field `h` on `ℂ` has the *chart property* on `D` with measure `μ`
(`MatedCRT.LQGMeasureChart.ChartProp`) if for every conformal map `ψ` from `D` onto a bounded open set, with inverse
`φ`, the smooth approximations of `h|_D ∘ φ + Q log |φ'|` (Sheffield–Wang, arXiv:1605.06171v2, (1.6) and §3.2)
converge vaguely in `ψ(D)` along `2^{-k}` to the measure `ν` with `ν(A) = μ(D ∩ ψ⁻¹(A))`: the conclusion of
Sheffield–Wang, Theorems 1.1, 1.2 and 1.4, on the disc, at the scales `2^{-k}`
(Duplantier–Sheffield, arXiv:0808.1560v2, Proposition 2.1 for a fixed map).

This file formalizes the first localization step of the coordinate change of the LQG measure for all inverse charts:
the property passes from a zero-boundary GFF on `D` (where it is the cited input `SheffieldWangDiscConformal`) to the
field `Xz + u` with a continuous remainder `u`, i.e. the Markov harmonic remainder multiplies the limit by its
exponential with coefficient `γ`, since its averages converge locally uniformly.

* `transport_admissible`, `integral_mul_transport`: for `ψ` injective and holomorphic on `D` and `v` smooth vanishing
  off a compact subset of `ψ(D)`, the transported test `1_D (v ∘ ψ) |ψ'|²` is smooth with compact support in `D`, and
  `∫ g 1_D (v ∘ ψ) |ψ'|² = ∫ (g ∘ φ) v` (change of variables `w = ψ(x)`, Jacobian `|ψ'|²`).
* `chartProp_of_decomposition`: deterministic. If `h = Xz + u` on `D` with `u` continuous, the circle averages of
  `h` are those of `Xz` plus those of `u`, `μ|_D` is the vague limit of the circle approximations of `h`, and `Xz`
  satisfies the conclusion of Sheffield–Wang with a measure `μ_z`, then `h` has the chart property with `μ`:
  the limits are multiplied by `e^{γ u}` (`isVagueLimitOn_lqgApprox_add`, `isVagueLimitOn_smoothApprox_add`) and
  `μ|_D = e^{γ u} μ_z`.
* `ae_chartProp_wholePlane`: a whole-plane GFF has the chart property on every disc, almost surely, with any measure
  whose restriction to the disc is the limit of its circle approximations.
* `MatedCRTEnv.IsValid.ae_chartProp`: the field of a valid environment has the chart property with its LQG measure
  `S.μ` on every disc avoiding the cone point `0`, almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

namespace LQGMeasureChart

open LQGMetric

/-- **The chart property on the disc `B(c, r)`** (the conclusion of Sheffield–Wang (2016), Theorems 1.1, 1.2 and
1.4, at the scales `2^{-k}`): for every conformal map `ψ` from `B(c, r)` onto a bounded open set, the smooth
approximations of `h|_{B(c,r)} ∘ φ + Q log |φ'|`, `φ = ψ⁻¹`, converge vaguely in `ψ(B(c, r))` to the measure `ν` with
`ν(A) = μ(B(c, r) ∩ ψ⁻¹(A))`. -/
def ChartProp (γ : ℝ) (f : ℂ → ℝ) (c : ℂ) (r : ℝ) (h : LQGMetric.DistC) (μ : Measure ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, InjOn ψ (ball c r) → DifferentiableOn ℂ ψ (ball c r) → Bornology.IsBounded (ψ '' ball c r) →
    ∃ ν : Measure ℂ, QuantumZipper.IsVagueLimitOn (ψ '' ball c r)
      (fun k => smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ (LQGMetric.restrictTo (disc c r) h) ψ)
        (HarmonicBalls.dyadicScale k)) ν ∧
      ∀ A : Set ℂ, MeasurableSet A → A ⊆ ψ '' ball c r → ν A = μ (ball c r ∩ ψ ⁻¹' A)

/-! ## Conformal maps of a disc and transported test functions -/

/-- The translates `w ↦ f_ε(z − w)` of a bump function are smooth. -/
theorem contDiff_mollScale_sub_left {f : ℂ → ℝ} (hf : IsMollifier f) (ε : ℝ) (z : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun w => mollScale f ε (z - w) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun w => (ε ^ 2)⁻¹ * f ((z - w) / (ε : ℂ))
  exact contDiff_const.mul (hf.contDiff.comp ((contDiff_const.sub contDiff_id).div_const (ε : ℂ)))

/-- An injective holomorphic map `ψ` on the disc `B(c, r)` has a continuous inverse `φ` on `ψ(B(c, r))`. -/
theorem exists_inverse_of_injOn {c : ℂ} {r : ℝ} {ψ : ℂ → ℂ} (hinj : InjOn ψ (ball c r))
    (hψ : DifferentiableOn ℂ ψ (ball c r)) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (ψ '' ball c r) ∧ MapsTo φ (ψ '' ball c r) (ball c r) ∧
      ∀ x ∈ ball c r, φ (ψ x) = x :=
  ⟨(QuantumZipper.CA.univalentOPH isOpen_ball hψ hinj).symm,
    (QuantumZipper.CA.univalentOPH isOpen_ball hψ hinj).continuousOn_symm,
    fun _ hw => (QuantumZipper.CA.univalentOPH isOpen_ball hψ hinj).map_target hw,
    fun _ hx => QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball hψ hinj hx⟩

/-- **The transported test function is a test function on the disc.** For `ψ` injective and holomorphic on
`B(c, r)` with inverse `φ`, and `v` smooth vanishing off a compact subset `K` of `ψ(B(c, r))`, the function
`1_{B(c,r)} (v ∘ ψ) |ψ'|²` is smooth with compact support in `B(c, r)` (its support lies in `φ(K)`). -/
theorem transport_admissible {c : ℂ} {r : ℝ} {ψ φ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ (ball c r))
    (hφc : ContinuousOn φ (ψ '' ball c r)) (hφm : MapsTo φ (ψ '' ball c r) (ball c r))
    (hφψ : ∀ x ∈ ball c r, φ (ψ x) = x) {v : ℂ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) {K : Set ℂ}
    (hK : IsCompact K) (hKV : K ⊆ ψ '' ball c r) (hvK : ∀ w, w ∉ K → v w = 0) :
    ContDiff ℝ (⊤ : ℕ∞) ((ball c r).indicator fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) ∧
      HasCompactSupport ((ball c r).indicator fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) ∧
      tsupport ((ball c r).indicator fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) ⊆ ball c r := by
  have hK'c : IsCompact (φ '' K) := hK.image_of_continuousOn (hφc.mono hKV)
  have hK'D : φ '' K ⊆ ball c r := by
    rintro _ ⟨w, hw, rfl⟩
    exact hφm (hKV hw)
  have hsupp : Function.support ((ball c r).indicator fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) ⊆ φ '' K := by
    intro x hx
    by_cases hxD : x ∈ ball c r
    · rw [Function.mem_support, indicator_of_mem hxD] at hx
      have hv0 : v (ψ x) ≠ 0 := left_ne_zero_of_mul hx
      have hψK : ψ x ∈ K := by
        by_contra hn
        exact hv0 (hvK _ hn)
      exact ⟨ψ x, hψK, hφψ x hxD⟩
    · exact absurd (indicator_of_notMem hxD _) hx
  have hts : tsupport ((ball c r).indicator fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) ⊆ φ '' K :=
    closure_minimal hsupp hK'c.isClosed
  refine ⟨?_, hK'c.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hK'D⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxD : x ∈ ball c r
  · have hA : AnalyticAt ℂ ψ x := hψ.analyticAt (isOpen_ball.mem_nhds hxD)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) ψ x := hA.contDiffAt.restrict_scalars ℝ
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (deriv ψ) x := hA.deriv.contDiffAt.restrict_scalars ℝ
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => v (ψ y) * ‖deriv ψ y‖ ^ 2) x :=
      (hv.contDiffAt.comp x h1).mul ((contDiff_norm_sq ℝ).contDiffAt.comp x h2)
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hxD] with y hy
    exact indicator_of_mem hy _
  · have hxK : x ∉ φ '' K := fun h => hxD (hK'D h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK'c.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact image_eq_zero_of_notMem_tsupport fun h => hy (hts h)

/-- **Change of variables for the transported test functions.** For `ψ` injective and holomorphic on `B(c, r)` with
inverse `φ` and `v` vanishing off `ψ(B(c, r))`, by the change of variables `w = ψ(x)` with Jacobian `|ψ'(x)|²`:
`∫ g(x) 1_{B(c,r)}(x) v(ψ(x)) |ψ'(x)|² dx = ∫ g(φ(w)) v(w) dw`. -/
theorem integral_mul_transport {c : ℂ} {r : ℝ} {ψ φ : ℂ → ℂ} (hinj : InjOn ψ (ball c r))
    (hψ : DifferentiableOn ℂ ψ (ball c r)) (hφψ : ∀ x ∈ ball c r, φ (ψ x) = x) (g v : ℂ → ℝ)
    (hv : ∀ w, w ∉ ψ '' ball c r → v w = 0) :
    ∫ x, g x * (ball c r).indicator (fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) x = ∫ w, g (φ w) * v w := by
  have hderiv : ∀ x ∈ ball c r, HasFDerivWithinAt ψ (fderiv ℝ ψ x) (ball c r) x := fun x hx =>
    ((hψ.differentiableAt (isOpen_ball.mem_nhds hx)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have h1 : ∫ x, g x * (ball c r).indicator (fun x => v (ψ x) * ‖deriv ψ x‖ ^ 2) x =
      ∫ x in ball c r, g x * (v (ψ x) * ‖deriv ψ x‖ ^ 2) := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ ball c r
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  have h2 : ∫ w, g (φ w) * v w = ∫ w in ψ '' ball c r, g (φ w) * v w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by rw [hv w hw, mul_zero]).symm
  rw [h1, h2, integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) measurableSet_ball hderiv hinj]
  refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
  have hd : DifferentiableAt ℂ ψ x := hψ.differentiableAt (isOpen_ball.mem_nhds hx)
  simp only [smul_eq_mul]
  rw [QuantumZipper.abs_det_fderiv_eq_normSq hd, hφψ x hx]
  ring

/-- The restriction of a dyadic LQG limit on `ℂ` to an open set is the vague limit in that set. -/
theorem isVagueLimitOn_restrict_of_isLQGLimit {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hm : HarmonicBalls.IsLQGLimit γ hε m) {U : Set ℂ} (hU : IsOpen U) :
    QuantumZipper.IsVagueLimitOn U
      (fun k => HarmonicBalls.lqgApprox γ hε (HarmonicBalls.dyadicScale k)) (m.restrict U) := by
  have := hm.isLocallyFiniteMeasure
  refine ⟨?_, fun K hK _ => (Measure.restrict_le_self K).trans_lt hK.measure_lt_top, fun g hg hgc hgU => ?_⟩
  · rw [Measure.restrict_apply hU.measurableSet.compl, compl_inter_self, measure_empty]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hgU h)]
    exact hm.tendsto_integral g hg hgc

/-! ## The chart property for a field with a continuous remainder -/

/-- **The Markov remainder multiplies the limits by its exponential** (first localization step). Let `h = Xz + u` on
the disc `D = B(c, r)` with `u` continuous on `D`, let the circle averages `hcirc` of `h` be those of `Xz` (`hc`) plus
those of `u` on the closed discs inside `D`, let `μ|_D` be the vague limit in `D` of the circle approximations of `h`,
and let `Xz` satisfy the conclusion of Sheffield–Wang (2016) on `D` with the vague limit `μz` of the circle
approximations of `hc`. Then `h` has the chart property on `D` with `μ`. -/
theorem chartProp_of_decomposition {γ : ℝ} {f : ℂ → ℝ} (hf : IsMollifier f) {c : ℂ} {r : ℝ}
    {h : DistC} {Xz : DistOn (disc c r)} {u : ℂ → ℝ} {hc hcirc : ℝ → ℂ → ℝ} {μ μz : Measure ℂ}
    (hu : ContinuousOn u (ball c r))
    (hdec : ∀ φ : TestOn (disc c r), restrictTo (disc c r) h φ = Xz φ + ∫ x, u x * φ x)
    (hcircEq : ∀ s : ℝ, 0 < s → ∀ z, closedBall z s ⊆ ball c r →
      hcirc s z = hc s z + Real.circleAverage u z s)
    (hμ : QuantumZipper.IsVagueLimitOn (ball c r)
      (fun k => HarmonicBalls.lqgApprox γ hcirc (HarmonicBalls.dyadicScale k)) (μ.restrict (ball c r)))
    (hz : QuantumZipper.IsVagueLimitOn (ball c r)
      (fun k => HarmonicBalls.lqgApprox γ hc (HarmonicBalls.dyadicScale k)) μz)
    (hSWψ : ∀ ψ : ℂ → ℂ, InjOn ψ (ball c r) → DifferentiableOn ℂ ψ (ball c r) →
      Bornology.IsBounded (ψ '' ball c r) → ∃ ν : Measure ℂ,
        QuantumZipper.IsVagueLimitOn (ψ '' ball c r)
          (fun k => smoothApprox γ f (ψ '' ball c r) (pullbackPairing γ Xz ψ) (HarmonicBalls.dyadicScale k)) ν ∧
        ∀ A : Set ℂ, MeasurableSet A → A ⊆ ψ '' ball c r → ν A = μz (ball c r ∩ ψ ⁻¹' A)) :
    ChartProp γ f c r h μ := by
  classical
  have hμz : μ.restrict (ball c r) = μz.withDensity fun x => ENNReal.ofReal (Real.exp (γ * u x)) :=
    QuantumZipper.isVagueLimitOn_unique isOpen_ball hμ
      (isVagueLimitOn_lqgApprox_add isOpen_ball hu hcircEq hz)
  intro ψ hinj hψ hbdd
  obtain ⟨ν, hν, hνA⟩ := hSWψ ψ hinj hψ hbdd
  have hVo : IsOpen (ψ '' ball c r) := QuantumZipper.CA.isOpen_image_of_injOn' isOpen_ball hψ hinj
  obtain ⟨φ, hφc, hφm, hφψ⟩ := exists_inverse_of_injOn hinj hψ
  have huφ : ContinuousOn (fun w => u (φ w)) (ψ '' ball c r) := hu.comp hφc hφm
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ → ℝ, b = (ψ '' ball c r).piecewise (fun w => u (φ w)) fun _ => 0 :=
    ⟨_, rfl⟩
  have hbV : ∀ w ∈ ψ '' ball c r, b w = u (φ w) := fun w hw => by
    rw [hbdef]
    exact piecewise_eq_of_mem _ _ _ hw
  have hbc : ContinuousOn b (ψ '' ball c r) := huφ.congr hbV
  have hbm : Measurable b := by
    rw [hbdef]
    exact huφ.measurable_piecewise continuousOn_const hVo.measurableSet
  refine ⟨ν.withDensity fun w => ENNReal.ofReal (Real.exp (γ * b w)),
    isVagueLimitOn_smoothApprox_add hf hVo hbc ?_ hν, fun A hA hAV => ?_⟩
  · -- the pullback of `h` is the pullback of `Xz` plus the remainder `u ∘ φ`
    intro ε hε z hz
    have hv0 : ∀ w, w ∉ closedBall z ε → mollScale f ε (z - w) = 0 := by
      intro w hw
      exact image_eq_zero_of_notMem_tsupport (f := fun w => mollScale f ε (z - w)) (x := w) fun h' =>
        hw (ball_subset_closedBall (tsupport_mollScale_sub_subset hf hε z h'))
    have hadm := transport_admissible hψ hφc hφm hφψ (contDiff_mollScale_sub_left hf ε z)
      (isCompact_closedBall z ε) hz hv0
    let F : ℂ → ℝ := (ball c r).indicator fun x => mollScale f ε (z - ψ x) * ‖deriv ψ x‖ ^ 2
    let φV : TestOn (disc c r) := ⟨F, hadm.1, hadm.2.1, hadm.2.2⟩
    have h1 : pairFun (restrictTo (disc c r) h) F = restrictTo (disc c r) h φV := dite_eq_left hadm
    have h2 : pairFun Xz F = Xz φV := dite_eq_left hadm
    have h4 : ∫ x, u x * φV x = ∫ w, b w * mollScale f ε (z - w) := by
      show ∫ x, u x * F x = _
      rw [integral_mul_transport hinj hψ hφψ u (fun w => mollScale f ε (z - w)) fun w hw =>
        hv0 w fun h' => hw (hz h')]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      by_cases hw : w ∈ ψ '' ball c r
      · show u (φ w) * mollScale f ε (z - w) = b w * mollScale f ε (z - w)
        rw [hbV w hw]
      · show u (φ w) * mollScale f ε (z - w) = b w * mollScale f ε (z - w)
        rw [hv0 w fun h' => hw (hz h'), mul_zero, mul_zero]
    show pairFun (restrictTo (disc c r) h) F +
        (2 / γ + γ / 2) * ∫ w, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (z - w) =
      pairFun Xz F +
        (2 / γ + γ / 2) * (∫ w, Real.log ‖deriv (Function.invFunOn ψ (ball c r)) w‖ * mollScale f ε (z - w)) +
        ∫ w, b w * mollScale f ε (z - w)
    rw [h1, h2, hdec φV, h4]
    ring
  · -- the limit measure: `ν(A) = μz(D ∩ ψ⁻¹A)` and `μ|_D = e^{γ u} μz`
    have hDm : MeasurableSet (ball c r) := measurableSet_ball
    have hψae : AEMeasurable ψ (μz.restrict (ball c r)) := hψ.continuousOn.aemeasurable hDm
    have hpre : ∀ B : Set ℂ, MeasurableSet B → MeasurableSet (ball c r ∩ ψ ⁻¹' B) := by
      intro B hB
      have hm : Measurable ((ball c r).piecewise ψ fun _ => (0 : ℂ)) :=
        hψ.continuousOn.measurable_piecewise continuousOn_const hDm
      have heq : ball c r ∩ ψ ⁻¹' B = ball c r ∩ ((ball c r).piecewise ψ fun _ => (0 : ℂ)) ⁻¹' B := by
        ext x
        constructor
        · rintro ⟨hx, hxB⟩
          exact ⟨hx, by rw [mem_preimage, piecewise_eq_of_mem _ _ _ hx]; exact hxB⟩
        · rintro ⟨hx, hxB⟩
          exact ⟨hx, by rw [mem_preimage, piecewise_eq_of_mem _ _ _ hx] at hxB; exact hxB⟩
      rw [heq]
      exact hDm.inter (hm hB)
    have hrestr : ν.restrict A = ((μz.restrict (ball c r)).map ψ).restrict A := by
      ext s hs
      rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
        Measure.map_apply_of_aemeasurable hψae (hs.inter hA), Measure.restrict_apply' hDm,
        hνA (s ∩ A) (hs.inter hA) (inter_subset_right.trans hAV), Set.inter_comm (ψ ⁻¹' (s ∩ A)) (ball c r)]
    have hGm : Measurable fun w => ENNReal.ofReal (Real.exp (γ * b w)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hbm.const_mul γ))
    have hR : μ (ball c r ∩ ψ ⁻¹' A) =
        (μz.withDensity fun x => ENNReal.ofReal (Real.exp (γ * u x))) (ball c r ∩ ψ ⁻¹' A) := by
      rw [← hμz, Measure.restrict_apply (hpre A hA), Set.inter_eq_left.2 inter_subset_left]
    rw [withDensity_apply _ hA, hrestr, Measure.restrict_map_of_aemeasurable hψae hA,
      lintegral_map' hGm.aemeasurable (hψae.mono_measure Measure.restrict_le_self),
      Measure.restrict_restrict' hDm, hR, withDensity_apply _ (hpre A hA),
      Set.inter_comm (ψ ⁻¹' A) (ball c r)]
    refine setLIntegral_congr_fun (hpre A hA) fun x hx => ?_
    show ENNReal.ofReal (Real.exp (γ * b (ψ x))) = ENNReal.ofReal (Real.exp (γ * u x))
    rw [hbV (ψ x) (mem_image_of_mem ψ hx.1), hφψ x hx.1]

/-! ## The whole-plane GFF and the field of a valid environment -/

/-- **The chart property for the whole-plane GFF on any disc.** Given the Sheffield–Wang theorem on discs
(`SheffieldWangDiscConformal`), `0 < γ < 2` and a bump function `f`: for a whole-plane GFF `X`, a disc `B(c, r)` and
random measures `μ` whose restrictions to the disc are almost surely the vague limits in the disc of the circle
approximations of `X`, almost surely `X` has the chart property on the disc with `μ`. -/
theorem ae_chartProp_wholePlane (hSW : SheffieldWangDiscConformal) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {f : ℂ → ℝ} (hf : IsMollifier f) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P) (c : ℂ) {r : ℝ} (hr : 0 < r)
    {μ : Ω → Measure ℂ}
    (hμ : ∀ᵐ ω ∂P, QuantumZipper.IsVagueLimitOn (ball c r)
      (fun k => HarmonicBalls.lqgApprox γ (circleAvg (X ω)) (HarmonicBalls.dyadicScale k))
      ((μ ω).restrict (ball c r))) :
    ∀ᵐ ω ∂P, ChartProp γ f c r (X ω) (μ ω) := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  obtain ⟨Xz, u, hc, hzb, hucont, hdec, hcirc, hid⟩ := exists_discMarkovDecomposition_wholePlane hX c hr
  have hsw := hSW γ hγ hγ2 f hf c r hr Ω P hP Xz hzb hc hcirc
  filter_upwards [hsw, hucont, hdec, hid, hμ] with ω hω hu hd hidω hμω
  obtain ⟨μz, hz, hψ⟩ := hω
  exact chartProp_of_decomposition hf hu hd (fun s hs z hz => hidω s z hs hz) hμω hz hψ

end LQGMeasureChart

open LQGMeasureChart in
/-- **The chart property for the field of a valid environment** on discs avoiding the cone point. Given the
Sheffield–Wang theorem on discs (`SheffieldWangDiscConformal`), `0 < γ < 2` and a bump function `f`: for a valid
environment, a measurable version `H` of its field and a disc `B(c, r)` whose closure avoids `0`, almost surely `H`
has the chart property on the disc with the LQG measure `S.μ` of the environment. -/
theorem MatedCRTEnv.IsValid.ae_chartProp (hSW : SheffieldWangDiscConformal) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {f : ℂ → ℝ} (hf : IsMollifier f) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} (hS : S.IsValid 𝒮 γ) {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (h0 : (0 : ℂ) ∉ closedBall c r) :
    ∀ᵐ ω ∂S.P, ChartProp γ f c r (H ω) (S.μ ω) := by
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨Xz, u, hc, hzb, hucont, hdec, hcirc, hid⟩ := hS.exists_discMarkovDecomposition hγ hγ2 hH c hr h0
  have hsw := hSW γ hγ hγ2 f hf c r hr Ω S.P hP Xz hzb hc hcirc
  have hL : ∀ᵐ ω ∂S.P, HarmonicBalls.IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  filter_upwards [hsw, hucont, hdec, hid, hL] with ω hω hu hd hidω hLω
  obtain ⟨μz, hz, hψ⟩ := hω
  exact chartProp_of_decomposition hf hu hd (fun s hs z hz => hidω s z hs hz)
    (isVagueLimitOn_restrict_of_isLQGLimit hLω isOpen_ball) hz hψ

end MatedCRT
