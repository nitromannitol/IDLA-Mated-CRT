import MatedCRT.FirstPass.Derived.IntrinsicWindowChartBG
import MatedCRT.FirstPass.Derived.WindowChartBGIntrinsicIndependence
import MatedCRT.FirstPass.Derived.WindowInverseChartJointLimit
import MatedCRT.FirstPass.Derived.ValidCurveRegularClosed

/-!
# The chart field of a window is a function of the intrinsic curve-decorated wedge

Berestycki–Gwynne (2020), arXiv:2003.10320, proof of Lemma 7.21: the chart field
`(h^D, η^D)` of a window is determined by the quantum surface of (7.35) containing it, with the two quantum surfaces
taken as intrinsic curve-decorated wedges (`intrinsicCurveDecoratedSurfaceSigma`). The function is the
**intrinsic chart field** `windowFieldIntr`:
`ρ ↦ ⟨h, 1_U (ρ ∘ ψ) |ψ'|²⟩ + Q ∫_𝔻 ρ log |φ'|` for the intrinsic inverse chart `ψ = windowChartIntr` of the window
domain `U` and the conformal map `φ = windowDiscMapIntr = ψ⁻¹` of the open disc, when the intrinsic construction
succeeds (`WindowGoodIntr`), and `0` otherwise.

* `windowFieldIntr` is a Borel function of (field, curve) (`measurable_windowFieldIntr`): the transported test function
  is a measurable `𝓓_{K_R}`-valued function of the curve on the curves with `η([a, b])` in the closed disc of radius
  `R`, its values being limits of difference quotients of the Borel map `(η, x) ↦ ψ(x)`; the same holds for the
  integrand `log |φ'| ρ` (Fubini).
* it is invariant under intrinsic re-embedding over times `T ⊇ [a, b]` (`IsIntrinsicCurveDecoratedReembedding.
  windowFieldIntr_eq`): with `φ₁ = f ∘ φ₂` on the disc (`windowDiscMapIntr_eq`), the coordinate change
  `h₂ = h₁ ∘ f + Q log |f'|` of the re-embedding applied to `(ρ ∘ ψ₂) |ψ₂'|²`, the change of variables `x = φ₂(w)`
  (`integral_mul_openChartTestFun`) and `log |φ₁'| = log |f' ∘ φ₂| + log |φ₂'|`; hence it is measurable for
  `intrinsicCurveDecoratedSurfaceSigma γ T`;
* when the window has an inverse chart, its time segments are regular closed and the curve visits `η(u)` only at `u`,
  it is the chart field `windowFieldBG` of Berestycki–Gwynne (`windowFieldBG_eq_windowFieldIntr`), since then
  `windowChartIntr = windowChartBG` on `U` (`windowGoodIntr_and_eqOn_windowChartBG`).

In a valid environment the last three conditions hold almost surely under `WindowFrontierJordanInput` (the frontier of
the window domain is a Jordan curve; Miller–Sheffield, Imaginary geometry IV), which gives
`bg20WindowFieldIntrinsicInput_of_windowFrontierJordan`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions

namespace MatedCRT

/-! ### Difference quotients -/

/-- The steps `1/(n+1)` of the difference quotients. -/
noncomputable def seqStep (n : ℕ) : ℂ :=
  ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

theorem seqStep_ne_zero (n : ℕ) : seqStep n ≠ 0 := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
  exact Complex.ofReal_ne_zero.2 hpos.ne'

theorem tendsto_seqStep : Tendsto seqStep atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Complex.ofReal_zero] at h
  exact h

/-- The difference quotient `(g(x + 1/(n+1)) - g(x)) (n + 1)`. -/
noncomputable def diffQuot (g : ℂ → ℂ) (x : ℂ) (n : ℕ) : ℂ :=
  (seqStep n)⁻¹ * (g (x + seqStep n) - g x)

theorem diffQuot_eq_slope (g : ℂ → ℂ) (x : ℂ) (n : ℕ) : diffQuot g x n = slope g x (x + seqStep n) := by
  rw [diffQuot, slope_def_field, add_sub_cancel_left, div_eq_inv_mul]

/-- The difference quotients of a function complex differentiable at `x` converge to its derivative. -/
theorem tendsto_diffQuot {g : ℂ → ℂ} {x : ℂ} (hg : DifferentiableAt ℂ g x) :
    Tendsto (fun n => diffQuot g x n) atTop (𝓝 (deriv g x)) := by
  have h1 : Tendsto (fun n => x + seqStep n) atTop (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h2 : Tendsto (fun n => x + seqStep n) atTop (𝓝 (x + 0)) := tendsto_const_nhds.add tendsto_seqStep
      rw [add_zero] at h2
      exact h2
    · rw [mem_compl_singleton_iff]
      intro h
      exact seqStep_ne_zero n (by simpa using h)
  have h3 := (hasDerivAt_iff_tendsto_slope.1 hg.hasDerivAt).comp h1
  refine h3.congr fun n => ?_
  exact (diffQuot_eq_slope g x n).symm

/-! ### Transported test functions for conformal maps of the open disc -/

/-- The transported function `x ↦ ρ(ψ x) |ψ'(x)|²` on `U`, extended by `0` outside `U`. -/
noncomputable def openChartTestFun (U : Set ℂ) (ψ : ℂ → ℂ) (ρ : ℂ → ℝ) : ℂ → ℝ :=
  U.indicator fun x => ρ (ψ x) * ‖deriv ψ x‖ ^ 2

section OpenChart

variable {U : Set ℂ} {φ ψ : ℂ → ℂ}

/-- A left inverse on `U` of a conformal map of the open disc onto `U` is holomorphic on `U`. -/
theorem IsOpenDiscMap.differentiableOn_of_leftInverse (hφ : IsOpenDiscMap U φ)
    (hφψ : ∀ x ∈ U, φ (ψ x) = x) (hψU : ∀ x ∈ U, ψ x ∈ ball (0 : ℂ) 1) : DifferentiableOn ℂ ψ U := by
  have hd := QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball hφ.differentiableOn hφ.injOn
  rw [hφ.image_ball] at hd
  refine hd.congr fun x hx => ?_
  have h1 := QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball hφ.differentiableOn hφ.injOn (hψU x hx)
  rw [hφψ x hx] at h1
  exact h1.symm

theorem openChartTestFun_eq_zero_of_notMem (hφψ : ∀ x ∈ U, φ (ψ x) = x) (ρ : ℂ → ℝ) {x : ℂ}
    (hx : x ∉ φ '' tsupport ρ) : openChartTestFun U ψ ρ x = 0 := by
  unfold openChartTestFun
  by_cases hxU : x ∈ U
  · have h0 : ρ (ψ x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨ψ x, h, hφψ x hxU⟩
    simp only [indicator_of_mem hxU, h0, zero_mul]
  · exact indicator_of_notMem hxU _

theorem contDiff_openChartTestFun (hφ : IsOpenDiscMap U φ) (hφψ : ∀ x ∈ U, φ (ψ x) = x)
    (hψU : ∀ x ∈ U, ψ x ∈ ball (0 : ℂ) 1) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (openChartTestFun U ψ ρ) := by
  have hU : IsOpen U := hφ.isOpen
  have hψd : DifferentiableOn ℂ ψ U := hφ.differentiableOn_of_leftInverse hφψ hψU
  have hψc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U := (hψd.contDiffOn hU).restrict_scalars ℝ
  have hψ'c : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv ψ) U :=
    ((hψd.deriv hU).contDiffOn hU).restrict_scalars ℝ
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ρ (ψ x) * ‖deriv ψ x‖ ^ 2) U :=
    (ρ.contDiff.comp_contDiffOn hψc).mul ((contDiff_norm_sq ℝ).comp_contDiffOn hψ'c)
  have hKD : tsupport ρ ⊆ ball (0 : ℂ) 1 := ρ.tsupport_subset
  have hK : IsCompact (φ '' tsupport ρ) :=
    (ρ.hasCompactSupport : IsCompact (tsupport ρ)).image_of_continuousOn (hφ.continuousOn.mono hKD)
  have hKU : φ '' tsupport ρ ⊆ U := (image_mono hKD).trans hφ.image_ball.subset
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · refine (hG.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  · have hxK : x ∉ φ '' tsupport ρ := fun h => hx (hKU h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact openChartTestFun_eq_zero_of_notMem hφψ _ hy

theorem hasCompactSupport_openChartTestFun (hφ : IsOpenDiscMap U φ) (hφψ : ∀ x ∈ U, φ (ψ x) = x)
    (ρ : 𝓓(unitDiscOpens, ℝ)) : HasCompactSupport (openChartTestFun U ψ ρ) := by
  have hKD : tsupport ρ ⊆ ball (0 : ℂ) 1 := ρ.tsupport_subset
  exact HasCompactSupport.intro ((ρ.hasCompactSupport : IsCompact (tsupport ρ)).image_of_continuousOn
    (hφ.continuousOn.mono hKD)) fun _ hx => openChartTestFun_eq_zero_of_notMem hφψ _ hx

/-- **Change of variables in the transported pairing.** For a conformal map `φ` of the open disc onto `U` and `ψ`
inverting it on the disc and holomorphic on `U`, `∫ g(x) (ρ ∘ ψ)(x) |ψ'(x)|² 1_U(x) dx = ∫ g(φ(w)) ρ(w) dw`. -/
theorem integral_mul_openChartTestFun (hφ : IsOpenDiscMap U φ) (hψφ : ∀ w ∈ ball (0 : ℂ) 1, ψ (φ w) = w)
    (hψd : DifferentiableOn ℂ ψ U) (g : ℂ → ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    ∫ x, g x * openChartTestFun U ψ ρ x = ∫ w, g (φ w) * ρ w := by
  have hU : IsOpen U := hφ.isOpen
  have hderiv : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt φ (fderiv ℝ φ w) (ball 0 1) w := fun w hw =>
    ((hφ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have h1 : ∫ x, g x * openChartTestFun U ψ ρ x =
      ∫ x in φ '' ball 0 1, g x * (ρ (ψ x) * ‖deriv ψ x‖ ^ 2) := by
    rw [hφ.image_ball, ← integral_indicator hU.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    unfold openChartTestFun
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  have h2 : ∫ w, g (φ w) * ρ w = ∫ w in ball (0 : ℂ) 1, g (φ w) * ρ w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by
      rw [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero]).symm
  rw [h1, integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) isOpen_ball.measurableSet hderiv hφ.injOn,
    h2]
  refine setIntegral_congr_fun isOpen_ball.measurableSet fun w hw => ?_
  have hφd : DifferentiableAt ℂ φ w := hφ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
  have hφU : φ w ∈ U := hφ.apply_mem hw
  have hψd' : DifferentiableAt ℂ ψ (φ w) := hψd.differentiableAt (hU.mem_nhds hφU)
  have hchain : deriv ψ (φ w) * deriv φ w = 1 := by
    rw [← deriv_comp w hψd' hφd]
    have hev : (ψ ∘ φ) =ᶠ[𝓝 w] id := by
      filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
      exact hψφ w' hw'
    rw [hev.deriv_eq, deriv_id]
  have hn : ‖deriv ψ (φ w)‖ ^ 2 * ‖deriv φ w‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, hchain, norm_one, one_pow]
  simp only [smul_eq_mul]
  rw [QuantumZipper.abs_det_fderiv_eq_normSq hφd, hψφ w hw]
  calc ‖deriv φ w‖ ^ 2 * (g (φ w) * (ρ w * ‖deriv ψ (φ w)‖ ^ 2))
      = g (φ w) * ρ w * (‖deriv ψ (φ w)‖ ^ 2 * ‖deriv φ w‖ ^ 2) := by ring
    _ = g (φ w) * ρ w := by rw [hn, mul_one]

end OpenChart

/-! ### The intrinsic chart field of a window -/

section Window

variable {a u b : ℝ} {η : C(ℝ, ℂ)}

theorem WindowGoodIntr.differentiableOn_windowChartIntr (hG : WindowGoodIntr a u b η) :
    DifferentiableOn ℂ (windowChartIntr a u b η) (windowDomain η a u b) :=
  hG.isOpenDiscMap.differentiableOn_of_leftInverse (fun _ hx => hG.windowDiscMapIntr_windowChartIntr hx)
    (fun x _ => windowChartIntr_mem_ball a u b η x)

theorem WindowGoodIntr.contDiff_windowTest (hG : WindowGoodIntr a u b η) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ) :=
  contDiff_openChartTestFun hG.isOpenDiscMap (fun _ hx => hG.windowDiscMapIntr_windowChartIntr hx)
    (fun x _ => windowChartIntr_mem_ball a u b η x) ρ

theorem WindowGoodIntr.hasCompactSupport_windowTest (hG : WindowGoodIntr a u b η) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    HasCompactSupport (openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ) :=
  hasCompactSupport_openChartTestFun hG.isOpenDiscMap (fun _ hx => hG.windowDiscMapIntr_windowChartIntr hx) ρ

end Window

open Classical in
/-- **The transported test function `1_U (ρ ∘ ψ) |ψ'|²` of the window for the intrinsic inverse chart `ψ`**, a test
function on the plane supported in the window domain `U` when the intrinsic construction succeeds (`0` otherwise). -/
noncomputable def windowTestIntr (a u b : ℝ) (η : C(ℝ, ℂ)) (ρ : 𝓓(unitDiscOpens, ℝ)) : LQGMetric.TestC :=
  if hG : WindowGoodIntr a u b η then
    ⟨openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ, hG.contDiff_windowTest ρ,
      hG.hasCompactSupport_windowTest ρ, fun _ _ => trivial⟩
  else 0

theorem windowTestIntr_apply {a u b : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η) (ρ : 𝓓(unitDiscOpens, ℝ))
    (x : ℂ) :
    windowTestIntr a u b η ρ x = openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ x := by
  unfold windowTestIntr
  rw [dite_eq_left hG]
  rfl

open Classical in
/-- **The intrinsic chart field of the window `(a, u, b)`**: `ρ ↦ ⟨h, 1_U (ρ ∘ ψ) |ψ'|²⟩ + Q ∫ log |φ'| ρ` for the
intrinsic inverse chart `ψ = windowChartIntr` and the conformal map `φ = windowDiscMapIntr` of the open disc onto the
window domain `U`, when the intrinsic construction succeeds (`0` otherwise). -/
noncomputable def windowFieldIntr (γ a u b : ℝ) (p : LQGMetric.DistC × C(ℝ, ℂ)) (ρ : 𝓓(unitDiscOpens, ℝ)) : ℝ :=
  if WindowGoodIntr a u b p.2 then
    p.1 (windowTestIntr a u b p.2 ρ) +
      MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (windowDiscMapIntr a u b p.2) w‖ * ρ w
  else 0

theorem windowFieldIntr_of_good {γ a u b : ℝ} {h : LQGMetric.DistC} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (ρ : 𝓓(unitDiscOpens, ℝ)) :
    windowFieldIntr γ a u b (h, η) ρ = h (windowTestIntr a u b η ρ) +
      MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (windowDiscMapIntr a u b η) w‖ * ρ w := by
  unfold windowFieldIntr
  exact ite_eq_left hG

theorem windowFieldIntr_of_not {γ a u b : ℝ} {h : LQGMetric.DistC} {η : C(ℝ, ℂ)} (hG : ¬WindowGoodIntr a u b η)
    (ρ : 𝓓(unitDiscOpens, ℝ)) : windowFieldIntr γ a u b (h, η) ρ = 0 := by
  unfold windowFieldIntr
  exact ite_eq_right hG

/-! ### Invariance under intrinsic re-embedding -/

namespace IsIntrinsicCurveDecoratedReembedding

variable {γ : ℝ} {T : Set ℝ} {h₁ h₂ : LQGMetric.DistC} {η₁ η₂ : C(ℝ, ℂ)} {f : ℂ → ℂ} {a u b : ℝ}

/-- **The intrinsic chart field of a window is invariant under intrinsic re-embedding** over times `T ⊇ [a, b]`
(Berestycki–Gwynne (2020), (2.1) and (7.34)). -/
theorem windowFieldIntr_eq (hf : IsIntrinsicCurveDecoratedReembedding γ T h₁ η₁ h₂ η₂ f) (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) : windowFieldIntr γ a u b (h₂, η₂) = windowFieldIntr γ a u b (h₁, η₁) := by
  funext ρ
  by_cases hG₂ : WindowGoodIntr a u b η₂
  swap
  · rw [windowFieldIntr_of_not hG₂, windowFieldIntr_of_not (mt (hf.windowGoodIntr_iff hJ hu).1 hG₂)]
  have hG₁ := (hf.windowGoodIntr_iff hJ hu).2 hG₂
  have hW := hf.image_windowDomain hJ hu
  have hφeq : ∀ w ∈ ball (0 : ℂ) 1, windowDiscMapIntr a u b η₁ w = f (windowDiscMapIntr a u b η₂ w) :=
    fun w hw => hf.windowDiscMapIntr_eq hJ hu hG₂ hw
  have hUint : windowDomain η₂ a u b ⊆ interior (η₂ '' T) := windowDomain_subset hJ η₂ u
  have h3 : InjOn f (interior (η₂ '' T)) := hf.2.2.1
  have h4 : DifferentiableOn ℂ f (interior (η₂ '' T)) := hf.2.2.2.1
  have h6 := hf.2.2.2.2.2
  have hφ₂ := hG₂.isOpenDiscMap
  have hψd₁ := hG₁.differentiableOn_windowChartIntr
  have hψd₂ := hG₂.differentiableOn_windowChartIntr
  have hcomp : ∀ x ∈ windowDomain η₂ a u b, windowChartIntr a u b η₁ (f x) = windowChartIntr a u b η₂ x := by
    intro x hx
    have hw := windowChartIntr_mem_ball a u b η₂ x
    have h1 : f x = windowDiscMapIntr a u b η₁ (windowChartIntr a u b η₂ x) := by
      rw [hφeq _ hw, hG₂.windowDiscMapIntr_windowChartIntr hx]
    rw [h1, hG₁.windowChartIntr_windowDiscMapIntr hw]
  -- the coordinate change `h₂ = h₁ ∘ f + Q log |f'|` on the transported test function
  have hKD : tsupport ρ ⊆ ball (0 : ℂ) 1 := ρ.tsupport_subset
  have hK₂ : IsCompact (windowDiscMapIntr a u b η₂ '' tsupport ρ) :=
    (ρ.hasCompactSupport : IsCompact (tsupport ρ)).image_of_continuousOn (hφ₂.continuousOn.mono hKD)
  have hKU₂ : windowDiscMapIntr a u b η₂ '' tsupport ρ ⊆ windowDomain η₂ a u b :=
    (image_mono hKD).trans hφ₂.image_ball.subset
  have hsupp : tsupport (windowTestIntr a u b η₂ ρ : ℂ → ℝ) ⊆ interior (η₂ '' T) := by
    unfold tsupport
    refine (closure_minimal (fun x hx => ?_) hK₂.isClosed).trans (hKU₂.trans hUint)
    by_contra hxK
    exact hx ((windowTestIntr_apply hG₂ ρ x).trans (openChartTestFun_eq_zero_of_notMem
      (φ := windowDiscMapIntr a u b η₂) (fun _ hy => hG₂.windowDiscMapIntr_windowChartIntr hy) _ hxK))
  have hcoord : ∀ x ∈ interior (η₂ '' T),
      (windowTestIntr a u b η₁ ρ) (f x) * ‖deriv f x‖ ^ 2 = (windowTestIntr a u b η₂ ρ) x := by
    intro x hx
    rw [windowTestIntr_apply hG₁, windowTestIntr_apply hG₂]
    unfold openChartTestFun
    by_cases hxU : x ∈ windowDomain η₂ a u b
    · have hfx : f x ∈ windowDomain η₁ a u b := hW ▸ mem_image_of_mem f hxU
      simp only [indicator_of_mem hfx, indicator_of_mem hxU]
      rw [hcomp x hxU]
      have hfd : DifferentiableAt ℂ f x := h4.differentiableAt (isOpen_interior.mem_nhds hx)
      have hψ₁d : DifferentiableAt ℂ (windowChartIntr a u b η₁) (f x) :=
        hψd₁.differentiableAt (hG₁.isOpenDiscMap.isOpen.mem_nhds hfx)
      have hd : deriv (windowChartIntr a u b η₂) x = deriv (windowChartIntr a u b η₁) (f x) * deriv f x := by
        rw [← deriv_comp x hψ₁d hfd]
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [hφ₂.isOpen.mem_nhds hxU] with y hy
        exact (hcomp y hy).symm
      rw [hd, norm_mul, mul_pow]
      ring
    · have hfx : f x ∉ windowDomain η₁ a u b := by
        rw [← hW]
        rintro ⟨y, hy, hfy⟩
        obtain rfl : y = x := h3 (hUint hy) hx hfy
        exact hxU hy
      simp only [indicator_of_notMem hfx, indicator_of_notMem hxU, zero_mul]
  have hzero : ∀ y, y ∉ f '' interior (η₂ '' T) → (windowTestIntr a u b η₁ ρ) y = 0 := by
    intro y hy
    rw [windowTestIntr_apply hG₁]
    unfold openChartTestFun
    refine indicator_of_notMem (fun hyU => hy ?_) _
    rw [← hW] at hyU
    exact image_mono hUint hyU
  have hpair := h6 _ _ hsupp hcoord hzero
  -- the change of variables `x = φ₂(w)` and `φ₁ = f ∘ φ₂`
  have hf'0 : ∀ w ∈ ball (0 : ℂ) 1, deriv f (windowDiscMapIntr a u b η₂ w) ≠ 0 := fun w hw =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_interior h4 h3 (hUint (hφ₂.apply_mem hw))
  have hI1 : ∫ x, Real.log ‖deriv f x‖ * (windowTestIntr a u b η₂ ρ) x =
      ∫ w, Real.log ‖deriv f (windowDiscMapIntr a u b η₂ w)‖ * ρ w := by
    simp only [windowTestIntr_apply hG₂]
    exact integral_mul_openChartTestFun hφ₂ (fun w hw => hG₂.windowChartIntr_windowDiscMapIntr hw) hψd₂
      (fun x => Real.log ‖deriv f x‖) ρ
  have hI3 : ∫ w, Real.log ‖deriv (windowDiscMapIntr a u b η₁) w‖ * ρ w =
      ∫ w, (Real.log ‖deriv f (windowDiscMapIntr a u b η₂ w)‖ * ρ w +
        Real.log ‖deriv (windowDiscMapIntr a u b η₂) w‖ * ρ w) := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · have hfd : DifferentiableAt ℂ f (windowDiscMapIntr a u b η₂ w) :=
        h4.differentiableAt (isOpen_interior.mem_nhds (hUint (hφ₂.apply_mem hw)))
      have hφd : DifferentiableAt ℂ (windowDiscMapIntr a u b η₂) w :=
        hφ₂.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
      have hev : windowDiscMapIntr a u b η₁ =ᶠ[𝓝 w] f ∘ windowDiscMapIntr a u b η₂ := by
        filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
        exact hφeq w' hw'
      dsimp only
      rw [hev.deriv_eq, deriv_comp w hfd hφd, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (hf'0 w hw)) (norm_ne_zero_iff.2 (hφ₂.deriv_ne_zero hw)), add_mul]
    · simp only [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero, add_zero]
  have hA : Integrable fun w => Real.log ‖deriv f (windowDiscMapIntr a u b η₂ w)‖ * ρ w :=
    integrable_log_norm_mul_test (g := fun w => deriv f (windowDiscMapIntr a u b η₂ w))
      ((h4.deriv isOpen_interior).continuousOn.comp hφ₂.continuousOn fun w hw => hUint (hφ₂.apply_mem hw))
      hf'0 ρ
  have hB : Integrable fun w => Real.log ‖deriv (windowDiscMapIntr a u b η₂) w‖ * ρ w :=
    integrable_log_norm_mul_test (hφ₂.differentiableOn.deriv isOpen_ball).continuousOn
      (fun w hw => hφ₂.deriv_ne_zero hw) ρ
  rw [windowFieldIntr_of_good hG₂, windowFieldIntr_of_good hG₁, hpair, hI1, hI3, integral_add hA hB]
  ring

end IsIntrinsicCurveDecoratedReembedding

/-! ### Measurability -/

theorem measurable_windowChartIntr_apply (a u b : ℝ) (x : ℂ) :
    Measurable fun η : C(ℝ, ℂ) => windowChartIntr a u b η x := by
  have h := (measurable_windowChartIntr a u b).comp
    (measurable_id'.prodMk (measurable_const : Measurable fun _ : C(ℝ, ℂ) => x))
  simp only [Function.comp_def] at h
  exact h

theorem measurable_diffQuot_windowChartIntr (a u b : ℝ) (x : ℂ) (n : ℕ) :
    Measurable fun η : C(ℝ, ℂ) => diffQuot (windowChartIntr a u b η) x n :=
  measurable_const.mul
    ((measurable_windowChartIntr_apply a u b _).sub (measurable_windowChartIntr_apply a u b x))

theorem measurable_discToPlane : Measurable discToPlane := by
  have h1 : Measurable fun w : ℂ => (1 : ℝ) - ‖w‖ := measurable_const.sub measurable_norm
  unfold discToPlane
  exact h1.inv.smul measurable_id

theorem measurable_windowDiscMapIntr (a u b : ℝ) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => windowDiscMapIntr a u b p.1 p.2 := by
  have hr : Measurable fun p : C(ℝ, ℂ) × ℂ => (unitRotation (windowEntryPoint a u b p.1))⁻¹ * p.2 :=
    ((measurable_unitRotation.comp ((measurable_windowEntryPoint a u b).comp measurable_fst)).inv).mul
      measurable_snd
  have hc : Measurable fun p : C(ℝ, ℂ) × ℂ => openWindowDiscCode a u b p.1 :=
    (measurable_openWindowDiscCode a u b).comp measurable_fst
  have hev : Measurable fun q : C(ℂ, ℂ) × ℂ => q.1 q.2 := continuous_eval.measurable
  have h := hev.comp (hc.prodMk (measurable_discToPlane.comp hr))
  simp only [Function.comp_def] at h
  show Measurable fun p : C(ℝ, ℂ) × ℂ =>
    openWindowDiscCode a u b p.1 (discToPlane ((unitRotation (windowEntryPoint a u b p.1))⁻¹ * p.2))
  exact h

theorem measurable_diffQuot_windowDiscMapIntr (a u b : ℝ) (n : ℕ) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => diffQuot (windowDiscMapIntr a u b p.1) p.2 n := by
  have h0 := measurable_windowDiscMapIntr a u b
  have h1 : Measurable fun p : C(ℝ, ℂ) × ℂ => windowDiscMapIntr a u b p.1 (p.2 + seqStep n) := by
    have h := h0.comp (measurable_fst.prodMk (measurable_snd.add_const (seqStep n)))
    simp only [Function.comp_def] at h
    exact h
  exact measurable_const.mul (h1.sub h0)

/-- The curves for which the intrinsic construction of the window succeeds and whose segment `η([a, b])` lies in the
closed disc of radius `R`. -/
def windowGoodIntrR (a u b : ℝ) (R : ℕ) : Set C(ℝ, ℂ) :=
  {η | WindowGoodIntr a u b η} ∩ {η | ∀ t ∈ Icc a b, η t ∈ closedBall (0 : ℂ) R}

theorem measurableSet_windowGoodIntrR (a u b : ℝ) (R : ℕ) : MeasurableSet (windowGoodIntrR a u b R) := by
  refine (measurableSet_setOf_windowGoodIntr a u b).inter ?_
  have hc : IsClosed {η : C(ℝ, ℂ) | ∀ t ∈ Icc a b, η t ∈ closedBall (0 : ℂ) R} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_closedBall.preimage (continuous_eval_const t)
  exact hc.measurableSet

theorem windowDomain_subset_closedBall {a u b : ℝ} {R : ℕ} {η : C(ℝ, ℂ)} (hη : η ∈ windowGoodIntrR a u b R) :
    windowDomain η a u b ⊆ closedBall (0 : ℂ) R := fun x hx => by
  obtain ⟨t, ht, rfl⟩ := windowDomain_subset_image η a u b hx
  exact hη.2 t ht

/-- The curves of `windowGoodIntrR a u b R` whose window domain contains `x`. -/
def windowGoodIntrRAt (a u b : ℝ) (R : ℕ) (x : ℂ) : Set C(ℝ, ℂ) :=
  windowGoodIntrR a u b R ∩ {η | x ∈ windowDomain η a u b}

theorem measurableSet_windowGoodIntrRAt (a u b : ℝ) (R : ℕ) (x : ℂ) :
    MeasurableSet (windowGoodIntrRAt a u b R x) :=
  (measurableSet_windowGoodIntrR a u b R).inter
    (measurableSet_setOf_mem_windowDomain a u b (f := fun _ => x) measurable_const)

open Classical in
/-- The values of the transported test function are Borel functions of the curve: limits of the difference quotients
of the Borel map `η ↦ ψ_η(x)`. -/
theorem measurable_windowTestValueIntr (a u b : ℝ) {g : ℂ → ℝ} (hg : Continuous g) (R : ℕ) (x : ℂ) :
    Measurable fun η : C(ℝ, ℂ) => if η ∈ windowGoodIntrR a u b R then
      openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) g x else 0 := by
  have hm := measurableSet_windowGoodIntrRAt a u b R x
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (η : C(ℝ, ℂ)) =>
      if η ∈ windowGoodIntrRAt a u b R x then
        g (windowChartIntr a u b η x) * ‖diffQuot (windowChartIntr a u b η) x n‖ ^ 2 else 0)
    (fun n => Measurable.ite hm ((hg.measurable.comp (measurable_windowChartIntr_apply a u b x)).mul
      ((measurable_diffQuot_windowChartIntr a u b x n).norm.pow_const 2)) measurable_const)
    (tendsto_pi_nhds.2 fun η => ?_)
  by_cases hη : η ∈ windowGoodIntrRAt a u b R x
  · have hR : η ∈ windowGoodIntrR a u b R := hη.1
    have hG : WindowGoodIntr a u b η := hR.1
    have hxU : x ∈ windowDomain η a u b := hη.2
    have hd : DifferentiableAt ℂ (windowChartIntr a u b η) x :=
      hG.differentiableOn_windowChartIntr.differentiableAt (hG.isOpenDiscMap.isOpen.mem_nhds hxU)
    simp only [ite_eq_left hη, ite_eq_left hR]
    unfold openChartTestFun
    rw [indicator_of_mem hxU]
    exact tendsto_const_nhds.mul ((tendsto_diffQuot hd).norm.pow 2)
  · simp only [ite_eq_right hη]
    by_cases hR : η ∈ windowGoodIntrR a u b R
    · have hxU : x ∉ windowDomain η a u b := fun h => hη ⟨hR, h⟩
      simp only [ite_eq_left hR]
      unfold openChartTestFun
      rw [indicator_of_notMem hxU]
      exact tendsto_const_nhds
    · simp only [ite_eq_right hR]
      exact tendsto_const_nhds

open Classical in
/-- **The transported test function of the window as an element of `𝓓_{K_R}`** on the curves of
`windowGoodIntrR a u b R` (and `0` otherwise). -/
noncomputable def windowTestIntrK (a u b : ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) (η : C(ℝ, ℂ)) :
    𝓓^{⊤}_{closedBallCompacts R}(ℂ, ℝ) :=
  if hη : η ∈ windowGoodIntrR a u b R then
    { toFun := openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ
      contDiff' := WindowGoodIntr.contDiff_windowTest hη.1 ρ
      zero_on_compl' := fun _ hx =>
        indicator_of_notMem (fun hxU => hx (windowDomain_subset_closedBall hη hxU)) _ }
  else 0

open Classical in
theorem windowTestIntrK_apply (a u b : ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) (η : C(ℝ, ℂ)) (x : ℂ) :
    windowTestIntrK a u b ρ R η x = if η ∈ windowGoodIntrR a u b R then
      openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ x else 0 := by
  by_cases hη : η ∈ windowGoodIntrR a u b R
  · rw [ite_eq_left hη]
    unfold windowTestIntrK
    rw [dite_eq_left hη]
    rfl
  · rw [ite_eq_right hη]
    unfold windowTestIntrK
    rw [dite_eq_right hη]
    rfl

open Classical in
theorem measurable_windowTestIntrK (a u b : ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) :
    Measurable (windowTestIntrK a u b ρ R) := by
  refine (measurable_testK_iff (closedBallCompacts R)).2 fun x => ?_
  have heq : (fun η => windowTestIntrK a u b ρ R η x) = fun η => if η ∈ windowGoodIntrR a u b R then
      openChartTestFun (windowDomain η a u b) (windowChartIntr a u b η) ρ x else 0 :=
    funext fun η => windowTestIntrK_apply a u b ρ R η x
  rw [heq]
  exact measurable_windowTestValueIntr a u b ρ.contDiff.continuous R x

theorem measurable_windowPairingIntrK (a u b : ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) (R : ℕ) :
    Measurable fun p : LQGMetric.DistC × C(ℝ, ℂ) =>
      p.1 (testKToTestC (closedBallCompacts R) (windowTestIntrK a u b ρ R p.2)) :=
  (measurable_distC_apply_testK (closedBallCompacts R)).comp
    (((measurable_windowTestIntrK a u b ρ R).comp measurable_snd).prodMk measurable_fst)

/-- The pairs (curve, point of the open disc) for which the intrinsic construction of the window succeeds. -/
def windowGoodBall (a u b : ℝ) : Set (C(ℝ, ℂ) × ℂ) :=
  {p | WindowGoodIntr a u b p.1 ∧ p.2 ∈ ball (0 : ℂ) 1}

theorem measurableSet_windowGoodBall (a u b : ℝ) : MeasurableSet (windowGoodBall a u b) :=
  (measurable_fst (measurableSet_setOf_windowGoodIntr a u b)).inter (measurable_snd measurableSet_ball)

open Classical in
/-- The term `∫ log |φ'| ρ` of the intrinsic chart field, with the integrand set to `0` off `windowGoodBall`, is a
Borel function of the curve (Fubini; the integrand is a limit of difference quotients). -/
theorem measurable_windowLogDerivIntr (a u b : ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    Measurable fun η : C(ℝ, ℂ) => ∫ w, (if (η, w) ∈ windowGoodBall a u b then
      Real.log ‖deriv (windowDiscMapIntr a u b η) w‖ * ρ w else 0) := by
  have hj : Measurable fun p : C(ℝ, ℂ) × ℂ => if p ∈ windowGoodBall a u b then
      Real.log ‖deriv (windowDiscMapIntr a u b p.1) p.2‖ * ρ p.2 else 0 := by
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (p : C(ℝ, ℂ) × ℂ) =>
        if p ∈ windowGoodBall a u b then
          Real.log ‖diffQuot (windowDiscMapIntr a u b p.1) p.2 n‖ * ρ p.2 else 0)
      (fun n => Measurable.ite (measurableSet_windowGoodBall a u b)
        ((Real.measurable_log.comp (measurable_diffQuot_windowDiscMapIntr a u b n).norm).mul
          (ρ.contDiff.continuous.measurable.comp measurable_snd)) measurable_const)
      (tendsto_pi_nhds.2 fun p => ?_)
    by_cases hp : p ∈ windowGoodBall a u b
    · have hG : WindowGoodIntr a u b p.1 := hp.1
      have hw : p.2 ∈ ball (0 : ℂ) 1 := hp.2
      have hφ := hG.isOpenDiscMap
      have hd : DifferentiableAt ℂ (windowDiscMapIntr a u b p.1) p.2 :=
        hφ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hw)
      simp only [ite_eq_left hp]
      exact (((tendsto_diffQuot hd).norm).log (norm_ne_zero_iff.2 (hφ.deriv_ne_zero hw))).mul tendsto_const_nhds
    · simp only [ite_eq_right hp]
      exact tendsto_const_nhds
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

open Classical in
theorem integral_logDeriv_windowDiscMapIntr {a u b : ℝ} {η : C(ℝ, ℂ)} (hG : WindowGoodIntr a u b η)
    (ρ : 𝓓(unitDiscOpens, ℝ)) :
    ∫ w, Real.log ‖deriv (windowDiscMapIntr a u b η) w‖ * ρ w =
      ∫ w, (if (η, w) ∈ windowGoodBall a u b then Real.log ‖deriv (windowDiscMapIntr a u b η) w‖ * ρ w else 0) := by
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ ball (0 : ℂ) 1
  · have hp : (η, w) ∈ windowGoodBall a u b := ⟨hG, hw⟩
    exact (ite_eq_left hp).symm
  · simp only [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero, ite_self]

open Classical in
/-- **The intrinsic chart field is measurable, tested against a test function on the disc.** -/
theorem measurable_windowFieldIntr_apply (γ a u b : ℝ) (ρ : 𝓓(unitDiscOpens, ℝ)) :
    Measurable fun p : LQGMetric.DistC × C(ℝ, ℂ) => windowFieldIntr γ a u b p ρ := by
  have hL := measurable_windowLogDerivIntr a u b ρ
  refine measurable_of_tendsto_metrizable (f := fun (R : ℕ) (p : LQGMetric.DistC × C(ℝ, ℂ)) =>
      if p.2 ∈ windowGoodIntrR a u b R then
        p.1 (testKToTestC (closedBallCompacts R) (windowTestIntrK a u b ρ R p.2)) +
          MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, (if (p.2, w) ∈ windowGoodBall a u b then
            Real.log ‖deriv (windowDiscMapIntr a u b p.2) w‖ * ρ w else 0)
      else 0)
    (fun R => Measurable.ite (measurable_snd (measurableSet_windowGoodIntrR a u b R))
      ((measurable_windowPairingIntrK a u b ρ R).add ((hL.comp measurable_snd).const_mul _)) measurable_const)
    (tendsto_pi_nhds.2 fun p => ?_)
  obtain ⟨h, η⟩ := p
  dsimp only
  by_cases hG : WindowGoodIntr a u b η
  · obtain ⟨r, hr⟩ := (isCompact_Icc.image η.continuous).isBounded.subset_closedBall (0 : ℂ)
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈r⌉₊) fun R hR => ?_
    have hηR : η ∈ windowGoodIntrR a u b R := ⟨hG, fun t ht =>
      closedBall_subset_closedBall ((Nat.le_ceil r).trans (Nat.cast_le.2 hR)) (hr (mem_image_of_mem _ ht))⟩
    have htest : testKToTestC (closedBallCompacts R) (windowTestIntrK a u b ρ R η) = windowTestIntr a u b η ρ := by
      ext x
      rw [testKToTestC_apply, windowTestIntrK_apply, ite_eq_left hηR, windowTestIntr_apply hG]
    rw [ite_eq_left hηR, windowFieldIntr_of_good hG, integral_logDeriv_windowDiscMapIntr hG ρ, htest]
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun R _ => ?_
    rw [ite_eq_right fun hR => hG hR.1, windowFieldIntr_of_not hG]

/-- **The intrinsic chart field of a window is a Borel function of (field, curve).** -/
theorem measurable_windowFieldIntr (γ a u b : ℝ) : Measurable (windowFieldIntr γ a u b) :=
  measurable_pi_iff.2 fun ρ => measurable_windowFieldIntr_apply γ a u b ρ

/-- A Borel function of (field, curve) taking the same value at two pairs with the same intrinsic curve-decorated
surface over `T` is measurable for `intrinsicCurveDecoratedSurfaceSigma γ T`. -/
theorem measurable_intrinsicCurveDecoratedSurfaceSigma_of_forall_eq {γ : ℝ} {T : Set ℝ} {β : Type*}
    [MeasurableSpace β] {F : LQGMetric.DistC × C(ℝ, ℂ) → β} (hF : Measurable F)
    (hinv : ∀ p₁ p₂, IsSameIntrinsicCurveDecoratedSurface γ T p₁ p₂ → F p₁ = F p₂) :
    Measurable[intrinsicCurveDecoratedSurfaceSigma γ T] F := fun _ hA =>
  ⟨hF hA, fun p₁ p₂ h => by rw [mem_preimage, mem_preimage, hinv p₁ p₂ h]⟩

/-- **The intrinsic chart field is a function of the intrinsic curve-decorated surface over `T ⊇ [a, b]`.** -/
theorem measurable_intrinsicSigma_windowFieldIntr {γ : ℝ} {T : Set ℝ} {a u b : ℝ} (hJ : Icc a b ⊆ T)
    (hu : u ∈ Icc a b) : Measurable[intrinsicCurveDecoratedSurfaceSigma γ T] (windowFieldIntr γ a u b) := by
  refine measurable_intrinsicCurveDecoratedSurfaceSigma_of_forall_eq (measurable_windowFieldIntr γ a u b) ?_
  rintro ⟨h₁, η₁⟩ ⟨h₂, η₂⟩ ⟨f, hf⟩
  exact (hf.windowFieldIntr_eq hJ hu).symm

/-! ### The intrinsic chart field is the chart field of Berestycki–Gwynne -/

/-- When the window has an inverse chart, its time segments are regular closed and the curve visits `η(u)` only at
the time `u`, the intrinsic chart field is the chart field `windowFieldBG` for the inverse chart `windowChartBG`. -/
theorem windowFieldBG_eq_windowFieldIntr {γ a u b : ℝ} {η : C(ℝ, ℂ)} (hau : a < u)
    (hψ : ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ) (hreg : SegmentsRegularClosed η)
    (hfib : ∀ t, η t = η u → t = u) (h : LQGMetric.DistC) :
    windowFieldBG γ a u b (h, η) = windowFieldIntr γ a u b (h, η) := by
  obtain ⟨hG, heq⟩ := windowGoodIntr_and_eqOn_windowChartBG hau hψ hreg hfib
  have hψBG := isInverseChart_windowChartBG hψ
  have hU : IsOpen (windowDomain η a u b) := isOpen_windowDomain η a u b
  have hc : IsInverseChart (windowDomain η a u b) (η u) (windowChartBG a u b η) ∧
      IsOpen (windowDomain η a u b) ∧ Bornology.IsBounded (windowDomain η a u b) :=
    ⟨hψBG, hU, isBounded_windowDomain η a u b⟩
  funext ρ
  rw [windowFieldIntr_of_good hG]
  show chartFieldPairing γ h (windowDomain η a u b) (η u) (windowChartBG a u b η) ρ = _
  rw [chartFieldPairing_eq_of_isInverseChart hc]
  have htest : chartTest hc.1 hc.2.1 hc.2.2 ρ = windowTestIntr a u b η ρ := by
    ext x
    rw [chartTest_apply, windowTestIntr_apply hG]
    unfold chartTestFun openChartTestFun
    by_cases hx : x ∈ windowDomain η a u b
    · have hd : deriv (windowChartBG a u b η) x = deriv (windowChartIntr a u b η) x :=
        Filter.EventuallyEq.deriv_eq (by
          filter_upwards [hU.mem_nhds hx] with y hy
          exact heq y hy)
      simp only [indicator_of_mem hx, heq x hx, hd]
    · simp only [indicator_of_notMem hx]
  have hmap : ∀ w ∈ ball (0 : ℂ) 1,
      chartMap (windowDomain η a u b) (windowChartBG a u b η) w = windowDiscMapIntr a u b η w := by
    intro w hw
    have hφU : windowDiscMapIntr a u b η w ∈ windowDomain η a u b := hG.isOpenDiscMap.apply_mem hw
    have hψw : windowChartBG a u b η (windowDiscMapIntr a u b η w) = w := by
      rw [heq _ hφU, hG.windowChartIntr_windowDiscMapIntr hw]
    have hex : ∃ x ∈ windowDomain η a u b, windowChartBG a u b η x = w := ⟨_, hφU, hψw⟩
    exact hψBG.injOn (subset_closure (Function.invFunOn_mem hex)) (subset_closure hφU)
      ((Function.invFunOn_eq hex).trans hψw.symm)
  have hint : ∀ w, Real.log ‖deriv (chartMap (windowDomain η a u b) (windowChartBG a u b η)) w‖ * ρ w =
      Real.log ‖deriv (windowDiscMapIntr a u b η) w‖ * ρ w := by
    intro w
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · have hd : deriv (chartMap (windowDomain η a u b) (windowChartBG a u b η)) w =
          deriv (windowDiscMapIntr a u b η) w :=
        Filter.EventuallyEq.deriv_eq (by
          filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
          exact hmap w' hw')
      rw [hd]
    · rw [testFunction_eq_zero_of_notMem_ball ρ hw, mul_zero, mul_zero]
  simp only [htest, integral_congr_ae (Eventually.of_forall hint)]

/-! ### The step of the proof of Lemma 7.21 -/

/-- **Berestycki–Gwynne (2020), proof of Lemma 7.21, with the two quantum surfaces
of (7.35) taken as intrinsic curve-decorated wedges (`BG20WindowFieldIntrinsicInput`)**, from `WindowFrontierJordanInput`
(the frontier of the window domain is almost surely a Jordan curve; Miller–Sheffield, Imaginary geometry IV, used in
Berestycki–Gwynne, proof of Lemma 7.21). The function is the intrinsic chart field `windowFieldIntr`: it is
measurable for `intrinsicCurveDecoratedSurfaceSigma γ (Iic s)` when `b < s` and for
`intrinsicCurveDecoratedSurfaceSigma γ (Ici s)` when `s < a` (`measurable_intrinsicSigma_windowFieldIntr`), and it
agrees almost surely with the chart field: the window has an inverse chart (`exists_isInverseChart_windowDomain`,
from the Jordan frontier and `MatedCRTEnv.IsValid.ae_fixedTime_mem_interior_image`), the time segments of the curve are
regular closed (`MatedCRTEnv.IsValid.ae_regularClosed_segmentImages`) and the curve visits `η(u)` only at the time `u`
(`MatedCRTEnv.IsValid.ae_fixedTime_singleton_fibre`), so `windowFieldBG_eq_windowFieldIntr` applies. -/
theorem bg20WindowFieldIntrinsicInput_of_windowFrontierJordan {𝒮 : SpaceFillingSLEModel}
    (hG : WindowFrontierJordanInput 𝒮) : BG20WindowFieldIntrinsicInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' _ hae H _ _ a u b s hau hub
  have hae' : ∀ᵐ ω ∂S.P, windowFieldBG γ a u b (H ω, η' ω) = windowFieldIntr γ a u b (H ω, η' ω) := by
    filter_upwards [hS.ae_fixedTime_mem_interior_image u, hG γ hγ hγ2 Ω S hS a u b hau hub,
      hS.ae_regularClosed_segmentImages, hS.ae_fixedTime_singleton_fibre u, hae] with ω hω hJ hr hfb he
    have hψ : ∃ ψ, IsInverseChart (windowDomain (η' ω) a u b) (η' ω u) ψ := by
      refine exists_isInverseChart_windowDomain (η' ω) ?_ ?_
      · rw [he]
        exact hω a b hau hub
      · rw [windowDomain_eq_of_coe_eq he]
        exact hJ
    have hreg : SegmentsRegularClosed (η' ω) := fun c d hcd => by
      rw [he]
      exact hr c d hcd
    have hfib : ∀ t, η' ω t = η' ω u → t = u := fun t ht => by
      rw [he] at ht
      exact hfb t ht
    exact windowFieldBG_eq_windowFieldIntr hau hψ hreg hfib (H ω)
  have hu : u ∈ Icc a b := ⟨hau.le, hub.le⟩
  exact ⟨fun hbs => ⟨windowFieldIntr γ a u b,
      measurable_intrinsicSigma_windowFieldIntr (Icc_subset_Iic_self.trans (Iic_subset_Iic.2 hbs.le)) hu, hae'⟩,
    fun hsa => ⟨windowFieldIntr γ a u b,
      measurable_intrinsicSigma_windowFieldIntr (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hsa.le)) hu, hae'⟩⟩

end MatedCRT
