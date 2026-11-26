import MatedCRT.FirstPass.Derived.ChartClockChangeOfVariables
import MatedCRT.FirstPass.Derived.ChartTransportMeasurable
import MatedCRT.FirstPass.Derived.OptionalTimePastVariable
import MatedCRT.FirstPass.Derived.PlanarBrownianExitDynkin
import MatedCRT.FirstPass.Derived.LQGClockApproxAdapted
import MatedCRT.FirstPass.Derived.LQGApproxLawKernel
import MatedCRT.FirstPass.Derived.ChartClockTransport
import MatedCRT.FirstPass.Derived.LBMPathRestart
import MatedCRT.FirstPass.Derived.PlanarOptionalTimeStrongMarkov
import MatedCRT.FirstPass.Derived.PlanarBrownianStoppedOccupationBound
import MatedCRT.FirstPass.Derived.RevuzOptionalClockInverse
import MatedCRT.Proofs.LBM.TimeChangeContinuity
import HarmonicBalls.Proofs.Potential.BrownianPairOccupationBound
import HarmonicBalls.Proofs.Sec6.BrownianScaling
import HarmonicBalls.FirstPass.S11d.SmoothCutoff

/-!
# Lévy's conformal invariance of planar Brownian motion for an inverse chart

Let `U ⊂ ℂ` be a bounded domain, `ψ : U → 𝔻` an inverse chart (a conformal map onto the unit disc, extended
continuously to `ℂ`), and `b` planar Brownian motion from `w ∈ U`. With the conformal clock
`A(t) = ∫_0^{t ∧ τ_U} |ψ'(b_s)|² ds` (`chartClock`), the chart path `Y_σ = ψ(b_{A⁻¹(σ) ∧ τ_U})` is planar Brownian
motion from `ψ(w)` stopped at its exit from the unit disc (`levyConformalChartStmt`). The proof uses no stochastic
calculus.

* **The clock at the boundary.** Dynkin's formula for `|ψ|²` through the chart (the conformal covariance
  `Δ(f ∘ ψ) = |ψ'|² (Δf) ∘ ψ`, `½ Δ|ψ|² = 2|ψ'|²`, `|ψ| ≤ 1`) bounds the mean of the clock before the exit
  time by `1/2`, so the clock at the exit time is almost surely finite.
* **Dynkin's identity for the chart path.** For a plane wave `f = e^{i⟪ξ, ·⟫}`, localization of the chart on an
  exhaustion of `U` and the time change by the clock give `E f(Y_{t ∧ L}) = f(ψ(w)) - (|ξ|²/2) E ∫_0^{t ∧ L} f(Y_σ) dσ`,
  where `L = A(τ_U)`.
* **The continued chart path.** Continue `Y` after `L` by the Brownian increments after `τ_U` (`zPath`). The strong
  Markov property at `τ_U` and the Gaussian decay of plane waves give a linear Volterra equation for the mean of
  `f(Z_t)`, whose bounded solutions are `e^{-|ξ|² t/2} f(ψ(w))`.
* **Increments.** At the optional time `A⁻¹(s)` the future of `Z` is the continued chart path of the shifted
  Brownian path before the exit and the shifted Brownian path after it; the strong Markov property then shows that
  `Z` has independent standard Gaussian increments, so `Z` is planar Brownian motion from `ψ(w)`, and `Y` is `Z`
  stopped at its exit from the unit disc.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.LevyChart

section ConformalCovariance

open Laplacian _root_.HarmonicBalls.Section6


/-! ### Conformal covariance of the Laplacian

Adapted from Leonardo Bonanno's formalizations (https://github.com/leobon12/lean-formalizations),
source `SmallGammaGeodesics/NIC/Laplacian.lean` (`bilin_scale`, `fderiv_fderiv_comp`, `laplacian_eq_fderiv_fderiv`,
`laplacian_comp_holomorphic`). -/

theorem bilin_scale_aux (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (p q : ℝ) :
    B (p • (1 : ℂ) + q • Complex.I) (p • (1 : ℂ) + q • Complex.I) +
      B ((-q) • (1 : ℂ) + p • Complex.I) ((-q) • (1 : ℂ) + p • Complex.I) =
      (p ^ 2 + q ^ 2) * (B 1 1 + B Complex.I Complex.I) := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- `B(a, a) + B(ia, ia) = ‖a‖² (B(1,1) + B(i,i))` for a real bilinear form `B` on `ℂ`. -/
theorem bilin_scale (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    B a a + B (Complex.I * a) (Complex.I * a) = ‖a‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by
  have ea : a = a.re • (1 : ℂ) + a.im • Complex.I := by apply Complex.ext <;> simp
  have eb : Complex.I * a = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp
  have hn : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  calc B a a + B (Complex.I * a) (Complex.I * a)
      = B (a.re • (1 : ℂ) + a.im • Complex.I) (a.re • (1 : ℂ) + a.im • Complex.I) +
        B ((-a.im) • (1 : ℂ) + a.re • Complex.I) ((-a.im) • (1 : ℂ) + a.re • Complex.I) := by
          rw [← ea, ← eb]
    _ = (a.re ^ 2 + a.im ^ 2) * (B 1 1 + B Complex.I Complex.I) := bilin_scale_aux B a.re a.im
    _ = ‖a‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by rw [hn]

theorem withTop_two_ne_zero : (2 : WithTop ℕ∞) ≠ 0 := by norm_num

theorem withTop_one_add_one_le_two : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num

/-- `D²(F ∘ Ψ)(z)(m₀, m₁) = D²F(Ψ z)(DΨ(z) m₀, DΨ(z) m₁) + DF(Ψ z)(D²Ψ(z)(m₀, m₁))` -/
theorem fderiv_fderiv_comp {F : ℂ → ℝ} {Ψ : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (hΨ : ContDiff ℝ 2 Ψ)
    (z m₀ m₁ : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => F (Ψ y))) z m₀ m₁ =
      fderiv ℝ (fderiv ℝ F) (Ψ z) (fderiv ℝ Ψ z m₀) (fderiv ℝ Ψ z m₁) +
        fderiv ℝ F (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z m₀ m₁) := by
  have hd1 : fderiv ℝ (fun y => F (Ψ y)) = fun y => (fderiv ℝ F (Ψ y)).comp (fderiv ℝ Ψ y) :=
    funext fun y => fderiv_comp (g := F) (f := Ψ) y (hF.differentiable withTop_two_ne_zero (Ψ y))
      (hΨ.differentiable withTop_two_ne_zero y)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right withTop_one_add_one_le_two
  have hΨ1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right withTop_one_add_one_le_two
  have hc : HasFDerivAt (fun y => fderiv ℝ F (Ψ y))
      ((fderiv ℝ (fderiv ℝ F) (Ψ z)).comp (fderiv ℝ Ψ z)) z :=
    ((hF1.differentiable one_ne_zero (Ψ z)).hasFDerivAt).comp z
      ((hΨ.differentiable withTop_two_ne_zero z).hasFDerivAt)
  have hd : HasFDerivAt (fun y => fderiv ℝ Ψ y) (fderiv ℝ (fderiv ℝ Ψ) z) z :=
    (hΨ1.differentiable one_ne_zero z).hasFDerivAt
  rw [hd1, (hc.clm_comp hd).fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  rw [add_comm]

/-- `Δ f z = D²f(z)(1, 1) + D²f(z)(i, i)` -/
theorem laplacian_eq_fderiv_fderiv_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) :
    Δ f z = fderiv ℝ (fderiv ℝ f) z 1 1 + fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]

/-- **Conformal covariance of the Laplacian**: `Δ(F ∘ Ψ)(z) = ‖Ψ'(z)‖² (ΔF)(Ψ z)` if `Ψ` is
holomorphic on an open `U ∋ z`. -/
theorem laplacian_comp_holomorphic {F : ℂ → ℝ} {Ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ContDiff ℝ 2 F) (hΨ2 : ContDiff ℝ 2 Ψ) (hΨ : DifferentiableOn ℂ Ψ U) {z : ℂ}
    (hz : z ∈ U) :
    Δ (fun y => F (Ψ y)) z = ‖deriv Ψ z‖ ^ 2 * Δ F (Ψ z) := by
  have hdz : HasDerivAt Ψ (deriv Ψ z) z :=
    ((hΨ z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hD : ∀ m : ℂ, fderiv ℝ Ψ z m = Complex.I ^ 0 * (m * deriv Ψ z) := fun m => by
    rw [(hdz.hasFDerivAt.restrictScalars ℝ).fderiv]
    simp
  have hD1 : fderiv ℝ Ψ z 1 = deriv Ψ z := by rw [hD]; simp
  have hDI : fderiv ℝ Ψ z Complex.I = Complex.I * deriv Ψ z := by rw [hD]; simp
  have hharm : Δ Ψ z = 0 :=
    ((hΨ.analyticAt (hU.mem_nhds hz)).harmonicAt).2.self_of_nhds
  rw [laplacian_eq_fderiv_fderiv_complex] at hharm
  rw [laplacian_eq_fderiv_fderiv_complex, laplacian_eq_fderiv_fderiv_complex, fderiv_fderiv_comp hF hΨ2,
    fderiv_fderiv_comp hF hΨ2, hD1, hDI]
  have hlin : fderiv ℝ F (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z 1 1) +
      fderiv ℝ F (Ψ z) (fderiv ℝ (fderiv ℝ Ψ) z Complex.I Complex.I) = 0 := by
    rw [← map_add, hharm, map_zero]
  have key := bilin_scale (fderiv ℝ (fderiv ℝ F) (Ψ z)) (deriv Ψ z)
  linear_combination key + hlin

/-! ### Plane waves -/

/-- The real pairing `⟪ξ, y⟫ = Re ξ Re y + Im ξ Im y` of `ℂ = ℝ²`, as a continuous linear functional of `y`. -/
noncomputable def pairingCLM (ξ : ℂ) : ℂ →L[ℝ] ℝ := ξ.re • Complex.reCLM + ξ.im • Complex.imCLM

@[simp] theorem pairingCLM_apply (ξ y : ℂ) : pairingCLM ξ y = ξ.re * y.re + ξ.im * y.im := by
  simp [pairingCLM]

theorem pairingCLM_one_sq_add_I_sq (ξ : ℂ) :
    (pairingCLM ξ 1) ^ 2 + (pairingCLM ξ Complex.I) ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [pairingCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem laplacian_cos_clm (L : ℂ →L[ℝ] ℝ) (x : ℂ) :
    Δ (fun y => Real.cos (L y)) x = -((L 1) ^ 2 + (L Complex.I) ^ 2) * Real.cos (L x) := by
  have h1 : fderiv ℝ (fun y => Real.cos (L y)) = fun y => (-Real.sin (L y)) • L :=
    funext fun y => ((Real.hasDerivAt_cos (L y)).comp_hasFDerivAt y L.hasFDerivAt).fderiv
  have h2 : HasFDerivAt (fun y => (-Real.sin (L y)) • L) ((-(Real.cos (L x) • L)).smulRight L) x :=
    (((Real.hasDerivAt_sin (L x)).comp_hasFDerivAt x L.hasFDerivAt).neg).smul_const L
  rw [laplacian_eq_fderiv_fderiv_complex, h1, h2.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.neg_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem laplacian_sin_clm (L : ℂ →L[ℝ] ℝ) (x : ℂ) :
    Δ (fun y => Real.sin (L y)) x = -((L 1) ^ 2 + (L Complex.I) ^ 2) * Real.sin (L x) := by
  have h1 : fderiv ℝ (fun y => Real.sin (L y)) = fun y => Real.cos (L y) • L :=
    funext fun y => ((Real.hasDerivAt_sin (L y)).comp_hasFDerivAt y L.hasFDerivAt).fderiv
  have h2 : HasFDerivAt (fun y => Real.cos (L y) • L) ((-Real.sin (L x) • L).smulRight L) x :=
    ((Real.hasDerivAt_cos (L x)).comp_hasFDerivAt x L.hasFDerivAt).smul_const L
  rw [laplacian_eq_fderiv_fderiv_complex, h1, h2.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-! ### Localization of an inverse chart -/

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- **A smooth global extension of an inverse chart near a compact subset of its domain.** For a compact `K ⊆ U` there
are an open `O` with `K ⊆ O ⊆ U` and a smooth compactly supported cutoff `χ` with support in `U`, equal to `1` on `O`,
such that `χ ψ` is smooth on `ℂ`. -/
theorem exists_chart_localization (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (O : Set ℂ) (χ : ℂ → ℝ), IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ v, 0 ≤ χ v ∧ χ v ≤ 1) ∧ (∀ v ∈ O, χ v = 1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (χ v : ℂ) * ψ v) := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχ1⟩ := exists_smooth_cutoff (hK.cthickening (r := δ)) hU hsub hUb
  have hψd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U :=
    (hψ.differentiableOn.contDiffOn hU).restrict_scalars ℝ
  refine ⟨Metric.thickening δ K, χ, Metric.isOpen_thickening, Metric.self_subset_thickening hδ K,
    (Metric.thickening_subset_cthickening δ K).trans hsub, hχ, hχc, hχU, hχ01,
    fun v hv => hχ1 v (Metric.thickening_subset_cthickening δ K hv), ?_⟩
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact ((Complex.ofRealCLM.contDiff.comp hχ).contDiffAt).mul (hψd.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
    simp [hy]

/-- **The Laplacian of a localized chart composition.** With `O`, `χ` as in `exists_chart_localization`, for a `C²`
function `F` and `v ∈ O`: `Δ (χ · F(χ ψ)) v = |ψ'(v)|² (Δ F)(ψ v)`. -/
theorem laplacian_localized_comp (hψ : IsInverseChart U z ψ) {O : Set ℂ} {χ : ℂ → ℝ}
    (hO : IsOpen O) (hOU : O ⊆ U) (hχ1 : ∀ v ∈ O, χ v = 1)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (χ v : ℂ) * ψ v))
    {F : ℂ → ℝ} (hF : ContDiff ℝ 2 F) {v : ℂ} (hv : v ∈ O) :
    Δ (fun y => χ y * F ((χ y : ℂ) * ψ y)) v = ‖deriv ψ v‖ ^ 2 * Δ F (ψ v) := by
  set Ψ : ℂ → ℂ := fun y => (χ y : ℂ) * ψ y with hΨdef
  have hΨψ : ∀ y ∈ O, Ψ y = ψ y := fun y hy => by simp [hΨdef, hχ1 y hy]
  have hev : (fun y => χ y * F (Ψ y)) =ᶠ[𝓝 v] fun y => F (Ψ y) := by
    filter_upwards [hO.mem_nhds hv] with y hy
    rw [hχ1 y hy, one_mul]
  have hevψ : Ψ =ᶠ[𝓝 v] ψ := by
    filter_upwards [hO.mem_nhds hv] with y hy
    exact hΨψ y hy
  have hdiff : DifferentiableOn ℂ Ψ O :=
    (hψ.differentiableOn.mono hOU).congr fun y hy => hΨψ y hy
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds,
    laplacian_comp_holomorphic hO hF (hΨ.of_le (by norm_cast)) hdiff hv, hevψ.deriv_eq,
    hΨψ v hv]

/-! ### Sublevel sets of an inverse chart -/

/-- The open sublevel set `U_r = {v ∈ U | |ψ v| < r}` of an inverse chart. -/
def chartSubdomain (U : Set ℂ) (ψ : C(ℂ, ℂ)) (r : ℝ) : Set ℂ := U ∩ ψ ⁻¹' Metric.ball 0 r

/-- The closed sublevel set `K_r = {v ∈ closure U | |ψ v| ≤ r}` of an inverse chart. -/
def chartSublevel (U : Set ℂ) (ψ : C(ℂ, ℂ)) (r : ℝ) : Set ℂ := closure U ∩ ψ ⁻¹' Metric.closedBall 0 r

theorem isOpen_chartSubdomain (hU : IsOpen U) (r : ℝ) : IsOpen (chartSubdomain U ψ r) :=
  hU.inter (Metric.isOpen_ball.preimage ψ.continuous)

theorem isClosed_chartSublevel (r : ℝ) : IsClosed (chartSublevel U ψ r) :=
  isClosed_closure.inter (Metric.isClosed_closedBall.preimage ψ.continuous)

theorem isCompact_chartSublevel (hUb : Bornology.IsBounded U) (r : ℝ) :
    IsCompact (chartSublevel U ψ r) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_chartSublevel r) (hUb.closure.subset inter_subset_left)

theorem chartSublevel_subset (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {r : ℝ} (hr : r < 1) :
    chartSublevel U ψ r ⊆ U := fun _ hv =>
  hψ.mem_of_mem_closure hU hv.1 (Metric.closedBall_subset_ball hr hv.2)

theorem chartSubdomain_subset_chartSublevel (r : ℝ) : chartSubdomain U ψ r ⊆ chartSublevel U ψ r :=
  inter_subset_inter subset_closure (preimage_mono Metric.ball_subset_closedBall)

theorem closure_chartSubdomain_subset (r : ℝ) : closure (chartSubdomain U ψ r) ⊆ chartSublevel U ψ r :=
  closure_minimal (chartSubdomain_subset_chartSublevel r) (isClosed_chartSublevel r)

theorem chartSubdomain_subset (r : ℝ) : chartSubdomain U ψ r ⊆ U := inter_subset_left

theorem chartSubdomain_mono {r r' : ℝ} (h : r ≤ r') : chartSubdomain U ψ r ⊆ chartSubdomain U ψ r' :=
  inter_subset_inter_right _ (preimage_mono (Metric.ball_subset_ball h))

/-- A path from a point of an open set stays in its closure up to the exit time. -/
theorem mem_closure_of_le_exitTime {D : Set ℂ} (hD : IsOpen D) {p : ContinuousPath ℂ} (hp0 : p 0 ∈ D)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ContinuousPath.exitTime D p) : p s ∈ closure D := by
  rcases hs.lt_or_eq with hlt | heq
  · exact subset_closure (ContinuousPath.mem_of_lt_exitTime D p _ hlt)
  · have hfin : ContinuousPath.exitTime D p ≠ ⊤ := by rw [← heq]; exact ENNReal.coe_ne_top
    have h := ContinuousPath.coordinate_exitTime_mem_frontier D hD p hp0 hfin
    rw [← heq, ENNReal.toNNReal_coe] at h
    exact frontier_subset_closure h

/-- A path which stays in an open set up to time `r` leaves it at time `r` or later. -/
theorem le_exitTime_of_forall_mem {D : Set ℂ} (hD : IsOpen D) {p : ContinuousPath ℂ} {r : ℝ≥0}
    (h : ∀ s ≤ r, p s ∈ D) : (r : ℝ≥0∞) ≤ ContinuousPath.exitTime D p := by
  by_contra hlt
  rw [not_le] at hlt
  have hfin : ContinuousPath.exitTime D p ≠ ⊤ := (hlt.trans ENNReal.coe_lt_top).ne
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier D hD p (h 0 zero_le) hfin
  have hle : (ContinuousPath.exitTime D p).toNNReal ≤ r := by
    have h' := ENNReal.toNNReal_mono ENNReal.coe_ne_top hlt.le
    rwa [ENNReal.toNNReal_coe] at h'
  rw [hD.frontier_eq] at hfr
  exact hfr.2 (h _ hle)

/-! ### Dynkin's formula through an inverse chart -/

/-- **Dynkin's formula through an inverse chart.** For a smooth `F`, a sublevel set `U_r` (`r < 1`), a start
`x ∈ U_r` and a bounded stopping time `T ≤ τ_{U_r}`:
`E_x F(ψ(B_T)) - F(ψ x) = ½ E_x ∫_0^T |ψ'(B_s)|² (ΔF)(ψ(B_s)) ds`, and the drift integral is integrable. -/
theorem chart_dynkin (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ) {r : ℝ}
    (hr : r < 1) {F : ℂ → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (T : ContinuousPath ℂ → ℝ≥0)
    (hT : IsStoppingTime ContinuousPath.canonicalFiltration fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0))
    {N : ℝ≥0} (hTN : ∀ ω, T ω ≤ N)
    (hTr : ∀ ω, ((T ω : ℝ≥0) : ℝ≥0∞) ≤ ContinuousPath.exitTime (chartSubdomain U ψ r) ω)
    {x : ℂ} (hx : x ∈ chartSubdomain U ψ r) :
    Integrable (fun p : ContinuousPath ℂ => ∫ s in (0 : ℝ)..(T p : ℝ),
        (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ F (ψ (p s.toNNReal)))) (planarBrownianMotion x) ∧
    (∫ p, F (ψ (p (T p))) ∂planarBrownianMotion x) - F (ψ x) =
      ∫ p, (∫ s in (0 : ℝ)..(T p : ℝ),
        (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ F (ψ (p s.toNNReal)))) ∂planarBrownianMotion x := by
  obtain ⟨O, χ, hO, hKO, hOU, hχ, hχc, -, -, hχ1, hΨ⟩ :=
    exists_chart_localization hU hUb hψ (isCompact_chartSublevel hUb r) (chartSublevel_subset hU hψ hr)
  set g : ℂ → ℝ := fun y => χ y * F ((χ y : ℂ) * ψ y) with hgdef
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := hχ.mul (hF.comp hΨ)
  have hgc : HasCompactSupport g := hχc.mul_right
  obtain ⟨f, hfg, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  have hdyn : (∫ p, g (p (T p)) ∂(planarBrownianMotion x)) - g x =
      ∫ p, (∫ s in (0 : ℝ)..(T p : ℝ), (1 / 2 : ℝ) * Δ g (p s.toNNReal)) ∂(planarBrownianMotion x) := by
    have h := isFellerKernelSemigroup_planarHeatSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
      isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f T hT hTN x
    rw [← planarBrownianMotion_eq_continuousProcess] at h
    simpa only [hfg, hgen] using h
  have hint : Integrable (fun p : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(T p : ℝ), (1 / 2 : ℝ) * Δ g (p s.toNNReal)) (planarBrownianMotion x) := by
    have h := isFellerKernelSemigroup_planarHeatSemigroup.integrable_integral_generator_stoppingTime
      isConservative_planarHeatSemigroup f T hT hTN x
    rw [← planarBrownianMotion_eq_continuousProcess] at h
    simpa only [hgen] using h
  have hgO : ∀ v ∈ O, g v = F (ψ v) := fun v hv => by simp [hgdef, hχ1 v hv]
  have hΔO : ∀ v ∈ O, Δ g v = ‖deriv ψ v‖ ^ 2 * Δ F (ψ v) := fun v hv =>
    laplacian_localized_comp hψ hO hOU hχ1 hΨ (hF.of_le (by norm_cast)) hv
  have hpath : ∀ᵐ p ∂planarBrownianMotion x, ∀ s : ℝ≥0, s ≤ T p → p s ∈ O := by
    filter_upwards [ae_planarBrownianMotion_eval_zero x] with p hp0 s hs
    exact hKO (closure_chartSubdomain_subset r (mem_closure_of_le_exitTime (isOpen_chartSubdomain hU r)
      (by rw [hp0]; exact hx) ((ENNReal.coe_le_coe.2 hs).trans (hTr p))))
  have hx0 : g x = F (ψ x) := hgO x (hKO (chartSubdomain_subset_chartSublevel r hx))
  have hdrift : (fun p : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(T p : ℝ), (1 / 2 : ℝ) * Δ g (p s.toNNReal)) =ᵐ[planarBrownianMotion x]
      fun p => ∫ s in (0 : ℝ)..(T p : ℝ),
        (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ F (ψ (p s.toNNReal))) := by
    filter_upwards [hpath] with p hp
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ≤ (T p : ℝ) := by
      rw [uIcc_of_le (NNReal.coe_nonneg _)] at hs
      exact hs.2
    show (1 / 2 : ℝ) * Δ g (p s.toNNReal) =
      (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ F (ψ (p s.toNNReal)))
    rw [hΔO _ (hp _ (Real.toNNReal_le_iff_le_coe.2 hs'))]
  refine ⟨hint.congr hdrift, ?_⟩
  have hL : ∫ p, F (ψ (p (T p))) ∂planarBrownianMotion x = ∫ p, g (p (T p)) ∂planarBrownianMotion x :=
    integral_congr_ae (by
      filter_upwards [hpath] with p hp
      exact (hgO _ (hp _ le_rfl)).symm)
  rw [hL, ← hx0, hdyn]
  exact integral_congr_ae hdrift

/-! ### The conformal clock before the exit time has finite mean -/

theorem contDiff_norm_sq_complex : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => ‖y‖ ^ 2) :=
  contDiff_norm_sq ℝ

theorem laplacian_norm_sq_complex (y : ℂ) : Δ (fun y : ℂ => ‖y‖ ^ 2) y = 4 := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun t ↦ t := ⟨_, rfl⟩
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hFdef ▸ contDiff_id
  have hdF : deriv F = fun _ ↦ (1 : ℝ) := by rw [hFdef]; exact deriv_id''
  have he : (fun y : ℂ => ‖y‖ ^ 2) = fun y => F (‖y‖ ^ 2) := by rw [hFdef]
  rw [he, laplacian_comp_norm_sq hF, hdF]
  norm_num [deriv_const']

/-- The conformal rate density `|ψ'|²` is continuous on `U`. -/
theorem continuousOn_chartRateDensity (hU : IsOpen U) (hψ : IsInverseChart U z ψ) :
    ContinuousOn (fun v => ‖deriv ψ v‖ ^ 2) U :=
  ((hψ.differentiableOn.deriv hU).continuousOn.norm).pow 2

theorem chartRateDensity_pos (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {v : ℂ} (hv : v ∈ U) :
    0 < ‖deriv ψ v‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (hψ.deriv_ne_zero hU hv)) 2

/-- **Dynkin's identity for `|ψ|²`.** Before `τ_{U_r} ∧ n`, the conformal clock has mean at most `1/2`
(`½ Δ|ψ|² = 2 |ψ'|²` and `|ψ| ≤ 1`). -/
theorem chart_occupation_bound (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {r : ℝ} (hr : r < 1) {x : ℂ} (hx : x ∈ chartSubdomain U ψ r) (n : ℕ) :
    Integrable (fun p : ContinuousPath ℂ =>
        ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc (chartSubdomain U ψ r) n p : ℝ),
          2 * ‖deriv ψ (p s.toNNReal)‖ ^ 2) (planarBrownianMotion x) ∧
    ∫ p, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc (chartSubdomain U ψ r) n p : ℝ),
      2 * ‖deriv ψ (p s.toNNReal)‖ ^ 2) ∂planarBrownianMotion x ≤ 1 := by
  set D := chartSubdomain U ψ r
  have hD : IsOpen D := isOpen_chartSubdomain hU r
  obtain ⟨hint, hdyn⟩ := chart_dynkin hU hUb hψ hr contDiff_norm_sq_complex
    (ContinuousPath.exitTimeTrunc D n) (ContinuousPath.isStoppingTime_exitTimeTrunc D hD n)
    (ContinuousPath.exitTimeTrunc_le D n)
    (fun p => by rw [ContinuousPath.coe_exitTimeTrunc_ennreal]; exact min_le_left _ _) hx
  have heq : ∀ p : ContinuousPath ℂ,
      (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ),
        (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ (fun y : ℂ => ‖y‖ ^ 2) (ψ (p s.toNNReal)))) =
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D n p : ℝ), 2 * ‖deriv ψ (p s.toNNReal)‖ ^ 2 := by
    intro p
    refine intervalIntegral.integral_congr fun s _ => ?_
    show (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ (fun y : ℂ => ‖y‖ ^ 2) (ψ (p s.toNNReal))) =
      2 * ‖deriv ψ (p s.toNNReal)‖ ^ 2
    rw [laplacian_norm_sq_complex]
    ring
  simp only [heq] at hint hdyn
  refine ⟨hint, ?_⟩
  rw [← hdyn]
  have hend : ∫ p, ‖ψ (p (ContinuousPath.exitTimeTrunc D n p))‖ ^ 2 ∂planarBrownianMotion x ≤ 1 := by
    by_cases hi : Integrable (fun p : ContinuousPath ℂ =>
        ‖ψ (p (ContinuousPath.exitTimeTrunc D n p))‖ ^ 2) (planarBrownianMotion x)
    · have h1 : ∫ _p : ContinuousPath ℂ, (1 : ℝ) ∂planarBrownianMotion x = 1 := by simp
      rw [← h1]
      refine integral_mono_ae hi (integrable_const _) ?_
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with p hp0
      have hmem : p (ContinuousPath.exitTimeTrunc D n p) ∈ chartSublevel U ψ r :=
        closure_chartSubdomain_subset (U := U) (ψ := ψ) r (mem_closure_of_le_exitTime hD
          (by rw [hp0]; exact hx) (by rw [ContinuousPath.coe_exitTimeTrunc_ennreal]; exact min_le_left _ _))
      have hle : ‖ψ (p (ContinuousPath.exitTimeTrunc D n p))‖ ≤ 1 := by
        have h2 := hmem.2
        rw [mem_preimage, Metric.mem_closedBall, dist_zero_right] at h2
        linarith
      show ‖ψ (p (ContinuousPath.exitTimeTrunc D n p))‖ ^ 2 ≤ 1
      nlinarith [norm_nonneg (ψ (p (ContinuousPath.exitTimeTrunc D n p)))]
    · rw [integral_undef hi]
      exact zero_le_one
  nlinarith [sq_nonneg ‖ψ x‖]

/-- **The conformal clock is almost surely finite before the exit time.** Under planar Brownian motion from
`w ∈ U`, almost surely the exit time from `U` is finite and the exit rate of `|ψ'|²` is locally integrable. -/
theorem ae_mem_exitRateGoodSet_chart (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {w : ℂ} (hw : w ∈ U) :
    ∀ᵐ b ∂planarBrownianMotion w, b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2) := by
  set a : ℂ → ℝ := fun v => ‖deriv ψ v‖ ^ 2 with hadef
  set ρ0 : ℝ := ‖ψ w‖ with hρ0def
  have hρ0 : ρ0 < 1 := by
    have h := hψ.mapsTo_ball hw
    rwa [Metric.mem_ball, dist_zero_right] at h
  set rr : ℕ → ℝ := fun k => 1 - (1 - ρ0) / ((k : ℝ) + 2) with hrrdef
  have hk2 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by positivity
  have hrr1 : ∀ k, rr k < 1 := fun k => by
    have : 0 < (1 - ρ0) / ((k : ℝ) + 2) := div_pos (by linarith) (hk2 k)
    simp only [hrrdef]
    linarith
  have hrr0 : ∀ k, ρ0 < rr k := fun k => by
    have h2 : (1 - ρ0) / ((k : ℝ) + 2) < 1 - ρ0 :=
      div_lt_self (by linarith) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
    simp only [hrrdef]
    linarith
  have hrrm : Monotone rr := fun k l hkl => by
    have hkl' : (k : ℝ) + 2 ≤ (l : ℝ) + 2 := by
      have : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
      linarith
    have : (1 - ρ0) / ((l : ℝ) + 2) ≤ (1 - ρ0) / ((k : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (hk2 k) hkl'
    simp only [hrrdef]
    linarith
  have hrrt : Tendsto rr atTop (𝓝 1) := by
    have h : Tendsto (fun k : ℕ => (1 - ρ0) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rw [sub_zero] at h'
    exact h'
  set D : ℕ → Set ℂ := fun k => chartSubdomain U ψ (rr k) with hDdef
  have hDo : ∀ k, IsOpen (D k) := fun k => isOpen_chartSubdomain hU (rr k)
  have hwD : ∀ k, w ∈ D k := fun k => ⟨hw, by rw [mem_preimage, Metric.mem_ball, dist_zero_right]; exact hrr0 k⟩
  set T : ℕ → ContinuousPath ℂ → ℝ≥0 := fun k => ContinuousPath.exitTimeTrunc (D k) k with hTdef
  have hTcoe : ∀ k p, ((T k p : ℝ≥0) : ℝ≥0∞) = min (ContinuousPath.exitTime (D k) p) k := fun k p =>
    by rw [ContinuousPath.coe_exitTimeTrunc_ennreal, ENNReal.coe_natCast]
  have hTmono : ∀ p, Monotone fun k => T k p := fun p k l hkl => by
    have h : ((T k p : ℝ≥0) : ℝ≥0∞) ≤ T l p := by
      rw [hTcoe, hTcoe]
      exact min_le_min (ContinuousPath.exitTime_mono (chartSubdomain_mono (hrrm hkl)) p)
        (by exact_mod_cast hkl)
    exact ENNReal.coe_le_coe.1 h
  set J : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k p =>
    ∫⁻ s in Ioc (0 : ℝ) (T k p), ENNReal.ofReal (2 * a (p s.toNNReal)) with hJdef
  set I : ℕ → ContinuousPath ℂ → ℝ := fun k p =>
    ∫ s in (0 : ℝ)..(T k p : ℝ), 2 * a (p s.toNNReal) with hIdef
  -- the clock up to `T k` is continuous along the path
  have hJI : ∀ᵐ p ∂planarBrownianMotion w, ∀ k, J k p = ENNReal.ofReal (I k p) := by
    filter_upwards [ae_planarBrownianMotion_eval_zero w] with p hp0 k
    have hcont : ContinuousOn (fun s : ℝ => 2 * a (p s.toNNReal)) (Icc 0 (T k p)) := by
      refine continuousOn_const.mul ((continuousOn_chartRateDensity hU hψ).comp
        (p.continuous.comp continuous_real_toNNReal).continuousOn fun s hs => ?_)
      have hsT : s.toNNReal ≤ T k p := Real.toNNReal_le_iff_le_coe.2 hs.2
      exact chartSublevel_subset hU hψ (hrr1 k) (closure_chartSubdomain_subset (rr k)
        (mem_closure_of_le_exitTime (hDo k) (by rw [hp0]; exact hwD k)
          ((ENNReal.coe_le_coe.2 hsT).trans (by rw [hTcoe]; exact min_le_left _ _))))
    have hio : IntegrableOn (fun s : ℝ => 2 * a (p s.toNNReal)) (Ioc 0 (T k p)) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    simp only [hJdef, hIdef]
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
      ofReal_integral_eq_lintegral_ofReal hio (ae_of_all _ fun s => mul_nonneg zero_le_two (sq_nonneg _))]
  have hIint : ∀ k, Integrable (I k) (planarBrownianMotion w) := fun k =>
    (chart_occupation_bound hU hUb hψ (hrr1 k) (hwD k) k).1
  have hInn : ∀ k p, 0 ≤ I k p := fun k p =>
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun s _ => mul_nonneg zero_le_two (sq_nonneg _)
  have hJm : ∀ k, AEMeasurable (J k) (planarBrownianMotion w) := fun k =>
    (ENNReal.measurable_ofReal.comp_aemeasurable (hIint k).aemeasurable).congr
      (by filter_upwards [hJI] with p hp; exact (hp k).symm)
  have hJle : ∀ k, ∫⁻ p, J k p ∂planarBrownianMotion w ≤ 1 := fun k => by
    have hae : (fun p => J k p) =ᵐ[planarBrownianMotion w] fun p => ENNReal.ofReal (I k p) := by
      filter_upwards [hJI] with p hp
      exact hp k
    rw [lintegral_congr_ae hae,
      ← ofReal_integral_eq_lintegral_ofReal (hIint k) (ae_of_all _ (hInn k))]
    exact ENNReal.ofReal_le_one.2 (chart_occupation_bound hU hUb hψ (hrr1 k) (hwD k) k).2
  have hJmono : ∀ p, Monotone fun k => J k p := fun p k l hkl =>
    lintegral_mono_set (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (hTmono p hkl)))
  have hsup : ∫⁻ p, ⨆ k, J k p ∂planarBrownianMotion w ≤ 1 := by
    rw [lintegral_iSup' hJm (ae_of_all _ hJmono)]
    exact iSup_le hJle
  have hsupfin : ∀ᵐ p ∂planarBrownianMotion w, ⨆ k, J k p < ⊤ :=
    ae_lt_top' (AEMeasurable.iSup hJm) (ne_top_of_le_ne_top ENNReal.one_ne_top hsup)
  filter_upwards [hsupfin, ae_planarBrownianMotion_eval_zero w,
    ae_planarBrownian_exitTime_bounded_lt_top w hUb] with p hS hp0 hτ
  refine ⟨hτ, mem_iInter.2 fun n => ?_⟩
  show ∫⁻ r in Ioc (0 : ℝ) n, ‖exitRate U a p r‖ₑ < ⊤
  -- before the exit time from `U`, the path is in some `D k` up to time `T k`
  have hreach : ∀ s : ℝ, 0 < s → ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U p →
      ∃ k, s ∈ Ioc (0 : ℝ) (T k p) := by
    intro s hs0 hsτ
    set σ : ℝ≥0 := s.toNNReal
    have hU' : ∀ u ≤ σ, p u ∈ U := fun u hu =>
      ContinuousPath.mem_of_lt_exitTime U p _ ((ENNReal.coe_le_coe.2 hu).trans_lt hsτ)
    obtain ⟨u0, hu0, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) σ)).exists_isMaxOn
      (nonempty_Icc.2 zero_le) ((continuous_norm.comp (ψ.continuous.comp p.continuous)).continuousOn)
    have hM : ‖ψ (p u0)‖ < 1 := by
      have h := hψ.mapsTo_ball (hU' u0 hu0.2)
      rwa [Metric.mem_ball, dist_zero_right] at h
    obtain ⟨k, hk1, hk2⟩ := ((hrrt.eventually (lt_mem_nhds hM)).and
      (eventually_ge_atTop ⌈s⌉₊)).exists
    refine ⟨k, hs0, ?_⟩
    have hinD : ∀ u ≤ σ, p u ∈ D k := fun u hu => by
      refine ⟨hU' u hu, ?_⟩
      rw [mem_preimage, Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (isMaxOn_iff.1 hmax u ⟨zero_le, hu⟩) hk1
    have hle := le_exitTime_of_forall_mem (hDo k) hinD
    have hσk : (σ : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by
      have : (σ : ℝ) ≤ k := by
        rw [Real.coe_toNNReal _ hs0.le]
        exact (Nat.le_ceil s).trans (by exact_mod_cast hk2)
      exact_mod_cast this
    have hσT : σ ≤ T k p := by
      have h : (σ : ℝ≥0∞) ≤ T k p := by rw [hTcoe]; exact le_min hle hσk
      exact ENNReal.coe_le_coe.1 h
    have := NNReal.coe_le_coe.2 hσT
    rwa [Real.coe_toNNReal _ hs0.le] at this
  set G : ℕ → ℝ → ℝ≥0∞ := fun k => (Ioc (0 : ℝ) (T k p)).indicator
    fun s => ENNReal.ofReal (2 * a (p s.toNNReal)) with hGdef
  have hGm : ∀ k, Measurable (G k) := fun k =>
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((measurable_deriv ψ).norm.pow_const 2).comp
        ((p.continuous.comp continuous_real_toNNReal).measurable)))).indicator measurableSet_Ioc
  have hGmono : Monotone G := fun k l hkl s =>
    indicator_le_indicator_of_subset (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (hTmono p hkl)))
      (fun _ => zero_le) s
  have hpt : ∀ s ∈ Ioc (0 : ℝ) n, ‖exitRate U a p s‖ₑ ≤ (⨆ k, G k s) + 1 := by
    intro s hs
    by_cases hsτ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U p
    · obtain ⟨k, hk⟩ := hreach s hs.1 hsτ
      rw [exitRate_of_lt_exitTime hsτ]
      refine le_trans ?_ le_self_add
      refine le_trans ?_ (le_iSup (fun k => G k s) k)
      simp only [hGdef, indicator_of_mem hk]
      have ha0 : 0 ≤ a (p s.toNNReal) := sq_nonneg _
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ha0]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [exitRate_of_exitTime_le (not_lt.1 hsτ)]
      simp
  calc ∫⁻ s in Ioc (0 : ℝ) n, ‖exitRate U a p s‖ₑ
      ≤ ∫⁻ s in Ioc (0 : ℝ) n, ((⨆ k, G k s) + 1) := setLIntegral_mono' measurableSet_Ioc hpt
    _ ≤ (∫⁻ s, ⨆ k, G k s) + ∫⁻ _s in Ioc (0 : ℝ) n, 1 := by
        rw [lintegral_add_right _ measurable_const]
        exact add_le_add (setLIntegral_le_lintegral _ _) le_rfl
    _ = (⨆ k, J k p) + ∫⁻ _s in Ioc (0 : ℝ) n, 1 := by
        rw [lintegral_iSup hGm hGmono]
        congr 1
        refine iSup_congr fun k => ?_
        simp only [hGdef, hJdef]
        rw [lintegral_indicator measurableSet_Ioc]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨hS, ?_⟩
        simp

/-- **The first two assertions of Lévy's theorem for an inverse chart**: almost surely the conformal rate is
locally integrable, and the stopped chart image of the time-changed path is almost everywhere measurable. -/
theorem levyChart_integrable_aemeasurable (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {w : ℂ} (hw : w ∈ U) :
    (∀ᵐ b ∂planarBrownianMotion w, ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T) ∧
    AEMeasurable (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))
      (planarBrownianMotion w) := by
  have hgood := ae_mem_exitRateGoodSet_chart hU hUb hψ hw
  refine ⟨?_, ?_⟩
  · filter_upwards [hgood] with b hb T
    exact intervalIntegrable_exitRate_of_mem_exitRateGoodSet hU (continuousOn_chartRateDensity hU hψ) hb T
  · exact (measurable_chartStopPath U hU ψ).comp_aemeasurable
      (aemeasurable_lbmContinuousPath_exitRateClock hU (continuousOn_chartRateDensity hU hψ)
        (fun v hv => chartRateDensity_pos hU hψ hv) hgood)


end ConformalCovariance

section ChartDynkin

open Laplacian _root_.HarmonicBalls.Section6


/-! ### Exit times and stopped paths -/

/-- A continuous path is in an open set strictly before its exit time exactly when it stays in the set up to
that time. -/
theorem lt_exitTime_iff_forall_mem {D : Set ℂ} (hD : IsOpen D) (p : ContinuousPath ℂ) (r : ℝ≥0) :
    (r : ℝ≥0∞) < ContinuousPath.exitTime D p ↔ ∀ s ≤ r, p s ∈ D := by
  constructor
  · intro h s hs
    exact ContinuousPath.mem_of_lt_exitTime D p s ((ENNReal.coe_le_coe.2 hs).trans_lt h)
  · intro h
    refine lt_of_le_of_ne (le_exitTime_of_forall_mem hD h) fun heq => ?_
    have hfin : ContinuousPath.exitTime D p ≠ ⊤ := by rw [← heq]; exact ENNReal.coe_ne_top
    have hfr := ContinuousPath.coordinate_exitTime_mem_frontier D hD p (h 0 zero_le) hfin
    rw [← heq, ENNReal.toNNReal_coe, hD.frontier_eq] at hfr
    exact hfr.2 (h r le_rfl)

/-- The exit-rate clock at time `u` only reads the path on `[0, u]`. -/
theorem exitRateClock_stoppedPath {D : Set ℂ} (hD : IsOpen D) (ρ : ℂ → ℝ) (w : ContinuousPath ℂ) (u : ℝ≥0) :
    exitRateClock D ρ (ContinuousPath.stoppedPath u w) u = exitRateClock D ρ w u := by
  unfold exitRateClock
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr' : r.toNNReal ≤ u := by
    have hs : r ≤ (u : ℝ) := by
      rcases Set.mem_uIcc.1 hr with h | h
      · exact h.2
      · exact h.2.trans u.2
    exact Real.toNNReal_le_iff_le_coe.2 hs
  have hpt : ∀ s ≤ r.toNNReal, ContinuousPath.stoppedPath u w s = w s := fun s hs =>
    ContinuousPath.stoppedPath_apply_of_le u w s (hs.trans hr')
  have hiff : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D (ContinuousPath.stoppedPath u w) ↔
      ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w := by
    rw [lt_exitTime_iff_forall_mem hD, lt_exitTime_iff_forall_mem hD]
    exact forall₂_congr fun s hs => by rw [hpt s hs]
  show exitRate D ρ (ContinuousPath.stoppedPath u w) r = exitRate D ρ w r
  unfold exitRate
  rw [hpt _ le_rfl]
  exact if_congr hiff rfl rfl

/-! ### Exit-rate clocks with bounded rates -/

theorem exitRate_mem_Icc {D : Set ℂ} {ρ : ℂ → ℝ} {m M : ℝ} (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M)
    (w : ContinuousPath ℂ) (r : ℝ) : min m 1 ≤ exitRate D ρ w r ∧ exitRate D ρ w r ≤ max M 1 := by
  by_cases h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w
  · rw [exitRate_of_lt_exitTime h]
    have hv := ContinuousPath.mem_of_lt_exitTime D w _ h
    exact ⟨(min_le_left _ _).trans (hρm _ hv), (hρM _ hv).trans (le_max_left _ _)⟩
  · rw [exitRate_of_exitTime_le (not_lt.1 h)]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem intervalIntegrable_exitRate_of_bounds {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ D)
    {m M : ℝ} (hm : 0 < m) (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M) (w : ContinuousPath ℂ)
    (s t : ℝ) : IntervalIntegrable (exitRate D ρ w) volume s t := by
  have hmeas : Measurable (exitRate D ρ w) :=
    (measurable_exitRate_uncurry hD hρ).comp (measurable_const.prodMk measurable_id)
  have h0 : 0 < min m 1 := lt_min hm one_pos
  refine ((continuous_const : Continuous fun _ : ℝ => max M 1).intervalIntegrable s t).mono_fun
    hmeas.aestronglyMeasurable (ae_of_all _ fun r => ?_)
  obtain ⟨h1, h2⟩ := exitRate_mem_Icc hρm hρM w r
  show ‖exitRate D ρ w r‖ ≤ ‖max M 1‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (h0.trans_le h1),
    abs_of_pos (lt_max_of_lt_right one_pos)]
  exact h2

theorem mul_le_exitRateClock {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ D) {m M : ℝ}
    (hm : 0 < m) (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M) (w : ContinuousPath ℂ) (t : ℝ≥0) :
    min m 1 * (t : ℝ) ≤ exitRateClock D ρ w t := by
  have h := intervalIntegral.integral_mono_on (NNReal.coe_nonneg t)
    ((continuous_const : Continuous fun _ : ℝ => min m 1).intervalIntegrable 0 t)
    (intervalIntegrable_exitRate_of_bounds hD hρ hm hρm hρM w 0 t)
    (fun x _ => (exitRate_mem_Icc hρm hρM w x).1)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  unfold exitRateClock
  linarith

/-- **An exit-rate clock with rate bounded above and below is a time-change clock**, for every path. -/
theorem isTimeChangeClock_exitRateClock_of_bounds {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ D) {m M : ℝ} (hm : 0 < m) (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M)
    (w : ContinuousPath ℂ) : IsTimeChangeClock (exitRateClock D ρ w) := by
  have hint := intervalIntegrable_exitRate_of_bounds hD hρ hm hρm hρM w
  have hpos : ∀ v ∈ D, 0 < ρ v := fun v hv => hm.trans_le (hρm v hv)
  refine ⟨exitRateClock_zero D ρ w, ?_, ?_, ?_⟩
  · exact (intervalIntegral.continuous_primitive hint 0).comp NNReal.continuous_coe
  · intro s t hst
    have hst' : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
    have hp := intervalIntegral.intervalIntegral_pos_of_pos_on (hint s t)
      (fun x _ => exitRate_pos hpos w x) hst'
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s t)
    simp only [exitRateClock]
    linarith
  · have hlin : Tendsto (fun t : ℝ≥0 => min m 1 * (t : ℝ)) atTop atTop :=
      (NNReal.tendsto_coe_atTop.2 tendsto_id).const_mul_atTop (lt_min hm one_pos)
    exact tendsto_atTop_mono (mul_le_exitRateClock hD hρ hm hρm hρM w) hlin

/-- The clock inverse of a bounded-rate exit-rate clock is at most `u` iff the clock at `u` of the path stopped
at `u` reaches the target. -/
theorem clockInverse_exitRateClock_le_iff {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ D)
    {m M : ℝ} (hm : 0 < m) (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M) (t u : ℝ≥0)
    (w : ContinuousPath ℂ) :
    _root_.HarmonicBalls.clockInverse (exitRateClock D ρ w) t ≤ u ↔
      (t : ℝ) ≤ exitRateClock D ρ (ContinuousPath.stoppedPath u w) u := by
  rw [exitRateClock_stoppedPath hD]
  exact clockInverse_le_iff_of_isTimeChangeClock
    (isTimeChangeClock_exitRateClock_of_bounds hD hρ hm hρm hρM w) t u

theorem measurableSet_clockInverse_exitRateClock_le {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ D) {m M : ℝ} (hm : 0 < m) (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M)
    (t u : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) u]
      {w : ContinuousPath ℂ | _root_.HarmonicBalls.clockInverse (exitRateClock D ρ w) t ≤ u} := by
  have h : {w : ContinuousPath ℂ | _root_.HarmonicBalls.clockInverse (exitRateClock D ρ w) t ≤ u} =
      (fun w => exitRateClock D ρ (ContinuousPath.stoppedPath u w) u) ⁻¹' Ici (t : ℝ) := by
    ext w
    exact clockInverse_exitRateClock_le_iff hD hρ hm hρm hρM t u w
  rw [h]
  exact ((measurable_exitRateClock hD hρ u).comp
    (LQGClockApproxAdapted.measurable_stoppedPath_canonicalFiltration u)) measurableSet_Ici

/-- **The inverse of a bounded-rate exit-rate clock is a stopping time.** -/
theorem isStoppingTime_clockInverse_exitRateClock {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ D) {m M : ℝ} (hm : 0 < m) (hρm : ∀ v ∈ D, m ≤ ρ v) (hρM : ∀ v ∈ D, ρ v ≤ M)
    (t : ℝ≥0) :
    IsStoppingTime ContinuousPath.canonicalFiltration fun w : ContinuousPath ℂ =>
      ((_root_.HarmonicBalls.clockInverse (exitRateClock D ρ w) t : ℝ≥0) : WithTop ℝ≥0) := by
  intro u
  simp only [WithTop.coe_le_coe]
  exact measurableSet_clockInverse_exitRateClock_le hD hρ hm hρm hρM t u

/-- A finite stopping time of the canonical filtration is a Borel function of the path. -/
theorem measurable_of_isStoppingTime_coe {T : ContinuousPath ℂ → ℝ≥0}
    (hT : IsStoppingTime ContinuousPath.canonicalFiltration fun w => ((T w : ℝ≥0) : WithTop ℝ≥0)) :
    Measurable T := by
  refine measurable_of_Iic fun u => ?_
  have h := hT u
  simp only [WithTop.coe_le_coe] at h
  exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).le u _ h

/-! ### The localized conformal clock -/

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The localized conformal clock: rate `|ψ'|²` until the exit from `U_r`, unit rate afterwards. -/
noncomputable def localConformalClock (U : Set ℂ) (ψ : C(ℂ, ℂ)) (r : ℝ) : ContinuousPath ℂ → ℝ≥0 → ℝ :=
  exitRateClock (chartSubdomain U ψ r) fun v => ‖deriv ψ v‖ ^ 2

/-- The stopping time `A_r⁻¹(t) ∧ τ_{U_r} ∧ N` of the localized conformal clock. -/
noncomputable def localConformalStop (U : Set ℂ) (ψ : C(ℂ, ℂ)) (r : ℝ) (t N : ℝ≥0) (b : ContinuousPath ℂ) :
    ℝ≥0 :=
  min (_root_.HarmonicBalls.clockInverse (localConformalClock U ψ r b) t)
    (ContinuousPath.exitTimeTrunc (chartSubdomain U ψ r) N b)

theorem exists_chartRateDensity_bounds (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {r : ℝ} (hr : r < 1) :
    ∃ m M : ℝ, 0 < m ∧ (∀ v ∈ chartSubdomain U ψ r, m ≤ ‖deriv ψ v‖ ^ 2) ∧
      (∀ v ∈ chartSubdomain U ψ r, ‖deriv ψ v‖ ^ 2 ≤ M) := by
  have hK : IsCompact (chartSublevel U ψ r) := isCompact_chartSublevel hUb r
  have hKU : chartSublevel U ψ r ⊆ U := chartSublevel_subset hU hψ hr
  have hc : ContinuousOn (fun v => ‖deriv ψ v‖ ^ 2) (chartSublevel U ψ r) :=
    (continuousOn_chartRateDensity hU hψ).mono hKU
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  have hMle : ∀ v ∈ chartSubdomain U ψ r, ‖deriv ψ v‖ ^ 2 ≤ M := fun v hv => by
    have h := hM v (chartSubdomain_subset_chartSublevel r hv)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  rcases (chartSublevel U ψ r).eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, M, one_pos, fun v hv => ?_, hMle⟩
    have h := chartSubdomain_subset_chartSublevel r hv
    rw [hKe] at h
    simp at h
  · obtain ⟨v0, hv0, hmin⟩ := hK.exists_isMinOn hKne hc
    exact ⟨‖deriv ψ v0‖ ^ 2, M, chartRateDensity_pos hU hψ (hKU hv0),
      fun v hv => isMinOn_iff.1 hmin v (chartSubdomain_subset_chartSublevel r hv), hMle⟩

theorem exists_chart_exhaustion {ρ0 : ℝ} (hρ0 : ρ0 < 1) :
    ∃ rr : ℕ → ℝ, (∀ k, ρ0 < rr k) ∧ (∀ k, rr k < 1) ∧ Tendsto rr atTop (𝓝 1) := by
  have hk2 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by positivity
  refine ⟨fun k => 1 - (1 - ρ0) / ((k : ℝ) + 2), fun k => ?_, fun k => ?_, ?_⟩
  · have h2 : (1 - ρ0) / ((k : ℝ) + 2) < 1 - ρ0 :=
      div_lt_self (by linarith) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
    show ρ0 < 1 - (1 - ρ0) / ((k : ℝ) + 2)
    linarith
  · have : 0 < (1 - ρ0) / ((k : ℝ) + 2) := div_pos (by linarith) (hk2 k)
    show 1 - (1 - ρ0) / ((k : ℝ) + 2) < 1
    linarith
  · have h : Tendsto (fun k : ℕ => (1 - ρ0) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rw [sub_zero] at h'
    exact h'

/-- For a path in the good set, the conformal clock is a time-change clock. -/
theorem isTimeChangeClock_chartClock_of_mem (hU : IsOpen U) (hψ : IsInverseChart U z ψ)
    {b : ContinuousPath ℂ} (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) :
    IsTimeChangeClock (chartClock U ψ b) :=
  isTimeChangeClock_chartClock hψ hU
    (intervalIntegrable_exitRate_of_mem_exitRateGoodSet hU (continuousOn_chartRateDensity hU hψ) hb) hb.1.ne

/-- The stopped chart path is constant from the clock value of the exit time on. -/
theorem chartStopPath_lbmContinuousPath_min_exit (hU : IsOpen U) (hψ : IsInverseChart U z ψ)
    {b : ContinuousPath ℂ} (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (t : ℝ≥0) :
    chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)
        (min (t : ℝ) (chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal)).toNNReal =
      chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  set τ := (ContinuousPath.exitTime U b).toNNReal with hτdef
  have hτe : ContinuousPath.exitTime U b = τ := (ENNReal.coe_toNNReal hb.1.ne).symm
  rcases le_total (t : ℝ) (chartClock U ψ b τ) with h | h
  · rw [min_eq_left h, Real.toNNReal_coe]
  · have h2 : τ ≤ _root_.HarmonicBalls.clockInverse (chartClock U ψ b) t :=
      hA.strictMono.le_iff_le.1 (h.trans_eq (IsTimeChangeClock.apply_clockInverse_eq hA t).symm)
    rw [min_eq_right h, chartStopPath_lbmContinuousPath_apply hA hτe,
      chartStopPath_lbmContinuousPath_apply hA hτe, clockInverse_clockValue hA.map_zero hA.strictMono,
      min_self, min_eq_right h2]

/-- **The localized stop along a good path.** For a path of the good set started in `U_r`, the localized stop
`T = A_r⁻¹(t) ∧ τ_{U_r} ∧ N` (with `N` large) is the inverse of the conformal clock at `θ = t ∧ A(τ_{U_r})`; the
chart image of the path at `T` is the chart path at `θ`, and the change of variables `v = A(s)` turns
`∫_0^T |ψ'(b_s)|² G(ψ(b_s)) ds` into `∫_0^θ G(Y_v) dv`. -/
theorem chart_localized_stop_pathwise (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {r : ℝ} (hr : r < 1)
    {m M : ℝ} (hm : 0 < m) (hρm : ∀ v ∈ chartSubdomain U ψ r, m ≤ ‖deriv ψ v‖ ^ 2)
    (hρM : ∀ v ∈ chartSubdomain U ψ r, ‖deriv ψ v‖ ^ 2 ≤ M) {t N : ℝ≥0} (hN : (t : ℝ) ≤ min m 1 * N)
    {b : ContinuousPath ℂ} (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2)
    (hb0 : b 0 ∈ chartSubdomain U ψ r) (G : ℂ → ℝ) :
    ψ (b (localConformalStop U ψ r t N b)) = chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)
        (min (t : ℝ) (chartClock U ψ b (ContinuousPath.exitTime (chartSubdomain U ψ r) b).toNNReal)).toNNReal ∧
      ∫ s in (0 : ℝ)..(localConformalStop U ψ r t N b : ℝ), ‖deriv ψ (b s.toNNReal)‖ ^ 2 * G (ψ (b s.toNNReal)) =
        ∫ v in (0 : ℝ)..min (t : ℝ) (chartClock U ψ b (ContinuousPath.exitTime (chartSubdomain U ψ r) b).toNNReal),
          G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) v.toNNReal) := by
  set D := chartSubdomain U ψ r with hDdef
  have hDo : IsOpen D := isOpen_chartSubdomain hU r
  have hDU : D ⊆ U := chartSubdomain_subset r
  have hρD : ContinuousOn (fun v => ‖deriv ψ v‖ ^ 2) D := (continuousOn_chartRateDensity hU hψ).mono hDU
  have hb0U : b 0 ∈ U := hDU hb0
  have hfinU : ContinuousPath.exitTime U b ≠ ⊤ := hb.1.ne
  have hfinD : ContinuousPath.exitTime D b ≠ ⊤ :=
    ne_top_of_le_ne_top hfinU (ContinuousPath.exitTime_mono hDU b)
  set τ : ℝ≥0 := (ContinuousPath.exitTime U b).toNNReal with hτdef
  set σ : ℝ≥0 := (ContinuousPath.exitTime D b).toNNReal with hσdef
  have hτe : ContinuousPath.exitTime U b = τ := (ENNReal.coe_toNNReal hfinU).symm
  have hσe : ContinuousPath.exitTime D b = σ := (ENNReal.coe_toNNReal hfinD).symm
  -- the exit point from `U_r` lies in `U`
  have hστ : σ < τ := by
    have h : ((σ : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U b := by
      rw [lt_exitTime_iff_forall_mem hU]
      intro s hs
      exact chartSublevel_subset hU hψ hr (closure_chartSubdomain_subset r
        (mem_closure_of_le_exitTime hDo hb0 (by rw [hσe]; exact ENNReal.coe_le_coe.2 hs)))
    rw [hτe] at h
    exact ENNReal.coe_lt_coe.1 h
  have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock_of_mem hU hψ hb
  have hAk : IsTimeChangeClock (localConformalClock U ψ r b) :=
    isTimeChangeClock_exitRateClock_of_bounds hDo hρD hm hρm hρM b
  -- the two clocks agree up to `σ`
  have hagree : ∀ s : ℝ≥0, s ≤ σ → localConformalClock U ψ r b s = chartClock U ψ b s := by
    intro s hs
    show exitRateClock D (fun v => ‖deriv ψ v‖ ^ 2) b s = exitRateClock U (fun v => ‖deriv ψ v‖ ^ 2) b s
    unfold exitRateClock
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton (s : ℝ)).ae_notMem volume] with x hx hxI
    rw [uIoc_of_le (NNReal.coe_nonneg s)] at hxI
    have hxs : x < s := lt_of_le_of_ne hxI.2 (mt Set.mem_singleton_iff.2 hx)
    have hlt : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D b := by
      rw [hσe, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hxI.1.le]
      exact hxs.trans_le (NNReal.coe_le_coe.2 hs)
    rw [exitRate_of_lt_exitTime hlt,
      exitRate_of_lt_exitTime (hlt.trans_le (ContinuousPath.exitTime_mono hDU b))]
  -- the value of the stop
  set C := _root_.HarmonicBalls.clockInverse (localConformalClock U ψ r b) t with hCdef
  have hCt : localConformalClock U ψ r b C = t := IsTimeChangeClock.apply_clockInverse_eq hAk t
  have hCN : C ≤ N := (clockInverse_le_iff_of_isTimeChangeClock hAk t N).2
    (hN.trans (mul_le_exitRateClock hDo hρD hm hρm hρM b N))
  have hEe : ContinuousPath.exitTimeTrunc D N b = min σ N := by
    have h : ((ContinuousPath.exitTimeTrunc D N b : ℝ≥0) : ℝ≥0∞) = ((min σ N : ℝ≥0) : ℝ≥0∞) := by
      rw [ContinuousPath.coe_exitTimeTrunc_ennreal, hσe, ENNReal.coe_min]
    exact ENNReal.coe_injective h
  have hTdef : localConformalStop U ψ r t N b = min C (min σ N) := by
    rw [← hEe]
    rfl
  have hT : localConformalStop U ψ r t N b ≤ σ ∧
      (chartClock U ψ b (localConformalStop U ψ r t N b) : ℝ) = min (t : ℝ) (chartClock U ψ b σ) := by
    rcases le_or_gt C σ with hCσ | hσC
    · have hmin : min C (min σ N) = C := min_eq_left (le_min hCσ hCN)
      rw [hTdef, hmin]
      refine ⟨hCσ, ?_⟩
      have h1 : chartClock U ψ b C = t := by rw [← hagree C hCσ]; exact hCt
      have h2 : (t : ℝ) ≤ chartClock U ψ b σ := by rw [← h1]; exact hA.strictMono.monotone hCσ
      rw [h1, min_eq_left h2]
    · have hmin : min C (min σ N) = σ := by
        rw [min_eq_right ((min_le_left σ N).trans hσC.le)]
        exact min_eq_left (hσC.le.trans hCN)
      rw [hTdef, hmin]
      refine ⟨le_rfl, ?_⟩
      have h1 : chartClock U ψ b σ < t := by
        rw [← hagree σ le_rfl, ← hCt]
        exact hAk.strictMono hσC
      rw [min_eq_right h1.le]
  set T := localConformalStop U ψ r t N b with hTdef'
  set θ := min (t : ℝ) (chartClock U ψ b σ) with hθdef
  have hθ0 : 0 ≤ θ := le_min (NNReal.coe_nonneg t) (IsTimeChangeClock.clock_nonneg hA σ)
  have hAT : chartClock U ψ b T = ((θ.toNNReal : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ hθ0]
    exact hT.2
  have hCinv : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) θ.toNNReal = T :=
    FirstPass.Derived.clockInverse_eq_of_apply_eq hA hAT
  have hTτ : T ≤ τ := hT.1.trans hστ.le
  have hθL : θ ≤ chartClock U ψ b τ := (min_le_right _ _).trans (hA.strictMono.monotone hστ.le)
  have hY : chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) θ.toNNReal = ψ (b T) := by
    rw [chartStopPath_lbmContinuousPath_apply hA hτe, hCinv, min_eq_left hTτ]
  refine ⟨hY.symm, ?_⟩
  have hexit : ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) =
      (((chartClock U ψ b τ).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0U hτe
  have hint : ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T :=
    intervalIntegrable_exitRate_of_mem_exitRateGoodSet hU (continuousOn_chartRateDensity hU hψ) hb
  have hθ'L : ((θ.toNNReal : ℝ≥0) : ℝ) ≤ chartClock U ψ b τ := by
    rw [Real.coe_toNNReal _ hθ0]
    exact hθL
  have hcov := exitRateClock_chartTransportRate_eq hψ hU hb0U hτe hint
    (fun v => ‖deriv ψ v‖ ^ 2 * G (ψ v)) hθ'L
  rw [hCinv] at hcov
  refine hcov.symm.trans ?_
  rw [exitRateClock, Real.coe_toNNReal _ hθ0]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(countable_singleton θ).ae_notMem volume] with v hv hvI
  rw [uIoc_of_le hθ0] at hvI
  have hvθ : v < θ := lt_of_le_of_ne hvI.2 (mt Set.mem_singleton_iff.2 hv)
  have hlt : ((v.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) := by
    rw [hexit, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hvI.1.le,
      Real.coe_toNNReal _ (IsTimeChangeClock.clock_nonneg hA τ)]
    exact hvθ.trans_le hθL
  have hmem := ContinuousPath.mem_of_lt_exitTime _ _ _ hlt
  rw [exitRate_of_lt_exitTime hlt]
  have hφ := hψ.chartMap_mem hmem
  simp only [chartTransportRate, hψ.apply_chartMap hmem]
  exact mul_div_cancel_left₀ _ (chartRateDensity_pos hU hψ hφ).ne'

/-- Along a good path, the exit times of the sublevel domains `U_{r_k}` (`r_k → 1`) converge to the exit time
of `U`, so their conformal clock values converge to `A(τ_U)`. -/
theorem tendsto_chartClock_exitTime_chartSubdomain (hU : IsOpen U) (hψ : IsInverseChart U z ψ)
    {rr : ℕ → ℝ} (hrrt : Tendsto rr atTop (𝓝 1)) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) :
    Tendsto (fun k => chartClock U ψ b (ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) b).toNNReal)
      atTop (𝓝 (chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal)) := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  refine (hA.continuous.tendsto _).comp ?_
  set τ := (ContinuousPath.exitTime U b).toNNReal with hτdef
  have hfinU : ContinuousPath.exitTime U b ≠ ⊤ := hb.1.ne
  have hτe : ContinuousPath.exitTime U b = τ := (ENNReal.coe_toNNReal hfinU).symm
  have hfin : ∀ k, ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) b ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hfinU (ContinuousPath.exitTime_mono (chartSubdomain_subset (rr k)) b)
  have hle : ∀ k, (ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) b).toNNReal ≤ τ := fun k =>
    ENNReal.toNNReal_mono hfinU (ContinuousPath.exitTime_mono (chartSubdomain_subset (rr k)) b)
  have hreach : ∀ s : ℝ≥0, s < τ →
      ∀ᶠ k in atTop, s ≤ (ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) b).toNNReal := by
    intro s hs
    have hU' : ∀ u ≤ s, b u ∈ U := fun u hu =>
      ContinuousPath.mem_of_lt_exitTime U b _ (by rw [hτe]; exact ENNReal.coe_lt_coe.2 (hu.trans_lt hs))
    obtain ⟨u0, hu0, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) s)).exists_isMaxOn
      (nonempty_Icc.2 zero_le) ((continuous_norm.comp (ψ.continuous.comp b.continuous)).continuousOn)
    have hM : ‖ψ (b u0)‖ < 1 := by
      have h := hψ.mapsTo_ball (hU' u0 hu0.2)
      rwa [Metric.mem_ball, dist_zero_right] at h
    filter_upwards [hrrt.eventually (lt_mem_nhds hM)] with k hk
    have hinD : ∀ u ≤ s, b u ∈ chartSubdomain U ψ (rr k) := fun u hu => by
      refine ⟨hU' u hu, ?_⟩
      rw [mem_preimage, Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (isMaxOn_iff.1 hmax u ⟨zero_le, hu⟩) hk
    have h := ENNReal.toNNReal_mono (hfin k) (le_exitTime_of_forall_mem (isOpen_chartSubdomain hU (rr k)) hinD)
    rwa [ENNReal.toNNReal_coe] at h
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨s, has, hsτ⟩ := exists_between ha
    filter_upwards [hreach s hsτ] with k hk
    exact has.trans_le hk
  · exact Eventually.of_forall fun k => (hle k).trans_lt ha

/-! ### Dynkin's identity for the chart path -/

/-- **Dynkin's identity for the chart path.** Let `F` be smooth with `ΔF = -c F` and `|F| ≤ 1`. Under planar
Brownian motion from `y ∈ U`, the chart path `Y` (the chart image of the path run with the conformal clock,
stopped at its exit from `U`) satisfies `E F(Y_t) - F(ψ y) = -(c/2) E ∫_0^{t ∧ L} F(Y_v) dv`, with `L = A(τ_U)`. -/
theorem chart_fourier_dynkin (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {F : ℂ → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) {c : ℝ} (hΔ : ∀ v, Δ F v = -c * F v)
    (hFb : ∀ v, |F v| ≤ 1) {y : ℂ} (hy : y ∈ U) (t : ℝ≥0) :
    (∫ b, F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t) ∂planarBrownianMotion y) - F (ψ y) =
      -(c / 2) * ∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal),
        F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) v.toNNReal)) ∂planarBrownianMotion y := by
  have hρy : ‖ψ y‖ < 1 := by
    have h := hψ.mapsTo_ball hy
    rwa [Metric.mem_ball, dist_zero_right] at h
  obtain ⟨rr, hrr0, hrr1, hrrt⟩ := exists_chart_exhaustion hρy
  have hyD : ∀ k, y ∈ chartSubdomain U ψ (rr k) := fun k =>
    ⟨hy, by rw [mem_preimage, Metric.mem_ball, dist_zero_right]; exact hrr0 k⟩
  choose m M hm hρm hρM using fun k => exists_chartRateDensity_bounds hU hUb hψ (hrr1 k)
  set N : ℕ → ℝ≥0 := fun k => ((t : ℝ) / min (m k) 1).toNNReal with hNdef
  have hN : ∀ k, (t : ℝ) ≤ min (m k) 1 * N k := fun k => by
    have hpos : 0 < min (m k) 1 := lt_min (hm k) one_pos
    refine le_of_eq ?_
    simp only [hNdef]
    rw [Real.coe_toNNReal _ (div_nonneg (NNReal.coe_nonneg t) hpos.le), mul_comm,
      div_mul_cancel₀ _ hpos.ne']
  have hDo : ∀ k, IsOpen (chartSubdomain U ψ (rr k)) := fun k => isOpen_chartSubdomain hU (rr k)
  have hρc : ∀ k, ContinuousOn (fun v => ‖deriv ψ v‖ ^ 2) (chartSubdomain U ψ (rr k)) := fun k =>
    (continuousOn_chartRateDensity hU hψ).mono (chartSubdomain_subset (rr k))
  have hTst : ∀ k, IsStoppingTime ContinuousPath.canonicalFiltration
      fun b => ((localConformalStop U ψ (rr k) t (N k) b : ℝ≥0) : WithTop ℝ≥0) := fun k => by
    have h := (isStoppingTime_clockInverse_exitRateClock (hDo k) (hρc k) (hm k) (hρm k) (hρM k) t).min
      (ContinuousPath.isStoppingTime_exitTimeTrunc _ (hDo k) (N k))
    simpa only [localConformalStop, localConformalClock, WithTop.coe_min] using h
  have hTN : ∀ k b, localConformalStop U ψ (rr k) t (N k) b ≤ N k := fun k b =>
    (min_le_right _ _).trans (ContinuousPath.exitTimeTrunc_le _ (N k) b)
  have hTr : ∀ k b, ((localConformalStop U ψ (rr k) t (N k) b : ℝ≥0) : ℝ≥0∞) ≤
      ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) b := fun k b =>
    (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans
      (by rw [ContinuousPath.coe_exitTimeTrunc_ennreal]; exact min_le_left _ _)
  have hdyn := fun k => chart_dynkin hU hUb hψ (hrr1 k) hF (localConformalStop U ψ (rr k) t (N k)) (hTst k)
    (hTN k) (hTr k) (hyD k)
  have hdrift : ∀ k (p : ContinuousPath ℂ), (∫ s in (0 : ℝ)..(localConformalStop U ψ (rr k) t (N k) p : ℝ),
      (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ F (ψ (p s.toNNReal)))) =
      -(c / 2) * ∫ s in (0 : ℝ)..(localConformalStop U ψ (rr k) t (N k) p : ℝ),
        ‖deriv ψ (p s.toNNReal)‖ ^ 2 * F (ψ (p s.toNNReal)) := by
    intro k p
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hΔ]
    ring
  have hgood := ae_mem_exitRateGoodSet_chart hU hUb hψ hy
  have h0 := ae_planarBrownianMotion_eval_zero y
  have hpw := fun (p : ContinuousPath ℂ) (hp : p ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (hp0 : p 0 = y)
    (k : ℕ) => chart_localized_stop_pathwise hU hψ (hrr1 k) (hm k) (hρm k) (hρM k) (hN k) hp
      (by rw [hp0]; exact hyD k) F
  have htheta : ∀ p ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2),
      Tendsto (fun k => min (t : ℝ)
        (chartClock U ψ p (ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) p).toNNReal)) atTop
        (𝓝 (min (t : ℝ) (chartClock U ψ p (ContinuousPath.exitTime U p).toNNReal))) := fun p hp =>
    tendsto_const_nhds.min (tendsto_chartClock_exitTime_chartSubdomain hU hψ hrrt hp)
  have hgm : ∀ k, Measurable fun p : ContinuousPath ℂ => F (ψ (p (localConformalStop U ψ (rr k) t (N k) p))) :=
    fun k => hF.continuous.measurable.comp (ψ.continuous.measurable.comp
      ((ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
        (measurable_id.prodMk (measurable_of_isStoppingTime_coe (hTst k)))))
  have hlimg : Tendsto (fun k => ∫ p, F (ψ (p (localConformalStop U ψ (rr k) t (N k) p)))
      ∂planarBrownianMotion y) atTop
      (𝓝 (∫ p, F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) p) t) ∂planarBrownianMotion y)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun k => (hgm k).aestronglyMeasurable)
      (integrable_const _) (fun k => ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hFb _) ?_
    filter_upwards [hgood, h0] with p hp hp0
    have hcY : Continuous fun x : ℝ =>
        F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) p) x.toNNReal) :=
      hF.continuous.comp ((ContinuousMap.continuous _).comp continuous_real_toNNReal)
    have hlim : Tendsto (fun k => F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) p)
        (min (t : ℝ) (chartClock U ψ p
          (ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) p).toNNReal)).toNNReal)) atTop
        (𝓝 (F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) p) t))) := by
      rw [← chartStopPath_lbmContinuousPath_min_exit hU hψ hp t]
      exact (hcY.tendsto _).comp (htheta p hp)
    refine hlim.congr fun k => ?_
    rw [(hpw p hp hp0 k).1]
  have hlimh : Tendsto (fun k => ∫ p, (∫ s in (0 : ℝ)..(localConformalStop U ψ (rr k) t (N k) p : ℝ),
      (1 / 2 : ℝ) * (‖deriv ψ (p s.toNNReal)‖ ^ 2 * Δ F (ψ (p s.toNNReal)))) ∂planarBrownianMotion y) atTop
      (𝓝 (∫ p, -(c / 2) * (∫ v in (0 : ℝ)..min (t : ℝ)
        (chartClock U ψ p (ContinuousPath.exitTime U p).toNNReal),
        F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) p) v.toNNReal)) ∂planarBrownianMotion y)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => |c| / 2 * t)
      (fun k => (hdyn k).1.aestronglyMeasurable) (integrable_const _) (fun k => ?_) ?_
    · filter_upwards [hgood, h0] with p hp hp0
      rw [hdrift k p, (hpw p hp hp0 k).2, norm_mul]
      have hθ0 : 0 ≤ min (t : ℝ)
          (chartClock U ψ p (ContinuousPath.exitTime (chartSubdomain U ψ (rr k)) p).toNNReal) :=
        le_min (NNReal.coe_nonneg t)
          (IsTimeChangeClock.clock_nonneg (isTimeChangeClock_chartClock_of_mem hU hψ hp) _)
      refine le_trans (mul_le_mul_of_nonneg_left (?_ : _ ≤ (t : ℝ)) (norm_nonneg _)) (le_of_eq ?_)
      · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun v _ => ?_).trans ?_
        · rw [Real.norm_eq_abs]
          exact hFb _
        · rw [one_mul, sub_zero, abs_of_nonneg hθ0]
          exact min_le_left _ _
      · rw [norm_neg, Real.norm_eq_abs, abs_div, abs_two]
    · filter_upwards [hgood, h0] with p hp hp0
      have hcF : Continuous fun v : ℝ =>
          F (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) p) v.toNNReal) :=
        hF.continuous.comp ((ContinuousMap.continuous _).comp continuous_real_toNNReal)
      have hprim := intervalIntegral.continuous_primitive (fun a b => hcF.intervalIntegrable (μ := volume) a b) 0
      refine (((hprim.tendsto _).comp (htheta p hp)).const_mul (-(c / 2))).congr fun k => ?_
      simp only [Function.comp_apply]
      rw [hdrift k p, (hpw p hp hp0 k).2]
  have huniq := tendsto_nhds_unique ((hlimg.sub_const (F (ψ y))).congr fun k => (hdyn k).2) hlimh
  exact huniq.trans (integral_const_mul _ _)


end ChartDynkin

section BrownianIncrements


theorem pairingCLM_add_left (ξ ζ y : ℂ) : pairingCLM (ξ + ζ) y = pairingCLM ξ y + pairingCLM ζ y := by
  simp only [pairingCLM_apply, Complex.add_re, Complex.add_im]
  ring

/-! ### Plane waves and Fourier functionals of paths -/

/-- The plane wave `v ↦ exp (i ⟪ξ, v⟫)`. -/
noncomputable def planeWave (ξ v : ℂ) : ℂ := Complex.exp ((pairingCLM ξ v : ℂ) * Complex.I)

theorem norm_planeWave (ξ v : ℂ) : ‖planeWave ξ v‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_planeWave (ξ : ℂ) : Continuous (planeWave ξ) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (pairingCLM ξ).continuous).mul continuous_const)

/-- The Fourier functional `exp (i Σ_{u ∈ I} ⟪η u, ω u⟫)` of a path at the finitely many times of `I`. -/
noncomputable def pathWave (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ) (ω : ContinuousPath ℂ) : ℂ :=
  Complex.exp (((∑ u ∈ I, pairingCLM (η u) (ω u) : ℝ) : ℂ) * Complex.I)

theorem norm_pathWave (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ) (ω : ContinuousPath ℂ) : ‖pathWave I η ω‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_pathWave (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ) : Continuous (pathWave I η) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_finsetSum I fun u _ =>
    (pairingCLM (η u)).continuous.comp (continuous_eval_const u))).mul continuous_const)

/-- **Standard planar Brownian increments.** A law `P` of planar paths has standard Brownian increments if, for all
times `s, t`, every `ξ` and every Fourier functional `Φ` of the path at times `≤ s`,
`E[Φ exp (i ⟪ξ, ω (s + t) - ω s⟫)] = exp (-|ξ|² t / 2) E[Φ]`. -/
def HasBrownianIncrements (P : Measure (ContinuousPath ℂ)) : Prop :=
  ∀ (s t : ℝ≥0) (ξ : ℂ) (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ), (∀ u ∈ I, u ≤ s) →
    ∫ ω, pathWave I η ω * planeWave ξ (ω (s + t) - ω s) ∂P =
      (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) * ∫ ω, pathWave I η ω ∂P

theorem integral_pathWave_singleton_zero {μ : Measure (ContinuousPath ℂ)} [IsProbabilityMeasure μ] {x : ℂ}
    (h0 : ∀ᵐ ω ∂μ, ω 0 = x) (c : ℂ) : ∫ ω, pathWave {0} (fun _ => c) ω ∂μ = planeWave c x := by
  rw [integral_congr_ae (g := fun _ => planeWave c x) ?_]
  · simp
  · filter_upwards [h0] with ω hω
    simp [pathWave, planeWave, hω]

/-- **Fourier functionals of the finite-dimensional laws.** Two laws of paths started at the same point with standard
planar Brownian increments give every Fourier functional the same mean. -/
theorem integral_pathWave_eq_of_hasBrownianIncrements {P Q : Measure (ContinuousPath ℂ)}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {x : ℂ}
    (hP0 : ∀ᵐ ω ∂P, ω 0 = x) (hQ0 : ∀ᵐ ω ∂Q, ω 0 = x)
    (hP : HasBrownianIncrements P) (hQ : HasBrownianIncrements Q) (I : Finset ℝ≥0) :
    ∀ η : ℝ≥0 → ℂ, ∫ ω, pathWave I η ω ∂P = ∫ ω, pathWave I η ω ∂Q := by
  induction I using Finset.induction_on_max with
  | empty =>
    intro η
    simp [pathWave]
  | insert M I' hlt ih =>
    intro η
    have hM : M ∉ I' := fun h => lt_irrefl M (hlt M h)
    obtain ⟨s, hsM, J, ζ, hJs, hfac, hJ⟩ : ∃ s : ℝ≥0, s ≤ M ∧
        ∃ (J : Finset ℝ≥0) (ζ : ℝ≥0 → ℂ), (∀ u ∈ J, u ≤ s) ∧
          (∀ ω : ContinuousPath ℂ, pathWave (insert M I') η ω =
            pathWave J ζ ω * planeWave (η M) (ω (s + (M - s)) - ω s)) ∧
          ∫ ω, pathWave J ζ ω ∂P = ∫ ω, pathWave J ζ ω ∂Q := by
      by_cases hne : I'.Nonempty
      · set s := I'.max' hne with hsdef
        have hsI : s ∈ I' := I'.max'_mem hne
        refine ⟨s, (hlt s hsI).le, I', fun u => η u + if u = s then η M else 0,
          fun u hu => I'.le_max' u hu, fun ω => ?_, ih _⟩
        rw [add_tsub_cancel_of_le (hlt s hsI).le]
        have hsplit : ∀ u, pairingCLM (η u + if u = s then η M else 0) (ω u) =
            pairingCLM (η u) (ω u) + (if u = s then pairingCLM (η M) (ω u) else 0) := by
          intro u
          split_ifs <;> simp only [add_zero, pairingCLM_add_left]
        have hsum : ∑ u ∈ I', pairingCLM (η u + if u = s then η M else 0) (ω u) =
            ∑ u ∈ I', pairingCLM (η u) (ω u) + pairingCLM (η M) (ω s) := by
          rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_add_distrib,
            Finset.sum_ite_eq' I' s (fun u => pairingCLM (η M) (ω u))]
          simp [hsI]
        simp only [pathWave, planeWave]
        rw [← Complex.exp_add, Finset.sum_insert hM, hsum, map_sub]
        congr 1
        push_cast
        ring
      · have hI' : I' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
        subst hI'
        refine ⟨0, zero_le, {0}, fun _ => η M, fun u hu => by rw [Finset.mem_singleton.1 hu], fun ω => ?_,
          ?_⟩
        · simp only [pathWave, planeWave]
          rw [← Complex.exp_add, Finset.sum_insert (Finset.notMem_empty M), Finset.sum_empty,
            Finset.sum_singleton, map_sub, zero_add, tsub_zero]
          congr 1
          push_cast
          ring
        · rw [integral_pathWave_singleton_zero hP0, integral_pathWave_singleton_zero hQ0]
    simp_rw [hfac]
    rw [hP s (M - s) (η M) J ζ hJs, hQ s (M - s) (η M) J ζ hJs, hJ]

/-- **Finite-dimensional laws from Fourier functionals.** -/
theorem map_restrict_eq_of_integral_pathWave_eq {P Q : Measure (ContinuousPath ℂ)}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ), ∫ ω, pathWave I η ω ∂P = ∫ ω, pathWave I η ω ∂Q)
    (I : Finset ℝ≥0) :
    P.map (fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t)) =
      Q.map (fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t)) := by
  have hm : Measurable (fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t)) :=
    Measurable.of_eval fun u => (continuous_eval_const (u : ℝ≥0)).measurable
  have : IsProbabilityMeasure (P.map fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (Q.map fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  set η : ℝ≥0 → ℂ := fun u => if hu : u ∈ I then
      ⟨L (Pi.single ⟨u, hu⟩ (1 : ℂ)), L (Pi.single ⟨u, hu⟩ Complex.I)⟩ else 0 with hη
  have hsingle : ∀ (i : I) (v : ℂ), L (Pi.single i v) = pairingCLM (η i) v := by
    intro i v
    have hv : (Pi.single i v : I → ℂ) =
        v.re • (Pi.single i (1 : ℂ) : I → ℂ) + v.im • (Pi.single i Complex.I : I → ℂ) := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simp [hj]
    have hηi : η i = ⟨L (Pi.single i (1 : ℂ)), L (Pi.single i Complex.I)⟩ := by
      simp [hη]
    rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hηi, pairingCLM_apply]
    dsimp only
    ring
  have hLsum : ∀ ω : ContinuousPath ℂ,
      L (I.restrict fun t => ω t) = ∑ u ∈ I, pairingCLM (η u) (ω u) := by
    intro ω
    rw [← Finset.univ_sum_single (I.restrict fun t => ω t), map_sum]
    rw [Finset.sum_congr rfl fun i _ => hsingle i ((I.restrict fun t => ω t) i)]
    exact Finset.sum_coe_sort I (fun u => pairingCLM (η u) (ω u))
  have hcont : Continuous fun y : I → ℂ => Complex.exp ((L y : ℂ) * Complex.I) := by fun_prop
  rw [charFunDual_apply, charFunDual_apply, integral_map hm.aemeasurable hcont.aestronglyMeasurable,
    integral_map hm.aemeasurable hcont.aestronglyMeasurable]
  simp only [hLsum]
  exact h I η

/-- Finite-dimensional distributions determine finite measures on planar continuous-path space (the planar form of
`HarmonicBalls.Section6.real_path_measure_eq_of_finite_dimensional_laws`). -/
theorem complex_path_measure_eq_of_finite_dimensional_laws
    (μ ν : Measure (ContinuousPath ℂ)) [IsFiniteMeasure μ]
    (h : ∀ I : Finset ℝ≥0,
      μ.map (fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t)) =
        ν.map (fun ω : ContinuousPath ℂ => I.restrict (fun t => ω t))) : μ = ν := by
  let eval : ContinuousPath ℂ → ℝ≥0 → ℂ := fun ω t => ω t
  have heval : Measurable eval := Measurable.of_eval fun t =>
    ContinuousPath.measurable_coordinateProcess t
  have hfull : μ.map eval = ν.map eval := by
    apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
    intro I
    have hI : Measurable (I.restrict : (ℝ≥0 → ℂ) → I → ℂ) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    rw [Measure.map_map hI heval, Measure.map_map hI heval]
    exact h I
  let restrict : (ℝ≥0 → ℂ) → DenseTime → ℂ := fun ω t => ω (DenseTime.castOrderEmbedding t)
  have hrestrict : Measurable restrict := Measurable.of_eval fun _ => measurable_pi_apply _
  have hdense := congrArg (fun ρ : Measure (ℝ≥0 → ℂ) => ρ.map restrict) hfull
  rw [Measure.map_map hrestrict heval, Measure.map_map hrestrict heval] at hdense
  apply MarkovProcess.Measure.map_denseRestriction_injective
  exact hdense

/-- **Uniqueness of planar Brownian motion.** Two laws of planar paths started at the same point with standard planar
Brownian increments are equal. -/
theorem eq_of_hasBrownianIncrements {P Q : Measure (ContinuousPath ℂ)}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {x : ℂ}
    (hP0 : ∀ᵐ ω ∂P, ω 0 = x) (hQ0 : ∀ᵐ ω ∂Q, ω 0 = x)
    (hP : HasBrownianIncrements P) (hQ : HasBrownianIncrements Q) : P = Q :=
  complex_path_measure_eq_of_finite_dimensional_laws P Q fun I =>
    map_restrict_eq_of_integral_pathWave_eq
      (fun I η => integral_pathWave_eq_of_hasBrownianIncrements hP0 hQ0 hP hQ I η) I

/-! ### The strong Markov property for bounded complex functionals -/

/-- **Strong Markov property at an optional time, parameter form for bounded complex functionals.** -/
theorem integral_planarLaw_shift_optionalTime_param {β : Type*} [MeasurableSpace β] (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | T ω < t})
    (V : ContinuousPath ℂ → β) (hVm : Measurable V)
    (hV : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (V ⁻¹' B ∩ {ω | T ω < t}))
    {H : β × ContinuousPath ℂ → ℂ} (hH : Measurable H) {C : ℝ} (hC : ∀ p, ‖H p‖ ≤ C) :
    ∫ ω in {ω | T ω < ⊤}, H (V ω, ContinuousPath.shift ((T ω).untopD 0) ω) ∂planarLaw z =
      ∫ ω in {ω | T ω < ⊤}, ∫ ω', H (V ω, ω') ∂planarLaw (ω ((T ω).untopD 0)) ∂planarLaw z := by
  set μ := (planarLaw z).restrict {ω | T ω < ⊤} with hμ
  set F : ContinuousPath ℂ → β × ContinuousPath ℂ :=
    fun ω => (V ω, ContinuousPath.shift ((T ω).untopD 0) ω) with hF
  have hFm : Measurable F :=
    hVm.prodMk (ContinuousPath.measurable_shift_of_measurable _ (MatedCRT.OptionalTime.measurable_untopD hT))
  set κ : Kernel (ContinuousPath ℂ) (β × ContinuousPath ℂ) :=
    Kernel.deterministic V hVm ×ₖ Kernel.comap planarBrownianMotion (fun ω => ω ((T ω).untopD 0))
      (MatedCRT.OptionalTime.measurable_eval_untopD hT) with hκ
  have hκapp : ∀ ω, κ ω = (planarLaw (ω ((T ω).untopD 0))).map (Prod.mk (V ω)) := by
    intro ω
    rw [hκ, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod, Kernel.comap_apply]
    rfl
  have heq : μ.map F = κ ∘ₘ μ := by
    ext S hS
    have h := MatedCRT.OptionalTime.lintegral_planarLaw_shift_optionalTime_param z T hT V hVm hV
      (H := S.indicator 1) (measurable_one.indicator hS)
    calc (μ.map F) S = ∫⁻ p, S.indicator 1 p ∂(μ.map F) := (lintegral_indicator_one hS).symm
      _ = ∫⁻ ω, S.indicator 1 (F ω) ∂μ := lintegral_map (measurable_one.indicator hS) hFm
      _ = ∫⁻ ω, ∫⁻ ω', S.indicator 1 (V ω, ω') ∂planarLaw (ω ((T ω).untopD 0)) ∂μ := h
      _ = ∫⁻ ω, κ ω S ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [hκapp, Measure.map_apply measurable_prodMk_left hS,
            ← lintegral_indicator_one (measurable_prodMk_left hS)]
          rfl
      _ = (κ ∘ₘ μ) S := (Measure.bind_apply hS (Kernel.aemeasurable _)).symm
  have hint0 : Integrable H (μ.map F) :=
    (integrable_const C).mono' hH.aestronglyMeasurable (ae_of_all _ hC)
  rw [heq, Measure.comp_eq_comp_const_apply] at hint0
  calc ∫ ω, H (F ω) ∂μ = ∫ p, H p ∂(μ.map F) :=
        (integral_map hFm.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ p, H p ∂(κ ∘ₘ μ) := by rw [heq]
    _ = ∫ ω, ∫ p, H p ∂(κ ω) ∂μ := by
        rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp hint0]
        rfl
    _ = ∫ ω, ∫ ω', H (V ω, ω') ∂planarLaw (ω ((T ω).untopD 0)) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        beta_reduce
        rw [hκapp, integral_map measurable_prodMk_left.aemeasurable hH.aestronglyMeasurable]

/-! ### Planar Brownian motion has standard increments -/

/-- An event which does not depend on the path is in every `F⁰_t`. -/
theorem measurableSet_setOf_const_filtration (p : Prop) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {_ω : ContinuousPath ℂ | p} := by
  by_cases h : p
  · rw [show {_ω : ContinuousPath ℂ | p} = Set.univ from Set.eq_univ_of_forall fun _ => h]
    exact @MeasurableSet.univ _ (ContinuousPath.canonicalFiltration (alpha := ℂ) t)
  · rw [show {_ω : ContinuousPath ℂ | p} = ∅ from Set.ext fun _ => by simp [h]]
    exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := ℂ) t)

theorem integral_exp_gaussianReal (m : ℝ) (v : ℝ≥0) (c : ℝ) :
    ∫ a, Complex.exp (((c * (a - m) : ℝ) : ℂ) * Complex.I) ∂gaussianReal m v =
      (Real.exp (-(c ^ 2 * (v : ℝ) / 2)) : ℂ) := by
  have h1 : ∀ a : ℝ, Complex.exp (((c * (a - m) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((c : ℂ) * (a : ℂ) * Complex.I) * Complex.exp (-((c : ℂ) * (m : ℂ) * Complex.I)) := by
    intro a
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h1]
  rw [integral_mul_const, ← charFun_apply_real, charFun_gaussianReal, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem integral_planeWave_sub_planarGaussian (ξ y : ℂ) (t : ℝ≥0) :
    ∫ v, planeWave ξ (v - y) ∂planarGaussian y t = (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) := by
  rw [planarGaussian, integral_map_equiv]
  have hfac : ∀ p : ℝ × ℝ, planeWave ξ (Complex.measurableEquivRealProd.symm p - y) =
      Complex.exp (((ξ.re * (p.1 - y.re) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((ξ.im * (p.2 - y.im) : ℝ) : ℂ) * Complex.I) := by
    intro p
    have hre : (Complex.measurableEquivRealProd.symm p).re = p.1 := rfl
    have him : (Complex.measurableEquivRealProd.symm p).im = p.2 := rfl
    rw [planeWave, ← Complex.exp_add, pairingCLM_apply, Complex.sub_re, Complex.sub_im, hre, him]
    congr 1
    push_cast
    ring
  simp_rw [hfac]
  rw [integral_prod_mul (fun a : ℝ => Complex.exp (((ξ.re * (a - y.re) : ℝ) : ℂ) * Complex.I))
      (fun b : ℝ => Complex.exp (((ξ.im * (b - y.im) : ℝ) : ℂ) * Complex.I)),
    integral_exp_gaussianReal, integral_exp_gaussianReal, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The characteristic function of a planar Brownian increment. -/
theorem integral_planeWave_increment (ξ y : ℂ) (t : ℝ≥0) :
    ∫ ω, planeWave ξ (ω t - ω 0) ∂planarBrownianMotion y = (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) := by
  calc ∫ ω, planeWave ξ (ω t - ω 0) ∂planarBrownianMotion y
      = ∫ ω, planeWave ξ (ω t - y) ∂planarBrownianMotion y := by
        refine integral_congr_ae ?_
        filter_upwards [ae_planarBrownianMotion_eval_zero y] with ω hω
        rw [hω]
    _ = ∫ v, planeWave ξ (v - y) ∂(planarBrownianMotion y).map (fun b => b t) :=
        (integral_map (continuous_eval_const t).measurable.aemeasurable
          ((continuous_planeWave ξ).comp (continuous_id.sub continuous_const)).aestronglyMeasurable).symm
    _ = _ := by
        rw [MatedCRT.KilledOccupation.map_eval_planarBrownianMotion, integral_planeWave_sub_planarGaussian]

/-- **Planar Brownian motion has standard planar Brownian increments** (Markov property at a fixed time). -/
theorem hasBrownianIncrements_planarBrownianMotion (y : ℂ) :
    HasBrownianIncrements (planarBrownianMotion y) := by
  intro s t ξ I η hIs
  set W : ℝ≥0 → ContinuousPath ℂ → WithTop ℝ≥0 := fun u _ => ((min u s : ℝ≥0) : WithTop ℝ≥0) with hW
  set T : ContinuousPath ℂ → WithTop ℝ≥0 := fun _ => (s : WithTop ℝ≥0) with hTdef
  set G : (ℝ≥0 → ℂ) → ℝ := fun v => ∑ u ∈ I, pairingCLM (η u) (v u) with hG
  set V : ContinuousPath ℂ → ℝ := G ∘ (fun ω (u : ℝ≥0) => ω ((W u ω).untopD 0)) with hVdef
  have hT : ∀ t' : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t'] {ω | T ω < t'} :=
    fun t' => measurableSet_setOf_const_filtration ((s : WithTop ℝ≥0) < t') t'
  have hWm : ∀ u, ∀ t' : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t'] {ω | W u ω < t'} :=
    fun u t' => measurableSet_setOf_const_filtration (((min u s : ℝ≥0) : WithTop ℝ≥0) < t') t'
  have hWT : ∀ u ω, W u ω ≤ T ω := fun u _ => WithTop.coe_le_coe.2 (min_le_right u s)
  have hGm : Measurable G :=
    Finset.measurable_sum _ fun u _ => (pairingCLM (η u)).continuous.measurable.comp (measurable_pi_apply u)
  have hφm : Measurable (fun ω : ContinuousPath ℂ => fun u : ℝ≥0 => ω ((W u ω).untopD 0)) := by
    refine Measurable.of_eval fun u => ?_
    simp only [hW, WithTop.untopD_coe]
    exact (continuous_eval_const _).measurable
  have hVm : Measurable V := hGm.comp hφm
  have hV : ∀ B : Set ℝ, MeasurableSet B → ∀ t' : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t'] (V ⁻¹' B ∩ {ω | T ω < t'}) :=
    fun B hB t' => MatedCRT.OptionalTime.measurableSet_pi_eval_untopD_inter_lt hWm hT hWT (hGm hB) t'
  set H : ℝ × ContinuousPath ℂ → ℂ :=
    fun p => Complex.exp ((p.1 : ℂ) * Complex.I) * planeWave ξ (p.2 t - p.2 0) with hH
  have hHc : Continuous H :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).mul
      ((continuous_planeWave ξ).comp (((continuous_eval_const t).comp continuous_snd).sub
        ((continuous_eval_const 0).comp continuous_snd)))
  have hHb : ∀ p, ‖H p‖ ≤ 1 := fun p => by
    simp only [hH, norm_mul, norm_planeWave, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hSM := integral_planarLaw_shift_optionalTime_param y T hT V hVm hV hHc.measurable hHb
  have hall : {ω : ContinuousPath ℂ | T ω < ⊤} = univ :=
    Set.eq_univ_of_forall fun _ => show (s : WithTop ℝ≥0) < ⊤ from WithTop.coe_lt_top ..
  simp only [hall, Measure.restrict_univ] at hSM
  have hVsum : ∀ ω : ContinuousPath ℂ, V ω = ∑ u ∈ I, pairingCLM (η u) (ω u) := by
    intro ω
    simp only [hVdef, hG, hW, Function.comp_apply, WithTop.untopD_coe]
    exact Finset.sum_congr rfl fun u hu => by rw [min_eq_left (hIs u hu)]
  have hlhs : ∀ ω : ContinuousPath ℂ, pathWave I η ω * planeWave ξ (ω (s + t) - ω s) =
      H (V ω, ContinuousPath.shift ((T ω).untopD 0) ω) := by
    intro ω
    simp only [hH, hTdef, WithTop.untopD_coe, ContinuousPath.shift_apply, add_zero, pathWave, hVsum]
  have hrhs : ∀ ω : ContinuousPath ℂ, ∫ ω', H (V ω, ω') ∂planarLaw (ω ((T ω).untopD 0)) =
      (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) * pathWave I η ω := by
    intro ω
    simp only [hH]
    rw [integral_const_mul, planarLaw, integral_planeWave_increment, pathWave, hVsum]
    exact mul_comm _ _
  simp_rw [hlhs]
  refine hSM.trans ?_
  simp_rw [hrhs]
  rw [integral_const_mul]
  rfl


end BrownianIncrements

section ContinuedChartPath


theorem planeWave_add (ξ a c : ℂ) : planeWave ξ (a + c) = planeWave ξ a * planeWave ξ c := by
  simp only [planeWave, map_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-! ### The conformal clock after the exit time -/

/-- After the exit time the conformal clock runs at unit rate. -/
theorem chartClock_exit_add (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (u : ℝ≥0) :
    chartClock U ψ b ((ContinuousPath.exitTime U b).toNNReal + u) =
      chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal + u := by
  set τ := (ContinuousPath.exitTime U b).toNNReal with hτdef
  have hτe : ContinuousPath.exitTime U b = τ := (ENNReal.coe_toNNReal hb.1.ne).symm
  have h0 := intervalIntegrable_exitRate_of_mem_exitRateGoodSet hU (continuousOn_chartRateDensity hU hψ) hb
  have hint : ∀ a c : ℝ, IntervalIntegrable (chartRate U ψ b) volume a c := fun a c =>
    (h0 a).symm.trans (h0 c)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ ((τ + u : ℝ≥0) : ℝ))
  have hcongr : EqOn (chartRate U ψ b) (fun _ => (1 : ℝ)) (uIcc (τ : ℝ) ((τ + u : ℝ≥0) : ℝ)) := by
    intro x hx
    rw [uIcc_of_le (NNReal.coe_le_coe.2 le_self_add)] at hx
    apply chartRate_of_exitTime_le
    rw [hτe]
    have h3 := Real.toNNReal_le_toNNReal hx.1
    rw [Real.toNNReal_coe] at h3
    exact ENNReal.coe_le_coe.2 h3
  have h1 : ∫ x in (τ : ℝ)..((τ + u : ℝ≥0) : ℝ), chartRate U ψ b x = u := by
    rw [intervalIntegral.integral_congr hcongr]
    simp
  simp only [chartClock]
  rw [← hsplit, h1]

/-! ### The chart path continued by the Brownian increments after the exit -/

/-- The chart path `Y` of `b`, continued after its exit time `L` by the increments of the time-changed path:
`Z_t = Y_t + (X_t - X_{t ∧ L})`, `X` the path run with the conformal clock. -/
noncomputable def zPath (U : Set ℂ) (ψ : C(ℂ, ℂ)) (b : ContinuousPath ℂ) : ContinuousPath ℂ :=
  ⟨fun t => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t +
      (lbmContinuousPath (chartClock U ψ) b t - stopAtExitTime U (lbmContinuousPath (chartClock U ψ) b) t),
    (ContinuousMap.continuous _).add ((ContinuousMap.continuous _).sub (ContinuousMap.continuous _))⟩

theorem zPath_apply (U : Set ℂ) (ψ : C(ℂ, ℂ)) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    zPath U ψ b t = chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t +
      (lbmContinuousPath (chartClock U ψ) b t - stopAtExitTime U (lbmContinuousPath (chartClock U ψ) b) t) :=
  rfl

/-- Along a good path, `Z_t = Y_t + (b(τ + (t - L)₊) - b(τ))`. -/
theorem zPath_apply_of_mem (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (t : ℝ≥0) :
    zPath U ψ b t = chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t +
      (b ((ContinuousPath.exitTime U b).toNNReal +
          ((t : ℝ) - chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal).toNNReal) -
        b (ContinuousPath.exitTime U b).toNNReal) := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  set τ := (ContinuousPath.exitTime U b).toNNReal with hτdef
  have hτe : ContinuousPath.exitTime U b = τ := (ENNReal.coe_toNNReal hb.1.ne).symm
  rw [zPath_apply, stopAtExitTime_lbmContinuousPath_apply hA hτe t]
  congr 1
  have hX : lbmContinuousPath (chartClock U ψ) b t =
      b (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) t) := by
    rw [lbmContinuousPath_of_isTimeChangeClock hA]
    rfl
  rw [hX]
  rcases le_total (t : ℝ) (chartClock U ψ b τ) with h | h
  · have h1 : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) t ≤ τ :=
      (clockInverse_le_iff_of_isTimeChangeClock hA t τ).2 h
    rw [min_eq_left h1, Real.toNNReal_of_nonpos (sub_nonpos.2 h), add_zero, sub_self, sub_self]
  · have h2 : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) t =
        τ + ((t : ℝ) - chartClock U ψ b τ).toNNReal := by
      refine FirstPass.Derived.clockInverse_eq_of_apply_eq hA ?_
      rw [chartClock_exit_add hU hψ hb, Real.coe_toNNReal _ (sub_nonneg.2 h)]
      ring
    rw [h2, min_eq_right le_self_add]

/-! ### An optional version of the inverse conformal clock -/

/-- The conformal clock at rational times, as `ℝ≥0`-valued functionals. -/
noncomputable def chartClockNN (U : Set ℂ) (ψ : C(ℂ, ℂ)) (q : ℚ≥0) (b : ContinuousPath ℂ) : ℝ≥0 :=
  (chartClock U ψ b q).toNNReal

/-- The rational inverse of the conformal clock, an optional time. -/
noncomputable def chartClockInverseOpt (U : Set ℂ) (ψ : C(ℂ, ℂ)) (s : ℝ≥0) :
    ContinuousPath ℂ → WithTop ℝ≥0 :=
  rationalClockInverse (chartClockNN U ψ) s

/-- The exit time from `U` as an optional time. -/
noncomputable def chartExitOpt (U : Set ℂ) (b : ContinuousPath ℂ) : WithTop ℝ≥0 :=
  ContinuousPath.exitTime U b

/-- The inverse conformal clock stopped at the exit time. -/
noncomputable def chartStopOpt (U : Set ℂ) (ψ : C(ℂ, ℂ)) (s : ℝ≥0) (b : ContinuousPath ℂ) : WithTop ℝ≥0 :=
  min (chartClockInverseOpt U ψ s b) (chartExitOpt U b)

theorem chartStopOpt_le (U : Set ℂ) (ψ : C(ℂ, ℂ)) (s : ℝ≥0) (b : ContinuousPath ℂ) :
    chartStopOpt U ψ s b ≤ chartExitOpt U b :=
  min_le_right _ _

theorem measurable_chartClock_canonicalFiltration (hU : IsOpen U) (hψ : IsInverseChart U z ψ) (q : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) q] fun b => chartClock U ψ b q := by
  have h : (fun b : ContinuousPath ℂ => chartClock U ψ b q) =
      (fun b => exitRateClock U (fun v => ‖deriv ψ v‖ ^ 2) b q) ∘ ContinuousPath.stoppedPath q := by
    funext b
    simp only [Function.comp_apply]
    exact (exitRateClock_stoppedPath hU (fun v => ‖deriv ψ v‖ ^ 2) b q).symm
  rw [h]
  exact (measurable_exitRateClock hU (continuousOn_chartRateDensity hU hψ) q).comp
    (LQGClockApproxAdapted.measurable_stoppedPath_canonicalFiltration q)

theorem measurableSet_chartClockInverseOpt_lt (hU : IsOpen U) (hψ : IsInverseChart U z ψ) (s t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {b | chartClockInverseOpt U ψ s b < t} := by
  have hset : {b | chartClockInverseOpt U ψ s b < t} =
      ⋃ (q : ℚ≥0) (_ : (q : ℝ≥0) < t), {b | s < chartClockNN U ψ q b} := by
    ext b
    simp only [chartClockInverseOpt, Set.mem_ofPred_eq, Set.mem_iUnion, rationalClockInverse_lt_iff,
      WithTop.coe_lt_coe, exists_prop]
    exact exists_congr fun q => and_comm
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hm : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (chartClockNN U ψ q) :=
    (measurable_chartClock_canonicalFiltration hU hψ q).real_toNNReal.mono
      ((ContinuousPath.canonicalFiltration (alpha := ℂ)).mono hq.le) le_rfl
  exact hm measurableSet_Ioi

theorem measurableSet_chartExitOpt_lt (hU : IsOpen U) (u : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) u] {b | chartExitOpt U b < u} :=
  (ContinuousPath.isStoppingTime_exitTime U hU).measurableSet_lt u

theorem measurableSet_chartStopOpt_lt (hU : IsOpen U) (hψ : IsInverseChart U z ψ) (s u : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) u] {b | chartStopOpt U ψ s b < u} := by
  have h : {b | chartStopOpt U ψ s b < (u : WithTop ℝ≥0)} =
      {b | chartClockInverseOpt U ψ s b < u} ∪ {b | chartExitOpt U b < u} := by
    ext b
    simp only [chartStopOpt, Set.mem_ofPred_eq, Set.mem_union, min_lt_iff]
  rw [h]
  exact (measurableSet_chartClockInverseOpt_lt hU hψ s u).union (measurableSet_chartExitOpt_lt hU u)

/-- Along a good path, the rational inverse clock is the inverse of the conformal clock. -/
theorem chartClockInverseOpt_eq (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (s : ℝ≥0) :
    chartClockInverseOpt U ψ s b =
      ((_root_.HarmonicBalls.clockInverse (chartClock U ψ b) s : ℝ≥0) : WithTop ℝ≥0) := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  set c := _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s with hcdef
  have hAc : chartClock U ψ b c = s := IsTimeChangeClock.apply_clockInverse_eq hA s
  have hiff : ∀ q : ℝ≥0, s < (chartClock U ψ b q).toNNReal ↔ c < q := fun q => by
    rw [Real.lt_toNNReal_iff_coe_lt, ← hAc]
    exact hA.strictMono.lt_iff_lt
  simp only [chartClockInverseOpt, rationalClockInverse, chartClockNN]
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
    induction d with
    | top => exact le_top
    | coe d =>
      rw [WithTop.coe_lt_coe] at hd
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal hd
      exact (iInf₂_le q ((hiff q).2 hq1)).trans (WithTop.coe_le_coe.2 hq2.le)
  · exact le_iInf₂ fun q hq => WithTop.coe_le_coe.2 ((hiff q).1 hq).le

theorem untopD_min_coe {a : WithTop ℝ≥0} {e : ℝ≥0∞} {c τ : ℝ≥0} (ha : a = (c : WithTop ℝ≥0))
    (he : e = (τ : ℝ≥0∞)) : (min a (e : WithTop ℝ≥0)).untopD 0 = min c τ := by
  subst ha he
  show (min (WithTop.some c) (WithTop.some τ)).untopD 0 = min c τ
  rw [← WithTop.coe_min, WithTop.untopD_coe]

theorem untopD_chartStopOpt (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (u : ℝ≥0) :
    (chartStopOpt U ψ u b).untopD 0 =
      min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) u) (ContinuousPath.exitTime U b).toNNReal :=
  untopD_min_coe (chartClockInverseOpt_eq hU hψ hb u) (ENNReal.coe_toNNReal hb.1.ne).symm

theorem untopD_chartExitOpt {b : ContinuousPath ℂ} (h : ContinuousPath.exitTime U b ≠ ⊤) :
    (chartExitOpt U b).untopD 0 = (ContinuousPath.exitTime U b).toNNReal := by
  unfold chartExitOpt
  generalize ContinuousPath.exitTime U b = e at h ⊢
  lift e to ℝ≥0 using h
  rw [ENNReal.toNNReal_coe]
  rfl

/-! ### The clock value of the exit time is read off the stopped path -/

/-- Along a good path from a point of `U`, `L = A(τ_U) = sup {q ∈ ℚ≥0 | b(A⁻¹(q) ∧ τ_U) ∈ U}`. -/
theorem iSup_mul_indicator_eq_chartClock_exit (hU : IsOpen U) (hψ : IsInverseChart U z ψ)
    {b : ContinuousPath ℂ} (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (hb0 : b 0 ∈ U) :
    (⨆ q : ℚ≥0, ((q : ℝ≥0) : ℝ) * U.indicator (fun _ => (1 : ℝ))
      (b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) q)
        (ContinuousPath.exitTime U b).toNNReal))) =
      chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  set τ := (ContinuousPath.exitTime U b).toNNReal with hτdef
  have hτe : ContinuousPath.exitTime U b = τ := (ENNReal.coe_toNNReal hb.1.ne).symm
  set L := chartClock U ψ b τ with hLdef
  have hL0 : 0 ≤ L := IsTimeChangeClock.clock_nonneg hA τ
  have hterm : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ) * U.indicator (fun _ => (1 : ℝ))
      (b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) q) τ)) =
      if ((q : ℝ≥0) : ℝ) < L then ((q : ℝ≥0) : ℝ) else 0 := by
    intro q
    by_cases hq : ((q : ℝ≥0) : ℝ) < L
    · have hlt : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) q < τ := by
        rw [← hA.strictMono.lt_iff_lt, IsTimeChangeClock.apply_clockInverse_eq hA]
        exact hq
      have hmem : b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) q) τ) ∈ U := by
        rw [min_eq_left hlt.le]
        exact ContinuousPath.mem_of_lt_exitTime U b _ (by rw [hτe]; exact ENNReal.coe_lt_coe.2 hlt)
      rw [indicator_of_mem hmem, ite_eq_left hq]
      simp
    · have hle : τ ≤ _root_.HarmonicBalls.clockInverse (chartClock U ψ b) q := by
        rw [← hA.strictMono.le_iff_le, IsTimeChangeClock.apply_clockInverse_eq hA]
        exact not_lt.1 hq
      have hnot : b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) q) τ) ∉ U := by
        rw [min_eq_right hle]
        have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU b hb0 hb.1.ne
        rw [hU.frontier_eq] at hfr
        exact hfr.2
      rw [indicator_of_notMem hnot, ite_eq_right hq]
      simp
  simp_rw [hterm]
  have hfle : ∀ q : ℚ≥0, (if ((q : ℝ≥0) : ℝ) < L then ((q : ℝ≥0) : ℝ) else 0) ≤ L := fun q => by
    by_cases h : ((q : ℝ≥0) : ℝ) < L
    · rw [ite_eq_left h]
      exact h.le
    · rw [ite_eq_right h]
      exact hL0
  have hbdd : BddAbove (range fun q : ℚ≥0 => if ((q : ℝ≥0) : ℝ) < L then ((q : ℝ≥0) : ℝ) else 0) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hfle q
  refine le_antisymm (ciSup_le hfle) (le_of_forall_lt fun c hc => ?_)
  · rcases lt_or_ge c 0 with hc0 | hc0
    · exact hc0.trans_le ((le_of_eq (by simp)).trans (le_ciSup hbdd 0))
    · obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal
        (show c.toNNReal < L.toNNReal from (Real.toNNReal_lt_toNNReal_iff_of_nonneg hc0).2 hc)
      have hq1' : c < ((q : ℝ≥0) : ℝ) := by
        have h := NNReal.coe_lt_coe.2 hq1
        rwa [Real.coe_toNNReal _ hc0] at h
      have hq2' : ((q : ℝ≥0) : ℝ) < L := by
        have h := NNReal.coe_lt_coe.2 hq2
        rwa [Real.coe_toNNReal _ hL0] at h
      refine hq1'.trans_le ((le_of_eq ?_).trans (le_ciSup hbdd q))
      simp [hq2']

/-! ### The strong Markov property at the exit time -/

/-- **The strong Markov property of `Z` at the exit time.** Under planar Brownian motion from `y ∈ U`,
`E e^{i⟪ξ, Z_t⟫} = E[e^{i⟪ξ, Y_t⟫} e^{-|ξ|² (t - L)₊ / 2}]`: after the exit, `Z` moves by the increments of
the Brownian path, which are independent of the stopped path. -/
theorem integral_planeWave_zPath (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) (ξ : ℂ) (t : ℝ≥0) :
    ∫ b, planeWave ξ (zPath U ψ b t) ∂planarBrownianMotion y =
      ∫ b, planeWave ξ (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t) *
        (Real.exp (-(‖ξ‖ ^ 2 * ((((t : ℝ) - chartClock U ψ b
          (ContinuousPath.exitTime U b).toNNReal).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) ∂planarBrownianMotion y := by
  set φ : ContinuousPath ℂ → ℝ≥0 → ℂ := fun b u => b ((chartStopOpt U ψ u b).untopD 0) with hφdef
  set G : (ℝ≥0 → ℂ) → ℝ × ℂ := fun v =>
    (⨆ q : ℚ≥0, ((q : ℝ≥0) : ℝ) * U.indicator (fun _ => (1 : ℝ)) (v q), ψ (v t)) with hGdef
  have hGm : Measurable G :=
    (Measurable.iSup fun q : ℚ≥0 => measurable_const.mul
      ((measurable_const.indicator hU.measurableSet).comp (measurable_pi_apply ((q : ℝ≥0))))).prodMk
      (ψ.continuous.measurable.comp (measurable_pi_apply t))
  have hφm : Measurable φ := measurable_pi_iff.mpr fun u =>
    MatedCRT.OptionalTime.measurable_eval_untopD (measurableSet_chartStopOpt_lt hU hψ u)
  set V : ContinuousPath ℂ → ℝ × ℂ := G ∘ φ with hVdef
  have hV : ∀ B : Set (ℝ × ℂ), MeasurableSet B → ∀ u : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) u]
        (V ⁻¹' B ∩ {b | chartExitOpt U b < u}) :=
    fun B hB u => MatedCRT.OptionalTime.measurableSet_pi_eval_untopD_inter_lt
      (fun s => measurableSet_chartStopOpt_lt hU hψ s) (measurableSet_chartExitOpt_lt hU)
      (fun s b => chartStopOpt_le U ψ s b) (hGm hB) u
  set H : (ℝ × ℂ) × ContinuousPath ℂ → ℂ := fun p =>
    planeWave ξ p.1.2 * planeWave ξ (p.2 (((t : ℝ) - p.1.1).toNNReal) - p.2 0) with hHdef
  have hev : Continuous fun p : (ℝ × ℂ) × ContinuousPath ℂ => p.2 (((t : ℝ) - p.1.1).toNNReal) :=
    (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp (continuous_const.sub continuous_fst.fst)))
  have hHc : Continuous H :=
    ((continuous_planeWave ξ).comp continuous_fst.snd).mul
      ((continuous_planeWave ξ).comp (hev.sub ((continuous_eval_const 0).comp continuous_snd)))
  have hHb : ∀ p, ‖H p‖ ≤ 1 := fun p => by
    simp only [hHdef, norm_mul, norm_planeWave, mul_one, le_refl]
  have hSM := integral_planarLaw_shift_optionalTime_param y (chartExitOpt U)
    (measurableSet_chartExitOpt_lt hU) V (hGm.comp hφm) hV hHc.measurable hHb
  have hfin : ∀ᵐ b ∂planarLaw y, b ∈ {b | chartExitOpt U b < ⊤} :=
    HarmonicBalls.Section6.ae_planarBrownian_exitTime_bounded_lt_top y hUb
  rw [Measure.restrict_eq_self_of_ae_mem hfin] at hSM
  simp only [planarLaw] at hSM
  have hgood := ae_mem_exitRateGoodSet_chart hU hUb hψ hy
  have h0 := ae_planarBrownianMotion_eval_zero y
  have hVid : ∀ b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2), b 0 = y →
      V b = (chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal,
        chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t) := by
    intro b hb hb0
    have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
    have hτe : ContinuousPath.exitTime U b = ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal hb.1.ne).symm
    have hφb : ∀ u, φ b u = b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) u)
        (ContinuousPath.exitTime U b).toNNReal) := fun u => by
      simp only [hφdef]
      rw [untopD_chartStopOpt hU hψ hb u]
    simp only [hVdef, hGdef, Function.comp_apply, hφb]
    rw [iSup_mul_indicator_eq_chartClock_exit hU hψ hb (by rw [hb0]; exact hy),
      chartStopPath_lbmContinuousPath_apply hA hτe]
  have hpath : ∀ b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2), b 0 = y →
      planeWave ξ (zPath U ψ b t) = H (V b, ContinuousPath.shift ((chartExitOpt U b).untopD 0) b) := by
    intro b hb hb0
    rw [hVid b hb hb0, untopD_chartExitOpt hb.1.ne, zPath_apply_of_mem hU hψ hb t, planeWave_add]
    simp only [hHdef, ContinuousPath.shift_apply, add_zero]
  have hinner : ∀ b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2), b 0 = y →
      ∫ ω', H (V b, ω') ∂planarBrownianMotion (b ((chartExitOpt U b).untopD 0)) =
        planeWave ξ (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) t) *
          (Real.exp (-(‖ξ‖ ^ 2 * ((((t : ℝ) - chartClock U ψ b
            (ContinuousPath.exitTime U b).toNNReal).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) := by
    intro b hb hb0
    rw [hVid b hb hb0]
    simp only [hHdef]
    rw [integral_const_mul, integral_planeWave_increment]
  calc ∫ b, planeWave ξ (zPath U ψ b t) ∂planarBrownianMotion y
      = ∫ b, H (V b, ContinuousPath.shift ((chartExitOpt U b).untopD 0) b) ∂planarBrownianMotion y := by
        refine integral_congr_ae ?_
        filter_upwards [hgood, h0] with b hb hb0
        exact hpath b hb hb0
    _ = ∫ b, ∫ ω', H (V b, ω') ∂planarBrownianMotion (b ((chartExitOpt U b).untopD 0))
          ∂planarBrownianMotion y := hSM
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hgood, h0] with b hb hb0
        exact hinner b hb hb0


end ContinuedChartPath

section CharacteristicFunction

open Laplacian _root_.HarmonicBalls.Section6


/-! ### Deterministic identities -/

theorem planeWave_eq_cos_add_sin (ξ v : ℂ) :
    planeWave ξ v = (Real.cos (pairingCLM ξ v) : ℂ) + (Real.sin (pairingCLM ξ v) : ℂ) * Complex.I := by
  rw [planeWave, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem mul_integral_exp_neg_mul (lam L t : ℝ) :
    lam * ∫ v in L..t, Real.exp (-(lam * (v - L))) = 1 - Real.exp (-(lam * (t - L))) := by
  have hderiv : ∀ v ∈ uIcc L t, HasDerivAt (fun v => -Real.exp (-(lam * (v - L))))
      (lam * Real.exp (-(lam * (v - L)))) v := by
    intro v _
    have h := ((((hasDerivAt_id' v).sub_const L).const_mul lam).neg.exp).neg
    convert h using 1
    simp only [Pi.neg_apply]
    ring
  have hcont : Continuous fun v => lam * Real.exp (-(lam * (v - L))) := by fun_prop
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- **The decay identity along one path.** For a continuous `w` constant from time `L ≥ 0` on, and
`k(v) = w(v) e^{-a (v - L)₊ / 2}`, `(a/2) ∫_0^t k = (a/2) ∫_0^{t ∧ L} w + w(t) - k(t)`. -/
theorem decay_identity {w : ℝ → ℂ} (hw : Continuous w) {a L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : 0 ≤ t)
    (hstop : ∀ v, L ≤ v → w v = w L) :
    ((a / 2 : ℝ) : ℂ) * ∫ v in (0 : ℝ)..t, w v *
        (Real.exp (-(a * (((((v.toNNReal : ℝ≥0) : ℝ) - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) =
      ((a / 2 : ℝ) : ℂ) * (∫ v in (0 : ℝ)..min t L, w v) + w t -
        w t * (Real.exp (-(a * (((((t.toNNReal : ℝ≥0) : ℝ) - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) := by
  have hexpc : Continuous fun v : ℝ =>
      ((Real.exp (-(a * (((((v.toNNReal : ℝ≥0) : ℝ) - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (((continuous_const.mul
      (NNReal.continuous_coe.comp (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp continuous_real_toNNReal).sub continuous_const)))).div_const 2).neg))
  have hk : Continuous fun v : ℝ => w v *
      ((Real.exp (-(a * (((((v.toNNReal : ℝ≥0) : ℝ) - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℝ) : ℂ) :=
    hw.mul hexpc
  have hm0 : 0 ≤ min t L := le_min ht hL
  rw [← intervalIntegral.integral_add_adjacent_intervals (hk.intervalIntegrable 0 (min t L))
    (hk.intervalIntegrable (min t L) t)]
  have h1 : ∫ v in (0 : ℝ)..min t L, w v *
      (Real.exp (-(a * (((((v.toNNReal : ℝ≥0) : ℝ) - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) =
      ∫ v in (0 : ℝ)..min t L, w v := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hm0] at hv
    have hvL : v ≤ L := hv.2.trans (min_le_right _ _)
    simp only [Real.coe_toNNReal _ hv.1, Real.toNNReal_of_nonpos (sub_nonpos.2 hvL), NNReal.coe_zero,
      mul_zero, zero_div, neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one]
  rw [h1, Real.coe_toNNReal t ht]
  rcases le_total t L with htL | htL
  · rw [min_eq_left htL, intervalIntegral.integral_same, Real.toNNReal_of_nonpos (sub_nonpos.2 htL)]
    simp only [NNReal.coe_zero, mul_zero, zero_div, neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one,
      add_zero]
    ring
  · rw [min_eq_right htL]
    have h2 : ∫ v in L..t, w v *
        (Real.exp (-(a * (((((v.toNNReal : ℝ≥0) : ℝ) - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) =
        w L * ((∫ v in L..t, Real.exp (-(a / 2 * (v - L))) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [uIcc_of_le htL] at hv
      simp only [Real.coe_toNNReal _ (hL.trans hv.1), Real.coe_toNNReal _ (sub_nonneg.2 hv.1), hstop v hv.1]
      rw [show -(a * (v - L) / 2) = -(a / 2 * (v - L)) by ring]
    have h3 := mul_integral_exp_neg_mul (a / 2) L t
    have h3' : ((a / 2 : ℝ) : ℂ) * ((∫ v in L..t, Real.exp (-(a / 2 * (v - L))) : ℝ) : ℂ) =
        1 - (Real.exp (-(a * (((t - L).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ) := by
      rw [← Complex.ofReal_mul, h3, Real.coe_toNNReal _ (sub_nonneg.2 htL),
        show -(a * (t - L) / 2) = -(a / 2 * (t - L)) by ring, Complex.ofReal_sub, Complex.ofReal_one]
    rw [h2, hstop t htL]
    linear_combination w L * h3'

/-- **Bounded solutions of `m(t) = c - λ ∫_0^t m` are exponentials** (Picard iteration). -/
theorem eq_exp_mul_of_integral_eq {m : ℝ → ℂ} {c : ℂ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hm : ∀ s, 0 ≤ s → ‖m s‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hint : ∀ s, 0 ≤ s → IntervalIntegrable m volume 0 s)
    (h : ∀ s, 0 ≤ s → m s = c - (lam : ℂ) * ∫ v in (0 : ℝ)..s, m v) {t : ℝ} (ht : 0 ≤ t) :
    m t = (Real.exp (-(lam * t)) : ℂ) * c := by
  have hec : Continuous fun s : ℝ => (Real.exp (-(lam * s)) : ℂ) * c :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).mul
      continuous_const
  have heq : ∀ s, (Real.exp (-(lam * s)) : ℂ) * c =
      c - (lam : ℂ) * ∫ v in (0 : ℝ)..s, (Real.exp (-(lam * v)) : ℂ) * c := by
    intro s
    have h0 := mul_integral_exp_neg_mul lam 0 s
    simp only [sub_zero] at h0
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, h0, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hD : ∀ s, 0 ≤ s → m s - (Real.exp (-(lam * s)) : ℂ) * c =
      -(lam : ℂ) * ∫ v in (0 : ℝ)..s, (m v - (Real.exp (-(lam * v)) : ℂ) * c) := by
    intro s hs
    rw [intervalIntegral.integral_sub (hint s hs) (hec.intervalIntegrable 0 s), h s hs, heq s]
    ring
  have hDb : ∀ s, 0 ≤ s → ‖m s - (Real.exp (-(lam * s)) : ℂ) * c‖ ≤ 2 := by
    intro s hs
    have he : ‖(Real.exp (-(lam * s)) : ℂ) * c‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(lam * s)) * ‖c‖ ≤ 1 * 1 :=
            mul_le_mul (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hlam hs))) hc (norm_nonneg _)
              zero_le_one
        _ = 1 := one_mul 1
    calc ‖m s - (Real.exp (-(lam * s)) : ℂ) * c‖ ≤ ‖m s‖ + ‖(Real.exp (-(lam * s)) : ℂ) * c‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hm s hs) he
      _ = 2 := by norm_num
  have hn : ∀ n : ℕ, ∀ s, 0 ≤ s → ‖m s - (Real.exp (-(lam * s)) : ℂ) * c‖ ≤
      2 * lam ^ n / n.factorial * s ^ n := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hDb s hs
    | succ n ih =>
      intro s hs
      have hI : ‖∫ v in (0 : ℝ)..s, (m v - (Real.exp (-(lam * v)) : ℂ) * c)‖ ≤
          ∫ v in (0 : ℝ)..s, 2 * lam ^ n / n.factorial * v ^ n :=
        intervalIntegral.norm_integral_le_of_norm_le hs (ae_of_all _ fun v hv => ih v hv.1.le)
          ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _)
      rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega : n + 1 ≠ 0),
        sub_zero] at hI
      rw [hD s hs, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      calc lam * ‖∫ v in (0 : ℝ)..s, (m v - (Real.exp (-(lam * v)) : ℂ) * c)‖
          ≤ lam * (2 * lam ^ n / n.factorial * (s ^ (n + 1) / (n + 1))) :=
            mul_le_mul_of_nonneg_left hI hlam
        _ = 2 * lam ^ (n + 1) / (n + 1).factorial * s ^ (n + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp
          ring
  have hlim : Tendsto (fun n : ℕ => 2 * lam ^ n / n.factorial * t ^ n) atTop (𝓝 0) := by
    have h0 := (FloorSemiring.tendsto_pow_div_factorial_atTop (lam * t)).const_mul 2
    rw [mul_zero] at h0
    refine h0.congr fun n => ?_
    rw [mul_pow]
    ring
  have hle := ge_of_tendsto' hlim fun n => hn n t ht
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-! ### Joint measurability of path functionals -/

theorem aestronglyMeasurable_pathTime {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {ν : Measure ℝ} [SFinite ν]
    {Y : Ω → ContinuousPath ℂ} (hY : AEMeasurable Y P) {L : Ω → ℝ} (hL : AEMeasurable L P)
    {Φ : ℂ × ℝ × ℝ → E} (hΦ : Measurable Φ) :
    AEStronglyMeasurable (fun p : Ω × ℝ => Φ (Y p.1 p.2.toNNReal, L p.1, p.2)) (P.prod ν) := by
  have hev : Measurable (Function.uncurry fun (t : ℝ≥0) (b : ContinuousPath ℂ) => b t) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (t : ℝ≥0) (b : ContinuousPath ℂ) => b t)
      (fun b => map_continuous b) (fun t => (continuous_eval_const t).measurable)
  have hYe : Measurable fun p : Ω × ℝ => hY.mk Y p.1 p.2.toNNReal :=
    hev.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk (hY.measurable_mk.comp measurable_fst))
  have hK : Measurable fun p : Ω × ℝ => Φ (hY.mk Y p.1 p.2.toNNReal, hL.mk L p.1, p.2) :=
    hΦ.comp (hYe.prodMk ((hL.measurable_mk.comp measurable_fst).prodMk measurable_snd))
  refine hK.aestronglyMeasurable.congr ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae
    (hY.ae_eq_mk.and hL.ae_eq_mk)] with p hp
  rw [← hp.1, ← hp.2]

theorem aestronglyMeasurable_pathAt {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {P : Measure Ω}
    {Y : Ω → ContinuousPath ℂ} (hY : AEMeasurable Y P) {L : Ω → ℝ} (hL : AEMeasurable L P)
    {Φ : ℂ × ℝ × ℝ → E} (hΦ : Measurable Φ) (s : ℝ) :
    AEStronglyMeasurable (fun ω => Φ (Y ω s.toNNReal, L ω, s)) P :=
  (hΦ.comp_aemeasurable (((continuous_eval_const s.toNNReal).measurable.comp_aemeasurable hY).prodMk
    (hL.prodMk aemeasurable_const))).aestronglyMeasurable

theorem integrable_intervalIntegral_path {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → ContinuousPath ℂ} (hY : AEMeasurable Y P)
    {L : Ω → ℝ} (hL : AEMeasurable L P) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω) {F : ℂ → E} (hF : Measurable F)
    (hFb : ∀ x, ‖F x‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => ∫ v in (0 : ℝ)..min t (L ω), F (Y ω v.toNNReal)) P := by
  have hΦ : Measurable fun q : ℂ × ℝ × ℝ => if q.2.2 ≤ q.2.1 then F q.1 else 0 :=
    Measurable.ite (measurableSet_le measurable_snd.snd measurable_snd.fst) (hF.comp measurable_fst)
      measurable_const
  have hJ := (aestronglyMeasurable_pathTime (ν := volume.restrict (Ioc (0 : ℝ) t)) hY hL
    hΦ).integral_prod_right'
  refine (integrable_const t).mono' (hJ.congr ?_) ?_
  · filter_upwards [hL0] with ω hω
    have hset : Ioc (0 : ℝ) t ∩ Iic (L ω) = Ioc 0 (min t (L ω)) := by
      ext v
      simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff, and_assoc]
    rw [intervalIntegral.integral_of_le (le_min ht hω), ← hset,
      ← setIntegral_indicator measurableSet_Iic]
    congr 1
  · filter_upwards [hL0] with ω hω
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun v _ => hFb _).trans ?_
    rw [one_mul, sub_zero, abs_of_nonneg (le_min ht hω)]
    exact min_le_left _ _

/-! ### The chart path, its exit clock and the decayed plane wave -/

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The chart path `Y = ψ(b)` run with the conformal clock and stopped at its exit time. -/
noncomputable def levyChartPath (U : Set ℂ) (ψ : C(ℂ, ℂ)) (b : ContinuousPath ℂ) : ContinuousPath ℂ :=
  chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)

/-- The exit time `L = A(τ_U)` of the chart path. -/
noncomputable def levyExitClock (U : Set ℂ) (ψ : C(ℂ, ℂ)) (b : ContinuousPath ℂ) : ℝ :=
  chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal

/-- The plane wave of a point decayed after the time `l`: `e^{i⟪ξ, x⟫} e^{-|ξ|² (v - l)₊ / 2}`. -/
noncomputable def decayWave (ξ : ℂ) (q : ℂ × ℝ × ℝ) : ℂ :=
  planeWave ξ q.1 * (Real.exp (-(‖ξ‖ ^ 2 * (((((q.2.2.toNNReal : ℝ≥0) : ℝ) - q.2.1).toNNReal : ℝ≥0) : ℝ) / 2)) : ℂ)

/-- The mean of the plane wave of the continued chart path at time `s`. -/
noncomputable def zWaveMean (U : Set ℂ) (ψ : C(ℂ, ℂ)) (ξ y : ℂ) (s : ℝ) : ℂ :=
  ∫ b, planeWave ξ (zPath U ψ b s.toNNReal) ∂planarBrownianMotion y

theorem continuous_decayWave (ξ : ℂ) : Continuous (decayWave ξ) :=
  ((continuous_planeWave ξ).comp continuous_fst).mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (((continuous_const.mul
      (NNReal.continuous_coe.comp (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp (continuous_real_toNNReal.comp continuous_snd.snd)).sub
          continuous_snd.fst)))).div_const 2).neg)))

theorem norm_decayWave_le (ξ : ℂ) (q : ℂ × ℝ × ℝ) : ‖decayWave ξ q‖ ≤ 1 := by
  rw [decayWave, norm_mul, norm_planeWave, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem aemeasurable_levyChartPath (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) : AEMeasurable (levyChartPath U ψ) (planarBrownianMotion y) :=
  (levyChart_integrable_aemeasurable hU hUb hψ hy).2

theorem aemeasurable_levyExitClock (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) : AEMeasurable (levyExitClock U ψ) (planarBrownianMotion y) := by
  refine ⟨fun b => ⨆ q : ℚ≥0, ((q : ℝ≥0) : ℝ) * U.indicator (fun _ => (1 : ℝ))
      (b ((chartStopOpt U ψ q b).untopD 0)), ?_, ?_⟩
  · exact Measurable.iSup fun q : ℚ≥0 => measurable_const.mul
      ((measurable_const.indicator hU.measurableSet).comp
        (MatedCRT.OptionalTime.measurable_eval_untopD (measurableSet_chartStopOpt_lt hU hψ q)))
  · filter_upwards [ae_mem_exitRateGoodSet_chart hU hUb hψ hy, ae_planarBrownianMotion_eval_zero y]
      with b hb hb0
    simp only [untopD_chartStopOpt hU hψ hb]
    exact (iSup_mul_indicator_eq_chartClock_exit hU hψ hb (by rw [hb0]; exact hy)).symm

theorem ae_levyExitClock_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) : ∀ᵐ b ∂planarBrownianMotion y, 0 ≤ levyExitClock U ψ b := by
  filter_upwards [ae_mem_exitRateGoodSet_chart hU hUb hψ hy] with b hb
  exact IsTimeChangeClock.clock_nonneg (isTimeChangeClock_chartClock_of_mem hU hψ hb) _

theorem ae_levyChartPath_stop (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) :
    ∀ᵐ b ∂planarBrownianMotion y, ∀ v : ℝ, levyExitClock U ψ b ≤ v →
      levyChartPath U ψ b v.toNNReal = levyChartPath U ψ b (levyExitClock U ψ b).toNNReal := by
  filter_upwards [ae_mem_exitRateGoodSet_chart hU hUb hψ hy] with b hb v hv
  have hL0 : 0 ≤ chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal :=
    IsTimeChangeClock.clock_nonneg (isTimeChangeClock_chartClock_of_mem hU hψ hb) _
  have hv' : chartClock U ψ b (ContinuousPath.exitTime U b).toNNReal ≤ v := hv
  have h1 := chartStopPath_lbmContinuousPath_min_exit hU hψ hb v.toNNReal
  rw [Real.coe_toNNReal _ (hL0.trans hv'), min_eq_right hv'] at h1
  exact h1.symm

theorem integrable_decayWave_prod (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) (ξ : ℂ) (s : ℝ) :
    Integrable (fun p : ContinuousPath ℂ × ℝ =>
      decayWave ξ (levyChartPath U ψ p.1 p.2.toNNReal, levyExitClock U ψ p.1, p.2))
      ((planarBrownianMotion y).prod (volume.restrict (Ioc (0 : ℝ) s))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) s)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact (integrable_const (1 : ℝ)).mono'
    (aestronglyMeasurable_pathTime (aemeasurable_levyChartPath hU hUb hψ hy)
      (aemeasurable_levyExitClock hU hUb hψ hy) (continuous_decayWave ξ).measurable)
    (ae_of_all _ fun p => norm_decayWave_le ξ _)

/-! ### The Dynkin identity for the plane wave -/

/-- **Dynkin's identity for the plane wave of the chart path**:
`E e^{i⟪ξ, Y_t⟫} - e^{i⟪ξ, ψ(y)⟫} = -(|ξ|²/2) E ∫_0^{t ∧ L} e^{i⟪ξ, Y_v⟫} dv`. -/
theorem chart_planeWave_dynkin (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) (ξ : ℂ) (t : ℝ≥0) :
    (∫ b, planeWave ξ (levyChartPath U ψ b t) ∂planarBrownianMotion y) - planeWave ξ (ψ y) =
      -((‖ξ‖ ^ 2 / 2 : ℝ) : ℂ) * ∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        planeWave ξ (levyChartPath U ψ b v.toNNReal)) ∂planarBrownianMotion y := by
  have hYm := aemeasurable_levyChartPath hU hUb hψ hy
  have hLm := aemeasurable_levyExitClock hU hUb hψ hy
  have hL0 := ae_levyExitClock_nonneg hU hUb hψ hy
  have hΔc : ∀ v, Δ (fun x => Real.cos (pairingCLM ξ x)) v = -‖ξ‖ ^ 2 * Real.cos (pairingCLM ξ v) :=
    fun v => by rw [laplacian_cos_clm, pairingCLM_one_sq_add_I_sq]
  have hΔs : ∀ v, Δ (fun x => Real.sin (pairingCLM ξ x)) v = -‖ξ‖ ^ 2 * Real.sin (pairingCLM ξ v) :=
    fun v => by rw [laplacian_sin_clm, pairingCLM_one_sq_add_I_sq]
  have hc : (∫ b, Real.cos (pairingCLM ξ (levyChartPath U ψ b t)) ∂planarBrownianMotion y) -
      Real.cos (pairingCLM ξ (ψ y)) =
      -(‖ξ‖ ^ 2 / 2) * ∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        Real.cos (pairingCLM ξ (levyChartPath U ψ b v.toNNReal))) ∂planarBrownianMotion y :=
    chart_fourier_dynkin hU hUb hψ (F := fun x => Real.cos (pairingCLM ξ x))
      (Real.contDiff_cos.comp (pairingCLM ξ).contDiff) hΔc (fun _ => Real.abs_cos_le_one _) hy t
  have hs : (∫ b, Real.sin (pairingCLM ξ (levyChartPath U ψ b t)) ∂planarBrownianMotion y) -
      Real.sin (pairingCLM ξ (ψ y)) =
      -(‖ξ‖ ^ 2 / 2) * ∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        Real.sin (pairingCLM ξ (levyChartPath U ψ b v.toNNReal))) ∂planarBrownianMotion y :=
    chart_fourier_dynkin hU hUb hψ (F := fun x => Real.sin (pairingCLM ξ x))
      (Real.contDiff_sin.comp (pairingCLM ξ).contDiff) hΔs (fun _ => Real.abs_sin_le_one _) hy t
  have hic : Integrable (fun b => Real.cos (pairingCLM ξ (levyChartPath U ψ b t))) (planarBrownianMotion y) :=
    (integrable_const (1 : ℝ)).mono'
      (((Real.continuous_cos.comp (pairingCLM ξ).continuous).measurable.comp_aemeasurable
        ((continuous_eval_const t).measurable.comp_aemeasurable hYm)).aestronglyMeasurable)
      (ae_of_all _ fun b => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have his : Integrable (fun b => Real.sin (pairingCLM ξ (levyChartPath U ψ b t))) (planarBrownianMotion y) :=
    (integrable_const (1 : ℝ)).mono'
      (((Real.continuous_sin.comp (pairingCLM ξ).continuous).measurable.comp_aemeasurable
        ((continuous_eval_const t).measurable.comp_aemeasurable hYm)).aestronglyMeasurable)
      (ae_of_all _ fun b => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hgc : Integrable (fun b => ∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
      Real.cos (pairingCLM ξ (levyChartPath U ψ b v.toNNReal))) (planarBrownianMotion y) :=
    integrable_intervalIntegral_path hYm hLm hL0 (F := fun x => Real.cos (pairingCLM ξ x))
      (Real.continuous_cos.comp (pairingCLM ξ).continuous).measurable
      (fun _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _) (NNReal.coe_nonneg t)
  have hgs : Integrable (fun b => ∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
      Real.sin (pairingCLM ξ (levyChartPath U ψ b v.toNNReal))) (planarBrownianMotion y) :=
    integrable_intervalIntegral_path hYm hLm hL0 (F := fun x => Real.sin (pairingCLM ξ x))
      (Real.continuous_sin.comp (pairingCLM ξ).continuous).measurable
      (fun _ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _) (NNReal.coe_nonneg t)
  have hpt : ∀ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
      planeWave ξ (levyChartPath U ψ b v.toNNReal)) =
      ((∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        Real.cos (pairingCLM ξ (levyChartPath U ψ b v.toNNReal)) : ℝ) : ℂ) +
      ((∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        Real.sin (pairingCLM ξ (levyChartPath U ψ b v.toNNReal)) : ℝ) : ℂ) * Complex.I := by
    intro b
    have hcY : Continuous fun v : ℝ => levyChartPath U ψ b v.toNNReal :=
      (ContinuousMap.continuous _).comp continuous_real_toNNReal
    have h1 : Continuous fun v : ℝ => (Real.cos (pairingCLM ξ (levyChartPath U ψ b v.toNNReal)) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_cos.comp ((pairingCLM ξ).continuous.comp hcY))
    have h2 : Continuous fun v : ℝ =>
        (Real.sin (pairingCLM ξ (levyChartPath U ψ b v.toNNReal)) : ℂ) * Complex.I :=
      (Complex.continuous_ofReal.comp (Real.continuous_sin.comp ((pairingCLM ξ).continuous.comp hcY))).mul
        continuous_const
    simp only [planeWave_eq_cos_add_sin]
    rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hE1 : (∫ b, planeWave ξ (levyChartPath U ψ b t) ∂planarBrownianMotion y) =
      ((∫ b, Real.cos (pairingCLM ξ (levyChartPath U ψ b t)) ∂planarBrownianMotion y : ℝ) : ℂ) +
      ((∫ b, Real.sin (pairingCLM ξ (levyChartPath U ψ b t)) ∂planarBrownianMotion y : ℝ) : ℂ) *
        Complex.I := by
    simp only [planeWave_eq_cos_add_sin]
    rw [integral_add hic.ofReal (his.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal]
  have hE2 : (∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
      planeWave ξ (levyChartPath U ψ b v.toNNReal)) ∂planarBrownianMotion y) =
      ((∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        Real.cos (pairingCLM ξ (levyChartPath U ψ b v.toNNReal))) ∂planarBrownianMotion y : ℝ) : ℂ) +
      ((∫ b, (∫ v in (0 : ℝ)..min (t : ℝ) (levyExitClock U ψ b),
        Real.sin (pairingCLM ξ (levyChartPath U ψ b v.toNNReal))) ∂planarBrownianMotion y : ℝ) : ℂ) *
        Complex.I := by
    simp only [hpt]
    rw [integral_add hgc.ofReal (hgs.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal]
  rw [hE1, hE2, planeWave_eq_cos_add_sin]
  have hc' := congrArg (fun r : ℝ => (r : ℂ)) hc
  have hs' := congrArg (fun r : ℝ => (r : ℂ)) hs
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] at hc' hs'
  linear_combination hc' + Complex.I * hs'

/-! ### The integral equation for the mean -/

theorem norm_zWaveMean_le (U : Set ℂ) (ψ : C(ℂ, ℂ)) (ξ y : ℂ) (s : ℝ) : ‖zWaveMean U ψ ξ y s‖ ≤ 1 := by
  unfold zWaveMean
  refine (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun b => (norm_planeWave ξ (zPath U ψ b s.toNNReal)).le)).trans ?_
  simp

theorem zWaveMean_eq_integral_decayWave (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {y : ℂ} (hy : y ∈ U) (ξ : ℂ) (s : ℝ) :
    zWaveMean U ψ ξ y s = ∫ b, decayWave ξ (levyChartPath U ψ b s.toNNReal, levyExitClock U ψ b, s)
      ∂planarBrownianMotion y :=
  integral_planeWave_zPath hU hUb hψ hy ξ s.toNNReal

theorem intervalIntegrable_zWaveMean (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {y : ℂ} (hy : y ∈ U) (ξ : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (zWaveMean U ψ ξ y) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs]
  exact (integrable_decayWave_prod hU hUb hψ hy ξ s).integral_prod_right.congr
    (ae_of_all _ fun v => (zWaveMean_eq_integral_decayWave hU hUb hψ hy ξ v).symm)

theorem integral_combine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G W WE K : Ω → ℂ} (lam : ℂ)
    (hG : Integrable G P) (hW : Integrable W P) (hWE : Integrable WE P)
    (hK : ∀ᵐ b ∂P, lam * K b = lam * G b + W b - WE b) :
    lam * ∫ b, K b ∂P = lam * ∫ b, G b ∂P + ∫ b, W b ∂P - ∫ b, WE b ∂P := by
  have hsum : Integrable (fun b => lam * G b + W b) P := (hG.const_mul lam).add hW
  rw [← integral_const_mul, integral_congr_ae hK, integral_sub hsum hWE, integral_add (hG.const_mul lam) hW,
    integral_const_mul]

/-- **The integral equation** `m(s) = e^{i⟪ξ, ψ(y)⟫} - (|ξ|²/2) ∫_0^s m`. -/
theorem zWaveMean_ode (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) (ξ : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    zWaveMean U ψ ξ y s = planeWave ξ (ψ y) -
      ((‖ξ‖ ^ 2 / 2 : ℝ) : ℂ) * ∫ v in (0 : ℝ)..s, zWaveMean U ψ ξ y v := by
  have hYm := aemeasurable_levyChartPath hU hUb hψ hy
  have hLm := aemeasurable_levyExitClock hU hUb hψ hy
  have hL0 := ae_levyExitClock_nonneg hU hUb hψ hy
  have hstop := ae_levyChartPath_stop hU hUb hψ hy
  have hF : ∫ v in (0 : ℝ)..s, zWaveMean U ψ ξ y v =
      ∫ b, (∫ v in (0 : ℝ)..s, decayWave ξ (levyChartPath U ψ b v.toNNReal, levyExitClock U ψ b, v))
        ∂planarBrownianMotion y := by
    simp only [intervalIntegral.integral_of_le hs]
    have hint := integrable_decayWave_prod hU hUb hψ hy ξ s
    refine Eq.trans ?_ ((integral_prod_symm _ hint).symm.trans (integral_prod _ hint))
    exact integral_congr_ae (ae_of_all _ fun v => zWaveMean_eq_integral_decayWave hU hUb hψ hy ξ v)
  have hpath : ∀ᵐ b ∂planarBrownianMotion y,
      ((‖ξ‖ ^ 2 / 2 : ℝ) : ℂ) *
          (∫ v in (0 : ℝ)..s, decayWave ξ (levyChartPath U ψ b v.toNNReal, levyExitClock U ψ b, v)) =
        ((‖ξ‖ ^ 2 / 2 : ℝ) : ℂ) * (∫ v in (0 : ℝ)..min s (levyExitClock U ψ b),
          planeWave ξ (levyChartPath U ψ b v.toNNReal)) +
          planeWave ξ (levyChartPath U ψ b s.toNNReal) -
          decayWave ξ (levyChartPath U ψ b s.toNNReal, levyExitClock U ψ b, s) := by
    filter_upwards [hL0, hstop] with b hb0 hbs
    exact decay_identity (w := fun v => planeWave ξ (levyChartPath U ψ b v.toNNReal)) (a := ‖ξ‖ ^ 2)
      ((continuous_planeWave ξ).comp ((ContinuousMap.continuous _).comp continuous_real_toNNReal))
      hb0 hs (fun v hv => congrArg (planeWave ξ) (hbs v hv))
  have hg : Integrable (fun b => ∫ v in (0 : ℝ)..min s (levyExitClock U ψ b),
      planeWave ξ (levyChartPath U ψ b v.toNNReal)) (planarBrownianMotion y) :=
    integrable_intervalIntegral_path hYm hLm hL0 (continuous_planeWave ξ).measurable
      (fun x => (norm_planeWave ξ x).le) hs
  have hw : Integrable (fun b => planeWave ξ (levyChartPath U ψ b s.toNNReal)) (planarBrownianMotion y) :=
    (integrable_const (1 : ℝ)).mono'
      (aestronglyMeasurable_pathAt hYm hLm (Φ := fun q : ℂ × ℝ × ℝ => planeWave ξ q.1)
        ((continuous_planeWave ξ).comp continuous_fst).measurable s)
      (ae_of_all _ fun b => (norm_planeWave ξ _).le)
  have hwe : Integrable (fun b => decayWave ξ (levyChartPath U ψ b s.toNNReal, levyExitClock U ψ b, s))
      (planarBrownianMotion y) :=
    (integrable_const (1 : ℝ)).mono' (aestronglyMeasurable_pathAt hYm hLm (continuous_decayWave ξ).measurable s)
      (ae_of_all _ fun b => norm_decayWave_le ξ _)
  have hC := integral_combine ((‖ξ‖ ^ 2 / 2 : ℝ) : ℂ) hg hw hwe hpath
  have hA := chart_planeWave_dynkin hU hUb hψ hy ξ s.toNNReal
  rw [Real.coe_toNNReal s hs] at hA
  have hP2 := zWaveMean_eq_integral_decayWave hU hUb hψ hy ξ s
  linear_combination hP2 + ((‖ξ‖ ^ 2 / 2 : ℝ) : ℂ) * hF + hC + hA

/-- **The characteristic function of the continued chart path**:
`E e^{i⟪ξ, Z_t⟫} = e^{-|ξ|² t / 2} e^{i⟪ξ, ψ(y)⟫}` for every `y ∈ U`. -/
theorem integral_planeWave_zPath_eq_exp (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {y : ℂ} (hy : y ∈ U) (ξ : ℂ) (t : ℝ≥0) :
    ∫ b, planeWave ξ (zPath U ψ b t) ∂planarBrownianMotion y =
      (Real.exp (-(‖ξ‖ ^ 2 / 2 * (t : ℝ))) : ℂ) * planeWave ξ (ψ y) := by
  have h := eq_exp_mul_of_integral_eq (m := zWaveMean U ψ ξ y) (c := planeWave ξ (ψ y))
    (lam := ‖ξ‖ ^ 2 / 2) (by positivity) (fun s _ => norm_zWaveMean_le U ψ ξ y s) (norm_planeWave ξ _).le
    (fun s hs => intervalIntegrable_zWaveMean hU hUb hψ hy ξ hs)
    (fun s hs => zWaveMean_ode hU hUb hψ hy ξ hs) (NNReal.coe_nonneg t)
  simpa only [zWaveMean, Real.toNNReal_coe] using h


end CharacteristicFunction

section Increments


variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

theorem planeWave_zero_right (ξ : ℂ) : planeWave ξ 0 = 1 := by
  simp [planeWave]

/-! ### The continued chart path along a path with a time-change clock -/

/-- `Z_t = ψ(b(A⁻¹t ∧ τ)) + b(A⁻¹t) - b(A⁻¹t ∧ τ)` when the conformal clock of `b` is a time-change clock and `b`
leaves `U` at the time `τ`. -/
theorem zPath_apply_eq {b : ContinuousPath ℂ} (hA : IsTimeChangeClock (chartClock U ψ b)) {τ : ℝ≥0}
    (hτ : ContinuousPath.exitTime U b = τ) (t : ℝ≥0) :
    zPath U ψ b t = ψ (b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) t) τ)) +
      (b (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) t) -
        b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) t) τ)) := by
  rw [zPath_apply, chartStopPath_lbmContinuousPath_apply hA hτ, stopAtExitTime_lbmContinuousPath_apply hA hτ]
  congr 1
  rw [lbmContinuousPath_of_isTimeChangeClock hA]
  rfl

theorem chartClockInverseOpt_eq_of_isTimeChangeClock {b : ContinuousPath ℂ}
    (hA : IsTimeChangeClock (chartClock U ψ b)) (s : ℝ≥0) :
    chartClockInverseOpt U ψ s b =
      ((_root_.HarmonicBalls.clockInverse (chartClock U ψ b) s : ℝ≥0) : WithTop ℝ≥0) := by
  set c := _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s with hcdef
  have hAc : chartClock U ψ b c = s := IsTimeChangeClock.apply_clockInverse_eq hA s
  have hiff : ∀ q : ℝ≥0, s < (chartClock U ψ b q).toNNReal ↔ c < q := fun q => by
    rw [Real.lt_toNNReal_iff_coe_lt, ← hAc]
    exact hA.strictMono.lt_iff_lt
  simp only [chartClockInverseOpt, rationalClockInverse, chartClockNN]
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
    induction d with
    | top => exact le_top
    | coe d =>
      rw [WithTop.coe_lt_coe] at hd
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal hd
      exact (iInf₂_le q ((hiff q).2 hq1)).trans (WithTop.coe_le_coe.2 hq2.le)
  · exact le_iInf₂ fun q hq => WithTop.coe_le_coe.2 ((hiff q).1 hq).le

theorem untopD_chartClockInverseOpt {b : ContinuousPath ℂ} (hA : IsTimeChangeClock (chartClock U ψ b))
    (u : ℝ≥0) :
    (chartClockInverseOpt U ψ u b).untopD 0 = _root_.HarmonicBalls.clockInverse (chartClock U ψ b) u := by
  rw [chartClockInverseOpt_eq_of_isTimeChangeClock hA u, WithTop.untopD_coe]

theorem untopD_chartStopOpt_of_isTimeChangeClock {b : ContinuousPath ℂ}
    (hA : IsTimeChangeClock (chartClock U ψ b)) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ) (u : ℝ≥0) :
    (chartStopOpt U ψ u b).untopD 0 = min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) u) τ :=
  untopD_min_coe (chartClockInverseOpt_eq_of_isTimeChangeClock hA u) hτ

theorem chartClockInverseOpt_mono (U : Set ℂ) (ψ : C(ℂ, ℂ)) {u s : ℝ≥0} (h : u ≤ s) (b : ContinuousPath ℂ) :
    chartClockInverseOpt U ψ u b ≤ chartClockInverseOpt U ψ s b := by
  simp only [chartClockInverseOpt, rationalClockInverse]
  exact le_iInf₂ fun q hq => iInf₂_le q (h.trans_lt hq)

/-! ### A Borel version of the coordinates of the continued chart path -/

/-- `Z_t` read off the path at the optional times `A⁻¹(t)` and `A⁻¹(t) ∧ τ_U`. -/
noncomputable def zEval (U : Set ℂ) (ψ : C(ℂ, ℂ)) (t : ℝ≥0) (b : ContinuousPath ℂ) : ℂ :=
  ψ (b ((chartStopOpt U ψ t b).untopD 0)) +
    (b ((chartClockInverseOpt U ψ t b).untopD 0) - b ((chartStopOpt U ψ t b).untopD 0))

theorem measurable_zEval (hU : IsOpen U) (hψ : IsInverseChart U z ψ) (t : ℝ≥0) :
    Measurable (zEval U ψ t) :=
  (ψ.continuous.measurable.comp (MatedCRT.OptionalTime.measurable_eval_untopD
    (measurableSet_chartStopOpt_lt hU hψ t))).add
    ((MatedCRT.OptionalTime.measurable_eval_untopD (measurableSet_chartClockInverseOpt_lt hU hψ t)).sub
      (MatedCRT.OptionalTime.measurable_eval_untopD (measurableSet_chartStopOpt_lt hU hψ t)))

theorem zEval_eq_zPath {b : ContinuousPath ℂ} (hA : IsTimeChangeClock (chartClock U ψ b)) {τ : ℝ≥0}
    (hτ : ContinuousPath.exitTime U b = τ) (t : ℝ≥0) : zEval U ψ t b = zPath U ψ b t := by
  rw [zEval, untopD_chartStopOpt_of_isTimeChangeClock hA hτ, untopD_chartClockInverseOpt hA,
    zPath_apply_eq hA hτ]

/-! ### The conformal clock restarted before the exit time -/

theorem chartRate_shift {b : ContinuousPath ℂ} {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ContinuousPath.exitTime U b)
    {r : ℝ} (hr : 0 ≤ r) :
    chartRate U ψ (ContinuousPath.shift T b) r = chartRate U ψ b ((T : ℝ) + r) := by
  have hadd := ContinuousPath.exitTime_shift_add U b T hT
  have hTr : ((T : ℝ) + r).toNNReal = T + r.toNNReal := by
    rw [Real.toNNReal_add (NNReal.coe_nonneg T) hr, Real.toNNReal_coe]
  have hiff : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U (ContinuousPath.shift T b) ↔
      ((((T : ℝ) + r).toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U b := by
    rw [hTr, ← hadd, ENNReal.coe_add, add_comm (T : ℝ≥0∞)]
    exact (ENNReal.add_lt_add_iff_right ENNReal.coe_ne_top).symm
  by_cases h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U (ContinuousPath.shift T b)
  · rw [chartRate_of_lt_exitTime h, chartRate_of_lt_exitTime (hiff.1 h), ContinuousPath.shift_apply, hTr]
  · rw [chartRate_of_exitTime_le (not_lt.1 h), chartRate_of_exitTime_le (not_lt.1 (mt hiff.2 h))]

/-- **Additivity of the conformal clock** at a time before the exit time. -/
theorem chartClock_shift (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ContinuousPath.exitTime U b) (u : ℝ≥0) :
    chartClock U ψ (ContinuousPath.shift T b) u = chartClock U ψ b (T + u) - chartClock U ψ b T := by
  have h0 := intervalIntegrable_exitRate_of_mem_exitRateGoodSet hU (continuousOn_chartRateDensity hU hψ) hb
  have hint : ∀ a c : ℝ, IntervalIntegrable (chartRate U ψ b) volume a c := fun a c =>
    (h0 a).symm.trans (h0 c)
  have hcongr : EqOn (chartRate U ψ (ContinuousPath.shift T b)) (fun r => chartRate U ψ b ((T : ℝ) + r))
      (uIcc 0 (u : ℝ)) := by
    intro r hr
    rw [uIcc_of_le (NNReal.coe_nonneg u)] at hr
    exact chartRate_shift hT hr.1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T ((T + u : ℝ≥0) : ℝ))
  simp only [chartClock]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_comp_add_left, add_zero, ← hsplit,
    NNReal.coe_add]
  ring

theorem isTimeChangeClock_chartClock_shift (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ContinuousPath.exitTime U b) :
    IsTimeChangeClock (chartClock U ψ (ContinuousPath.shift T b)) :=
  FirstPass.Derived.isTimeChangeClock_shift (F := chartClock U ψ) (isTimeChangeClock_chartClock_of_mem hU hψ hb)
    (chartClock_shift hU hψ hb hT)

theorem exitTime_shift_eq {b : ContinuousPath ℂ} {τ T : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hT : T < τ) : ContinuousPath.exitTime U (ContinuousPath.shift T b) = ((τ - T : ℝ≥0) : ℝ≥0∞) := by
  have h := ContinuousPath.exitTime_shift_add U b T (by rw [hτ]; exact ENNReal.coe_lt_coe.2 hT)
  rw [hτ] at h
  rw [ENNReal.coe_sub, ← h, ENNReal.add_sub_cancel_right ENNReal.coe_ne_top]

/-! ### The restart identities for the continued chart path -/

/-- Before the exit time, the continued chart path after the clock value `s` is the continued chart path of the
Brownian path shifted by `A⁻¹(s)`. -/
theorem zPath_shift_clockInverse (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) {s T : ℝ≥0}
    (hT : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s = T)
    (hs : (T : ℝ≥0∞) < ContinuousPath.exitTime U b) (σ : ℝ≥0) :
    zPath U ψ (ContinuousPath.shift T b) σ = zPath U ψ b (s + σ) := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  have hAT : chartClock U ψ b T = s := by
    rw [← hT]
    exact IsTimeChangeClock.apply_clockInverse_eq hA s
  obtain ⟨τ, hτe⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
    ⟨_, (ENNReal.coe_toNNReal hb.1.ne).symm⟩
  have hTτ : T < τ := by
    rw [hτe] at hs
    exact ENNReal.coe_lt_coe.1 hs
  have hA' := isTimeChangeClock_chartClock_shift hU hψ hb hs
  have hτ' := exitTime_shift_eq hτe hTτ
  have hinv : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) (s + σ) =
      T + _root_.HarmonicBalls.clockInverse (chartClock U ψ (ContinuousPath.shift T b)) σ := by
    rw [funext (chartClock_shift hU hψ hb hs), ← FirstPass.Derived.clockInverse_clockValue_add hA, hAT,
      Real.toNNReal_coe]
  have hmin : ∀ x : ℝ≥0, T + min x (τ - T) = min (T + x) τ := by
    intro x
    rcases le_total x (τ - T) with h | h
    · rw [min_eq_left h, min_eq_left ((le_tsub_iff_left hTτ.le).1 h)]
    · rw [min_eq_right h, add_tsub_cancel_of_le hTτ.le, min_eq_right (tsub_le_iff_left.1 h)]
  rw [zPath_apply_eq hA' hτ', zPath_apply_eq hA hτe, hinv]
  simp only [ContinuousPath.shift_apply, hmin]

/-- Before the exit time, `Z` at the clock value `s` is the chart image of `b(A⁻¹(s))`. -/
theorem zPath_eq_of_lt_exitTime (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) {s T : ℝ≥0}
    (hT : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s = T)
    (hs : (T : ℝ≥0∞) < ContinuousPath.exitTime U b) : zPath U ψ b s = ψ (b T) := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  obtain ⟨τ, hτe⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
    ⟨_, (ENNReal.coe_toNNReal hb.1.ne).symm⟩
  have hTτ : T ≤ τ := by
    rw [hτe] at hs
    exact (ENNReal.coe_lt_coe.1 hs).le
  rw [zPath_apply_eq hA hτe, hT, min_eq_left hTτ, sub_self, add_zero]

/-- After the exit time, the increments of `Z` after the clock value `s` are the increments of the Brownian path
after `A⁻¹(s)`. -/
theorem zPath_add_sub_of_exitTime_le (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) {s T : ℝ≥0}
    (hT : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s = T)
    (hs : ContinuousPath.exitTime U b ≤ (T : ℝ≥0∞)) (σ : ℝ≥0) :
    zPath U ψ b (s + σ) - zPath U ψ b s = ContinuousPath.shift T b σ - ContinuousPath.shift T b 0 := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  have hAT : chartClock U ψ b T = s := by
    rw [← hT]
    exact IsTimeChangeClock.apply_clockInverse_eq hA s
  obtain ⟨τ, hτe⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
    ⟨_, (ENNReal.coe_toNNReal hb.1.ne).symm⟩
  have hτn : (ContinuousPath.exitTime U b).toNNReal = τ := by rw [hτe, ENNReal.toNNReal_coe]
  have hτT : τ ≤ T := by
    rw [hτe] at hs
    exact ENNReal.coe_le_coe.1 hs
  have hinv : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) (s + σ) = T + σ := by
    refine FirstPass.Derived.clockInverse_eq_of_apply_eq hA ?_
    have h3 := chartClock_exit_add hU hψ hb (T - τ + σ)
    have h4 := chartClock_exit_add hU hψ hb (T - τ)
    rw [hτn, add_tsub_cancel_of_le hτT, hAT] at h4
    rw [hτn, ← add_assoc, add_tsub_cancel_of_le hτT] at h3
    rw [h3, NNReal.coe_add, NNReal.coe_add]
    linarith
  rw [zPath_apply_eq hA hτe, zPath_apply_eq hA hτe, hinv, hT, min_eq_right (hτT.trans le_self_add),
    min_eq_right hτT]
  simp only [ContinuousPath.shift_apply, add_zero]
  ring

/-! ### The past of the optional time `A⁻¹(s)` and the functional of the future -/

/-- The optional times `A⁻¹(u ∧ s)` (`true`) and `A⁻¹(u ∧ s) ∧ τ_U` (`false`), all below `A⁻¹(s)`. -/
noncomputable def incTimes (U : Set ℂ) (ψ : C(ℂ, ℂ)) (s : ℝ≥0) (j : Bool × ℝ≥0) :
    ContinuousPath ℂ → WithTop ℝ≥0 :=
  cond j.1 (chartClockInverseOpt U ψ (min j.2 s)) (chartStopOpt U ψ (min j.2 s))

theorem measurableSet_incTimes_lt (hU : IsOpen U) (hψ : IsInverseChart U z ψ) (s : ℝ≥0)
    (j : Bool × ℝ≥0) (u : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) u] {b | incTimes U ψ s j b < u} := by
  rcases j with ⟨_ | _, v⟩
  · exact measurableSet_chartStopOpt_lt hU hψ (min v s) u
  · exact measurableSet_chartClockInverseOpt_lt hU hψ (min v s) u

theorem incTimes_le (U : Set ℂ) (ψ : C(ℂ, ℂ)) (s : ℝ≥0) (j : Bool × ℝ≥0) (b : ContinuousPath ℂ) :
    incTimes U ψ s j b ≤ chartClockInverseOpt U ψ s b := by
  rcases j with ⟨_ | _, v⟩
  · show min (chartClockInverseOpt U ψ (min v s) b) (chartExitOpt U b) ≤ chartClockInverseOpt U ψ s b
    exact (min_le_left _ _).trans (chartClockInverseOpt_mono U ψ (min_le_right v s) b)
  · exact chartClockInverseOpt_mono U ψ (min_le_right v s) b

/-- The past variable: the Fourier phase `Σ_{u ∈ I} ⟪η_u, Z_u⟫` and the position at `A⁻¹(s) ∧ τ_U`. -/
noncomputable def incPast (ψ : C(ℂ, ℂ)) (s : ℝ≥0) (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ) (v : Bool × ℝ≥0 → ℂ) :
    ℝ × ℂ :=
  (∑ u ∈ I, pairingCLM (η u) (ψ (v (false, u)) + (v (true, u) - v (false, u))), v (false, s))

theorem measurable_incPast (ψ : C(ℂ, ℂ)) (s : ℝ≥0) (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ) :
    Measurable (incPast ψ s I η) :=
  (Finset.measurable_sum I fun u _ => (pairingCLM (η u)).continuous.measurable.comp
    ((ψ.continuous.measurable.comp (measurable_pi_apply (false, u))).add
      ((measurable_pi_apply (true, u)).sub (measurable_pi_apply (false, u))))).prodMk
    (measurable_pi_apply (false, s))

open Classical in
/-- The functional of the past variable and the shifted path: `e^{i⟪η, Z⟫}` times `e^{i⟪ξ, Z'_t - ψ(b'_0)⟫}` before the
exit time and `e^{i⟪ξ, b'_t - b'_0⟫}` after it. -/
noncomputable def incWave (U : Set ℂ) (ψ : C(ℂ, ℂ)) (ξ : ℂ) (t : ℝ≥0) (p : (ℝ × ℂ) × ContinuousPath ℂ) : ℂ :=
  Complex.exp ((p.1.1 : ℂ) * Complex.I) *
    if p.1.2 ∈ U then planeWave ξ (zEval U ψ t p.2 - ψ (p.2 0)) else planeWave ξ (p.2 t - p.2 0)

theorem measurable_incWave (hU : IsOpen U) (hψ : IsInverseChart U z ψ) (ξ : ℂ) (t : ℝ≥0) :
    Measurable (incWave U ψ ξ t) := by
  classical
  have h1 : Measurable fun p : (ℝ × ℂ) × ContinuousPath ℂ => Complex.exp ((p.1.1 : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp measurable_fst.fst).mul_const _)
  have h2 : Measurable fun p : (ℝ × ℂ) × ContinuousPath ℂ => planeWave ξ (zEval U ψ t p.2 - ψ (p.2 0)) :=
    (continuous_planeWave ξ).measurable.comp (((measurable_zEval hU hψ t).comp measurable_snd).sub
      (ψ.continuous.measurable.comp ((continuous_eval_const 0).measurable.comp measurable_snd)))
  have h3 : Measurable fun p : (ℝ × ℂ) × ContinuousPath ℂ => planeWave ξ (p.2 t - p.2 0) :=
    (continuous_planeWave ξ).measurable.comp (((continuous_eval_const t).measurable.comp measurable_snd).sub
      ((continuous_eval_const 0).measurable.comp measurable_snd))
  have h4 : MeasurableSet {p : (ℝ × ℂ) × ContinuousPath ℂ | p.1.2 ∈ U} :=
    hU.measurableSet.preimage measurable_fst.snd
  have h5 : Measurable fun p : (ℝ × ℂ) × ContinuousPath ℂ =>
      if p.1.2 ∈ U then planeWave ξ (zEval U ψ t p.2 - ψ (p.2 0)) else planeWave ξ (p.2 t - p.2 0) :=
    Measurable.ite h4 h2 h3
  exact h1.mul h5

theorem norm_incWave_le (U : Set ℂ) (ψ : C(ℂ, ℂ)) (ξ : ℂ) (t : ℝ≥0) (p : (ℝ × ℂ) × ContinuousPath ℂ) :
    ‖incWave U ψ ξ t p‖ ≤ 1 := by
  rw [incWave, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  split_ifs
  · exact (norm_planeWave ξ _).le
  · exact (norm_planeWave ξ _).le

/-- The plane wave of the increment `Z_t - ψ(x)` has the Gaussian mean, for `x ∈ U`. -/
theorem integral_planeWave_zEval_sub (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {x : ℂ} (hx : x ∈ U) (ξ : ℂ) (t : ℝ≥0) :
    ∫ ω, planeWave ξ (zEval U ψ t ω - ψ (ω 0)) ∂planarBrownianMotion x =
      (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) := by
  have h3 := integral_planeWave_zPath_eq_exp hU hUb hψ hx ξ t
  calc ∫ ω, planeWave ξ (zEval U ψ t ω - ψ (ω 0)) ∂planarBrownianMotion x
      = ∫ ω, planeWave ξ (zPath U ψ ω t) * planeWave ξ (-ψ x) ∂planarBrownianMotion x := by
        refine integral_congr_ae ?_
        filter_upwards [ae_mem_exitRateGoodSet_chart hU hUb hψ hx, ae_planarBrownianMotion_eval_zero x]
          with ω hω hω0
        rw [zEval_eq_zPath (isTimeChangeClock_chartClock_of_mem hU hψ hω) (ENNReal.coe_toNNReal hω.1.ne).symm,
          hω0, sub_eq_add_neg, planeWave_add]
    _ = _ := by
        rw [integral_mul_const, h3, mul_assoc, ← planeWave_add, add_neg_cancel, planeWave_zero_right, mul_one,
          show -(‖ξ‖ ^ 2 / 2 * (t : ℝ)) = -(‖ξ‖ ^ 2 * (t : ℝ) / 2) by ring]

/-! ### Standard planar Brownian increments -/

/-- **The increments of the continued chart path** (strong Markov property at `A⁻¹(s)`). -/
theorem integral_pathWave_mul_planeWave_zPath (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {y : ℂ} (hy : y ∈ U) (s t : ℝ≥0) (ξ : ℂ) (I : Finset ℝ≥0) (η : ℝ≥0 → ℂ)
    (hI : ∀ u ∈ I, u ≤ s) :
    ∫ b, pathWave I η (zPath U ψ b) * planeWave ξ (zPath U ψ b (s + t) - zPath U ψ b s)
        ∂planarBrownianMotion y =
      (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) * ∫ b, pathWave I η (zPath U ψ b) ∂planarBrownianMotion y := by
  have hφm : Measurable fun (b : ContinuousPath ℂ) (j : Bool × ℝ≥0) => b ((incTimes U ψ s j b).untopD 0) :=
    measurable_pi_iff.mpr fun j =>
      MatedCRT.OptionalTime.measurable_eval_untopD (measurableSet_incTimes_lt hU hψ s j)
  have hV : ∀ B : Set (ℝ × ℂ), MeasurableSet B → ∀ u : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) u]
        ((fun b => incPast ψ s I η fun j => b ((incTimes U ψ s j b).untopD 0)) ⁻¹' B ∩
          {b | chartClockInverseOpt U ψ s b < u}) :=
    fun B hB u => MatedCRT.OptionalTime.measurableSet_pi_eval_untopD_inter_lt
      (measurableSet_incTimes_lt hU hψ s) (measurableSet_chartClockInverseOpt_lt hU hψ s)
      (incTimes_le U ψ s) (measurable_incPast ψ s I η hB) u
  have hSM := integral_planarLaw_shift_optionalTime_param y (chartClockInverseOpt U ψ s)
    (measurableSet_chartClockInverseOpt_lt hU hψ s)
    (fun b => incPast ψ s I η fun j => b ((incTimes U ψ s j b).untopD 0))
    ((measurable_incPast ψ s I η).comp hφm) hV (measurable_incWave hU hψ ξ t) (norm_incWave_le U ψ ξ t)
  have hgood := ae_mem_exitRateGoodSet_chart hU hUb hψ hy
  have h0 := ae_planarBrownianMotion_eval_zero y
  have hfin : ∀ᵐ b ∂planarLaw y, b ∈ {b | chartClockInverseOpt U ψ s b < ⊤} := by
    filter_upwards [hgood] with b hb
    show chartClockInverseOpt U ψ s b < ⊤
    rw [chartClockInverseOpt_eq hU hψ hb s]
    exact WithTop.coe_lt_top _
  rw [Measure.restrict_eq_self_of_ae_mem hfin] at hSM
  simp only [planarLaw] at hSM
  have hstep : ∀ b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2),
      incPast ψ s I η (fun j => b ((incTimes U ψ s j b).untopD 0)) =
        (∑ u ∈ I, pairingCLM (η u) (zPath U ψ b u),
          b (min (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) s)
            (ContinuousPath.exitTime U b).toNNReal)) := by
    intro b hb
    have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
    have hτe : ContinuousPath.exitTime U b = ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal hb.1.ne).symm
    simp only [incPast, incTimes, Bool.cond_true, Bool.cond_false, min_self]
    rw [untopD_chartStopOpt_of_isTimeChangeClock hA hτe s]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [min_eq_left (hI u hu), zPath_apply_eq hA hτe, untopD_chartStopOpt_of_isTimeChangeClock hA hτe u,
      untopD_chartClockInverseOpt hA u]
  have hlhs : ∀ b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2), b 0 = y →
      pathWave I η (zPath U ψ b) * planeWave ξ (zPath U ψ b (s + t) - zPath U ψ b s) =
        incWave U ψ ξ t (incPast ψ s I η (fun j => b ((incTimes U ψ s j b).untopD 0)),
          ContinuousPath.shift ((chartClockInverseOpt U ψ s b).untopD 0) b) := by
    intro b hb hb0
    have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
    obtain ⟨T, hT⟩ : ∃ T, _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s = T := ⟨_, rfl⟩
    obtain ⟨τ, hτe⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
      ⟨_, (ENNReal.coe_toNNReal hb.1.ne).symm⟩
    have hτn : (ContinuousPath.exitTime U b).toNNReal = τ := by rw [hτe, ENNReal.toNNReal_coe]
    rw [hstep b hb, untopD_chartClockInverseOpt hA s, hT, hτn]
    simp only [incWave]
    refine congrArg₂ (· * ·) rfl ?_
    by_cases hTτ : T < τ
    · have hTlt : (T : ℝ≥0∞) < ContinuousPath.exitTime U b := by
        rw [hτe]
        exact ENNReal.coe_lt_coe.2 hTτ
      have hmem : b (min T τ) ∈ U := by
        rw [min_eq_left hTτ.le]
        exact ContinuousPath.mem_of_lt_exitTime U b T hTlt
      have hA' := isTimeChangeClock_chartClock_shift hU hψ hb hTlt
      have hτ' := exitTime_shift_eq hτe hTτ
      rw [ite_eq_left hmem, zEval_eq_zPath hA' hτ', zPath_shift_clockInverse hU hψ hb hT hTlt,
        ContinuousPath.shift_apply, add_zero, ← zPath_eq_of_lt_exitTime hU hψ hb hT hTlt]
    · have hτT : τ ≤ T := not_lt.1 hTτ
      have hnot : b (min T τ) ∉ U := by
        rw [min_eq_right hτT, ← hτn]
        have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU b (by rw [hb0]; exact hy) hb.1.ne
        rw [hU.frontier_eq] at hfr
        exact hfr.2
      rw [ite_eq_right hnot, zPath_add_sub_of_exitTime_le hU hψ hb hT
        (by rw [hτe]; exact ENNReal.coe_le_coe.2 hτT)]
  have hrhs : ∀ b ∈ exitRateGoodSet U (fun v => ‖deriv ψ v‖ ^ 2), b 0 = y →
      ∫ ω', incWave U ψ ξ t (incPast ψ s I η (fun j => b ((incTimes U ψ s j b).untopD 0)), ω')
          ∂planarBrownianMotion (b ((chartClockInverseOpt U ψ s b).untopD 0)) =
        pathWave I η (zPath U ψ b) * (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ) := by
    intro b hb hb0
    have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
    obtain ⟨T, hT⟩ : ∃ T, _root_.HarmonicBalls.clockInverse (chartClock U ψ b) s = T := ⟨_, rfl⟩
    obtain ⟨τ, hτe⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
      ⟨_, (ENNReal.coe_toNNReal hb.1.ne).symm⟩
    have hτn : (ContinuousPath.exitTime U b).toNNReal = τ := by rw [hτe, ENNReal.toNNReal_coe]
    rw [hstep b hb, untopD_chartClockInverseOpt hA s, hT, hτn]
    simp only [incWave]
    rw [integral_const_mul]
    refine congrArg₂ (· * ·) rfl ?_
    by_cases hTτ : T < τ
    · have hTlt : (T : ℝ≥0∞) < ContinuousPath.exitTime U b := by
        rw [hτe]
        exact ENNReal.coe_lt_coe.2 hTτ
      have hbT : b T ∈ U := ContinuousPath.mem_of_lt_exitTime U b T hTlt
      have hmem : b (min T τ) ∈ U := by
        rw [min_eq_left hTτ.le]
        exact hbT
      simp only [hmem, ↓reduceIte]
      exact integral_planeWave_zEval_sub hU hUb hψ hbT ξ t
    · have hτT : τ ≤ T := not_lt.1 hTτ
      have hnot : b (min T τ) ∉ U := by
        rw [min_eq_right hτT, ← hτn]
        have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU b (by rw [hb0]; exact hy) hb.1.ne
        rw [hU.frontier_eq] at hfr
        exact hfr.2
      simp only [hnot, ↓reduceIte]
      exact integral_planeWave_increment ξ (b T) t
  calc ∫ b, pathWave I η (zPath U ψ b) * planeWave ξ (zPath U ψ b (s + t) - zPath U ψ b s)
        ∂planarBrownianMotion y
      = ∫ b, incWave U ψ ξ t (incPast ψ s I η (fun j => b ((incTimes U ψ s j b).untopD 0)),
          ContinuousPath.shift ((chartClockInverseOpt U ψ s b).untopD 0) b) ∂planarBrownianMotion y := by
        refine integral_congr_ae ?_
        filter_upwards [hgood, h0] with b hb hb0
        exact hlhs b hb hb0
    _ = ∫ b, ∫ ω', incWave U ψ ξ t (incPast ψ s I η (fun j => b ((incTimes U ψ s j b).untopD 0)), ω')
          ∂planarBrownianMotion (b ((chartClockInverseOpt U ψ s b).untopD 0)) ∂planarBrownianMotion y := hSM
    _ = ∫ b, pathWave I η (zPath U ψ b) * (Real.exp (-(‖ξ‖ ^ 2 * (t : ℝ) / 2)) : ℂ)
          ∂planarBrownianMotion y := by
        refine integral_congr_ae ?_
        filter_upwards [hgood, h0] with b hb hb0
        exact hrhs b hb hb0
    _ = _ := (integral_mul_const _ _).trans (mul_comm _ _)

theorem aemeasurable_zPath (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) : AEMeasurable (zPath U ψ) (planarBrownianMotion y) := by
  have hF : Measurable fun x : ContinuousPath ℂ =>
      (⟨fun t => chartStopPath U ψ x t + (x t - stopAtExitTime U x t),
        (ContinuousMap.continuous _).add ((ContinuousMap.continuous _).sub (ContinuousMap.continuous _))⟩ :
          ContinuousPath ℂ) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((continuous_eval_const t).measurable.comp (measurable_chartStopPath U hU ψ)).add
      ((continuous_eval_const t).measurable.sub
        ((continuous_eval_const t).measurable.comp (measurable_stopAtExitTime U hU)))
  exact hF.comp_aemeasurable (aemeasurable_lbmContinuousPath_exitRateClock hU
    (continuousOn_chartRateDensity hU hψ) (fun v hv => chartRateDensity_pos hU hψ hv)
    (ae_mem_exitRateGoodSet_chart hU hUb hψ hy))

/-- **The continued chart path has standard planar Brownian increments.** -/
theorem hasBrownianIncrements_map_zPath (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hψ : IsInverseChart U z ψ) {y : ℂ} (hy : y ∈ U) :
    HasBrownianIncrements ((planarBrownianMotion y).map (zPath U ψ)) := by
  intro s t ξ I η hI
  have hZ := aemeasurable_zPath hU hUb hψ hy
  have hm1 : AEStronglyMeasurable (fun ω : ContinuousPath ℂ => pathWave I η ω * planeWave ξ (ω (s + t) - ω s))
      ((planarBrownianMotion y).map (zPath U ψ)) :=
    ((continuous_pathWave I η).mul ((continuous_planeWave ξ).comp
      ((continuous_eval_const (s + t)).sub (continuous_eval_const s)))).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun ω : ContinuousPath ℂ => pathWave I η ω)
      ((planarBrownianMotion y).map (zPath U ψ)) :=
    (continuous_pathWave I η).aestronglyMeasurable
  rw [integral_map hZ hm1, integral_map hZ hm2]
  exact integral_pathWave_mul_planeWave_zPath hU hUb hψ hy s t ξ I η hI

/-! ### Lévy's theorem for an inverse chart -/

theorem exitTime_le_of_eqOn_aux {D : Set ℂ} (hD : IsOpen D) {ω ω' : ContinuousPath ℂ} {v : ℝ≥0}
    (h : ∀ t ≤ v, ω t = ω' t) (hle : ContinuousPath.exitTime D ω ≤ v) :
    ContinuousPath.exitTime D ω' ≤ v := by
  obtain ⟨⟨t, ht⟩, htU⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy D hD v ω).1 hle
  have ht' : t ≤ v := ht
  have hω't : ω' t ∉ D := by
    rw [← h t ht']
    exact htU
  exact (ContinuousPath.exitTime_le_of_notMem D ω' t hω't).trans (by exact_mod_cast ht')

theorem exitTime_eq_of_eqOn_aux {D : Set ℂ} (hD : IsOpen D) {ω ω' : ContinuousPath ℂ} {u : ℝ≥0}
    (h : ∀ t ≤ u, ω t = ω' t) (hle : ContinuousPath.exitTime D ω ≤ u) :
    ContinuousPath.exitTime D ω' = ContinuousPath.exitTime D ω := by
  have hfin : ContinuousPath.exitTime D ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  obtain ⟨e, he⟩ : ∃ e : ℝ≥0, ContinuousPath.exitTime D ω = e := ⟨_, (ENNReal.coe_toNNReal hfin).symm⟩
  have heu : e ≤ u := by
    rw [he] at hle
    exact_mod_cast hle
  have hle' : ContinuousPath.exitTime D ω' ≤ e :=
    exitTime_le_of_eqOn_aux hD (fun t ht => h t (ht.trans heu)) he.le
  refine le_antisymm (hle'.trans he.ge) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hfin' : ContinuousPath.exitTime D ω' ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨e', he'⟩ : ∃ e' : ℝ≥0, ContinuousPath.exitTime D ω' = e' :=
    ⟨_, (ENNReal.coe_toNNReal hfin').symm⟩
  have he'e : e' ≤ e := by
    rw [← ENNReal.coe_le_coe, ← he']
    exact hle'
  have hback : ContinuousPath.exitTime D ω ≤ e' :=
    exitTime_le_of_eqOn_aux hD (fun t ht => (h t (ht.trans (he'e.trans heu))).symm) he'.le
  rw [← he'] at hback
  exact absurd hback (not_le.2 hlt)

/-- The chart path is the continued chart path stopped at its exit from the unit disc. -/
theorem stopAtExitTime_ball_zPath (hU : IsOpen U) (hψ : IsInverseChart U z ψ) {b : ContinuousPath ℂ}
    (hb : b ∈ exitRateGoodSet U fun v => ‖deriv ψ v‖ ^ 2) (hb0 : b 0 ∈ U) :
    stopAtExitTime (Metric.ball (0 : ℂ) 1) (zPath U ψ b) =
      chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) := by
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  obtain ⟨τ, hτe⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
    ⟨_, (ENNReal.coe_toNNReal hb.1.ne).symm⟩
  have hL0 : 0 ≤ chartClock U ψ b τ := IsTimeChangeClock.clock_nonneg hA τ
  have hYexit := exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0 hτe
  have hagree : ∀ σ ≤ (chartClock U ψ b τ).toNNReal,
      chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) σ = zPath U ψ b σ := by
    intro σ hσ
    have hσ' : (σ : ℝ) ≤ chartClock U ψ b τ := by
      have h := NNReal.coe_le_coe.2 hσ
      rwa [Real.coe_toNNReal _ hL0] at h
    have hle := (clockInverse_le_iff_of_isTimeChangeClock hA σ τ).2 hσ'
    rw [chartStopPath_lbmContinuousPath_apply hA hτe, zPath_apply_eq hA hτe, min_eq_left hle, sub_self,
      add_zero]
  have hZexit : ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) (zPath U ψ b) =
      (((chartClock U ψ b τ).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    (exitTime_eq_of_eqOn_aux Metric.isOpen_ball hagree hYexit.le).trans hYexit
  ext σ
  show zPath U ψ b (exitClamp (ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) (zPath U ψ b)) σ) = _
  rw [hZexit, exitClamp_apply, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe,
    ← hagree _ (min_le_right _ _), chartStopPath_lbmContinuousPath_apply hA hτe,
    chartStopPath_lbmContinuousPath_apply hA hτe,
    (IsTimeChangeClock.strictMono_clockInverse hA).monotone.map_min,
    clockInverse_clockValue hA.map_zero hA.strictMono τ, min_assoc, min_self]

/-- **The law of the continued chart path** is planar Brownian motion from `ψ(y)`. -/
theorem map_zPath_eq (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {y : ℂ} (hy : y ∈ U) : (planarBrownianMotion y).map (zPath U ψ) = planarBrownianMotion (ψ y) := by
  have hZ := aemeasurable_zPath hU hUb hψ hy
  have hP : IsProbabilityMeasure ((planarBrownianMotion y).map (zPath U ψ)) :=
    (Measure.isProbabilityMeasure_map_iff hZ).mpr inferInstance
  refine eq_of_hasBrownianIncrements (x := ψ y) ?_ (ae_planarBrownianMotion_eval_zero (ψ y))
    (hasBrownianIncrements_map_zPath hU hUb hψ hy) (hasBrownianIncrements_planarBrownianMotion (ψ y))
  rw [ae_map_iff hZ (isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet]
  filter_upwards [ae_mem_exitRateGoodSet_chart hU hUb hψ hy, ae_planarBrownianMotion_eval_zero y]
    with b hb hb0
  have hA := isTimeChangeClock_chartClock_of_mem hU hψ hb
  have h0 : _root_.HarmonicBalls.clockInverse (chartClock U ψ b) 0 = 0 :=
    FirstPass.Derived.clockInverse_eq_of_apply_eq hA (by rw [hA.map_zero]; rfl)
  rw [zPath_apply_eq hA (ENNReal.coe_toNNReal hb.1.ne).symm, h0, min_eq_left zero_le, sub_self, add_zero,
    hb0]

/-- **The law of the chart path**: planar Brownian motion from `ψ(w)` stopped at its exit from the unit disc. -/
theorem levyChart_map_eq (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ)
    {w : ℂ} (hw : w ∈ U) :
    (planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) =
      (planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1)) := by
  have hZ := aemeasurable_zPath hU hUb hψ hw
  rw [← map_zPath_eq hU hUb hψ hw, AEMeasurable.map_map_of_aemeasurable
    (measurable_stopAtExitTime (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball).aemeasurable hZ]
  refine Measure.map_congr ?_
  filter_upwards [ae_mem_exitRateGoodSet_chart hU hUb hψ hw, ae_planarBrownianMotion_eval_zero w]
    with b hb hb0
  exact (stopAtExitTime_ball_zPath hU hψ hb (by rw [hb0]; exact hw)).symm

/-- **Lévy's conformal invariance of planar Brownian motion for an inverse chart.** -/
theorem levyConformalChartStmt : LevyConformalChartStmt := by
  intro U z ψ hU hUb hψ w hw
  obtain ⟨h1, h2⟩ := levyChart_integrable_aemeasurable hU hUb hψ hw
  exact ⟨h1, h2, levyChart_map_eq hU hUb hψ hw⟩


end Increments

end MatedCRT.LevyChart
