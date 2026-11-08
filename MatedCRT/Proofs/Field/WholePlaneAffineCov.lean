import MatedCRT.Proofs.Field.WholePlaneKernelAffine
import MatedCRT.Proofs.Field.Translation
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# Covariance identities of the whole-plane GFF under real affine maps

For `r > 0`, `z ∈ ℂ` and `T x = r x + z`, let `φ^T = φ ((· - z)/r)` (the pullback of a test function). The affine
transform `h ↦ h(T ·) - h_r(z)` of a whole-plane GFF has the covariance expansion
`r^{-2} h(φ^T) - (∫φ) h_r(z)` for pairings and `h_{rs}(rw + z) - h_r(z)` for circle averages.
The identities below say that these expansions reproduce the whole-plane covariance kernel
`G x y = wholePlaneCov x y` (Duplantier-Sheffield 2011, Section 3.1; Harmonic-Balls `WholePlaneGFFAffineInvariance`):

* `affine_pp`: pairing with pairing;
* `affine_pc`: pairing with a circle average (the circle `∂B_{rs}(rw + z)` is the image of `∂B_s(w)`);
* `affine_cc`: circle average with circle average.

The kernel identity `G(Tx, Ty) = G(x, y) + A₀(Tx) + A₀(Ty) - B₀` (`WholePlaneKernelAffine.lean`) is used off the
diagonal, which is Lebesgue-null and a single point on each circle.
-/

namespace MatedCRT.Field

open MeasureTheory Filter Set Metric

/-- The pullback `y ↦ φ ((y - z)/r)` of a function under `x ↦ r x + z`. -/
noncomputable def affPull (r : ℝ) (z : ℂ) (φ : ℂ → ℝ) : ℂ → ℝ := fun y => φ ((y - z) / (r : ℂ))

/-- The affine map `x ↦ r x + z` is continuous. -/
theorem continuous_affine_map (r : ℝ) (z : ℂ) : Continuous fun x : ℂ => (r : ℂ) * x + z :=
  (continuous_const.mul continuous_id).add continuous_const

/-- `A₀ z r` is continuous (closed form). -/
theorem continuous_A0 (z : ℂ) {r : ℝ} (hr : 0 < r) : Continuous fun u => A0 z r u := by
  have hfun : (fun u => A0 z r u) = fun u =>
      Real.log (max ‖u‖ 1) + F0 z r - (Real.log r + Real.posLog (r⁻¹ * ‖z - u‖)) :=
    funext fun u => circleAverage_wholePlaneCov_eq z u hr
  rw [hfun]
  exact (continuous_log_max_norm.add continuous_const).sub
    (continuous_const.add (Real.continuous_posLog.comp (continuous_const.mul (continuous_const.sub continuous_id).norm)))

/-- The circle average `y ↦ avg_{u ∈ ∂B_ρ(c)} G(y, u)` is continuous (closed form). -/
theorem continuous_circleAverage_wholePlaneCov (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous fun y => Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) c ρ := by
  have hfun : (fun y => Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) c ρ) = fun y =>
      Real.log (max ‖y‖ 1) + F0 c ρ - (Real.log ρ + Real.posLog (ρ⁻¹ * ‖c - y‖)) :=
    funext fun y => circleAverage_wholePlaneCov_eq c y hρ
  rw [hfun]
  exact (continuous_log_max_norm.add continuous_const).sub
    (continuous_const.add (Real.continuous_posLog.comp (continuous_const.mul (continuous_const.sub continuous_id).norm)))

/-- **Kernel averaged over a circle.** For `y ∈ ℂ`, `ρ > 0`, `c ∈ ℂ`:
`avg_{v ∈ ∂B_ρ(c)} G(T y, T v) = avg_{v} G(y, v) + A₀(T y) + avg_{v} A₀(T v) - B₀`. -/
theorem circleAverage_kernel_affine {r : ℝ} (hr : 0 < r) (z y c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun v => HarmonicBalls.wholePlaneCov ((r : ℂ) * y + z) ((r : ℂ) * v + z)) c ρ =
      Real.circleAverage (fun v => HarmonicBalls.wholePlaneCov y v) c ρ + A0 z r ((r : ℂ) * y + z)
        + Real.circleAverage (fun v => A0 z r ((r : ℂ) * v + z)) c ρ - B0 z r := by
  have hg : CircleIntegrable
      (fun v : ℂ => (Real.log (max ‖y‖ 1) + Real.log (max ‖v‖ 1)) - Real.log ‖v - y‖) c ρ :=
    ((continuous_const.add continuous_log_max_norm).continuousOn.circleIntegrable hρ.le).sub
      (circleIntegrable_log_norm_sub_const (a := y) (c := c) ρ)
  have hA : CircleIntegrable (fun v : ℂ => A0 z r ((r : ℂ) * v + z)) c ρ :=
    ((continuous_A0 z hr).comp (continuous_affine_map r z)).continuousOn.circleIntegrable hρ.le
  have hC : CircleIntegrable (fun _ : ℂ => A0 z r ((r : ℂ) * y + z)) c ρ := circleIntegrable_const _ _ _
  have hB : CircleIntegrable (fun _ : ℂ => B0 z r) c ρ := circleIntegrable_const _ _ _
  have hcongr1 : (fun v => HarmonicBalls.wholePlaneCov ((r : ℂ) * y + z) ((r : ℂ) * v + z))
      =ᶠ[codiscreteWithin (sphere c |ρ|)]
      (fun v => ((Real.log (max ‖y‖ 1) + Real.log (max ‖v‖ 1)) - Real.log ‖v - y‖)
        + A0 z r ((r : ℂ) * y + z) + A0 z r ((r : ℂ) * v + z) - B0 z r) := by
    filter_upwards [eventually_ne_codiscreteWithin (sphere c |ρ|) y] with v hv
    rw [wholePlaneCov_affine_eq hr z (Ne.symm hv), wholePlaneCov_of_ne (Ne.symm hv), norm_sub_rev y v]
    ring
  have hcongr2 : (fun v => (Real.log (max ‖y‖ 1) + Real.log (max ‖v‖ 1)) - Real.log ‖v - y‖)
      =ᶠ[codiscreteWithin (sphere c |ρ|)] (fun v => HarmonicBalls.wholePlaneCov y v) := by
    filter_upwards [eventually_ne_codiscreteWithin (sphere c |ρ|) y] with v hv
    rw [wholePlaneCov_of_ne (Ne.symm hv), norm_sub_rev v y]
    ring
  have hI1 : CircleIntegrable
      (fun v => (((Real.log (max ‖y‖ 1) + Real.log (max ‖v‖ 1)) - Real.log ‖v - y‖)
        + A0 z r ((r : ℂ) * y + z)) + A0 z r ((r : ℂ) * v + z)) c ρ :=
    (hg.add hC).add hA
  have hI2 : CircleIntegrable
      (fun v => ((Real.log (max ‖y‖ 1) + Real.log (max ‖v‖ 1)) - Real.log ‖v - y‖)
        + A0 z r ((r : ℂ) * y + z)) c ρ :=
    hg.add hC
  rw [Real.circleAverage_congr_codiscreteWithin hcongr1 hρ.ne',
    Real.circleAverage_fun_sub hI1 hB, Real.circleAverage_fun_add hI2 hA,
    Real.circleAverage_fun_add hg hC, Real.circleAverage_const, Real.circleAverage_const,
    Real.circleAverage_congr_codiscreteWithin hcongr2 hρ.ne']

/-- **Pairing with pairing.** For test functions `φ, ψ` and `r > 0`, the covariance of the transformed pairings
`r^{-2} h(φ^T) - (∫φ) h_r(z)` and `r^{-2} h(ψ^T) - (∫ψ) h_r(z)` is the whole-plane covariance of `φ` and `ψ`. -/
theorem affine_pp {r : ℝ} (hr : 0 < r) (z : ℂ) {φ ψ : ℂ → ℝ}
    (hφ : HarmonicBalls.IsTestFunction Set.univ φ) (hψ : HarmonicBalls.IsTestFunction Set.univ ψ) :
    (r ^ 2)⁻¹ * (r ^ 2)⁻¹
        * (∫ x, affPull r z φ x * ∫ y, affPull r z ψ y * HarmonicBalls.wholePlaneCov x y)
      - (r ^ 2)⁻¹ * (∫ x, ψ x) * (∫ x, affPull r z φ x * A0 z r x)
      - (r ^ 2)⁻¹ * (∫ x, φ x) * (∫ x, affPull r z ψ x * A0 z r x)
      + (∫ x, φ x) * (∫ x, ψ x) * B0 z r
      = ∫ x, φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov x y := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hψc : Continuous ψ := hψ.1.continuous
  have hψs : HasCompactSupport ψ := hψ.2.1
  have hφc : Continuous φ := hφ.1.continuous
  have hφs : HasCompactSupport φ := hφ.2.1
  have hΨc : Continuous fun x => ∫ y, ψ y * HarmonicBalls.wholePlaneCov x y :=
    HarmonicBalls.continuous_wholePlaneCov_potential_general hψc hψs
  have hA0c : Continuous fun u => A0 z r u := continuous_A0 z hr
  have hA0T : Continuous fun u : ℂ => A0 z r ((r : ℂ) * u + z) := hA0c.comp (continuous_affine_map r z)
  -- the inner pullback
  have hstep1 : ∀ x : ℂ, ∫ y, affPull r z ψ y * HarmonicBalls.wholePlaneCov x y
      = r ^ 2 * ∫ y, ψ y * HarmonicBalls.wholePlaneCov x ((r : ℂ) * y + z) :=
    fun x => integral_affine_pullback ψ (fun y => HarmonicBalls.wholePlaneCov x y) hr z
  -- the outer pullback
  have hstep2 : ∫ x, affPull r z φ x * ∫ y, affPull r z ψ y * HarmonicBalls.wholePlaneCov x y
      = r ^ 2 * (r ^ 2 * ∫ x, φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov ((r : ℂ) * x + z) ((r : ℂ) * y + z)) := by
    have h1 : ∀ x : ℂ, affPull r z φ x * ∫ y, affPull r z ψ y * HarmonicBalls.wholePlaneCov x y
        = r ^ 2 * (affPull r z φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov x ((r : ℂ) * y + z)) := by
      intro x
      rw [hstep1 x]
      ring
    simp_rw [h1]
    rw [integral_const_mul]
    congr 1
    exact integral_affine_pullback φ
      (fun x => ∫ y, ψ y * HarmonicBalls.wholePlaneCov x ((r : ℂ) * y + z)) hr z
  -- the kernel identity inside the integral against ψ
  have hJ : ∀ x : ℂ, ∫ y, ψ y * HarmonicBalls.wholePlaneCov ((r : ℂ) * x + z) ((r : ℂ) * y + z)
      = (∫ y, ψ y * HarmonicBalls.wholePlaneCov x y) + A0 z r ((r : ℂ) * x + z) * (∫ y, ψ y)
        + (∫ y, ψ y * A0 z r ((r : ℂ) * y + z)) - B0 z r * (∫ y, ψ y) := by
    intro x
    have hae : ∀ᵐ y ∂(volume : Measure ℂ),
        ψ y * HarmonicBalls.wholePlaneCov ((r : ℂ) * x + z) ((r : ℂ) * y + z)
          = ψ y * HarmonicBalls.wholePlaneCov x y + ψ y * A0 z r ((r : ℂ) * x + z)
            + ψ y * A0 z r ((r : ℂ) * y + z) - ψ y * B0 z r := by
      filter_upwards [ae_ne x] with y hy
      rw [wholePlaneCov_affine_eq hr z (Ne.symm hy)]
      ring
    rw [integral_congr_ae hae]
    have i1 : Integrable fun y => ψ y * HarmonicBalls.wholePlaneCov x y :=
      integrable_mul_wholePlaneCov hψ x
    have i2 : Integrable fun y => ψ y * A0 z r ((r : ℂ) * x + z) :=
      (integrable_of_isTestFunction hψ).mul_const _
    have i3 : Integrable fun y => ψ y * A0 z r ((r : ℂ) * y + z) :=
      (hψc.mul (hA0c.comp (continuous_affine_map r z))).integrable_of_hasCompactSupport hψs.mul_right
    have i4 : Integrable fun y => ψ y * B0 z r := (integrable_of_isTestFunction hψ).mul_const _
    have i12 : Integrable fun y => ψ y * HarmonicBalls.wholePlaneCov x y + ψ y * A0 z r ((r : ℂ) * x + z) :=
      i1.add i2
    have i123 : Integrable fun y => ψ y * HarmonicBalls.wholePlaneCov x y + ψ y * A0 z r ((r : ℂ) * x + z)
        + ψ y * A0 z r ((r : ℂ) * y + z) := i12.add i3
    rw [integral_sub i123 i4, integral_add i12 i3, integral_add i1 i2,
      integral_mul_const, integral_mul_const]
    ring
  -- the integral of φ against the kernel identity
  have hmain : ∫ x, φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov ((r : ℂ) * x + z) ((r : ℂ) * y + z)
      = (∫ x, φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov x y)
        + (∫ y, ψ y) * (∫ x, φ x * A0 z r ((r : ℂ) * x + z))
        + (∫ x, φ x) * (∫ y, ψ y * A0 z r ((r : ℂ) * y + z))
        - B0 z r * (∫ y, ψ y) * (∫ x, φ x) := by
    have e : ∀ x : ℂ, φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov ((r : ℂ) * x + z) ((r : ℂ) * y + z)
        = φ x * (∫ y, ψ y * HarmonicBalls.wholePlaneCov x y)
          + (∫ y, ψ y) * (φ x * A0 z r ((r : ℂ) * x + z))
          + (∫ y, ψ y * A0 z r ((r : ℂ) * y + z)) * φ x - B0 z r * (∫ y, ψ y) * φ x := by
      intro x
      rw [hJ x]
      ring
    simp_rw [e]
    have f1 : Integrable fun x => φ x * ∫ y, ψ y * HarmonicBalls.wholePlaneCov x y :=
      (hφc.mul hΨc).integrable_of_hasCompactSupport hφs.mul_right
    have f2 : Integrable fun x => (∫ y, ψ y) * (φ x * A0 z r ((r : ℂ) * x + z)) :=
      ((hφc.mul hA0T).integrable_of_hasCompactSupport hφs.mul_right).const_mul _
    have f3 : Integrable fun x => (∫ y, ψ y * A0 z r ((r : ℂ) * y + z)) * φ x :=
      (integrable_of_isTestFunction hφ).const_mul _
    have f4 : Integrable fun x => B0 z r * (∫ y, ψ y) * φ x :=
      (integrable_of_isTestFunction hφ).const_mul _
    have f12 : Integrable fun x => φ x * (∫ y, ψ y * HarmonicBalls.wholePlaneCov x y)
        + (∫ y, ψ y) * (φ x * A0 z r ((r : ℂ) * x + z)) := f1.add f2
    have f123 : Integrable fun x => φ x * (∫ y, ψ y * HarmonicBalls.wholePlaneCov x y)
        + (∫ y, ψ y) * (φ x * A0 z r ((r : ℂ) * x + z))
        + (∫ y, ψ y * A0 z r ((r : ℂ) * y + z)) * φ x := f12.add f3
    rw [integral_sub f123 f4, integral_add f12 f3, integral_add f1 f2,
      integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  have hsecond1 : ∫ x, affPull r z φ x * A0 z r x = r ^ 2 * ∫ x, φ x * A0 z r ((r : ℂ) * x + z) :=
    integral_affine_pullback φ (fun x => A0 z r x) hr z
  have hsecond2 : ∫ x, affPull r z ψ x * A0 z r x = r ^ 2 * ∫ x, ψ x * A0 z r ((r : ℂ) * x + z) :=
    integral_affine_pullback ψ (fun x => A0 z r x) hr z
  rw [hstep2, hsecond1, hsecond2, hmain]
  field_simp
  ring

/-- **Pairing with a circle average.** For a test function `φ`, `r > 0`, `s > 0`, `w ∈ ℂ`: the covariance of
`r^{-2} h(φ^T) - (∫φ) h_r(z)` with `h_{rs}(rw + z) - h_r(z)` is the whole-plane covariance of `φ` and `h_s(w)`. -/
theorem affine_pc {r : ℝ} (hr : 0 < r) (z : ℂ) {φ : ℂ → ℝ} (hφ : HarmonicBalls.IsTestFunction Set.univ φ)
    {s : ℝ} (hs : 0 < s) (w : ℂ) :
    (r ^ 2)⁻¹ * ((∫ x, affPull r z φ x
          * Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) ((r : ℂ) * w + z) (r * s))
        - ∫ x, affPull r z φ x * A0 z r x)
      - (∫ x, φ x) * (Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s) - B0 z r)
      = ∫ x, φ x * Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) w s := by
  have hφc : Continuous φ := hφ.1.continuous
  have hφs : HasCompactSupport φ := hφ.2.1
  have hCav : Continuous fun y => Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) w s :=
    continuous_circleAverage_wholePlaneCov w hs
  have hA0c : Continuous fun u => A0 z r u := continuous_A0 z hr
  have ha : ∀ x : ℂ, Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) ((r : ℂ) * w + z) (r * s)
      = Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov x ((r : ℂ) * u + z)) w s :=
    fun x => (circleAverage_affine (fun y => HarmonicBalls.wholePlaneCov x y) r z w s).symm
  have hG : ∀ y : ℂ,
      Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov ((r : ℂ) * y + z) ((r : ℂ) * u + z)) w s
        = Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) w s + A0 z r ((r : ℂ) * y + z)
          + Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s) - B0 z r := by
    intro y
    rw [circleAverage_kernel_affine hr z y w hs, circleAverage_affine (A0 z r) r z w s]
  have h1 : ∫ x, affPull r z φ x
      * Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) ((r : ℂ) * w + z) (r * s)
      = r ^ 2 * ∫ y, φ y
          * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov ((r : ℂ) * y + z) ((r : ℂ) * u + z)) w s := by
    simp_rw [ha]
    exact integral_affine_pullback φ
      (fun x => Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov x ((r : ℂ) * u + z)) w s) hr z
  have h2 : ∫ x, affPull r z φ x * A0 z r x = r ^ 2 * ∫ y, φ y * A0 z r ((r : ℂ) * y + z) :=
    integral_affine_pullback φ (fun x => A0 z r x) hr z
  have hmain : ∫ y, φ y
        * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov ((r : ℂ) * y + z) ((r : ℂ) * u + z)) w s
      = (∫ y, φ y * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) w s)
        + (∫ y, φ y * A0 z r ((r : ℂ) * y + z))
        + (∫ y, φ y) * (Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s) - B0 z r) := by
    have e : ∀ y : ℂ,
        φ y * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov ((r : ℂ) * y + z) ((r : ℂ) * u + z)) w s
          = φ y * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) w s
            + φ y * A0 z r ((r : ℂ) * y + z)
            + φ y * (Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s) - B0 z r) := by
      intro y
      rw [hG y]
      ring
    simp_rw [e]
    have f1 : Integrable fun y => φ y * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) w s :=
      (hφc.mul hCav).integrable_of_hasCompactSupport hφs.mul_right
    have f2 : Integrable fun y => φ y * A0 z r ((r : ℂ) * y + z) :=
      (hφc.mul (hA0c.comp (continuous_affine_map r z))).integrable_of_hasCompactSupport hφs.mul_right
    have f3 : Integrable fun y => φ y * (Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s) - B0 z r) :=
      (integrable_of_isTestFunction hφ).mul_const _
    have f12 : Integrable fun y => φ y * Real.circleAverage (fun u => HarmonicBalls.wholePlaneCov y u) w s
        + φ y * A0 z r ((r : ℂ) * y + z) := f1.add f2
    rw [integral_add f12 f3, integral_add f1 f2, integral_mul_const]
  rw [h1, h2, hmain]
  field_simp
  ring

/-- **Circle average with circle average.** For `s, t > 0` and `w, v ∈ ℂ`: the covariance of
`h_{rs}(rw + z) - h_r(z)` and `h_{rt}(rv + z) - h_r(z)` is the whole-plane covariance of `h_s(w)` and `h_t(v)`. -/
theorem affine_cc {r : ℝ} (hr : 0 < r) (z : ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w v : ℂ) :
    Real.circleAverage
        (fun x => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) ((r : ℂ) * v + z) (r * t))
        ((r : ℂ) * w + z) (r * s)
      - Real.circleAverage (A0 z r) ((r : ℂ) * w + z) (r * s)
      - Real.circleAverage (A0 z r) ((r : ℂ) * v + z) (r * t) + B0 z r
      = Real.circleAverage (fun u => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov u y) v t) w s := by
  have hCav : Continuous fun u => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov u y) v t :=
    continuous_circleAverage_wholePlaneCov v ht
  have hA0T : Continuous fun u : ℂ => A0 z r ((r : ℂ) * u + z) :=
    (continuous_A0 z hr).comp (continuous_affine_map r z)
  have hL : Real.circleAverage
        (fun x => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) ((r : ℂ) * v + z) (r * t))
        ((r : ℂ) * w + z) (r * s)
      = Real.circleAverage
        (fun u => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov ((r : ℂ) * u + z) y) ((r : ℂ) * v + z) (r * t))
        w s :=
    (circleAverage_affine
      (fun x => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov x y) ((r : ℂ) * v + z) (r * t))
      r z w s).symm
  have hF : ∀ u : ℂ,
      Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov ((r : ℂ) * u + z) y) ((r : ℂ) * v + z) (r * t)
        = (Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov u y) v t + A0 z r ((r : ℂ) * u + z))
          + (Real.circleAverage (A0 z r) ((r : ℂ) * v + z) (r * t) - B0 z r) := by
    intro u
    have e1 : Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov ((r : ℂ) * u + z) y) ((r : ℂ) * v + z) (r * t)
        = Real.circleAverage (fun v' => HarmonicBalls.wholePlaneCov ((r : ℂ) * u + z) ((r : ℂ) * v' + z)) v t :=
      (circleAverage_affine (fun y => HarmonicBalls.wholePlaneCov ((r : ℂ) * u + z) y) r z v t).symm
    rw [e1, circleAverage_kernel_affine hr z u v ht, circleAverage_affine (A0 z r) r z v t]
    ring
  rw [hL]
  simp_rw [hF]
  have hc2 : CircleIntegrable
      (fun u => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov u y) v t + A0 z r ((r : ℂ) * u + z)) w s :=
    (hCav.add hA0T).continuousOn.circleIntegrable hs.le
  have hcCav : CircleIntegrable (fun u => Real.circleAverage (fun y => HarmonicBalls.wholePlaneCov u y) v t) w s :=
    hCav.continuousOn.circleIntegrable hs.le
  have hcA : CircleIntegrable (fun u : ℂ => A0 z r ((r : ℂ) * u + z)) w s :=
    hA0T.continuousOn.circleIntegrable hs.le
  rw [Real.circleAverage_fun_add hc2 (circleIntegrable_const _ _ _), Real.circleAverage_fun_add hcCav hcA,
    Real.circleAverage_const, circleAverage_affine (A0 z r) r z w s]
  ring

end MatedCRT.Field

