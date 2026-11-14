import HarmonicBalls.Proofs.Potential.Fundamental
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The logarithmic potential of a smooth compactly supported function

For `g : ℂ → ℝ` let `U g (x) = ∫ N(x, y) g(y) dy` be its logarithmic (Newtonian) potential, with the Newtonian
kernel `N(x, y) = -(2π)⁻¹ log |x - y|` of the plane (`HarmonicBalls.newtonKernel`, normalized by `ΔN(x, ·) = -δ_x`).
`U g` is the convolution of the locally integrable kernel `t ↦ N(0, t)` with `g`, so for `g` of class `C^n` with
compact support it is of class `C^n`, and its derivatives fall on `g`. For `g` of class `C²` with compact support this
gives the Poisson equation `Δ U g = U (Δ g) = -g` (Armitage-Gardiner, *Classical Potential Theory*, §4.3), the last
step being the fundamental-solution identity `∫ N(x, y) Δg(y) dy = -g(x)` (`integral_newtonKernel_mul_laplacian`).

This is the first step of the occupation identity of planar Brownian motion killed on exiting a disc,
`E_y ∫_0^τ g(B_t) dt = 2 ∫_D G_D(y, x) g(x) dx`: by Dynkin's formula applied to a compactly supported modification of
`2 U g`, the left side is `2 U g (y) - 2 E_y U g (B_τ)`.

## Main results

* `logPotential_eq_convolution`: `U g = N(0, ·) ⋆ g`;
* `contDiff_logPotential`: `U g` is `C^n` when `g` is `C^n` with compact support;
* `fderiv_logPotential_apply`: `D(U g)(x) v = U (D g(·) v)(x)`;
* `laplacian_logPotential`: `Δ (U g) = -g` for `g` of class `C²` with compact support.
-/

open MeasureTheory Set Laplacian ContinuousLinearMap HarmonicBalls
open scoped ContDiff Convolution

namespace MatedCRT.KilledOccupation

/-- The **logarithmic potential** `U g (x) = ∫ N(x, y) g(y) dy` of `g : ℂ → ℝ`, with the Newtonian kernel
`N(x, y) = -(2π)⁻¹ log |x - y|` of the plane. -/
noncomputable def logPotential (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, HarmonicBalls.newtonKernel x y * g y

/-- The logarithmic potential is the convolution of the kernel `t ↦ N(0, t) = -(2π)⁻¹ log |t|` with `g`. -/
theorem logPotential_eq_convolution (g : ℂ → ℝ) :
    logPotential g = HarmonicBalls.newtonKernel 0 ⋆[lsmul ℝ ℝ, volume] g := by
  funext x
  have h : ∫ t, HarmonicBalls.newtonKernel x (x - t) * g (x - t) =
      ∫ y, HarmonicBalls.newtonKernel x y * g y :=
    integral_sub_left_eq_self (f := fun y => HarmonicBalls.newtonKernel x y * g y) (μ := volume) x
  rw [convolution_lsmul, logPotential, ← h]
  congr 1
  funext t
  simp only [smul_eq_mul, HarmonicBalls.newtonKernel, sub_sub_cancel, zero_sub, norm_neg]

/-- The logarithmic potential of a `C^n` function with compact support is `C^n`. -/
theorem contDiff_logPotential {g : ℂ → ℝ} {n : ℕ∞} (hg : ContDiff ℝ n g) (hgc : HasCompactSupport g) :
    ContDiff ℝ n (logPotential g) := by
  rw [logPotential_eq_convolution]
  exact hgc.contDiff_convolution_right (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0) hg

/-- The directional derivatives of the logarithmic potential of a `C¹` function with compact support fall on the
function: `D(U g)(x) v = U (D g(·) v)(x)`. -/
theorem fderiv_logPotential_apply {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (x v : ℂ) :
    fderiv ℝ (logPotential g) x v = logPotential (fun y => fderiv ℝ g y v) x := by
  rw [logPotential_eq_convolution, logPotential_eq_convolution,
    (hgc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0) hg x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0)
    (hgc.fderiv (𝕜 := ℝ)) (hg.continuous_fderiv one_ne_zero) x v

/-- A directional derivative of a function with compact support has compact support. -/
theorem hasCompactSupport_fderiv_apply {g : ℂ → ℝ} (hgc : HasCompactSupport g) (v : ℂ) :
    HasCompactSupport (fun y => fderiv ℝ g y v) :=
  (hgc.fderiv (𝕜 := ℝ)).mono fun y hy h =>
    (Function.mem_support.1 hy) (by simp [h])

/-- **Poisson equation for the logarithmic potential.** For `g` of class `C²` with compact support,
`Δ (U g) = -g` everywhere. -/
theorem laplacian_logPotential {g : ℂ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (x : ℂ) :
    Δ (logPotential g) x = -g x := by
  have hu : ContDiff ℝ 2 (logPotential g) := by
    have := contDiff_logPotential (n := 2) (by exact_mod_cast hg) hgc
    exact_mod_cast this
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hgv : ∀ v : ℂ, ContDiff ℝ 1 (fun y => fderiv ℝ g y v) := fun v =>
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (logPotential g) z v) = logPotential (fun y => fderiv ℝ g y v) :=
    fun v => funext fun z => fderiv_logPotential_apply hg1 hgc z v
  rw [laplacian_eq_fderiv_fderiv hu, h1 1, h1 Complex.I,
    fderiv_logPotential_apply (hgv 1) (hasCompactSupport_fderiv_apply hgc 1),
    fderiv_logPotential_apply (hgv Complex.I) (hasCompactSupport_fderiv_apply hgc Complex.I),
    logPotential_eq_convolution, logPotential_eq_convolution]
  have hex : ∀ v : ℂ, ConvolutionExistsAt (HarmonicBalls.newtonKernel 0)
      (fun y => fderiv ℝ (fun z => fderiv ℝ g z v) y v) x (lsmul ℝ ℝ) volume := fun v =>
    (hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hgc v) v).convolutionExists_right
      (lsmul ℝ ℝ) (HarmonicBalls.locallyIntegrable_newtonKernel 0)
      (((hgv v).continuous_fderiv one_ne_zero).clm_apply continuous_const) x
  rw [← ConvolutionExistsAt.distrib_add (hex 1) (hex Complex.I)]
  have hΔ : (fun y => fderiv ℝ (fun z => fderiv ℝ g z 1) y 1) +
      (fun y => fderiv ℝ (fun z => fderiv ℝ g z Complex.I) y Complex.I) = Δ g := by
    funext y
    rw [Pi.add_apply, laplacian_eq_fderiv_fderiv hg]
  rw [hΔ, ← logPotential_eq_convolution, logPotential, integral_newtonKernel_mul_laplacian hg hgc]

end MatedCRT.KilledOccupation
