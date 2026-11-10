import MatedCRT.FirstPass.S2y.ConeCircleDecoder
import MatedCRT.FirstPass.S2y.ConeRadialCodes

/-!
# Pairing approximations of a quantum cone (chat 240, §2; fp-S2y-lateral-240, z8)

The measurable approximants of the pairing `hC · φ` from the circle average process (the input of
`coneCircleDecoderStep_of_pairingApprox`, `S2y/ConeCircleDecoder.lean`):

* `pairingApprox φ n` is the limit superior of the midpoint Riemann sums of `z ↦ φ(z) h_ε(z)` at the
  radius `ε = pairingRadius n = 2^{-(n+1)}` (`circleSmearCode`, `ConeRadialCodes.lean` `planeQuad`);
  it is a Borel function of the circle process, by the finite-coordinate measurability of `planeQuad`.
* For a cone, the circle average `h_ε(z)` splits as the lateral observable plus the circle average of the
  radial part, `h_ε(z) = lateralEval (.circle ε z) + A_ε(z)` with `A_ε(z)` the circle average of
  `x ↦ h_{|x|}(0)` (Armitage-Gardiner, circle averages; Duplantier-Sheffield, Section 3.1).
  `limsup_planeQuad_split` and `circleSmearCode_circleProcess_split` give the deterministic splitting
  of the limit superior, provided the Riemann sums of the radial part converge.
-/

open MeasureTheory Filter Topology Set Metric
open scoped Real

namespace MatedCRT.LQGMeasure

/-- The radius `2^{-(n+1)}` of the pairing approximation at level `n`. -/
noncomputable def pairingRadius (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (n + 1)

lemma pairingRadius_pos (n : ℕ) : 0 < pairingRadius n := pow_pos (by norm_num) _

lemma pairingRadius_tendsto : Tendsto pairingRadius atTop (𝓝 0) := by
  unfold pairingRadius
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  exact h.comp (tendsto_add_atTop_nat 1)

/-- **Circle smear code** (chat 240, §2): the limit superior of the midpoint Riemann sums of
`z ↦ φ(z) q(ε, z)`; a Borel function of the circle process `q` (`ConeCircleCode`). -/
noncomputable def circleSmearCode (φ : ℂ → ℝ) (ε : ℝ) (hε : 0 < ε) (q : ConeCircleCode) : ℝ :=
  limsup (fun k => planeQuad k (fun z => φ z * q (⟨ε, hε⟩, z))) atTop

/-- **Pairing approximant** at level `n` (chat 240, §2): the circle smear at radius `pairingRadius n`. -/
noncomputable def pairingApprox (φ : ℂ → ℝ) (n : ℕ) : ConeCircleCode → ℝ :=
  circleSmearCode φ (pairingRadius n) (pairingRadius_pos n)

/-- The pairing approximants are Borel functions of the circle process (finite-coordinate Riemann sums,
`measurable_planeQuad_eval`, and the `limsup` of a sequence of Borel functions). -/
theorem measurable_pairingApprox (φ : ℂ → ℝ) (n : ℕ) : Measurable (pairingApprox φ n) := by
  unfold pairingApprox circleSmearCode
  refine Measurable.limsup fun k => ?_
  exact measurable_planeQuad_eval (n := k) (p := fun z : ℂ => ((⟨pairingRadius n, pairingRadius_pos n⟩ :
    Set.Ioi (0 : ℝ)), z)) (a := φ)

/-- The midpoint Riemann sum is linear. -/
lemma planeQuad_sub (n : ℕ) (f g : ℂ → ℝ) :
    planeQuad n (fun z => f z - g z) = planeQuad n f - planeQuad n g := by
  unfold planeQuad
  simp only [← Finset.sum_sub_distrib, mul_sub]

/-- **Splitting of a `limsup` of Riemann sums** (deterministic). If the Riemann sums of `φ A` converge to
`Y` and `h` is continuous, then the `limsup` of the Riemann sums of `φ h` is the `limsup` of those of
`φ (h - A)` plus `Y`. The Riemann sums of `φ (h - A)` converge, so both `limsup`s are limits. -/
theorem limsup_planeQuad_split {φ h A : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : Continuous h) {Y : ℝ}
    (hY : Tendsto (fun k => planeQuad k (fun z => φ z * A z)) atTop (𝓝 Y)) :
    limsup (fun k => planeQuad k (fun z => φ z * h z)) atTop =
      limsup (fun k => planeQuad k (fun z => φ z * (h z - A z))) atTop + Y := by
  have hs : Tendsto (fun k => planeQuad k (fun z => φ z * h z)) atTop
      (𝓝 (∫ z, φ z * h z)) :=
    planeQuad_tendsto_integral (hφ.mul hh) (hφc.mul_right)
  have hx : Tendsto (fun k => planeQuad k (fun z => φ z * (h z - A z))) atTop
      (𝓝 ((∫ z, φ z * h z) - Y)) := by
    refine Tendsto.congr (fun k => ?_) (hs.sub hY)
    simp only [mul_sub, planeQuad_sub]
  rw [hs.limsup_eq, hx.limsup_eq]
  ring

/-- **Splitting of the circle smear of a cone** (deterministic). For a continuous circle average at radius
`ε` and a radial circle average `A` of `x ↦ h_{|x|}(0)` whose Riemann sums converge to `Y`, the smear of the
circle process is the smear of the lateral observables `lateralEval (.circle ε z)` plus `Y`. -/
theorem circleSmearCode_circleProcess_split (φ : ℂ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {ε : ℝ} (hε : 0 < ε) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (hcont : Continuous fun z => hcirc ε z)
    {Y : ℝ}
    (hY : Tendsto (fun k => planeQuad k (fun z => φ z *
      Real.circleAverage (fun x => hcirc ‖x‖ 0) z ε)) atTop (𝓝 Y)) :
    circleSmearCode φ ε hε (circleProcess hcirc) =
      circleSmearCode φ ε hε (fun p => lateralEval hC hcirc (.circle p.1.1 p.2)) + Y := by
  unfold circleSmearCode
  simp only [circleProcess, lateralEval]
  exact limsup_planeQuad_split hφ hφc hcont hY

end MatedCRT.LQGMeasure
