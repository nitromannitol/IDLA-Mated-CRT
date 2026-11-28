import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraKernelSine
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatDens
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatSqKer

/-!
# The boundary layer of the killed interval kernel

Planar Brownian motion started at distance `e` from the left side of a square of side `L`, at mid-height, stays in
the square up to time `t` and ends in a fixed window inside it with probability at least a constant times `e`, as soon
as the first Dirichlet mode dominates (`exp(-π² t/(2L²)) ≤ 1/4`). On the square the killed heat kernel is the product
of two killed interval kernels (`LQGMetric.KilledHeatSq.killedHeat_sqOpen`); the kernel of the horizontal coordinate
is at least `2/L² · exp(-π² t/(2L²)) · e` at distance `e` from the side and that of the vertical coordinate at least
`1/L · exp(-π² t/(2L²))` at mid-height (`intervalDirKernel_ge_linear`, `intervalDirKernel_ge_firstMode`, from the
sine series of the kernel, the Fourier expansion of the image series of Karatzas–Shreve, *Brownian Motion and
Stochastic Calculus*, §2.8.C, Proposition 8.10, (8.12); `LQGMetric.HeatSq.hasSum_intervalDirKernel_sine`); the
probability is the integral of the kernel over the window (`LQGMetric.KilledHeat.lintegral_killedHeat_eq`), for any
planar Brownian motion `W` (`LQGMetric.KilledHeat.IsPlanarBM`).

* `layerWindow e L`: the window `(e + 5L/16, e + 7L/16) × (L/4, 3L/4)` of the square `(0, L)²`.
* `le_measure_layer`: the lower bound `exp(-π² t/(2L²))² / (8L) · e` for `0 < e ≤ L/16`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MatedCRT.PeanosphereTriplePoints

open LQGMetric.HeatSq

/-- The window `(e + 5L/16, e + 7L/16) × (L/4, 3L/4)` of the square `(0, L)²`. -/
def layerWindow (e L : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Ioo (e + 5 * L / 16) (e + 7 * L / 16) ×ˢ Ioo (L / 4) (3 * L / 4))

theorem measurableSet_layerWindow (e L : ℝ) : MeasurableSet (layerWindow e L) :=
  Complex.measurableEquivRealProd.measurable (measurableSet_Ioo.prod measurableSet_Ioo)

theorem volume_layerWindow {e L : ℝ} (hL : 0 < L) :
    volume (layerWindow e L) = ENNReal.ofReal (L ^ 2 / 16) := by
  unfold layerWindow
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

theorem mem_of_mem_layerWindow {e L : ℝ} {w : ℂ} (hw : w ∈ layerWindow e L) :
    e + 5 * L / 16 < w.re ∧ w.re < e + 7 * L / 16 ∧ L / 4 < w.im ∧ w.im < 3 * L / 4 := by
  simp only [layerWindow, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Ioo] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2.1, hw.2.2⟩

/-- **The boundary layer.** For a planar Brownian motion `W`, the planar path `z + W` with
`z = e + (L/2) i` stays in the square `(0, L)²` up to time `t` and ends in
`layerWindow e L` with probability at least `exp(-π² t/(2L²))² / (8L) · e`, for `0 < e ≤ L/16`, when
`exp(-π² t/(2L²)) ≤ 1/4`. -/
theorem le_measure_layer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℂ}
    (hW : LQGMetric.KilledHeat.IsPlanarBM W P) {L : ℝ} (hL : 0 < L)
    {t : ℝ≥0} (ht : 0 < t) (hr : Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * t) ≤ 1 / 4)
    {e : ℝ} (he0 : 0 < e) (he : e ≤ L / 16) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * t) ^ 2 / (8 * L) * e) ≤
      P {ω | (e : ℂ) + ((L / 2 : ℝ) : ℂ) * Complex.I + W t ω ∈ layerWindow e L ∧
        ∀ s : ℝ≥0, s ≤ t → (e : ℂ) + ((L / 2 : ℝ) : ℂ) * Complex.I + W s ω ∈ sqOpen 0 L} := by
  set r := Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * t) with hrdef
  set z : ℂ := (e : ℂ) + ((L / 2 : ℝ) : ℂ) * Complex.I with hzdef
  have hr0 : 0 < r := Real.exp_pos _
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
  rw [← LQGMetric.KilledHeat.lintegral_killedHeat_eq (isOpen_sqOpen 0 L) (by exact_mod_cast ht')
    hW z (measurableSet_layerWindow e L)]
  have hzre : z.re = e := by simp [hzdef]
  have hzim : z.im = L / 2 := by simp [hzdef]
  have hzQ : z ∈ sqOpen 0 L := by
    simp only [sqOpen, mem_ofPred_eq, hzre, hzim]
    refine ⟨he0, by linarith, by linarith, by linarith⟩
  -- the pointwise lower bound of the kernel on the window
  have hbound : ∀ w ∈ layerWindow e L, 2 * r ^ 2 / L ^ 3 * e ≤
      LQGMetric.KilledHeat.killedHeat (sqOpen 0 L) t z w := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := mem_of_mem_layerWindow hw
    have hwQ : w ∈ sqOpen 0 L := by
      simp only [sqOpen, mem_ofPred_eq]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    rw [LQGMetric.KilledHeatSq.killedHeat_sqOpen hL t (by exact_mod_cast ht') z w hzQ hwQ]
    unfold sqDirKernel
    rw [hzre, hzim]
    have hX := intervalDirKernel_ge_linear (a := 0) (L := L) (s := t) (u := e) (v := w.re) hL
      (by exact_mod_cast ht) hr (by linarith) (by linarith) (by linarith) (by linarith)
    have hY := intervalDirKernel_ge_firstMode (a := 0) (L := L) (s := t) (u := L / 2) (v := w.im) hL
      (by exact_mod_cast ht) hr (by linarith) (by linarith) (by linarith) (by linarith)
    have hsin : Real.sin (Real.pi * (L / 2 - 0) / L) = 1 := by
      rw [show Real.pi * (L / 2 - 0) / L = Real.pi / 2 by field_simp; ring]
      exact Real.sin_pi_div_two
    rw [hsin, mul_one] at hY
    rw [sub_zero] at hX
    have hXn : 0 ≤ 2 / L ^ 2 * r * e := by positivity
    have hYn : 0 ≤ 1 / L * r := by positivity
    calc 2 * r ^ 2 / L ^ 3 * e = (2 / L ^ 2 * r * e) * (1 / L * r) := by
          field_simp
      _ ≤ intervalDirKernel 0 L t e w.re * intervalDirKernel 0 L t (L / 2) w.im :=
          mul_le_mul hX hY hYn (hXn.trans hX)
  calc ENNReal.ofReal (r ^ 2 / (8 * L) * e)
      = ENNReal.ofReal (2 * r ^ 2 / L ^ 3 * e) * volume (layerWindow e L) := by
        rw [volume_layerWindow hL, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ∫⁻ _ in layerWindow e L, ENNReal.ofReal (2 * r ^ 2 / L ^ 3 * e) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in layerWindow e L,
          ENNReal.ofReal (LQGMetric.KilledHeat.killedHeat (sqOpen 0 L) t z w) :=
        setLIntegral_mono' (measurableSet_layerWindow e L) fun w hw =>
          ENNReal.ofReal_le_ofReal (hbound w hw)

end MatedCRT.PeanosphereTriplePoints
