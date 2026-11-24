import MatedCRT.FirstPass.Derived.ChartTransportMeasurable
import HarmonicBalls.Defs.Green
import LatticeProb.Bonanno.LQGMetric.Complex.HarmonicComp
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Conformal invariance of the Green function under an inverse chart

Step R2 of the Revuz route to Berestycki (2015), Theorem 1.3: the Green function of a bounded open set `U` is the
Green function of the unit disc transported by an inverse chart `ψ` of `U`,
`G_U(x, y) = G_𝔻(ψ x, ψ y)` for `x, y ∈ U` (Armitage–Gardiner, *Classical potential theory*, §4.1, with the Green
function defined through the greatest harmonic minorant of the Newtonian kernel, as in `HarmonicBalls.greenFunction`).

The proof is analytic: harmonic functions compose with holomorphic maps (`LQGMetric.harmonicOnNhd_comp_holo`), so the
greatest harmonic minorants on `𝔻` and on `U` correspond under `ψ` and its inverse `φ = chartMap U ψ`
(`greatestHarmonicMinorant_comp_of_biholomorphic`), and the Newtonian kernels differ by the harmonic function
`y ↦ -(2π)⁻¹ log |(ψ y - ψ x) / (y - x)|` (`chartGreenCorrector`), which passes through the greatest harmonic minorant
(`greatestHarmonicMinorant_add_harmonic`).

## Main statements

* `IsInverseChart.hasDerivAt_chartMap`, `IsInverseChart.differentiableOn_chartMap`: the inverse `φ` of an inverse
  chart is holomorphic on the unit disc, with `φ'(w) = ψ'(φ w)⁻¹`.
* `greatestHarmonicMinorant_comp_of_biholomorphic`: greatest harmonic minorants commute with biholomorphic maps.
* `greatestHarmonicMinorant_add_harmonic`: adding a harmonic function to the majorant adds it to the greatest
  harmonic minorant.
* `greenFunction_chart`: `G_𝔻(ψ x, ψ y) = G_U(x, y)` for `x, y ∈ U`.
-/

set_option autoImplicit false

open Set Filter Topology InnerProductSpace
open _root_.HarmonicBalls

namespace MatedCRT

/-! ### The inverse of an inverse chart is holomorphic -/

section ChartMap

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The inverse `φ = chartMap U ψ` of an inverse chart has derivative `ψ'(φ w)⁻¹` at every point `w` of the unit
disc. -/
theorem IsInverseChart.hasDerivAt_chartMap (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (chartMap U ψ) (deriv ψ (chartMap U ψ w))⁻¹ w := by
  have hmem := hψ.chartMap_mem hw
  have hc : ContinuousAt (chartMap U ψ) w :=
    (hψ.continuousOn_chartMap hU hUb).continuousAt (Metric.isOpen_ball.mem_nhds hw)
  have hd : HasDerivAt ψ (deriv ψ (chartMap U ψ w)) (chartMap U ψ w) :=
    (hψ.differentiableOn.differentiableAt (hU.mem_nhds hmem)).hasDerivAt
  refine hd.of_local_left_inverse hc (hψ.deriv_ne_zero hU hmem) ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
  exact hψ.apply_chartMap hv

/-- The inverse `φ = chartMap U ψ` of an inverse chart is holomorphic on the unit disc. -/
theorem IsInverseChart.differentiableOn_chartMap (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) : DifferentiableOn ℂ (chartMap U ψ) (Metric.ball (0 : ℂ) 1) := fun _ hw =>
  (hψ.hasDerivAt_chartMap hU hUb hw).differentiableAt.differentiableWithinAt

end ChartMap

/-! ### Greatest harmonic minorants under biholomorphic maps -/

/-- Greatest harmonic minorants depend only on the majorant on the set. -/
theorem greatestHarmonicMinorant_congr {O : Set ℂ} {u u' : ℂ → EReal} (h : ∀ y ∈ O, u y = u' y) :
    greatestHarmonicMinorant O u = greatestHarmonicMinorant O u' := by
  have hm : ∀ k : ℂ → ℝ, IsHarmonicMinorant O u k ↔ IsHarmonicMinorant O u' k := fun k =>
    and_congr_right fun _ => forall₂_congr fun y hy => by rw [h y hy]
  funext y
  apply le_antisymm
  · exact iSup₂_le fun k hk => ((hm k).1 hk).le_greatestHarmonicMinorant y
  · exact iSup₂_le fun k hk => ((hm k).2 hk).le_greatestHarmonicMinorant y

/-- **Greatest harmonic minorants commute with biholomorphic maps.** If `ψ : U → V` is holomorphic with holomorphic
inverse `φ : V → U`, then the greatest harmonic minorant of `u` on `V` at `ψ y` is the greatest harmonic minorant of
`u ∘ ψ` on `U` at `y`. -/
theorem greatestHarmonicMinorant_comp_of_biholomorphic {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {ψ φ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ U) (hφ : DifferentiableOn ℂ φ V) (hψV : MapsTo ψ U V)
    (hφU : MapsTo φ V U) (hψφ : ∀ w ∈ V, ψ (φ w) = w) (hφψ : ∀ y ∈ U, φ (ψ y) = y) (u : ℂ → EReal)
    {y : ℂ} (hy : y ∈ U) :
    greatestHarmonicMinorant V u (ψ y) = greatestHarmonicMinorant U (fun y' => u (ψ y')) y := by
  apply le_antisymm
  · apply iSup₂_le
    intro h hh
    have hv : IsHarmonicMinorant U (fun y' => u (ψ y')) (h ∘ ψ) :=
      ⟨_root_.LQGMetric.harmonicOnNhd_comp_holo hV hU hh.1 hψ hψV, fun y' hy' => hh.2 (ψ y') (hψV hy')⟩
    exact hv.le_greatestHarmonicMinorant y
  · apply iSup₂_le
    intro k hk
    have hv : IsHarmonicMinorant V u (k ∘ φ) := by
      refine ⟨_root_.LQGMetric.harmonicOnNhd_comp_holo hU hV hk.1 hφ hφU, fun w hw => ?_⟩
      have h1 : (k (φ w) : EReal) ≤ u (ψ (φ w)) := hk.2 (φ w) (hφU hw)
      rw [hψφ w hw] at h1
      exact h1
    have h2 := hv.le_greatestHarmonicMinorant (ψ y)
    simp only [Function.comp_apply, hφψ y hy] at h2
    exact h2

/-- **Adding a harmonic function to the majorant.** If `H` is harmonic on `O`, the greatest harmonic minorant of
`u + H` on `O` is the greatest harmonic minorant of `u` plus `H`. -/
theorem greatestHarmonicMinorant_add_harmonic {O : Set ℂ} (u : ℂ → EReal) {H : ℂ → ℝ}
    (hH : HarmonicOnNhd H O) (y : ℂ) :
    greatestHarmonicMinorant O (fun z => u z + (H z : EReal)) y =
      greatestHarmonicMinorant O u y + (H y : EReal) := by
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + ((H y : ℝ) : EReal)
      invFun := fun x => x - ((H y : ℝ) : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe (H y)).add_le_add_iff_right }
  change greatestHarmonicMinorant O (fun z => u z + (H z : EReal)) y =
    e (greatestHarmonicMinorant O u y)
  unfold greatestHarmonicMinorant
  rw [e.map_iSup₂]
  apply le_antisymm
  · apply iSup₂_le
    intro h hh
    have hv : IsHarmonicMinorant O u (fun z => h z - H z) := by
      constructor
      · intro z hz
        exact (hh.1 z hz).sub (hH z hz)
      · intro z hz
        change ((h z - H z : ℝ) : EReal) ≤ u z
        rw [EReal.coe_sub]
        exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 (hh.2 z hz)
    have hvle : ((h y - H y : ℝ) : EReal) + ((H y : ℝ) : EReal) ≤
        ⨆ j, ⨆ (_ : IsHarmonicMinorant O u j), (j y : EReal) + ((H y : ℝ) : EReal) :=
      le_iSup_of_le (fun z => h z - H z) (le_iSup_of_le hv le_rfl)
    have he : ((h y - H y : ℝ) : EReal) + ((H y : ℝ) : EReal) = (h y : EReal) := by
      rw [← EReal.coe_add, sub_add_cancel]
    rw [he] at hvle
    exact hvle
  · apply iSup₂_le
    intro h hh
    have hv : IsHarmonicMinorant O (fun z => u z + (H z : EReal)) (fun z => h z + H z) := by
      constructor
      · intro z hz
        exact (hh.1 z hz).add (hH z hz)
      · intro z hz
        change ((h z + H z : ℝ) : EReal) ≤ u z + (H z : EReal)
        rw [EReal.coe_add]
        exact add_le_add (hh.2 z hz) le_rfl
    exact le_iSup_of_le (fun z => h z + H z) (le_iSup_of_le hv (le_of_eq (EReal.coe_add (h y) (H y)).symm))

/-! ### The Green function under an inverse chart -/

/-- The logarithmic corrector of an inverse chart `ψ` with pole `x`: `y ↦ -(2π)⁻¹ log |(ψ y - ψ x) / (y - x)|`
(with the value `-(2π)⁻¹ log |ψ'(x)|` at `y = x`), the difference of the Newtonian kernels with poles `ψ x` and `x`
evaluated at `ψ y` and `y`. -/
noncomputable def chartGreenCorrector (ψ : ℂ → ℂ) (x y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log ‖dslope ψ x y‖

section Green

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The difference quotient of an inverse chart does not vanish on its domain. -/
theorem IsInverseChart.dslope_ne_zero (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {x y : ℂ} (hx : x ∈ U)
    (hy : y ∈ U) : dslope ψ x y ≠ 0 := by
  rcases eq_or_ne y x with rfl | hyx
  · rw [dslope_same]
    exact hψ.deriv_ne_zero hU hy
  · rw [dslope_of_ne _ hyx, slope_def_field]
    have hne : ψ y ≠ ψ x := fun h => hyx (hψ.injOn (subset_closure hy) (subset_closure hx) h)
    exact div_ne_zero (sub_ne_zero.2 hne) (sub_ne_zero.2 hyx)

/-- The logarithmic corrector is harmonic on the domain of the chart. -/
theorem harmonicOnNhd_chartGreenCorrector (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    HarmonicOnNhd (chartGreenCorrector ψ x) U := by
  intro y hy
  have hd : DifferentiableOn ℂ (dslope ψ x) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hx)).2 hψ.differentiableOn
  have ha : AnalyticAt ℂ (dslope ψ x) y := hd.analyticAt (hU.mem_nhds hy)
  have h1 := (ha.harmonicAt_log_norm (hψ.dslope_ne_zero hU hx hy)).const_smul (c := -(2 * Real.pi)⁻¹)
  convert h1 using 1
  funext u
  simp [chartGreenCorrector, smul_eq_mul]

/-- The Newtonian kernels with poles `ψ x` and `x` differ by the corrector: for `x ≠ y` in `U`,
`N(ψ x, ψ y) = N(x, y) - (2π)⁻¹ log |(ψ y - ψ x) / (y - x)|`. -/
theorem newtonKernel_chart (hψ : IsInverseChart U z ψ) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U)
    (hyx : y ≠ x) : newtonKernel (ψ x) (ψ y) = newtonKernel x y + chartGreenCorrector ψ x y := by
  have hxy : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyx)
  have hψne : ψ x - ψ y ≠ 0 :=
    sub_ne_zero.2 fun h => hyx (hψ.injOn (subset_closure hy) (subset_closure hx) h.symm)
  have hd : ‖dslope ψ x y‖ = ‖ψ x - ψ y‖ / ‖x - y‖ := by
    rw [dslope_of_ne _ hyx, slope_def_field, norm_div, norm_sub_rev (ψ y) (ψ x), norm_sub_rev y x]
  simp only [newtonKernel, chartGreenCorrector]
  rw [hd, Real.log_div (norm_ne_zero_iff.2 hψne) (norm_ne_zero_iff.2 hxy)]
  ring

/-- The extended Newtonian kernels with poles `ψ x` and `x` differ by the corrector on `U` (both are `+∞` at the
pole). -/
theorem newtonKernelEReal_chart (hψ : IsInverseChart U z ψ) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    newtonKernelEReal (ψ x) (ψ y) = newtonKernelEReal x y + (chartGreenCorrector ψ x y : EReal) := by
  rcases eq_or_ne y x with rfl | hyx
  · simp [newtonKernelEReal]
  · have hψne : ψ y ≠ ψ x := fun h => hyx (hψ.injOn (subset_closure hy) (subset_closure hx) h)
    simp only [newtonKernelEReal, hψne, hyx, ↓reduceIte]
    rw [newtonKernel_chart hψ hx hy hyx, EReal.coe_add]

/-- **Conformal invariance of the Green function under an inverse chart.** For a bounded open set `U` with inverse
chart `ψ` and `x, y ∈ U`, `G_𝔻(ψ x, ψ y) = G_U(x, y)`. -/
theorem greenFunction_chart (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    greenFunction (Metric.ball 0 1) (ψ x) (ψ y) = greenFunction U x y := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [greenFunction_self, greenFunction_self]
  have hψxy : ψ x ≠ ψ y := fun h => hxy (hψ.injOn (subset_closure hx) (subset_closure hy) h)
  have hg : greatestHarmonicMinorant (Metric.ball 0 1) (newtonKernelEReal (ψ x)) (ψ y) =
      greatestHarmonicMinorant U (newtonKernelEReal x) y + (chartGreenCorrector ψ x y : EReal) := by
    rw [greatestHarmonicMinorant_comp_of_biholomorphic hU Metric.isOpen_ball hψ.differentiableOn
      (hψ.differentiableOn_chartMap hU hUb) hψ.mapsTo_ball (fun _ hw => hψ.chartMap_mem hw)
      (fun _ hw => hψ.apply_chartMap hw) (fun _ hw => hψ.chartMap_apply hw) _ hy]
    rw [greatestHarmonicMinorant_congr
      (u' := fun y' => newtonKernelEReal x y' + (chartGreenCorrector ψ x y' : EReal))
      (fun _ hw => newtonKernelEReal_chart hψ hx hw)]
    exact greatestHarmonicMinorant_add_harmonic _ (harmonicOnNhd_chartGreenCorrector hψ hU hx) y
  obtain ⟨r, hr⟩ := hUb.subset_closedBall x
  have hbot : greatestHarmonicMinorant U (newtonKernelEReal x) y ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      ((isHarmonicMinorant_const_newtonKernelEReal hr).le_greatestHarmonicMinorant y)
  have htop : greatestHarmonicMinorant U (newtonKernelEReal x) y ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [newtonKernelEReal, Ne.symm hxy]) (greatestHarmonicMinorant_le hy)
  rw [greenFunction, greenFunction, ite_eq_left ⟨hψ.mapsTo_ball hx, hψ.mapsTo_ball hy, hψxy⟩,
    ite_eq_left ⟨hx, hy, hxy⟩, hg, newtonKernel_chart hψ hx hy (Ne.symm hxy),
    EReal.toReal_add htop hbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  ring

end Green

end MatedCRT
