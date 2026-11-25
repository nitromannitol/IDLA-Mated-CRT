import MatedCRT.FirstPass.Derived.ChartGreenFunction
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward

/-!
# Transported rates as image measures under an inverse chart

Let `ψ` be an inverse chart of the open set `U` (a conformal map of `U` onto the unit disc) and `ρ` a rate on `U`.
The transported rate `ρ̃(v) = ρ(φ v) / |ψ'(φ v)|²` on the unit disc, `φ = ψ⁻¹`, is the density of the image under `ψ`
of the measure `ρ(x) dx` on `U`: by the change of variables `v = ψ(x)`, `dv = |ψ'(x)|² dx`,
`∫_{B(0,1)} F(v) ρ̃(v) dv = ∫_U F(ψ x) ρ(x) dx` (`lintegral_ball_chartTransportRate`), that is,
`ρ̃(v) dv = ψ_* (ρ(x) dx |_U)` on the disc (`withDensity_chartTransportRate_eq_map`).

On every closed disc `B̄(0, R)`, `R < 1`, the conformal map `φ` is Lipschitz (its derivative is holomorphic, hence
bounded on compact sets; `IsInverseChart.exists_norm_chartMap_sub_le`), so the preimage under `ψ` of a disc
`B(x, s) ⊆ B̄(0, R)` lies in the disc `B(φ x, L s)` (`IsInverseChart.inter_preimage_ball_subset`): local power bounds
on the masses of discs (Frostman-type bounds) pass from a measure on `U` to its image on the disc.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- **Change of variables for transported rates.** For an inverse chart `ψ` of the open set `U`, a rate `ρ` and a
weight `F ≥ 0`: `∫_{B(0,1)} F(v) ρ̃(v) dv = ∫_U F(ψ x) ρ(x) dx`, where `ρ̃ = chartTransportRate U ψ ρ`. -/
theorem lintegral_ball_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (ρ : ℂ → ℝ)
    (F : ℂ → ℝ≥0∞) :
    ∫⁻ v in ball (0 : ℂ) 1, F v * ENNReal.ofReal (chartTransportRate U ψ ρ v) =
      ∫⁻ x in U, F (ψ x) * ENNReal.ofReal (ρ x) := by
  have hinj : InjOn ψ U := hψ.injOn.mono subset_closure
  have hderiv : ∀ x ∈ U, HasFDerivWithinAt ψ (fderiv ℝ ψ x) U x := fun x hx =>
    ((hψ.differentiableOn.differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [← hψ.image_eq, lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hU.measurableSet hderiv hinj]
  refine setLIntegral_congr_fun hU.measurableSet (fun x hx => ?_)
  have hd : DifferentiableAt ℂ ψ x := hψ.differentiableOn.differentiableAt (hU.mem_nhds hx)
  have hne : ‖deriv ψ x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (hψ.deriv_ne_zero hU hx))
  have hpos : 0 ≤ ‖deriv ψ x‖ ^ 2 := by positivity
  have hcalc : ‖deriv ψ x‖ ^ 2 * (ρ x / ‖deriv ψ x‖ ^ 2) = ρ x := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hne
  simp only [QuantumZipper.abs_det_fderiv_eq_normSq hd, chartTransportRate, hψ.chartMap_apply hx]
  rw [mul_left_comm, ← ENNReal.ofReal_mul hpos, hcalc]

/-- **The transported rate is the density of the image measure.** On the unit disc, `ρ̃(v) dv` is the image under
the inverse chart `ψ` of the measure `ρ(x) dx` restricted to `U`. -/
theorem withDensity_chartTransportRate_eq_map (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (ρ : ℂ → ℝ) :
    (volume.restrict (ball (0 : ℂ) 1)).withDensity (fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v)) =
      ((volume.withDensity fun x => ENNReal.ofReal (ρ x)).restrict U).map ψ := by
  ext A hA
  have hpre : MeasurableSet (ψ ⁻¹' A) := ψ.continuous.measurable hA
  have h1 := lintegral_ball_chartTransportRate hψ hU ρ (A.indicator 1)
  rw [withDensity_apply _ hA, Measure.map_apply ψ.continuous.measurable hA, Measure.restrict_apply hpre,
    withDensity_apply _ (hpre.inter hU.measurableSet), ← lintegral_indicator hA]
  have e1 : ∫⁻ v, A.indicator (fun v => ENNReal.ofReal (chartTransportRate U ψ ρ v)) v
      ∂(volume.restrict (ball (0 : ℂ) 1)) =
      ∫⁻ v in ball (0 : ℂ) 1, A.indicator 1 v * ENNReal.ofReal (chartTransportRate U ψ ρ v) := by
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A <;> simp [hv]
  have e2 : ∫⁻ x in U, A.indicator 1 (ψ x) * ENNReal.ofReal (ρ x) =
      ∫⁻ x in ψ ⁻¹' A ∩ U, ENNReal.ofReal (ρ x) := by
    rw [← Measure.restrict_restrict hpre, ← lintegral_indicator hpre]
    refine lintegral_congr fun x => ?_
    by_cases hx : ψ x ∈ A <;> simp [hx]
  exact e1.trans (h1.trans e2)

/-- **The conformal map of an inverse chart is Lipschitz on smaller closed discs.** -/
theorem IsInverseChart.exists_norm_chartMap_sub_le (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {R : ℝ} (hR : R < 1) :
    ∃ L : ℝ, 0 < L ∧ ∀ v ∈ closedBall (0 : ℂ) R, ∀ w ∈ closedBall (0 : ℂ) R,
      ‖chartMap U ψ v - chartMap U ψ w‖ ≤ L * ‖v - w‖ := by
  have hd := hψ.differentiableOn_chartMap hU hUb
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR
  have hcont : ContinuousOn (deriv (chartMap U ψ)) (closedBall (0 : ℂ) R) :=
    ((hd.deriv isOpen_ball).continuousOn).mono hsub
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcont
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun v hv w hw => ?_⟩
  exact (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hd.differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
    (fun x hx => (hC x hx).trans (le_max_left _ _)) hw hv

/-- **Preimages of small discs under an inverse chart.** If the conformal map `φ = chartMap U ψ` is `L`-Lipschitz on
`B̄(0, R)` and `B̄(x, s) ⊆ B̄(0, R)`, the points of `U` mapped by `ψ` into `B(x, s)` lie in `B(φ x, L s)`. -/
theorem IsInverseChart.inter_preimage_ball_subset (hψ : IsInverseChart U z ψ) {L R : ℝ} (hL0 : 0 < L)
    (hL : ∀ v ∈ closedBall (0 : ℂ) R, ∀ w ∈ closedBall (0 : ℂ) R,
      ‖chartMap U ψ v - chartMap U ψ w‖ ≤ L * ‖v - w‖)
    {x : ℂ} {s : ℝ} (hs : 0 ≤ s) (hxs : closedBall x s ⊆ closedBall 0 R) :
    U ∩ ψ ⁻¹' ball x s ⊆ ball (chartMap U ψ x) (L * s) := by
  rintro y ⟨hyU, hy⟩
  have hy' : ψ y ∈ closedBall (0 : ℂ) R := hxs (ball_subset_closedBall hy)
  have hx : x ∈ closedBall (0 : ℂ) R := hxs (mem_closedBall_self hs)
  rw [mem_preimage, mem_ball, dist_eq_norm] at hy
  rw [mem_ball, dist_eq_norm]
  calc ‖y - chartMap U ψ x‖ = ‖chartMap U ψ (ψ y) - chartMap U ψ x‖ := by rw [hψ.chartMap_apply hyU]
    _ ≤ L * ‖ψ y - x‖ := hL _ hy' _ hx
    _ < L * s := mul_lt_mul_of_pos_left hy hL0

/-- **Disc masses of an image measure under an inverse chart.** With `φ` `L`-Lipschitz on `B̄(0, R)` and
`B̄(x, s) ⊆ B̄(0, R)`, the image under `ψ` of a measure `m` restricted to `U` gives `B(x, s)` at most the mass
`m(B(φ x, L s))`. -/
theorem IsInverseChart.map_restrict_ball_le (hψ : IsInverseChart U z ψ) (m : Measure ℂ)
    {L R : ℝ} (hL0 : 0 < L)
    (hL : ∀ v ∈ closedBall (0 : ℂ) R, ∀ w ∈ closedBall (0 : ℂ) R,
      ‖chartMap U ψ v - chartMap U ψ w‖ ≤ L * ‖v - w‖)
    {x : ℂ} {s : ℝ} (hs : 0 ≤ s) (hxs : closedBall x s ⊆ closedBall 0 R) :
    (m.restrict U).map ψ (ball x s) ≤ m (ball (chartMap U ψ x) (L * s)) := by
  rw [Measure.map_apply ψ.continuous.measurable measurableSet_ball,
    Measure.restrict_apply (ψ.continuous.measurable measurableSet_ball), inter_comm]
  exact measure_mono (hψ.inter_preimage_ball_subset hL0 hL hs hxs)

end MatedCRT
