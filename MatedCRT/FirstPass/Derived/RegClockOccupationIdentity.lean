import MatedCRT.FirstPass.Derived.RegClockIntegralMeasurable
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockIdentificationConcrete
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof

/-!
# The regularized clock integral as an integral against the occupation measure

Let `hc` be continuous circle averages of a whole-plane field `h^ℂ` with `h^ℂ_1(0) = 0`, and let
`h = h^ℂ - γ log|·|`. For a path `b` that stays in `B_r(z) ⊆ B_ρ(0)` before the time `σ(b)`, a scale
`0 < ε < 1 - ρ` and a weight `g` vanishing on `B̄_ε(0)`, the integral of `g(b_u)` against the regularized clock
`ε^{γ²/2} e^{γ h_ε(b_u)} du` on `[0, σ(b)]` is the integral of the singular weight `g(x) |x|^{-γ²}` times the
normalized exponential `ε^{γ²/2} e^{γ (h^ℂ_ε(x) - h^ℂ_1(0))}` against the occupation measure
`ν_b = (du|_{[0, σ(b)]}) ∘ b⁻¹` of the path. This is the form in which the `L¹` increment bound of circle-average
Gaussian multiplicative chaos over a general base measure applies path by path.

## Main results

* `singularWeight γ g x = g(x) e^{-γ² log ‖x‖}`.
* `setLIntegral_regClockMeasure_eq_lintegral_occupation`: the identity as lower Lebesgue integrals.
* `setLIntegral_regClockMeasure_toReal_eq_integral_occupation`: for `g ≥ 0`, the identity of real integrals.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The singular weight `g(x) |x|^{-γ²} = g(x) e^{-γ² log ‖x‖}`: the factor `e^{-γ² log |x|}` is the contribution of
the logarithmic singularity `-γ log|·|` to `e^{γ h_ε(x)}` at scales `ε ≤ ‖x‖`. -/
noncomputable def singularWeight (γ : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  g x * Real.exp (-(γ ^ 2 * Real.log ‖x‖))

lemma measurable_singularWeight (γ : ℝ) {g : ℂ → ℝ} (hg : Measurable g) : Measurable (singularWeight γ g) := by
  unfold singularWeight
  exact hg.mul (Real.measurable_exp.comp ((Real.measurable_log.comp measurable_norm).const_mul _).neg)

/-- Pointwise form of the identity: for `‖x‖ < 1 - ε` and `g` vanishing unless `ε ≤ ‖x‖`, the regularized density
of `h = h^ℂ - γ log|·|` times `g(x)` is the singular weight times the normalized exponential of `h^ℂ`. -/
lemma ofReal_regDensity_mul_ofReal_eq (γ : ℝ) {hc : ℝ → ℂ → ℝ} (h10 : hc 1 0 = 0) {ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖) (x : ℂ) :
    ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage γ hc ε x)) * ENNReal.ofReal (g x) =
      ENNReal.ofReal (singularWeight γ g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - hc 1 0)))) := by
  have hA : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage γ hc ε x) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hA]
  congr 1
  by_cases hgx : g x = 0
  · simp [singularWeight, hgx]
  have hle := hgε x hgx
  unfold fieldCircleAverage singularWeight
  rw [circleAverage_log_norm_eq hε x, max_eq_left hle, h10, sub_zero,
    show γ * (hc ε x - γ * Real.log ‖x‖) = γ * hc ε x + -(γ ^ 2 * Real.log ‖x‖) by ring, Real.exp_add]
  ring

/-- **The regularized clock integral against the occupation measure.** If the circle averages `hc` are continuous
on `(0, ∞) × ℂ` with `hc 1 0 = 0`, `B_r(z) ⊆ B_ρ(0)`, `0 < ε < 1 - ρ`, `g` is measurable and vanishes unless
`ε ≤ ‖x‖`, and the path stays in `B_r(z)` before `σ(b)`, then
`∫_{[0,σ(b)]} g(b_u) dF_ε(u) = ∫ g(x) |x|^{-γ²} ε^{γ²/2} e^{γ (h^ℂ_ε(x) - h^ℂ_1(0))} dν_b(x)`, where `F_ε` is the
regularized clock of `h = h^ℂ - γ log|·|` and `ν_b` is the image of Lebesgue measure on `[0, σ(b)]` under `b`. -/
theorem setLIntegral_regClockMeasure_eq_lintegral_occupation (γ : ℝ) {hc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ)) (h10 : hc 1 0 = 0)
    {ρ r ε : ℝ} {z : ℂ} (hball : ball z r ⊆ ball 0 ρ) (hε : 0 < ε) (hερ : ε < 1 - ρ)
    {g : ℂ → ℝ} (hg : Measurable g) (hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖)
    (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (hb : ∀ s : ℝ≥0, s < σ b → b s ∈ ball z r) :
    ∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u))
        ∂regClockMeasure γ ε (fun q : UnitDiskCircleIndex => fieldCircleAverage γ hc q.1.1 q.1.2) σ b =
      ∫⁻ x, ENNReal.ofReal (singularWeight γ g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - hc 1 0))))
        ∂((lebNN.restrict (Icc 0 (σ b))).map fun u => b u) := by
  set ψ : UnitDiskCircleIndex → ℝ := fun q => fieldCircleAverage γ hc q.1.1 q.1.2 with hψdef
  have hF := continuousOn_fieldCircleAverage (α₀ := γ) hcont
  have hsub : (UnitDiskCircleIndex : Set (ℝ × ℂ)) ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨hq.1, mem_univ _⟩
  have hψ : Continuous ψ := continuousOn_iff_continuous_domRestrict.1 (hF.mono hsub)
  have hxc : Continuous fun x : ℂ => hc ε x :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hε, mem_univ x⟩)
  have hbm : Measurable fun u : ℝ≥0 => b u := (map_continuous b).measurable
  have hHm : Measurable fun x : ℂ =>
      ENNReal.ofReal (singularWeight γ g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - hc 1 0)))) :=
    ENNReal.measurable_ofReal.comp ((measurable_singularWeight γ hg).mul
      (measurable_const.mul (Real.measurable_exp.comp ((hxc.measurable.sub measurable_const).const_mul γ))))
  rw [setLIntegral_regClockMeasure_eq γ ε ψ σ b (F := fun u => ENNReal.ofReal (g (b u)))
      (ENNReal.measurable_ofReal.comp (hg.comp hbm)),
    lintegral_map hHm hbm]
  have hne : ∀ᵐ u ∂(lebNN.restrict (Icc 0 (σ b))), u ≠ σ b := by
    refine ae_restrict_of_ae ?_
    have h0 : lebNN {σ b} = 0 := lebNN_singleton (σ b)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with u hu
    exact hu
  refine lintegral_congr_ae ?_
  filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with u hu hmem
  have hlt : u < σ b := lt_of_le_of_ne hmem.2 hu
  have hnorm : ‖b u‖ < ρ := mem_ball_zero_iff.1 (hball (hb u hlt))
  rw [circleAverageRep_eq_of_lt (ρ₂ := 1 - ε) (H := fieldCircleAverage γ hc) hψ (fun _ => rfl) hε (by linarith)
    (by linarith)]
  exact ofReal_regDensity_mul_ofReal_eq γ h10 hε hgε (b u)

/-- **Real form of the occupation identity.** Under the hypotheses of
`setLIntegral_regClockMeasure_eq_lintegral_occupation` and `g ≥ 0`, the real regularized clock integral is the
Bochner integral of `g(x) |x|^{-γ²} ε^{γ²/2} e^{γ (h^ℂ_ε(x) - h^ℂ_1(0))}` against the occupation measure. -/
theorem setLIntegral_regClockMeasure_toReal_eq_integral_occupation (γ : ℝ) {hc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hc p.1 p.2) (Ioi 0 ×ˢ univ)) (h10 : hc 1 0 = 0)
    {ρ r ε : ℝ} {z : ℂ} (hball : ball z r ⊆ ball 0 ρ) (hε : 0 < ε) (hερ : ε < 1 - ρ)
    {g : ℂ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖)
    (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (hb : ∀ s : ℝ≥0, s < σ b → b s ∈ ball z r) :
    (∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u))
        ∂regClockMeasure γ ε (fun q : UnitDiskCircleIndex => fieldCircleAverage γ hc q.1.1 q.1.2) σ b).toReal =
      ∫ x, singularWeight γ g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - hc 1 0)))
        ∂((lebNN.restrict (Icc 0 (σ b))).map fun u => b u) := by
  have hxc : Continuous fun x : ℂ => hc ε x :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hε, mem_univ x⟩)
  have hm : Measurable fun x : ℂ =>
      singularWeight γ g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - hc 1 0))) :=
    (measurable_singularWeight γ hg).mul
      (measurable_const.mul (Real.measurable_exp.comp ((hxc.measurable.sub measurable_const).const_mul γ)))
  have h0 : ∀ x, 0 ≤ singularWeight γ g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ε x - hc 1 0))) := fun x =>
    mul_nonneg (mul_nonneg (hg0 x) (Real.exp_pos _).le)
      (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hm.aestronglyMeasurable,
    setLIntegral_regClockMeasure_eq_lintegral_occupation γ hcont h10 hball hε hερ hg hgε σ b hb]

end MatedCRT.KilledOccupation
