import MatedCRT.FirstPass.Derived.ConeReferenceData
import MatedCRT.Proofs.Field.WholePlaneBrownian

/-!
# The radial process of the explicit quantum cone data

Let `h^ℂ` be a whole-plane Gaussian free field (normalized so that `h^ℂ_1(0) = 0`) with circle averages `c₁`, and `w` a
continuous path. The cone data `coneRefCircle γ c₁ w` (`ConeReferenceData.lean`) are the circle averages of
`h^ℂ - γ log |·|` plus those of the radial correction `coneRefField`, which vanishes on the unit disk and equals
`(w(log ρ) - w(0)) - (h^ℂ_ρ(0) - h^ℂ_1(0))` at `|x| = ρ ≥ 1`.

* `radialProcess_coneRefCircle`: the radial process of the cone data is exactly
  `(t ↦ h^ℂ_{e^{-t}}(0) + γ t, s ↦ w(s) - w(0) + h^ℂ_1(0) - γ s)`, for every sample.
* `isBMConditionedPositive_ae_eval_zero`: a law `ν` of the conditioned Brownian motion starts at `0` almost surely.
* `map_radialProcess_coneRefCircle`: under the product of the law of `h^ℂ` and `ν`, the radial process of the cone
  data has the law `quantumConeRadialLaw γ ν` of the process `A` of Definition 2.1.
-/

open MeasureTheory ProbabilityTheory MarkovProcess HarmonicBalls
open scoped NNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- The average of `log |·|` over a circle centred at the origin of radius `ρ ≥ 0` is `log ρ`. -/
theorem circleAverage_log_norm_zero {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) 0 ρ = Real.log ρ :=
  Real.circleAverage_const_on_circle fun y hy => by
    rw [mem_sphere_zero_iff_norm, abs_of_nonneg hρ] at hy
    rw [hy]

/-- The cone circle average at the origin: the one of `h^ℂ - γ log |·|` plus the radial correction. -/
theorem coneRefCircle_norm_zero (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coneRefCircle γ hcirc w ρ 0 =
      hcirc ρ 0 - γ * Real.log ρ + coneRefProfile (fun ρ => hcirc ρ 0) w ρ := by
  have h2 : Real.circleAverage (coneRefField hcirc w) 0 ρ = coneRefProfile (fun ρ => hcirc ρ 0) w ρ :=
    Real.circleAverage_const_on_circle fun y hy => by
      rw [mem_sphere_zero_iff_norm, abs_of_nonneg hρ] at hy
      simp [coneRefField, hy]
  rw [coneRefCircle, fieldCircleAverage, circleAverage_log_norm_zero hρ, h2]

/-- The radial process of the cone data, in closed form: the pair of paths
`t ↦ h^ℂ_{e^{-t}}(0) + γ t` and `s ↦ w(s) - w(0) + h^ℂ_1(0) - γ s`. -/
noncomputable def coneRefRadial (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) :
    (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  (fun t => hcirc (Real.exp (-(t : ℝ))) 0 + γ * t, fun s => w s - w 0 + hcirc 1 0 - γ * s)

/-- **The radial process of the cone data**, for every sample. -/
theorem radialProcess_coneRefCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) :
    radialProcess (coneRefCircle γ hcirc w) = coneRefRadial γ hcirc w := by
  refine Prod.ext (funext fun t => ?_) (funext fun s => ?_)
  · have hle : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 t.2)
    simp only [radialProcess, coneRefRadial]
    rw [coneRefCircle_norm_zero γ hcirc w (Real.exp_pos _).le, coneRefProfile_of_le hle, Real.log_exp]
    ring
  · have hge : 1 ≤ Real.exp (s : ℝ) := Real.one_le_exp s.2
    simp only [radialProcess, coneRefRadial]
    rw [coneRefCircle_norm_zero γ hcirc w (Real.exp_pos _).le, Real.log_exp]
    simp only [coneRefProfile, max_eq_left hge, Real.log_exp, Real.toNNReal_coe]
    ring

/-- **The conditioned Brownian motion starts at `0`.** A law `ν` of the Brownian motion conditioned to stay positive
(a weak limit of Brownian motions started at `0` conditioned on positive-probability events) satisfies `w 0 = 0`
for `ν`-almost every path `w`. -/
theorem isBMConditionedPositive_ae_eval_zero {c : ℝ} {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive c ν) : ∀ᵐ w ∂ν, w 0 = 0 := by
  obtain ⟨hprob, hlim⟩ := hν
  have hcont : Continuous fun w : ContinuousPath ℝ => min 1 |w 0| :=
    continuous_const.min ((continuous_eval_const (0 : ℝ≥0)).abs)
  let f : ContinuousPath ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨_, hcont⟩ 1 fun a b => by
    have h0 : ∀ w : ContinuousPath ℝ, 0 ≤ min 1 |w 0| := fun w => le_min zero_le_one (abs_nonneg _)
    have h1 : ∀ w : ContinuousPath ℝ, min 1 |w 0| ≤ 1 := fun w => min_le_left _ _
    rw [Real.dist_eq, abs_le]
    constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith [h0 a, h0 b, h1 a, h1 b]
  have hf : ∀ w, f w = min 1 |w 0| := fun w => rfl
  have hzero : ∀ δ > (0 : ℝ), ∫ w, f w ∂((brownianMotion 0)[|stayAboveEvent c δ]) = 0 := by
    intro δ _
    refine integral_eq_zero_of_ae ?_
    filter_upwards [cond_absolutelyContinuous.ae_le MatedCRT.Field.brownian_coord_zero_ae] with w hw
    simp [hf, hw]
  have hint : ∫ w, f w ∂ν = 0 := by
    have := hprob
    refine tendsto_nhds_unique (hlim f) (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hzero δ hδ).symm
  have := hprob
  have hnn : 0 ≤ᵐ[ν] f := Filter.Eventually.of_forall fun w => by
    rw [hf]; exact le_min zero_le_one (abs_nonneg _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn (f.integrable ν)).1 hint] with w hw
  have hw' : min 1 |w 0| = 0 := by simpa [hf] using hw
  rcases min_choice 1 |w 0| with h | h
  · rw [h] at hw'; exact absurd hw' one_ne_zero
  · rw [h] at hw'; exact abs_eq_zero.1 hw'

section Law

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
  {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {c₁ : Ω₁ → ℝ → ℂ → ℝ}

/-- **The law of the radial process of the cone data.** If `h^ℂ` is a whole-plane GFF with circle averages `c₁` and
`ν` a law of the conditioned Brownian motion, then under `P₁ ⊗ ν` the radial process of the cone data has the law
`quantumConeRadialLaw γ ν` of the process `A` of Definition 2.1. -/
theorem map_radialProcess_coneRefCircle [IsProbabilityMeasure P₁] (hh : IsWholePlaneGFF P₁ hC₁ c₁) (γ : ℝ)
    {c : ℝ} {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive c ν) :
    (P₁.prod ν).map (fun ω : Ω₁ × ContinuousPath ℝ => radialProcess (coneRefCircle γ (c₁ ω.1) ω.2)) =
      quantumConeRadialLaw γ ν := by
  have := hν.1
  set Φ : Ω₁ → (ℝ≥0 → ℝ) := fun ω t => c₁ ω (Real.exp (-(t : ℝ))) 0 + γ * t with hΦdef
  set Ψ : ContinuousPath ℝ → (ℝ≥0 → ℝ) := fun w s => w s - γ * s with hΨdef
  have hrad : Measurable fun ω (t : ℝ≥0) => c₁ ω (Real.exp (-(t : ℝ))) 0 :=
    Measurable.of_eval fun t => hh.measurable_circle _ _ (Real.exp_pos _)
  have hG : Measurable fun (x : ℝ≥0 → ℝ) (t : ℝ≥0) => x t + γ * t :=
    Measurable.of_eval fun t => (measurable_pi_apply t).add_const _
  have hΦ : Measurable Φ := hG.comp hrad
  have hΨ : Measurable Ψ :=
    Measurable.of_eval fun s => (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).sub_const _
  have hae : ∀ᵐ ω ∂(P₁.prod ν), radialProcess (coneRefCircle γ (c₁ ω.1) ω.2) = (Φ ω.1, Ψ ω.2) := by
    have h1 : ∀ᵐ ω ∂(P₁.prod ν), c₁ ω.1 1 0 = 0 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hh.ae_circleAverage_one_zero
    have h2 : ∀ᵐ ω ∂(P₁.prod ν), ω.2 0 = 0 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
        (isBMConditionedPositive_ae_eval_zero hν)
    filter_upwards [h1, h2] with ω h1 h2
    rw [radialProcess_coneRefCircle]
    refine Prod.ext rfl (funext fun s => ?_)
    simp only [coneRefRadial, hΨdef, h1, h2, sub_zero, add_zero]
  rw [Measure.map_congr hae]
  have hprod : (P₁.prod ν).map (fun ω : Ω₁ × ContinuousPath ℝ => (Φ ω.1, Ψ ω.2)) =
      (P₁.map Φ).prod (ν.map Ψ) := (Measure.map_prod_map P₁ ν hΦ hΨ).symm
  rw [hprod, quantumConeRadialLaw]
  congr 1
  calc P₁.map Φ = (P₁.map fun ω (t : ℝ≥0) => c₁ ω (Real.exp (-(t : ℝ))) 0).map
        (fun (x : ℝ≥0 → ℝ) (t : ℝ≥0) => x t + γ * t) := (Measure.map_map hG hrad).symm
    _ = ((brownianMotion 0).map fun w (t : ℝ≥0) => w t).map
        (fun (x : ℝ≥0 → ℝ) (t : ℝ≥0) => x t + γ * t) := by
        rw [MatedCRT.Field.map_radial_eq_brownian hh]
    _ = (brownianMotion 0).map fun w (t : ℝ≥0) => w t + γ * t :=
        Measure.map_map hG (Measurable.of_eval fun t =>
          ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t)

end Law

end MatedCRT.FirstPass.Derived
