import MatedCRT.FirstPass.S2x.ConeScaleRadiusPos
import MatedCRT.FirstPass.S2x.BrownianNegativeDrift
import MatedCRT.FirstPass.S1c.RadialDivergence
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# The radial limits of the quantum cone and `ConeScaleRadiusPosStep` (PRO Section 2, hypothesis `hlim`)

Discharges the hypothesis `hlim` of `ae_coneScaleRadius_pos_of_limits` (ConeScaleRadiusPos.lean) and proves
`ConeScaleRadiusPosStep` from the corrected radial divergence `FrozenConeRadialDivergenceCorrected` alone.

Definition 2.1 (Duplantier-Miller-Sheffield, arXiv:1409.7055, Definition 4.10): the radial process of the cone is
`t ↦ h_{e^{-t}}(0) = B_t + γ t` (first coordinate of `radialProcess`, with `B` a standard Brownian motion) and
`s ↦ h_{e^s}(0) = B̂_s - γ s` (second coordinate, `B̂` of law `ν`, `IsBMConditionedPositive (Q - γ) ν`).

* Near `r = 0`: `h_r(0) + Q log r = B_t - (Q - γ) t` with `t = -log r → ∞`, which diverges to `-∞` almost surely by the
  Brownian negative drift `ae_brownian_lqgQ_drift_tendsto_atBot` (BrownianNegativeDrift.lean; Karatzas-Shreve, Chapter 2,
  Problem 9.3).
* Near `r = ∞`: `h_r(0) + Q log r = B̂_s + (Q - γ) s` with `s = log r → ∞`, which diverges to `+∞` almost surely by the
  corrected radial divergence `FrozenConeRadialDivergenceCorrected` (the named input, not proved here).

Both are transferred from the law `quantumConeRadialLaw γ ν` to `P` through the events of divergence along the rationals
(`RatDivergence`, countable and measurable on the raw product space), then passed to the reals by the almost sure
continuity of the circle average process (`IsQuantumCone.ae_continuousOn_circle`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open _root_.HarmonicBalls MarkovProcess
open scoped NNReal

namespace MatedCRT.FirstPass2x

/-- Divergence to `-∞` along the rationals of the first coordinate of the cone's radial law: if the Brownian path `w` satisfies
`w t - (Q - γ) t → -∞`, then `q ↦ -(w_q + γ q) + Q q` diverges to `+∞` along the rationals (`RatDivergence`). -/
lemma ratDivergence_neg_of_tendsto_shift (w : ℝ≥0 → ℝ) (γ Q : ℝ)
    (h : Tendsto (fun t : ℝ≥0 => w t - (Q - γ) * (t : ℝ)) atTop atBot) :
    RatDivergence (fun q : ℚ => -(w (q : ℝ).toNNReal + γ * (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) + Q * q) := by
  intro n
  obtain ⟨S, hS⟩ := eventually_atTop.1 (h.eventually (Iic_mem_atBot (-(n : ℝ))))
  obtain ⟨N, hSN⟩ := exists_nat_ge S
  refine ⟨N, fun q hq => ?_⟩
  have hq0' : (0 : ℚ) ≤ q := le_trans (Nat.cast_nonneg N) hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0'
  have hqq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = (q : ℝ) := Real.coe_toNNReal _ hq0
  have hNq : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hSN' : (S : ℝ) ≤ (N : ℝ) := by exact_mod_cast hSN
  have hSq : S ≤ (q : ℝ).toNNReal := by
    rw [← NNReal.coe_le_coe, hqq]
    exact hSN'.trans hNq
  have key : w (q : ℝ).toNNReal - (Q - γ) * (((q : ℝ).toNNReal : ℝ≥0) : ℝ) ≤ -(n : ℝ) := hS _ hSq
  show (n : ℝ) ≤ -(w (q : ℝ).toNNReal + γ * (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) + Q * (q : ℝ)
  rw [hqq] at key ⊢
  linarith

/-- Almost sure events of the first coordinate of a product law: the first marginal of `μ.prod ν'` is `μ`. -/
lemma ae_fst_prod_of_ae {μ ν' : Measure (ℝ≥0 → ℝ)} [SFinite ν'] {p : (ℝ≥0 → ℝ) → Prop} (hp : MeasurableSet {y | p y})
    (h : ∀ᵐ y ∂μ, p y) : ∀ᵐ x ∂(μ.prod ν'), p x.1 := by
  have h3 : ∀ᵐ y ∂((μ.prod ν').map Prod.fst), p y := by
    rw [Measure.map_fst_prod]
    exact Measure.ae_smul_measure h _
  exact (ae_map_iff measurable_fst.aemeasurable hp).1 h3

/-- The first coordinate of the cone's radial law, `t ↦ B_t + γ t`, diverges along the rationals almost surely: the
Brownian negative drift `B_t - (Q - γ) t → -∞` (`ae_brownian_lqgQ_drift_tendsto_atBot`) transferred through `B ↦ B + γ ·`. -/
lemma ae_ratDivergence_neg_quantumConeRadialLaw {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (ν : Measure (ContinuousPath ℝ)) [IsFiniteMeasure ν] :
    ∀ᵐ x ∂(quantumConeRadialLaw γ ν), RatDivergence (fun q : ℚ => -x.1 (q : ℝ).toNNReal + lqgQ γ * q) := by
  have hψ : Measurable (fun w : ContinuousPath ℝ => fun t : ℝ≥0 => w t + γ * (t : ℝ)) :=
    Measurable.of_eval fun t => ((continuous_eval_const t).measurable).add_const (γ * (t : ℝ))
  have hEm : MeasurableSet {y : ℝ≥0 → ℝ | RatDivergence (fun q : ℚ => -y (q : ℝ).toNNReal + lqgQ γ * q)} :=
    measurableSet_ratDivergence (fun (q : ℚ) (y : ℝ≥0 → ℝ) => -y (q : ℝ).toNNReal + lqgQ γ * q)
      fun q => ((measurable_pi_apply ((q : ℝ).toNNReal)).neg).add_const _
  have h1 : ∀ᵐ y ∂((brownianMotion (0 : ℝ)).map fun w (t : ℝ≥0) => w t + γ * (t : ℝ)),
      RatDivergence (fun q : ℚ => -y (q : ℝ).toNNReal + lqgQ γ * q) := by
    rw [ae_map_iff hψ.aemeasurable hEm]
    filter_upwards [MatedCRT.S2x.BrownianDrift.ae_brownian_lqgQ_drift_tendsto_atBot hγ0 hγ2] with w hw
    exact ratDivergence_neg_of_tendsto_shift w γ (lqgQ γ) hw
  unfold quantumConeRadialLaw
  exact ae_fst_prod_of_ae hEm h1

/-- The circle average radial process `(R_ω)` of a quantum cone is measurable (each coordinate is a product of
measurable circle averages at positive radii). -/
lemma measurable_radialProcess_of_quantumCone {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) :
    Measurable fun ω => radialProcess (hcirc ω) := by
  refine Measurable.prodMk (Measurable.of_eval fun t => ?_) (Measurable.of_eval fun s => ?_)
  · exact hcone.measurable_circle _ _ (Real.exp_pos _)
  · exact hcone.measurable_circle _ _ (Real.exp_pos _)

/-- Deterministic limit at `r → 0+` (`s = -log r → ∞`): if `c` is continuous on `(0, ∞)` and `s ↦ -c(e^{-s}) + Q s`
diverges to `+∞` along the rationals, then `c r + Q log r → -∞` as `r → 0+`. -/
lemma tendsto_log_circle_nhdsGT_zero {c : ℝ → ℝ} (hc : ContinuousOn c (Ioi 0)) (Q : ℝ)
    (h : RatDivergence (fun q : ℚ => -c (Real.exp (-(((q : ℝ).toNNReal : ℝ≥0) : ℝ))) + Q * q)) :
    Tendsto (fun r : ℝ => c r + Q * Real.log r) (𝓝[>] 0) atBot := by
  have hcomp : Continuous (fun s : ℝ => c (Real.exp (-s))) :=
    hc.comp_continuous (Real.continuous_exp.comp continuous_neg) (fun s => Real.exp_pos _)
  have hK : Continuous (fun s : ℝ => -c (Real.exp (-s)) + Q * s) :=
    hcomp.neg.add (continuous_const.mul continuous_id)
  have hKq : RatDivergence (fun q : ℚ => -c (Real.exp (-(q : ℝ))) + Q * q) := by
    refine ratDivergence_congr h fun q hq => ?_
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    show -c (Real.exp (-(((q : ℝ).toNNReal : ℝ≥0) : ℝ))) + Q * (q : ℝ) = -c (Real.exp (-(q : ℝ))) + Q * (q : ℝ)
    rw [Real.coe_toNNReal _ hq0]
  have hKt : Tendsto (fun s : ℝ => -c (Real.exp (-s)) + Q * s) atTop atTop :=
    tendsto_atTop_of_ratDivergence hK hKq
  have hlog : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hfin := tendsto_neg_atTop_atBot.comp (hKt.comp hlog)
  refine hfin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  have he : Real.exp (-(-Real.log r)) = r := by rw [neg_neg, Real.exp_log hr']
  simp only [Function.comp_apply, he]
  ring

/-- Deterministic limit at `r → ∞` (`s = log r → ∞`): if `c` is continuous on `(0, ∞)` and `s ↦ c(e^s) + Q s` diverges to
`+∞` along the rationals, then `c r + Q log r → +∞` as `r → ∞`. -/
lemma tendsto_log_circle_atTop {c : ℝ → ℝ} (hc : ContinuousOn c (Ioi 0)) (Q : ℝ)
    (h : RatDivergence (fun q : ℚ => c (Real.exp (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) + Q * q)) :
    Tendsto (fun r : ℝ => c r + Q * Real.log r) atTop atTop := by
  have h1 := (tendsto_circle_of_ratDivergence hc Q h).comp Real.tendsto_log_atTop
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [Function.comp_apply, Real.exp_log hr]

/-- **`hlim` (PRO Section 2, `ConeScaleRadiusPos.lean:55`).** For a quantum cone `(P, hC, hcirc)` of parameter `0 < γ < 2`,
almost surely the radial part `r ↦ h_r(0) + Q log r` diverges to `-∞` as `r → 0+` and to `+∞` as `r → ∞`. The first limit is
the Brownian negative drift (no hypothesis); the second is the corrected radial divergence of the conditioned Brownian motion
`hdiv` (`FrozenConeRadialDivergenceCorrected`, the only named input). -/
theorem ae_radialPart_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hdiv : FrozenConeRadialDivergenceCorrected)
    (hcone : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, Tendsto (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r) (𝓝[>] 0) atBot ∧
      Tendsto (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r) atTop atTop := by
  obtain ⟨ν, hνcond, hradial⟩ := hcone.radial_law
  have : IsProbabilityMeasure ν := hνcond.1
  have hν := hdiv γ hγ0 hγ2 ν hνcond
  have hx1 := ae_ratDivergence_neg_quantumConeRadialLaw hγ0 hγ2 ν
  have hx2 := ae_ratDivergence_quantumConeRadialLaw hν
  have hRm := measurable_radialProcess_of_quantumCone hcone
  have hE1 : MeasurableSet {x : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) |
      RatDivergence (fun q : ℚ => -x.1 (q : ℝ).toNNReal + lqgQ γ * q)} :=
    measurableSet_ratDivergence (fun (q : ℚ) (x : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) => -x.1 (q : ℝ).toNNReal + lqgQ γ * q)
      fun q => (((measurable_pi_apply ((q : ℝ).toNNReal)).comp measurable_fst).neg).add_const _
  have hE2 : MeasurableSet {x : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) |
      RatDivergence (fun q : ℚ => x.2 (q : ℝ).toNNReal + lqgQ γ * q)} :=
    measurableSet_ratDivergence (fun (q : ℚ) (x : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) => x.2 (q : ℝ).toNNReal + lqgQ γ * q)
      fun q => ((measurable_pi_apply ((q : ℝ).toNNReal)).comp measurable_snd).add_const _
  rw [← hradial] at hx1 hx2
  have hr1 := (ae_map_iff hRm.aemeasurable hE1).1 hx1
  have hr2 := (ae_map_iff hRm.aemeasurable hE2).1 hx2
  filter_upwards [hr1, hr2, hcone.ae_continuousOn_circle] with ω h1 h2 hω
  have hc : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
    hω.comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ _⟩)
  exact ⟨tendsto_log_circle_nhdsGT_zero hc (lqgQ γ) h1, tendsto_log_circle_atTop hc (lqgQ γ) h2⟩

/-- **`ConeScaleRadiusPosStep` without `hlim`.** The only named input is the corrected radial divergence
`FrozenConeRadialDivergenceCorrected`; the Brownian negative drift is proved (BrownianNegativeDrift.lean). -/
theorem coneScaleRadiusPosStep_of_radialDivergence (hdiv : FrozenConeRadialDivergenceCorrected) :
    MatedCRT.ConeScaleRadiusPosStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc _ hcone b _
  exact ae_coneScaleRadius_pos_of_limits hcone b (ae_radialPart_tendsto hγ0 hγ2 hdiv hcone)

end MatedCRT.FirstPass2x
