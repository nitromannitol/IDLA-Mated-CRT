import MatedCRT.FirstPass.Derived.NormalizedFieldGivenVanishing
import MatedCRT.FirstPass.Derived.ConeReferenceData
import MatedCRT.FirstPass.Derived.PlanarBrownianStoppedOccupationBound
import LatticeProb.LQG.CircleAverageCorrectionBallPower
import LatticeProb.Analysis.GaussianBallMassPower

/-!
# Stopped heat bound for the dyadic approximants of the reference cone

Let `Y` be a normalized whole-plane GFF with continuous circle-average coordinates `c`, and let the
cone field be `h = h^ℂ - γ log |·|` plus the radial correction built from a path `w`
(`coneRefCircle`). Almost surely, for every `R > 0`:

* the dyadic approximants `ε^{γ²/2} e^{γ h_ε(x)} dx` of the `γ`-LQG measure of the cone give every
  ball `B(z, r)` with `‖z‖ ≤ R` and `0 < r ≤ 1` mass at most `C r^β`, uniformly in the level and
  for every path `w` (`ae_coneRef_approximant_ball_rpow_bound`);
* consequently the occupation integral of the approximant density along planar Brownian motion
  from `z`, `‖z‖ ≤ R`, stopped at `t ∧ τ_{B(0, R+1)}`, has expectation at most `C t^β`, uniformly
  in the level (`ae_coneRef_stopped_heat_bound`), and this bound tends to `0` as `t ↓ 0`
  uniformly in the start and the level (`ae_coneRef_stopped_heat_tendsto_zero`).

The second bound restricts the density to `B(0, R+1)`, bounds the stopped occupation by the time
integral of planar Gaussian averages, and integrates the Gaussian averages of a density with
power-law ball masses over the variances `s ∈ (0, t]`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open LatticeProb.LQG
open LatticeProb.Gauss (fieldCircleAverage)
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- **Ball bounds for the approximants of the reference cone.** Almost surely, for every path `w`
and every `R > 0` there are `β, C > 0` such that the dyadic approximants of the `γ`-LQG measure of
the cone built from `c (Y ω)` and `w` give every ball `B(z, r)` with `‖z‖ ≤ R` and `0 < r ≤ 1`
mass at most `C r^β`, for every level `k`. -/
theorem ae_coneRef_approximant_ball_rpow_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ w : ContinuousPath ℝ, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ (coneRefCircle γ (c (Y ω)) w) (LatticeProb.LQG.dyadicScale k)
            (ball z r) ≤
          ENNReal.ofReal (C * r ^ β) := by
  let μ := P.map Y
  let : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hY.1.measurable.aemeasurable).2 inferInstance
  have hnorm : IsNormalizedWPGFF id μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hY.1, ?_⟩
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hY.2
  have hG : IsWholePlaneGFF μ hC c :=
    isWholePlaneGFF_selected_coordinates hY hp hc hcont hmeas
  have hcm : ∀ r, 0 < r → ∀ z, ∀ᵐ x ∂μ, c x r z = circleAvg x r z := by
    intro r hr z
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (hG.measurable_circle r z hr)
        (measurable_circleAvg_left r z))).2 (hc r hr z)
  have hbound := ae_singular_approximant_add_circleAverage_ball_rpow_bound hnorm
    ((HarmonicBalls.LPBridge.isWholePlaneGFF_iff _ _ _).1 hG) hcont hcm hγ hγ2 hγ.le
    (self_lt_lqgQ hγ hγ2)
  have hcone : ∀ᵐ x ∂μ, ∀ w : ContinuousPath ℝ, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
        LatticeProb.LQG.lqgApprox γ (coneRefCircle γ (c x) w) (LatticeProb.LQG.dyadicScale k)
            (ball z r) ≤
          ENNReal.ofReal (C * r ^ β) := by
    filter_upwards [hbound] with x hx w R hR
    have h0 : ContinuousOn (fun ρ => c x ρ 0) (Ioi 0) :=
      (hcont x).comp (continuous_id.prodMk continuous_const).continuousOn
        fun ρ hρ => ⟨hρ, mem_univ _⟩
    exact hx (coneRefField (c x) w) (continuous_coneRefField h0 w) R hR
  exact ae_of_ae_map hY.1.measurable.aemeasurable hcone

/-- **Stopped heat bound for the approximants of the reference cone.** Almost surely, for every
`R > 0` there are `β, C > 0` such that for every start `z` with `‖z‖ ≤ R`, every level `k` and every
`t ≥ 0`, the expected occupation integral of the approximant density
`ε^{γ²/2} e^{γ h_ε}`, `ε = 2^{-k}`, along planar Brownian motion from `z` stopped at
`t ∧ τ_{B(0, R+1)}` is at most `C t^β`. -/
theorem ae_coneRef_stopped_heat_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * coneRefCircle γ (c (Y ω)) (w ω) (LatticeProb.LQG.dyadicScale k)
                (b s.toNNReal))))
          ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β) := by
  filter_upwards [ae_coneRef_approximant_ball_rpow_bound hY hp hc hcont hmeas hγ hγ2]
    with ω hω R hR
  obtain ⟨β, C, hβ, hC0, hball⟩ := hω (w ω) (R + 1) (by linarith)
  obtain ⟨N, hN⟩ :=
    LatticeProb.exists_lintegral_Ioc_lintegral_map_prod_gaussianReal_indicator_le (0 : ℂ) (R + 1)
  have hβ' : 0 < min β 1 / 2 := half_pos (lt_min hβ one_pos)
  have hmax : 0 < max C (N * C) := lt_max_of_lt_left hC0
  refine ⟨min β 1 / 2, 1024 / 7 / (2 * Real.pi) * max C (N * C) / (min β 1 / 2), hβ',
    div_pos (mul_pos (by positivity) hmax) hβ', fun z hz k t ht => ?_⟩
  have hk : 0 < LatticeProb.LQG.dyadicScale k := by unfold LatticeProb.LQG.dyadicScale; positivity
  have hcc : Continuous fun x : ℂ =>
      coneRefCircle γ (c (Y ω)) (w ω) (LatticeProb.LQG.dyadicScale k) x :=
    (continuousOn_coneRefCircle γ (hcont (Y ω)) (w ω)).comp_continuous
      (continuous_const.prodMk continuous_id) fun x => ⟨hk, mem_univ _⟩
  have hρm : Measurable fun x : ℂ => ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * coneRefCircle γ (c (Y ω)) (w ω) (LatticeProb.LQG.dyadicScale k) x)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcc))).measurable)
  refine (MatedCRT.KilledOccupation.lintegral_stoppedOccupation_le_lintegral_planarGaussian
    isOpen_ball z hρm t).trans ?_
  refine hN _ hρm C β hC0.le hβ (fun c' hc' r hr hr1 => ?_) z
    (mem_closedBall_zero_iff.2 (by linarith)) t ht
  have h := hball c' (mem_closedBall_zero_iff.1 hc') r hr hr1 k
  rwa [LatticeProb.LQG.lqgApprox, withDensity_apply _ measurableSet_ball] at h

/-- **Small-time vanishing of the stopped heat bound.** Almost surely, for every `R > 0`, the
supremum over starts `‖z‖ ≤ R` and levels `k` of the expected occupation integral of the approximant
density along planar Brownian motion from `z`, stopped at `t ∧ τ_{B(0, R+1)}`, tends to `0` as
`t ↓ 0`. -/
theorem ae_coneRef_stopped_heat_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      Tendsto (fun t : ℝ => ⨆ z ∈ closedBall (0 : ℂ) R, ⨆ k : ℕ,
        ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
            ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * coneRefCircle γ (c (Y ω)) (w ω) (LatticeProb.LQG.dyadicScale k)
                (b s.toNNReal))))
          ∂(planarBrownianMotion z)) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_coneRef_stopped_heat_bound hY hp hc hcont hmeas hγ hγ2 w] with ω hω R hR
  obtain ⟨β, C, hβ, -, hb⟩ := hω R hR
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (C * t ^ β)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => C * t ^ β) (𝓝 0) (𝓝 (C * 0 ^ β)) :=
      (continuous_const.mul (Real.continuous_rpow_const hβ.le)).tendsto 0
    rw [Real.zero_rpow hβ.ne', mul_zero] at h0
    simpa using (ENNReal.tendsto_ofReal h0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact iSup₂_le fun z hz => iSup_le fun k =>
    hb z (mem_closedBall_zero_iff.1 hz) k t (le_of_lt ht)

end MatedCRT.FirstPass.Derived
