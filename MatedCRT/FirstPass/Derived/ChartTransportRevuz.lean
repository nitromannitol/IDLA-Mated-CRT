import MatedCRT.FirstPass.Derived.ChartRevuzGluedClock
import MatedCRT.FirstPass.Derived.ChartFieldLBM
import MatedCRT.FirstPass.Derived.ConeApproxBallPowerProof
import MatedCRT.FirstPass.Derived.DyadicVagueRelValid

/-!
# The transported approximating laws converge to the time change with the transported Revuz measure

`revuzTimeChangeLaw ν` is the weak limit of the disc time-change laws `discTimeChangeProbLaw (g_k(ν))` of the
canonical rates `g_k(ν) = discCanonicalRate k ν` (the absolutely continuous approximations of the additive functional
of Brownian motion killed on exiting the unit disc with Revuz measure `ν`, Fukushima–Oshima–Takeda (2011), §5.1,
§6.2); it is a Borel function of `ν` (`measurable_revuzTimeChangeLaw`).

For an inverse chart `ψ` of a bounded open set `U` at `z`, the LQG limit `μ` of approximations with a uniform
small-ball power bound, and an LQG clock `F` of Brownian motion from `z`, the disc time-change laws of the canonical
rates of `ν₀ = ψ_*(μ|_U)` converge to the chart image of Brownian motion run with `F`
(`tendsto_integral_discTimeChangeLaw_discCanonicalRate`), and so do the transported approximating laws
(`tendsto_integral_chartTransportApproxLaw_of_levy`): both converge to `revuzTimeChangeLaw ν₀`
(`tendsto_integral_chartTransportApproxLaw_revuzTimeChangeLaw`). In a valid environment this gives
`ChartTransportRevuzStmt` from Lévy's conformal invariance and the uniform small-ball power bound of the dyadic
approximations of the cone LQG measure (`chartTransportRevuzStmt_of_levy`; Berestycki (2015), Theorem 1.3, along the
Revuz route). The small-ball bound holds (`coneApproxBallPowerStmt`), so Lévy's conformal invariance alone gives
`ChartTransportRevuzStmt γ` (`chartTransportRevuzStmt_of_levyConformalChart`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

/-- The laws of continuous planar paths form a nonempty space. -/
instance nonempty_probabilityMeasure_continuousPath : Nonempty (ProbabilityMeasure (ContinuousPath ℂ)) :=
  ⟨discTimeChangeProbLaw 0⟩

/-- **The time change of killed disc Brownian motion with Revuz measure `ν`.** The weak limit (when it exists) of the
disc time-change laws of the canonical rates `g_k(ν) = discCanonicalRate k ν`: Brownian motion from `0` killed on
exiting the unit disc, time-changed by the absolutely continuous additive functionals with densities `g_k(ν)`, whose
Revuz measures converge to `ν`. -/
noncomputable def revuzTimeChangeLaw (ν : Measure ℂ) : ProbabilityMeasure (ContinuousPath ℂ) :=
  limUnder atTop fun k : ℕ => discTimeChangeProbLaw (discCanonicalRate k ν)

/-- **The time change with Revuz measure `ν` is a Borel function of `ν`.** -/
theorem measurable_revuzTimeChangeLaw : Measurable revuzTimeChangeLaw := by
  have hk : ∀ k : ℕ, Measurable fun ν : Measure ℂ => discTimeChangeProbLaw (discCanonicalRate k ν) := fun k =>
    measurable_discTimeChangeProbLaw (g := discCanonicalRate k) (measurable_discCanonicalRate k)
      (fun ν v _ => discCanonicalRate_pos k ν v) (fun ν => ⟨_, fun v _ => abs_discCanonicalRate_le k ν v⟩)
  exact (StronglyMeasurable.limUnder fun k => (hk k).stronglyMeasurable).measurable

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)} {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} {R₁ β t₀ : ℝ}
  {F : ContinuousPath ℂ → ℝ≥0 → ℝ}

/-- **The transported approximating laws converge to the time change with the transported Revuz measure.** Let `ψ`
be an inverse chart of the bounded open set `U ⊆ B̄(0, R₁)` at `z`, `μ` the LQG limit of the approximations `μ_{ε_n}`
(continuous at the dyadic scales, with `μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`, `x ∈ B̄(0, R₁)`, `t < t₀`), and `F` an
LQG clock of Brownian motion from `z` which is almost surely a time-change clock, with `b ↦ b ∘ F(b)⁻¹` measurable.
Assuming Lévy's conformal invariance, the transported approximating laws from `ψ(z) = 0` converge weakly to
`revuzTimeChangeLaw (ψ_*(μ|_U))`. -/
theorem tendsto_integral_chartTransportApproxLaw_revuzTimeChangeLaw (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hμ : IsLQGLimit γ hε μ)
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (hβ : 0 < β) (ht₀ : 0 < t₀) (hU₁ : U ⊆ closedBall 0 R₁)
    (hpow : ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R₁, ∀ t, 0 < t → t < t₀ →
      lqgApprox γ hε (dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β))
    (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hFm : AEMeasurable (lbmContinuousPath F) (planarBrownianMotion z)) (f : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ W, f W ∂chartTransportApproxLaw γ hε n U ψ 0) atTop
      (𝓝 (∫ W, f W ∂(revuzTimeChangeLaw ((μ.restrict U).map ψ) : Measure (ContinuousPath ℂ)))) := by
  have hm : AEMeasurable (fun b => chartStopPath U ψ (lbmContinuousPath F b)) (planarBrownianMotion z) :=
    (measurable_chartStopPath U hU ψ).comp_aemeasurable hFm
  have hP : IsProbabilityMeasure ((planarBrownianMotion z).map fun b => chartStopPath U ψ (lbmContinuousPath F b)) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  set Λ : ProbabilityMeasure (ContinuousPath ℂ) :=
    ⟨(planarBrownianMotion z).map fun b => chartStopPath U ψ (lbmContinuousPath F b), hP⟩ with hΛ_def
  have hΛ : ∀ g : ContinuousPath ℂ →ᵇ ℝ, ∫ W, g W ∂(Λ : Measure (ContinuousPath ℂ)) =
      ∫ b, g (chartStopPath U ψ (lbmContinuousPath F b)) ∂planarBrownianMotion z := fun g =>
    integral_map hm g.continuous.aestronglyMeasurable
  have hk : Tendsto (fun k : ℕ => discTimeChangeProbLaw (discCanonicalRate k ((μ.restrict U).map ψ))) atTop
      (𝓝 Λ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    rw [hΛ g]
    refine Tendsto.congr (fun k => ?_) (tendsto_integral_discTimeChangeLaw_discCanonicalRate hLevy hψ hU hUb hμ
      hcont hβ ht₀ hU₁ hpow hF hFc g)
    rw [discTimeChangeProbLaw_coe (isProbabilityMeasure_discTimeChangeLaw_discCanonicalRate k _)]
  have hL : revuzTimeChangeLaw ((μ.restrict U).map ψ) = Λ := hk.limUnder_eq
  rw [hL, hΛ f]
  have h1 := tendsto_integral_chartTransportApproxLaw_of_levy hLevy hψ hU hUb hψ.mem hF hFc hcont f
  rw [hψ.apply_point] at h1
  exact h1

/-- **`ChartTransportRevuzStmt` from Lévy's conformal invariance and the uniform small-ball power bound.** For
`0 < γ < 2`, Lévy's conformal invariance of planar Brownian motion (`LevyConformalChartStmt`) and the uniform
small-ball power bound for the dyadic approximations of the cone LQG measure (`ConeApproxBallPowerStmt γ`) give
`ChartTransportRevuzStmt γ` with `L = revuzTimeChangeLaw`. -/
theorem chartTransportRevuzStmt_of_levy (hγ : 0 < γ) (hγ2 : γ < 2) (hLevy : LevyConformalChartStmt)
    (hpow : ConeApproxBallPowerStmt γ) : ChartTransportRevuzStmt γ := by
  refine ⟨revuzTimeChangeLaw, measurable_revuzTimeChangeLaw, fun 𝒮 Ω _ S hS H hH hrep => ?_⟩
  filter_upwards [hS.ae_lbmLawFieldSelection_eq hH hrep
      (FirstPass.Derived.lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS),
    hS.ae_isLQGClock_coordCircleAverage hrep, hS.ae_continuous_coordCircleAverage_dyadicScale hrep,
    hS.ae_isLQGLimit_coordCircleAverage hγ hγ2 hrep, hS.ae_coordCircleAverage_eq hrep, hpow 𝒮 Ω S hS]
    with ω hsel hclk hcont hlim heq hpw U z ψ hU hUb hψ f
  obtain ⟨hg, -⟩ := hsel z
  obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
  obtain ⟨β, hβ, t₀, ht₀, hp⟩ := hpw (max R 1) (lt_of_lt_of_le one_pos (le_max_right R 1))
  have hp' : ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) (max R 1), ∀ t, 0 < t → t < t₀ →
      lqgApprox γ (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) (dyadicScale n) (ball x t) ≤
        ENNReal.ofReal (t ^ β) := by
    intro n x hx t ht htt
    have he : coordCircleAverage (LQGMetric.pairJ ⊤ (H ω)) (dyadicScale n) = S.hcirc ω (dyadicScale n) :=
      funext fun w => heq _ (dyadicScale_pos n) w
    rw [lqgApprox, he]
    exact hp n x hx t ht htt
  exact tendsto_integral_chartTransportApproxLaw_revuzTimeChangeLaw hLevy hψ hU hUb hlim hcont hβ ht₀
    (hR.trans (closedBall_subset_closedBall (le_max_left R 1))) hp' (hclk z).1 (hclk z).2 hg f

/-- **`ChartTransportRevuzStmt` from Lévy's conformal invariance.** For `0 < γ < 2`, Lévy's conformal invariance of
planar Brownian motion (`LevyConformalChartStmt`) gives `ChartTransportRevuzStmt γ` with `L = revuzTimeChangeLaw`:
the uniform small-ball power bound of the dyadic approximations of the cone LQG measure holds
(`coneApproxBallPowerStmt`). -/
theorem chartTransportRevuzStmt_of_levyConformalChart (hγ : 0 < γ) (hγ2 : γ < 2)
    (hLevy : LevyConformalChartStmt) : ChartTransportRevuzStmt γ :=
  chartTransportRevuzStmt_of_levy hγ hγ2 hLevy (coneApproxBallPowerStmt hγ hγ2)

end MatedCRT
