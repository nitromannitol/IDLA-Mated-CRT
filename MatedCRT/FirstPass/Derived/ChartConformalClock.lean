import MatedCRT.FirstPass.Derived.HN9OfChartField
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# The conformal clock of an inverse chart and Lévy's conformal invariance of planar Brownian motion

Step R1 of the Revuz route to Berestycki (2015), Theorem 1.3 (*Diffusion in planar Liouville quantum gravity*,
arXiv:1301.3356), for the Liouville Brownian motion of the field: the chart image of a planar Brownian path, run with
the conformal clock of the chart, is a planar Brownian path stopped at its exit from the unit disc.

For an open set `U`, a map `ψ` and a path `b`, the *conformal rate* is `‖ψ'(b_s)‖²` before the exit time `τ_U` of
`b` and `1` afterwards (`chartRate`), and the *conformal clock* is its primitive (`chartClock`):
`A_b(t) = ∫_0^{t ∧ τ_U} ‖ψ'(b_s)‖² ds + (t - τ_U)₊`. For an inverse chart `ψ` of `U` the rate is positive
(`chartRate_pos`: an injective holomorphic map has a non-vanishing derivative), so the clock is a time-change clock as
soon as the rate is locally integrable and the path leaves `U` (`isTimeChangeClock_chartClock`).

Lévy's theorem (Mörters–Peres, *Brownian motion*, Theorem 7.20): for `w ∈ U`, the process `ψ(B_t)`, `t ≤ τ_U`, is a
planar Brownian motion `B̃` from `ψ(w)` run with the clock `A`, that is `ψ(B_t) = B̃(A_t)`. In terms of laws of paths:
the chart image of the path `b` run with the clock `A_b` and stopped at its exit from `U` has the law of planar
Brownian motion from `ψ(w)` stopped at its exit from the unit disc (`LevyConformalChartStmt`; the exit time of the
time-changed path from `U` is `A_b(τ_U)`, and `|ψ| = 1` on the frontier of `U`). The printed proofs use stochastic
calculus, which the repository does not have; the statement is used as an explicit hypothesis.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

open Classical in
/-- The conformal rate of the map `ψ` along the path `b` for the open set `U`: `‖ψ'(b_s)‖²` before the exit time of
`b` from `U`, and `1` from the exit time on (for `s < 0`, the value at `0`). -/
noncomputable def chartRate (U : Set ℂ) (ψ : ℂ → ℂ) (b : ContinuousPath ℂ) (s : ℝ) : ℝ :=
  if ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U b then ‖deriv ψ (b s.toNNReal)‖ ^ 2 else 1

/-- **The conformal clock** `A_b(t) = ∫_0^t (conformal rate)`, that is
`∫_0^{t ∧ τ_U} ‖ψ'(b_s)‖² ds + (t - τ_U)₊`. -/
noncomputable def chartClock (U : Set ℂ) (ψ : ℂ → ℂ) (b : ContinuousPath ℂ) (t : ℝ≥0) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), chartRate U ψ b s

/-- From the exit time on, the conformal rate is `1`. -/
theorem chartRate_of_exitTime_le {U : Set ℂ} {ψ : ℂ → ℂ} {b : ContinuousPath ℂ} {s : ℝ}
    (hs : ContinuousPath.exitTime U b ≤ ((s.toNNReal : ℝ≥0) : ℝ≥0∞)) : chartRate U ψ b s = 1 := by
  unfold chartRate
  exact ite_eq_right (not_lt.2 hs)

/-- Before the exit time, the conformal rate is `‖ψ'(b_s)‖²`. -/
theorem chartRate_of_lt_exitTime {U : Set ℂ} {ψ : ℂ → ℂ} {b : ContinuousPath ℂ} {s : ℝ}
    (hs : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U b) :
    chartRate U ψ b s = ‖deriv ψ (b s.toNNReal)‖ ^ 2 := by
  unfold chartRate
  exact ite_eq_left hs

theorem chartClock_zero (U : Set ℂ) (ψ : ℂ → ℂ) (b : ContinuousPath ℂ) : chartClock U ψ b 0 = 0 := by
  simp [chartClock]

section InverseChart

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- An inverse chart has a non-vanishing derivative on `U` (it is injective and holomorphic there). -/
theorem IsInverseChart.deriv_ne_zero (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    deriv ψ x ≠ 0 :=
  QuantumZipper.CA.deriv_ne_zero_of_injOn hU hψ.differentiableOn (hψ.injOn.mono subset_closure) hx

/-- The conformal rate of an inverse chart is positive. -/
theorem chartRate_pos (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (b : ContinuousPath ℂ) (s : ℝ) :
    0 < chartRate U ψ b s := by
  by_cases h : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U b
  · rw [chartRate_of_lt_exitTime h]
    exact pow_pos (norm_pos_iff.2 (hψ.deriv_ne_zero hU (ContinuousPath.mem_of_lt_exitTime U b _ h))) 2
  · rw [chartRate_of_exitTime_le (not_lt.1 h)]
    exact one_pos

/-- **The conformal clock is a time-change clock.** For an inverse chart `ψ` of the open set `U` and a path `b` which
leaves `U` and along which the conformal rate is locally integrable, the conformal clock starts at `0`, is
continuous, strictly increasing and unbounded (it grows at unit speed after the exit time). -/
theorem isTimeChangeClock_chartClock (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {b : ContinuousPath ℂ}
    (hint : ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T)
    (hfin : ContinuousPath.exitTime U b ≠ ⊤) : IsTimeChangeClock (chartClock U ψ b) := by
  have hint' : ∀ a c : ℝ, IntervalIntegrable (chartRate U ψ b) volume a c :=
    fun a c => (hint a).symm.trans (hint c)
  refine ⟨chartClock_zero U ψ b, ?_, ?_, ?_⟩
  · exact (intervalIntegral.continuous_primitive hint' 0).comp NNReal.continuous_coe
  · intro s t hst
    have hst' : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
    have hpos : 0 < ∫ x in (s : ℝ)..(t : ℝ), chartRate U ψ b x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hint' s t) (fun x _ => chartRate_pos hψ hU b x) hst'
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint' 0 s) (hint' s t)
    simp only [chartClock]
    linarith
  · set τ : ℝ≥0 := (ContinuousPath.exitTime U b).toNNReal with hτ
    have hτe : ContinuousPath.exitTime U b = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
    have hlow : ∀ t : ℝ≥0, τ ≤ t → (t : ℝ) + -(τ : ℝ) ≤ chartClock U ψ b t := by
      intro t hτt
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint' 0 τ) (hint' τ t)
      have h0 : 0 ≤ ∫ x in (0 : ℝ)..(τ : ℝ), chartRate U ψ b x :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg τ) (fun x _ => (chartRate_pos hψ hU b x).le)
      have hcongr : EqOn (chartRate U ψ b) (fun _ => (1 : ℝ)) (uIcc (τ : ℝ) t) := by
        intro x hx
        rw [Set.uIcc_of_le (NNReal.coe_le_coe.2 hτt)] at hx
        have h2 : τ ≤ x.toNNReal := by
          have h3 := Real.toNNReal_le_toNNReal hx.1
          rwa [Real.toNNReal_coe] at h3
        apply chartRate_of_exitTime_le
        rw [hτe]
        exact ENNReal.coe_le_coe.2 h2
      have h1 : ∫ x in (τ : ℝ)..(t : ℝ), chartRate U ψ b x = (t : ℝ) - τ := by
        rw [intervalIntegral.integral_congr hcongr]
        simp
      simp only [chartClock]
      linarith
    have hlin : Tendsto (fun t : ℝ≥0 => (t : ℝ) + -(τ : ℝ)) atTop atTop :=
      (NNReal.tendsto_coe_atTop.2 tendsto_id).atTop_add tendsto_const_nhds
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [eventually_ge_atTop τ] with t ht
    exact hlow t ht

end InverseChart

/-- **GAP (step R1): Lévy's conformal invariance of planar Brownian motion, for an inverse chart.** For a bounded open
set `U`, an inverse chart `ψ` of `U` and a starting point `w ∈ U`: under planar Brownian motion from `w`, the chart
image of the path run with its conformal clock and stopped at its exit from `U` is a measurable function of the path
whose law is planar Brownian motion from `ψ(w)` stopped at its exit from the unit disc.

Source: Mörters–Peres, *Brownian motion* (2010), Theorem 7.20 (Lévy): `ψ(B_t) = B̃(∫_0^t |ψ'(B_s)|² ds)` for
`t ≤ τ_U`, with `B̃` a planar Brownian motion from `ψ(w)`; since `ψ(B_t)` stays in the unit disc before `τ_U` and
`|ψ(B_{τ_U})| = 1`, the time `A(τ_U)` is the exit time of `B̃` from the disc. The printed proof uses stochastic
calculus (Itô's formula and Lévy's characterization), which the repository does not provide. -/
def LevyConformalChartStmt : Prop :=
  ∀ (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)), IsOpen U → Bornology.IsBounded U → IsInverseChart U z ψ →
    ∀ w ∈ U,
      AEMeasurable (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))
        (planarBrownianMotion w) ∧
      (planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) =
        (planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))

end MatedCRT
