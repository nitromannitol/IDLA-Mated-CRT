import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockFun
import MatedCRT.Proofs.Sec3.KilledOccupation.RemovedTail
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosure4

/-!
# Occupation identity of the regularized occupation clocks

Fix circle averages `ψ`, a scale `ε` and the regularized weight `w(x) = ε^{γ²/2} e^{γ ψ̃(ε, x)}` of the regularized
occupation clock `regClockFun γ ε ψ σ b`, whose Stieltjes measure on `[0, σ(b)]` is `w(b_u) du`
(`regClockFun_eq_withDensity_Iic`, `MatedCRT/FirstPass/Derived/LimClockUniform.lean`). For planar Brownian motion
started at `y ∈ D = B_r(z)` and killed on exiting `D`, the Brownian occupation identity (generator `½Δ`, Green function
`ΔG = -δ`) applied to the integrand `w · g` gives, for every measurable `g ≥ 0`,
`E_y ∫_{[0, σ]} g(b_u) w(b_u) du = 2 ∫_D G_D(y, x) w(x) g(x) dx`:
the expected occupation measure of the regularized clock up to the exit time is `2 · 1_D · G_D(y, ·) · w` times
Lebesgue measure. This is the regularized occupation identity of the Revuz-measure argument for the Liouville clock
(Garban-Rhodes-Vargas, Liouville Brownian motion, Thm 2.7(1); Berestycki, Diffusion in planar Liouville quantum
gravity, §2-3), before the passage to the limit `ε → 0`.

## Main results
* `measurable_circleAverageRep_right`: `x ↦ ψ̃(ε, x)` is measurable for fixed `ψ`.
* `lintegral_regClock_occupation_eq_green`: the identity above, from the lintegral form `BrownianOccupationOnBall`.
* `lintegral_regClock_occupation_eq_green_of_killed`: the same identity from the bounded-integrand form
  `KilledBrownianOccupationOnBall`.
* `lintegral_regClock_occupation_eq_green_ofReal`: the same for a real integrand `g ≥ 0`.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The circle-average representative `x ↦ ψ̃(ε, x)` of a fixed family `ψ` is measurable. -/
lemma measurable_circleAverageRep_right (ψ : UnitDiskCircleIndex → ℝ) (ε : ℝ) :
    Measurable fun x : ℂ => circleAverageRep ψ ε x := by
  have h : Measurable ((fun q : (UnitDiskCircleIndex → ℝ) × ℂ => circleAverageRep q.1 ε q.2) ∘
      fun x : ℂ => (ψ, x)) :=
    (measurable_circleAverageRep ε).comp measurable_prodMk_left
  exact h

/-- The regularized weight `x ↦ ε^{γ²/2} e^{γ ψ̃(ε, x)}` is measurable. -/
lemma measurable_regClockWeight (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) :
    Measurable fun x : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε x)) :=
  measurable_ofReal_exp_mul _ γ (measurable_circleAverageRep_right ψ ε)

/-- Integrals against the Stieltjes measure `w(b_u) du` of the regularized clock on `[0, σ]`: for a measurable
`g ≥ 0`, `∫_{[0, σ]} g(b_u) w(b_u) du` with respect to Lebesgue measure. -/
lemma setLIntegral_withDensity_regClockWeight (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) (b : ContinuousPath ℂ)
    (σ : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u in Icc 0 σ, g (b u) ∂((lebNN.restrict (Icc 0 σ)).withDensity fun u =>
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u)))) =
      ∫⁻ u in Icc 0 σ, (fun x : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) *
        Real.exp (γ * circleAverageRep ψ ε x)) * g x) (b u) ∂lebNN := by
  have hb : Measurable fun u : ℝ≥0 => b u := b.continuous.measurable
  have hw : Measurable fun u : ℝ≥0 =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u))) :=
    (measurable_regClockWeight γ ε ψ).comp hb
  have hgb : Measurable fun u : ℝ≥0 => g (b u) := hg.comp hb
  rw [restrict_withDensity measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc, inter_self]
  exact lintegral_withDensity_eq_lintegral_mul _ hw hgb

/-- **Regularized occupation identity.** For planar Brownian motion started at `y ∈ D = B_r(z)` and killed on exiting
`D`, the expected integral of `g(b_u)` against the Stieltjes measure `w(b_u) du` of the regularized clock on
`[0, σ(b)]` is `2 ∫_D G_D(y, x) w(x) g(x) dx`, for every measurable `g ≥ 0`. -/
theorem lintegral_regClock_occupation_eq_green {z : ℂ} {r : ℝ} (hB : BrownianOccupationOnBall z r)
    (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) {y : ℂ} (hy : y ∈ ball z r) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), g (b u) ∂((lebNN.restrict (Icc 0 (exitNN z r b))).withDensity fun u =>
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u)))) ∂planarBrownianMotion y =
      2 * ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) *
        (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε x)) * g x) := by
  simp_rw [setLIntegral_withDensity_regClockWeight γ ε ψ _ _ hg]
  exact hB y hy _ ((measurable_regClockWeight γ ε ψ).mul hg)

/-- The regularized occupation identity `lintegral_regClock_occupation_eq_green` from the bounded-integrand form
`KilledBrownianOccupationOnBall` of the Brownian occupation identity. -/
theorem lintegral_regClock_occupation_eq_green_of_killed {z : ℂ} {r : ℝ}
    (hK : KilledBrownianOccupationOnBall z r) (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) {y : ℂ}
    (hy : y ∈ ball z r) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), g (b u) ∂((lebNN.restrict (Icc 0 (exitNN z r b))).withDensity fun u =>
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u)))) ∂planarBrownianMotion y =
      2 * ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) *
        (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε x)) * g x) :=
  lintegral_regClock_occupation_eq_green (brownianOccupationOnBall_of_killed hK) γ ε ψ hy hg

/-- The regularized occupation identity for a measurable real integrand `g`, through `ofReal ∘ g`. -/
theorem lintegral_regClock_occupation_eq_green_ofReal {z : ℂ} {r : ℝ} (hB : BrownianOccupationOnBall z r)
    (γ ε : ℝ) (ψ : UnitDiskCircleIndex → ℝ) {y : ℂ} (hy : y ∈ ball z r) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
        ∂((lebNN.restrict (Icc 0 (exitNN z r b))).withDensity fun u =>
          ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε (b u)))) ∂planarBrownianMotion y =
      2 * ∫⁻ x in ball z r, ENNReal.ofReal (greenFunction (ball z r) y x) *
        (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAverageRep ψ ε x)) * ENNReal.ofReal (g x)) :=
  lintegral_regClock_occupation_eq_green hB γ ε ψ hy (g := fun x => ENNReal.ofReal (g x)) hg.ennreal_ofReal

end MatedCRT.KilledOccupation
