import MatedCRT.FirstPass.Derived.RegClockOccupation
import MatedCRT.FirstPass.Derived.GmcGreenApproxGFF
import MatedCRT.FirstPass.Derived.LimClockIntegralConvergence

/-!
# Annealed limit of the regularized occupation clocks

Let `h = h^ℂ - γ log |·|` be built from a whole-plane GFF `h^ℂ`, with circle-average weights
`w_ε(x) = ε^{γ²/2} e^{γ h_ε(x)}`, and let `b` be a planar Brownian motion started at `y ∈ D = B_r(z)` and killed on
exiting `D`. For a fixed field sample, the expected integral of `g(b_u)` against the regularized clock measure
`w_ε(b_u) du` on `[0, σ(b)]` equals `2 ∫_D G_D(y, x) w_ε(x) g(x) dx` (the regularized occupation identity,
`lintegral_regClock_occupation_eq_green_ofReal`). Almost surely in the field, the right side converges along every
sequence of dyadic scales `2^{-n_k} → 0` to `∫ g dμ`, where `μ = gmcGreenMeasure` is the Green-weighted Gaussian
multiplicative chaos measure `2 G_D(y, x) M_γ(dx)` (`ae_tendsto_two_mul_setLIntegral_green_regWeight_gff`).

Combining the two: almost surely in the field, for every such sequence and every continuous `g ≥ 0` with compact
support in `D` avoiding `y`, the annealed (in the Brownian path) regularized clock integrals converge to `∫ g dμ`.
This is the convergence of the expectations in the Revuz-measure argument for the Liouville clock
(Garban-Rhodes-Vargas, Liouville Brownian motion, Thm 2.7(1); Berestycki, Diffusion in planar Liouville quantum
gravity, §2-3), stated on the field space itself rather than on the law of the circle averages.

## Main results

* `ae_tendsto_lintegral_setLIntegral_regClockMeasure`: the convergence above, from the lintegral form
  `BrownianOccupationOnBall` of the Brownian occupation identity.
* `ae_tendsto_lintegral_setLIntegral_regClockMeasure_of_killed`: the same from the bounded-integrand form
  `KilledBrownianOccupationOnBall`.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Annealed limit of the regularized clocks.** For a whole-plane GFF, `0 < γ < 2`, `ρ < ρ₂ < 1`, a ball
`D = B_r(z) ⊆ B̄_ρ(0)` and `y ∈ D`: almost surely in the field, for every sequence `n k → ∞` and every continuous
`g ≥ 0` with compact support in `D` and `y ∉ tsupport g`, the Brownian expectation (started at `y`) of the integral of
`g(b_u)` over `[0, σ_D(b)]` against the regularized clock measure at scale `2^{-n_k}` converges to
`∫ g d(gmcGreenMeasure γ ρ ρ₂ z y r ψ)`. -/
theorem ae_tendsto_lintegral_setLIntegral_regClockMeasure {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hD : ball z r ⊆ closedBall 0 ρ) (hy : y ∈ ball z r)
    (hB : BrownianOccupationOnBall z r) :
    ∀ᵐ ω' ∂P', ∀ n : ℕ → ℕ, Tendsto n atTop atTop → ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      HasCompactSupport g → tsupport g ⊆ ball z r → y ∉ tsupport g →
        Tendsto (fun k => ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
            ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
              (exitNN z r) b ∂planarBrownianMotion y)
          atTop (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
            (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω'))) := by
  filter_upwards [ae_tendsto_two_mul_setLIntegral_green_regWeight_gff hG hγ hγ2 hρρ₂ hρ₂]
    with ω' hω n hn g hgc hg0 hgK hgD hgy
  refine (hω z y r hD hy n hn g hgc hg0 hgK hgD hgy).congr fun k => ?_
  exact (lintegral_regClock_occupation_eq_green_ofReal hB γ _ _ hy hgc.measurable).symm

/-- `ae_tendsto_lintegral_setLIntegral_regClockMeasure` from the bounded-integrand form
`KilledBrownianOccupationOnBall` of the Brownian occupation identity. -/
theorem ae_tendsto_lintegral_setLIntegral_regClockMeasure_of_killed {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ}
    (hG : HarmonicBalls.IsWholePlaneGFF P' hC' hc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ ρ₂ : ℝ}
    (hρρ₂ : ρ < ρ₂) (hρ₂ : ρ₂ < 1) {z y : ℂ} {r : ℝ} (hD : ball z r ⊆ closedBall 0 ρ) (hy : y ∈ ball z r)
    (hK : KilledBrownianOccupationOnBall z r) :
    ∀ᵐ ω' ∂P', ∀ n : ℕ → ℕ, Tendsto n atTop atTop → ∀ g : ℂ → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      HasCompactSupport g → tsupport g ⊆ ball z r → y ∉ tsupport g →
        Tendsto (fun k => ∫⁻ b, ∫⁻ u in Icc 0 (exitNN z r b), ENNReal.ofReal (g (b u))
            ∂regClockMeasure γ (dyadicScale (n k)) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω')
              (exitNN z r) b ∂planarBrownianMotion y)
          atTop (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂gmcGreenMeasure γ ρ ρ₂ z y r
            (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω'))) :=
  ae_tendsto_lintegral_setLIntegral_regClockMeasure hG hγ hγ2 hρρ₂ hρ₂ hD hy
    (brownianOccupationOnBall_of_killed hK)

end MatedCRT.KilledOccupation
