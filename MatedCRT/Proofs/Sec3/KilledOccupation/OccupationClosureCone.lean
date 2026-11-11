import MatedCRT.Proofs.Sec3.KilledOccupation.ConeOccupationTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.RescaledClockOccupation
import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationAssembly
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockFinite
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.HarmonicPathExit

/-!
# The killed-occupation identity of Liouville Brownian motion on the quantum cone, from the whole-plane GFF

`frozenLBMGreenOccupationRescaled_of_coneGFFLaw` proves `FrozenLBMGreenOccupationRescaled 𝒮`, the occupation identity
`E_y ∫_0^τ f(X_t) dt = (2 / m₀) ∫_D G_D(y, x) f(x) μ(dx)` of the median-rescaled Liouville Brownian motion `X` killed
on exiting a disc `D = B_r(z) ⊆ B_ρ(0)`, `ρ < 1` (Appendix B of the paper), from two inputs:

* `hlaw : ConeUnitDiskGFFLaw`, eq:gff of the paper: on the unit disk the circle averages of the γ-quantum cone have
  the law of those of `h^ℂ - γ log|·|`, for a whole-plane GFF `h^ℂ`;
* `hGFF`, the occupation identity of the clock for the field `h^ℂ - γ log|·|` and an independent planar Brownian
  motion (Garban, Rhodes and Vargas, *Liouville Brownian motion*; Berestycki, *Diffusion in planar Liouville quantum
  gravity*), stated for the limit clock of the circle averages along a sequence of dyadic scales whose consecutive
  gaps satisfy the summable bounds, as agreement of its expected occupation measure with the Gaussian multiplicative
  chaos limit weighted by `2 · 1_D · G_D(y, ·)` on countable families of measurable subsets of `D`.

The proof takes for `dA ω b` the Stieltjes kernel of the limit clock of the circle averages `ψ_S(ω)` of the cone
along the good subsequence. This kernel is measurable in the path `b`, and for almost every `(ω, b)` it is the
Stieltjes measure of the clock `S.clock ω b` stopped at the exit time of `D` (`ae_limClockKernel_Iic_cone`). The cone
occupation identity (`ae_lintegral_clock_occupation_eq_green_cone`) and the pathwise change of variables
(`rescaled_occupation_green_identity_of_clock`) then give the statement. The positivity of `m₀`, the time-change
property of the clock and the finiteness of the Brownian exit time of `D` come from the validity of the environment
and from `planar_exit_ae_lt_top`.

No base clock, no weight identity, no bound on the mass of dyadic squares and no convergence in probability of
clock distances is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- **Occupation identity of the median-rescaled Liouville Brownian motion on the γ-quantum cone** (Appendix B of the
paper), from eq:gff (`hlaw`) and the occupation identity of the clock of the field `h^ℂ - γ log|·|`, `h^ℂ` a
whole-plane GFF, with an independent planar Brownian motion (`hGFF`).

`hGFF`: for every whole-plane GFF model, every strictly increasing sequence `n` of dyadic scales with
`dyadicScale (n 0) < 1 - ρ` along which the consecutive gaps of the regularized clocks of `h^ℂ - γ log|·|` satisfy the
summable bounds, and every countable family `C` of measurable subsets of `D = B_r(z)`, almost surely the expected
occupation measure of the limit clock along `n`, up to the exit time of `D`, is finite on `D` and agrees on `C` with
the chaos limit weighted by `2 · 1_D · G_D(y, ·)`. -/
theorem frozenLBMGreenOccupationRescaled_of_coneGFFLaw (𝒮 : SpaceFillingSLEModel) (hlaw : ConeUnitDiskGFFLaw)
    (hGFF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
      ball z r ⊆ ball 0 ρ → y ∈ ball z r →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
      ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
      (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
        {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
          clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
          ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
      ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
        ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
          occupationAgreementEvent
            (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
            (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C) :
    FrozenLBMGreenOccupationRescaled 𝒮 := by
  intro γ hγ0 hγ2 ρ hρ0 hρ1 Ω _ S hS r z y hr hball hy
  -- The good subsequence and the Stieltjes kernel of the limit clock on the cone.
  obtain ⟨n, -, -, -, hid⟩ :=
    exists_strictMono_ae_limClockFun_eq_clock_cone 𝒮 γ ρ hρ1 z y r hr hball hy S hS
  have hκ := ae_limClockKernel_Iic_cone 𝒮 γ z y r S hS n hid
  have hclock : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, IsTimeChangeClock (S.clock ω b) :=
    hS.isLQGClock.mono fun _ hω => (hω y).2
  have hσexit : ∀ᵐ b ∂planarBrownianMotion y,
      (∀ s < exitNN z r b, b s ∈ ball z r) ∧ b (exitNN z r b) ∉ ball z r :=
    (planar_exit_ae_lt_top y z r).mono fun b hb => exitNN_props_of_lt_top hb
  filter_upwards [ae_lintegral_clock_occupation_eq_green_cone hlaw 𝒮 γ hγ0 hγ2 ρ hρ1 S hS r z y hr hball hy
    (hGFF γ hγ0 hγ2 ρ hρ0 hρ1 r z y hr hball hy), hclock, hκ] with ω hcone hcl hκω
  obtain ⟨hfin, hocc⟩ := hcone
    (fun b => limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b)) hκω
  -- The inner clock integrals are measurable in the path.
  have hmeas : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      AEMeasurable (fun b => ∫⁻ u in Icc (0 : ℝ≥0) (exitNN z r b), q (b u)
        ∂(limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b)))
        (planarBrownianMotion y) := fun q hq =>
    (measurable_setLIntegral_exitNN
      (fun b => limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b))
      (fun b t => limClockKernel_Iic_ne_top γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b) t)
      (fun t => (measurable_limClockKernel_Iic γ (fun k => dyadicScale (n k)) (exitNN z r)
        (measurable_exitNN z r) t).comp measurable_prodMk_left) z r q hq).aemeasurable
  exact rescaled_occupation_green_identity_of_clock S r z y (exitNN z r) (hS.m₀_pos hγ0 hγ2) ω
    (fun b => limClockKernel γ (fun k => dyadicScale (n k)) (exitNN z r) (clockPsi S.hcirc ω, b))
    hcl hσexit hκω hmeas hfin hocc

end MatedCRT.KilledOccupation
