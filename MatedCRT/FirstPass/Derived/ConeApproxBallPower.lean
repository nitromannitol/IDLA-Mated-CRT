import MatedCRT.Defs.Setting
import HarmonicBalls.Defs.LQG

/-!
# Uniform small-ball power bound for the approximations of the cone LQG measure

`ConeApproxBallPowerStmt γ` is the uniform-in-`ε` upper power bound for the masses of small discs under the
circle-average approximations `μ_ε = ε^{γ²/2} e^{γ h_ε(z)} dz` of the γ-LQG measure of the γ-quantum cone field,
along the dyadic scales `ε_n = 2^{-n}`: almost surely, for every `R > 0` there are `β, t₀ > 0` such that
`μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`, all centers `x ∈ B̄(0, R)` and all `t ∈ (0, t₀)`.

It is the input that makes the Green potentials of the transported approximating rates converge uniformly on discs
(the identification of the limit of the transported Liouville clocks through the Revuz measure, Berestycki (2015),
Theorem 1.3). The corresponding bound for the limit measure is a Frostman-type bound of the LQG measure
(`LatticeProb.LQG.ae_exists_compact_center_ball_power_bound_of_vague_limit`).

Sources: the uniform moment estimates of the circle-average approximations, Garban–Rhodes–Vargas (2016),
*Liouville Brownian motion*, §2, and Berestycki (2015), *Diffusion in planar Liouville quantum gravity*, §2; for the
whole-plane GFF plus an `α log` singularity, the Green-potential form of the bound is
`HarmonicBalls.IsWholePlaneGFF.ae_singular_green_integral_ball_bound` (Harmonic-Balls-LQG,
Proofs/Potential/LQGUniformGreenTail.lean); the γ-quantum cone field agrees with such a field on discs up to a
scaling of the embedding.

Proved: `coneApproxBallPowerStmt` (`ConeApproxBallPowerProof.lean`), for `0 < γ < 2`.
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal

namespace MatedCRT

/-- **Uniform small-ball power bound for the dyadic approximations of the cone LQG measure.** In every valid
environment, almost surely, for every `R > 0` there are `β > 0` and `t₀ > 0` such that, for all `n`, all centers
`x ∈ B̄(0, R)` and all `t ∈ (0, t₀)`, `μ_{ε_n}(B(x, t)) ≤ t^β`, where `μ_{ε_n} = ε_n^{γ²/2} e^{γ h_{ε_n}(z)} dz` is the
circle-average approximation of the γ-LQG measure of the γ-quantum cone field at `ε_n = 2^{-n}`.

Proved: `coneApproxBallPowerStmt` (`ConeApproxBallPowerProof.lean`), for `0 < γ < 2`. -/
def ConeApproxBallPowerStmt (γ : ℝ) : Prop :=
  ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ R : ℝ, 0 < R → ∃ β > (0 : ℝ), ∃ t₀ > (0 : ℝ), ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R,
      ∀ t : ℝ, 0 < t → t < t₀ →
        HarmonicBalls.lqgApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β)

end MatedCRT
