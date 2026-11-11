import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockFun

/-!
# Limit occupation clock `Ψ(ψ, b)(s)` (step B2 of the transfer of thm:occ-main)

For a sequence of regularization parameters `ε = (ε_k)_{k ∈ ℕ}`, a family `ψ` of circle averages and a path `b`,
the regularized occupation clock `Ψ_{ε_k}(ψ, b)(q)` of `regClockFun` is defined for every rational time `q ≥ 0`.
The limit clock is obtained by taking, at each time `s`, the infimum over rational `q > s` of the limit superior
along `k` of `Ψ_{ε_k}(ψ, b)(q)`: this is the right-continuous regularization in the time variable, as in the
occupation-time identities of Duplantier-Sheffield and Berestycki-Powell for the LQG measure.

The lemma of this file gives joint measurability of `(ψ, b) ↦ Ψ(ψ, b)(s)` for a measurable exit time `σ`, from
the joint measurability of each `regClockFun` (`measurable_regClockFun`), `Measurable.limsup` over `ℕ` and
`Measurable.iInf` over the countable index set `{q : ℚ≥0 // s < q}`. Identification of the limit clock with the
occupation measure of the coupled model is a later step and is not stated here.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The limit occupation clock `Ψ(ψ, b)(s) = inf_{q ∈ ℚ≥0, q > s} limsup_k Ψ_{ε_k}(ψ, b)(q)`, where
`Ψ_{ε_k}` is the regularized clock `regClockFun` at parameter `ε_k` (B2 of MQ-li-8 (b)). -/
noncomputable def limClockFun (γ : ℝ) (ε : ℕ → ℝ) (ψ : UnitDiskCircleIndex → ℝ) (σ : ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) (s : ℝ≥0) : ℝ≥0∞ :=
  ⨅ q : {q : ℚ≥0 // s < (q : ℝ≥0)}, Filter.limsup (fun k => regClockFun γ (ε k) ψ σ b (q.1 : ℝ≥0)) Filter.atTop

/-- **Step B2 (measurability of the limit clock).** For a measurable exit time `σ`, the map
`(ψ, b) ↦ Ψ(ψ, b)(s)` is measurable for the product of the cylinder σ-algebra on `UnitDiskCircleIndex → ℝ` and the
Borel σ-algebra on `ContinuousPath ℂ`. -/
theorem measurable_limClockFun (γ : ℝ) (ε : ℕ → ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ) (s : ℝ≥0) :
    Measurable fun p : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ => limClockFun γ ε p.1 σ p.2 s := by
  unfold limClockFun
  refine Measurable.iInf fun q => ?_
  exact Measurable.limsup fun k => measurable_regClockFun γ (ε k) σ hσ (q.1 : ℝ≥0)

end MatedCRT.KilledOccupation
