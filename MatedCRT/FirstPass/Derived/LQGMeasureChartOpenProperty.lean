import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth

/-!
# The coordinate change of the LQG measure on open sets

`OpenChartProp γ f h μ`: for every open set `V` and every injective holomorphic map `ψ` on `V` with bounded image, the
smooth approximations (Sheffield–Wang (2016), §3.2) of the field `h ∘ φ + Q log |φ'|` on `ψ(V)`, `φ = ψ⁻¹`, converge
weakly inside `ψ(V)` along `2^{-k}` to the measure `ν` with `ν(A) = μ(φ(A))`. This is the property of the field and its
LQG measure that the localization step of the coordinate change for all inverse charts produces on the open sets
covered by discs, and that the inverse charts use (`LQGMeasureChartStmt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Distributions

namespace MatedCRT

namespace LQGMeasureChart

/-- **The pairings of `h ∘ φ + Q log |φ'|` on `ψ(V)`** for a field `h` on the plane and a conformal map
`ψ : V → ψ(V)` with inverse `φ = ψ⁻¹`: `(h ∘ φ, u) = (h, |ψ'|² u ∘ ψ)` plus `Q ∫ log |φ'| u`, `Q = 2/γ + γ/2`
(Sheffield–Wang (2016), (1.6), Proposition 2.3, Remark 3.3). -/
def pullbackPairingOn (γ : ℝ) (h : LQGMetric.DistC) (V : Set ℂ) (ψ : ℂ → ℂ) (u : ℂ → ℝ) : ℝ :=
  pairFun (V := ⊤) h (V.indicator fun x => u (ψ x) * ‖deriv ψ x‖ ^ 2) +
    (2 / γ + γ / 2) * ∫ w, Real.log ‖deriv (Function.invFunOn ψ V) w‖ * u w

/-- **The coordinate change of the LQG measure `μ` of the field `h` on every open set**: for every open `V` and every
injective holomorphic `ψ` on `V` with bounded image, the smooth approximations of `h ∘ φ + Q log |φ'|` on `ψ(V)`
converge weakly inside `ψ(V)` along `2^{-k}` to a measure `ν` with `ν(A) = μ(V ∩ ψ⁻¹(A))` for Borel `A ⊆ ψ(V)`. -/
def OpenChartProp (γ : ℝ) (f : ℂ → ℝ) (h : LQGMetric.DistC) (μ : Measure ℂ) : Prop :=
  ∀ V : Set ℂ, IsOpen V → ∀ ψ : ℂ → ℂ, InjOn ψ V → DifferentiableOn ℂ ψ V →
    Bornology.IsBounded (ψ '' V) →
    ∃ ν : Measure ℂ,
      QuantumZipper.IsVagueLimitOn (ψ '' V)
        (fun k => smoothApprox γ f (ψ '' V) (pullbackPairingOn γ h V ψ) (HarmonicBalls.dyadicScale k)) ν ∧
      ∀ A : Set ℂ, MeasurableSet A → A ⊆ ψ '' V → ν A = μ (V ∩ ψ ⁻¹' A)

end LQGMeasureChart

end MatedCRT
