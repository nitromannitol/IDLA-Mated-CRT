import MatedCRT.FirstPass.Derived.ExitTimeLowerLemma67
import MatedCRT.FirstPass.Derived.ConeBallRatio

/-!
# Lemma 6.7 of Berestycki-Gwynne with the quantum cone ratio bound supplied

`exitTimeLowerTail_weak` takes the concentric ball-mass ratio bound for the quantum cone measure
(Berestycki-Gwynne, arXiv:2003.10320v2, Lemma A.2) as the hypothesis `h618`. That bound is the theorem
`polyHighProb_coneBallRatio`, applied to the cone field of a valid environment; this file supplies it.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb.Gauss
open scoped ENNReal

/-- **Berestycki-Gwynne, Lemma 6.7** (arXiv:2003.10320, p. 37), in the quantifier order of the printed
statement, with the quantum cone ratio bound (Lemma A.2) proved. Let `0 < γ < 2`, `ℓ > 0`, `a > ℓγ²/2`,
`b > (2 + γ)²ℓ/2` and `ρ ∈ (0, 1)`. For a valid environment and every `θ > 0` there is `δ₀ > 0` such that for
each `δ ∈ (0, δ₀)` there is `ε₀ > 0` with: for `ε ∈ (0, ε₀)`, outside an event of probability at most `θ`, every
vertex `x ∈ V^ε(B_{ρ - δ^ℓ})` satisfies `δ^a ≤ P_x[ε⁻¹ δ^b ≤ τ]`, where `τ` is the exit time from the interior
vertices of `B_{δ^ℓ}(η(x))`. Inputs: the Green kernel lower bound `h213` (Lemma 2.13) and the exit time moment
bound `h214` (Lemma 2.14, first conjunct). -/
theorem exitTimeLowerTail_weak_derived {𝒮 : SpaceFillingSLEModel} (h213 : GreenKernelLowerBoundStmt 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ℓ a b : ℝ} (hℓ : 0 < ℓ)
    (ha : ℓ * γ ^ 2 / 2 < a) (hb : (2 + γ) ^ 2 * ℓ / 2 < b) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ ^ ℓ)),
        ENNReal.ofReal (δ ^ a) ≤ srwLaw (S.mult ε ω) x {y | ENNReal.ofReal (ε⁻¹ * δ ^ b) ≤
          (vExitTime (interiorCellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) (δ ^ ℓ))) y :
            ℝ≥0∞)}}ᶜ ≤ ENNReal.ofReal θ :=
  exitTimeLowerTail_weak h213 h214 hγ hγ2 hℓ ha hb hρ hρ1 hS
    (fun _ hc0 hc1 _ hζ => polyHighProb_coneBallRatio hγ hγ2 hS.isConeField hc0 hc1 hζ) hθ

end MatedCRT.FirstPass.Derived
