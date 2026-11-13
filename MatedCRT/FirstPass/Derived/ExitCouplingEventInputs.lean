import MatedCRT.FirstPass.Derived.LimLimSmall
import MatedCRT.FirstPass.Derived.ExitTimeLowerLemma611Strong

/-!
# Negligible failure events for the inputs of Proposition 6.12 of Berestycki-Gwynne

Berestycki and Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*
(arXiv:2003.10320), Proposition 6.12 compares the walks from two nearby starting vertices in an environment
`(h, η)` that satisfies, simultaneously, three estimates: the expected exit time bound of Lemma 2.19, the lower
tail of the exit time of Lemma 6.11, and the successive exit bound (6.36) (Lemma 6.10).  All three hold with
probability tending to `1` as `ε → 0` and then `δ → 0`.  This file states the first two in the form of
`LimLimSmall` for the failure events, with exactly the conclusion that the deterministic good-environment
theorem `ExitCouplingGoodEnv.levyProkhorovEDist_stoppedWalk_le_of_goodEnv` consumes.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ExitCouplingEventInputs

open MeasureTheory Set Metric Filter LatticeProb.Gauss MatedCRT.FirstPass.Derived
open scoped ENNReal Topology

/-- **Lemma 2.19 as a negligible failure event.** With the exponent `q = q(γ) > 0` of Lemma 2.19, for every
valid environment and every `ρ ∈ (0, 1)` the event that some ball `B_s(y) ⊆ B_ρ` has a vertex `a` whose expected
exit time from the interior vertices of `B_s(y)` exceeds `ε⁻¹ s^q` is negligible as `ε → 0` and then `s → 0`. -/
theorem limLimSmall_expectedExitTime {𝒮 : SpaceFillingSLEModel}
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ q : ℝ, 0 < q ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      LimLimSmall S.P (fun s ε => {ω | ¬ ∀ y : ℂ, ball y s ⊆ ball (0 : ℂ) ρ → ∀ a : ℤ,
        expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y s)) a ≤
          ENNReal.ofReal (ε⁻¹ * s ^ q)}) := by
  obtain ⟨_, q, -, hq, h⟩ := h219 γ hγ hγ2
  refine ⟨q, hq, fun ρ hρ hρ1 Ω _ S hS => ?_⟩
  have hlim := h ρ hρ hρ1 Ω S hS
  refine LimLimSmall.mono ?_ (LimLimSmall.of_tendsto_limsup (P := S.P) hlim.2)
  intro s ε ω hω hG
  exact hω fun y hy a => (hG y hy a).2

/-- **Lemma 6.11 (strong form) as a negligible failure event.** For `χ > 2(2 + γ)/(2 - γ)` and `ρ ∈ (0, 1)`
there is a superpolynomial `ψ`, depending only on the model, such that for every valid environment the event
that some vertex `x ∈ V^ε(B_{ρ - δ})` leaves `V^ε(B_δ(η(x)))` before time `ε⁻¹ δ^χ` with probability
exceeding `ψ(δ)` is negligible as `ε → 0` and then `δ → 0`.  The input `h632` is the estimate (6.32) (the
conclusion of Lemma 6.9). -/
theorem limLimSmall_exitTimeLower_611 {𝒮 : SpaceFillingSLEModel} (h213 : GreenKernelLowerBoundStmt 𝒮)
    (h214 : ExitTimeUpperBoundStmt 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ}
    (hχ : 2 * (2 + γ) / (2 - γ) < χ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h632 : ∀ ℓ : ℝ, 1 < ℓ → ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ ψ₀ : ℝ → ℝ,
      ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ₀ δ) ∧ ψ₀ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ₀ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ θ : ℝ, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        S.P {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y <
              SuccessiveExitGaps.succExit
                (fun z => cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) z) (δ ^ ℓ)))
                ⌊δ ^ (-((2 - ζ) * (ℓ - 1)))⌋₊ y} ≤ ENNReal.ofReal (ψ₀ δ)}ᶜ ≤ ENNReal.ofReal θ) :
    ∃ ψ : ℝ → ℝ, ((∀ δ : ℝ, 0 ≤ δ → 0 ≤ ψ δ) ∧ ψ 0 = 0 ∧
        ∀ p : ℝ, 0 < p → Tendsto (fun δ => δ ^ (-p) * ψ δ) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        LimLimSmall S.P (fun δ ε => {ω | ¬ ∀ x ∈ cellVertices ε (S.η ω) (ball 0 (ρ - δ)),
          srwLaw (S.mult ε ω) x {y |
            (vExitTime (cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) x) δ)) y : ℝ≥0∞) <
              ENNReal.ofReal (ε⁻¹ * δ ^ χ)} ≤ ENNReal.ofReal (ψ δ)}) := by
  obtain ⟨ψ, hψ, h⟩ := exitTimeLowerTail_611_strong h213 h214 hγ hγ2 hχ hρ hρ1 h632
  refine ⟨ψ, hψ, fun Ω _ S hS θ hθ => ?_⟩
  obtain ⟨δ₀, hδ₀, h'⟩ := h θ hθ
  exact ⟨δ₀, hδ₀, fun δ hδ hδlt => h' δ hδ hδlt Ω S hS⟩

end ExitCouplingEventInputs
end MatedCRT

#print axioms MatedCRT.ExitCouplingEventInputs.limLimSmall_expectedExitTime
#print axioms MatedCRT.ExitCouplingEventInputs.limLimSmall_exitTimeLower_611
