import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 8: statement of Proposition 8.1 (lines 3267-3336)

Convergence of IDLA and the divisible sandpile on the event `{t < T}`. Conventions: see
`MatedCRT/Draft/Section1.lean` and `MatedCRT/Draft/Section4.lean`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Proposition 8.1** (prop:IDLA-constrained-convergence, line 3270). For each `δ ∈ (0, ρ)` and `t > 0`, on the
event `{t < T}`, except on an event of probability tending to `0` as `ε → 0`, `B⁻_δ(Λ_t) ⊆ 𝒳̄_ε(t ε⁻¹) ⊆ B⁺_δ(Λ_t)`
for `𝒳 ∈ {A, D}`: both the IDLA cluster (after `⌊t ε⁻¹⌋` walkers; annealed outer probability `MatedCRTEnv.idlaProb`,
review-S (S5)) and the divisible sandpile cluster (mass `t ε⁻¹`). -/
def IDLAConstrainedConvergenceStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    Tendsto (fun ε => S.idlaProb ε {p | t < clusterExitTime (Λ p.1) ρ ∧
        ¬ (innerNbhd δ (Λ p.1 t) ⊆ fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ∧
          fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊) ⊆ outerNbhd δ (Λ p.1 t))})
      (𝓝[>] 0) (𝓝 0) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (sandpileCluster (S.mult ε ω) (t / ε)) ∧
        fillCells ε (S.η ω) (sandpileCluster (S.mult ε ω) (t / ε)) ⊆ outerNbhd δ (Λ ω t)}

end MatedCRT
