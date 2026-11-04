import MatedCRT.Draft.Section4
import MatedCRT.Draft.Section5
import MatedCRT.Draft.Section6
import MatedCRT.Draft.Section7
import MatedCRT.Draft.Section8
import MatedCRT.Proofs.Sec8.Annealed

/-!
# Proposition 8.1 from Propositions 4.2, 5.1, 6.1 and 7.1 (line 3270)

The paper states Proposition 8.1 as the combination of the lower bounds (Propositions 4.2 and 5.1:
`B⁻_δ(Λ_t) ⊆ 𝒳̄_ε(t ε⁻¹)`) and the upper bounds (Propositions 6.1 and 7.1: `𝒳̄_ε(t ε⁻¹) ⊆ B⁺_δ(Λ_t)`), all on the event
`{t < T}` and except on an event of probability tending to `0`. The combination is a union bound: for the IDLA cluster
for the annealed outer probability (`MatedCRTEnv.idlaProb`, countably subadditive,
`Sec8.annealedOuterProb_le_add_of_subset_union`), for the divisible sandpile for the outer measure `P`. No other input
is used; only the first conjunct of Proposition 5.1 (unstopped walkers) enters.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Proposition 8.1** (prop:IDLA-constrained-convergence, line 3270) from Propositions 4.2, 5.1, 6.1 and 7.1: for
`δ ∈ (0, ρ)` and `t > 0`, on `{t < T}`, except on an event of probability tending to `0`,
`B⁻_δ(Λ_t) ⊆ 𝒳̄_ε(t ε⁻¹) ⊆ B⁺_δ(Λ_t)` for the IDLA cluster and the divisible sandpile cluster. -/
theorem iDLAConstrainedConvergence_of_steps (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮) :
    IDLAConstrainedConvergenceStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨?_, ?_⟩
  · have hA := (h51 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht).1
    have hB := h61 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hA.add hB)
      (fun _ => zero_le) (fun ε => ?_)
    refine Sec8.annealedOuterProb_le_add_of_subset_union S.P _ ?_
    rintro ⟨ω, xs⟩ ⟨hT, hn⟩
    by_cases h1 : innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (idlaCluster xs ⌊t / ε⌋₊)
    · exact Or.inr ⟨hT, fun h2 => hn ⟨h1, h2⟩⟩
    · exact Or.inl ⟨hT, h1⟩
  · have hA := h42 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
    have hB := h71 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
    unfold TendsToOneOn at hA hB ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hA.add hB)
      (fun _ => zero_le) (fun ε => ?_)
    refine (measure_mono ?_).trans (measure_union_le _ _)
    rintro ω ⟨hT, hn⟩
    by_cases h1 : innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (sandpileCluster (S.mult ε ω) (t / ε))
    · exact Or.inr ⟨hT, fun h2 => hn ⟨h1, h2⟩⟩
    · exact Or.inl ⟨hT, h1⟩

end MatedCRT
