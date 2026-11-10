import MatedCRT.FirstPass.S5d.CoverEvent
import MatedCRT.FirstPass.S5c.GreenCount
import MatedCRT.Steps.Sec5.IDLALowerBound

/-!
# The discrete cluster inner bound (G1c) from the compact-containment step (task fp-S5d-5-1-stopped-repair)

Referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md section 3: the strict discrete cluster `matedDiscreteCluster`
(the surplus set `S_ε = {v_ε > 0}`) covers the inner neighbourhood `K_s = B⁻_s(Λ_t)` by `fillCells` with probability tending
to one on `{t < T}` (compact-containment statement (3.1)). This file reduces `DiscreteClusterInnerBoundStep`
(Steps/Sec5/IDLALowerBound.lean:57) to (3.1), `StrictClusterCompactContainmentStep` (NEW, OPEN), and to the cell-size
estimate `CellSizeEstimateStmt` (Lemma 2.8, Draft/Section2.lean:131), through `tendsToOneOn_cover_vertexThresholdSet`
(CoverEvent.lean:78).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **NEW, OPEN (probabilistic input; referee section 3, compact-containment statement (3.1)).** For deterministic `s > 0`
and `t > 0`, on `F = {t < T}`: `P*(F ∩ {∃ a : H^ε_a ∩ K_s ≠ ∅, a ∉ S^ε_t}) → 0`, where `K_s = B⁻_s(Λ_t) = innerNbhd s (Λ_t)`
and `S^ε_t` is the strict discrete cluster `matedDiscreteCluster` (the surplus set `{v_ε > 0}`). Its written argument is
referee section 3 (fixed-time strict positivity, convergence, decoding to every label), which uses the paper's convergence
statements. -/
def StrictClusterCompactContainmentStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ s t : ℝ, 0 < s → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a : ℤ, (cell ε (S.η ω) a ∩ innerNbhd s (Λ ω t)).Nonempty →
        a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t}

/-- A set contained in `B ∪ N` with `P N = 0` has probability at most `P B`. -/
theorem measure_le_of_subset_union_null_fp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {A B N : Set Ω}
    (h : A ⊆ B ∪ N) (hN : P N = 0) : P A ≤ P B := by
  calc P A ≤ P (B ∪ N) := measure_mono h
    _ ≤ P B + P N := measure_union_le _ _
    _ = P B := by rw [hN, add_zero]

/-- **G1c from the compact containment.** `DiscreteClusterInnerBoundStep` follows from the NEW step
`StrictClusterCompactContainmentStep` (with `s = δ/2`) and the cell-size estimate `CellSizeEstimateStmt`. -/
theorem discreteClusterInnerBound_of_compactContainment (𝒮 : SpaceFillingSLEModel) (h28 : CellSizeEstimateStmt 𝒮)
    (hK : StrictClusterCompactContainmentStep 𝒮) : DiscreteClusterInnerBoundStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have := hS.isProbabilityMeasure
  have hK' := hK γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ (δ / 2) t (by positivity) ht
  have hsurjAe : ∀ᵐ ω ∂S.P, Function.Surjective (S.η ω) := by
    filter_upwards [hS.isAreaParametrized] with ω h1
    exact h1.2.2.1
  set N : Set Ω := {ω | ¬ Function.Surjective (S.η ω)} with hN_def
  have hN : S.P N = 0 := ae_iff.1 hsurjAe
  -- the cover of `B⁻_{δ/2}(Λ_t)` by the cells of the strict cluster (off the null set `N`)
  have hcov : TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ}
      fun ε => {ω | innerNbhd (δ / 2) (Λ ω t) ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)} := by
    unfold TendsToOneOn at hK' ⊢
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK'
      (Filter.Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    refine measure_le_of_subset_union_null_fp ?_ hN
    intro ω hω
    obtain ⟨hωF, hωE⟩ := hω
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ⟨hωF, fun hE => hωE ?_⟩
      intro x hx
      obtain ⟨a, hxa⟩ := MatedCRT.S5c.exists_mem_cell_of_surj hε0 (not_not.1 hωN) x
      exact mem_iUnion₂.2 ⟨a, hE a ⟨x, hxa, hx⟩, hxa⟩
  -- the cell-size estimate and Lemma 2.8: the vertex-threshold cover of `B⁻_δ(Λ_t)`
  have hfin := tendsToOneOn_cover_vertexThresholdSet hγ hγ2 hρ hρ1 h28 S hS Λ hΛ δ t hδ ht
    (fun ε ω => matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) hcov
  unfold TendsToOneOn at hfin ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfin
    (Filter.Eventually.of_forall fun _ => zero_le) (Filter.Eventually.of_forall fun ε => measure_mono ?_)
  -- the vertex-threshold set lies in the strict cluster
  intro ω hω
  refine ⟨hω.1, fun h => hω.2 ?_⟩
  intro x hx
  exact IDLALowerBound.fillCells_mono' (fun a ha => (show _ ∧ _ from ha).1.1) (h hx)

end MatedCRT
