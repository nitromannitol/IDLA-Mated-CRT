import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Defs.Map

/-!
# Geometric inputs of the trace bound of the printed Lemma 6.8 (D)

The hypotheses of `ConfigBound68.trace_half` about the cells `cell ε η k = η '' Icc (ε (k-1)) (ε k)`:

* `ae_continuous_eta`: almost surely `η` is continuous (from the `areaParam` clause of `IsValid.matingOfTrees`);
* `cell_isBounded`, `cell_isPreconnected`, `cell_nonempty`: deterministic, from continuity;
* `ae_adjacent`: almost surely adjacent vertices have intersecting cells (`adjacentCellsMeetAeStep`, proved);
* `closure_cells_meet_of_mult`: the closed-cell form `hadj` of `trace_half`;
* `cellVertices_finite_of_tendsto`: a bounded set meets finitely many cells when `η` is proper
  (`IsValid.ae_tendsto_cocompact`, proved; this replaces the frozen `FrozenProperEta`).

Geometric assumptions (cells are nonempty compact connected sets; adjacent cells intersect; `η(t) → ∞`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace MatedCRT

namespace TraceInputs68

/-- Almost surely the space-filling curve `η` is continuous: `η ω = ηL ω ∘ φ` with `ηL ω` a continuous path and
`φ` a homeomorphism (the `areaParam` clause of the mating-of-trees coupling). -/
theorem ae_continuous_eta {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, Continuous (S.η ω) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  filter_upwards [hC.areaParam, htie] with ω hap hω
  obtain ⟨⟨φ, -, hφ⟩, -⟩ := hap
  have hη : S.η ω = ηL ω ∘ φ := by
    rw [← hω.1]
    funext t
    exact hφ t
  rw [hη]
  exact (ηL ω).continuous.comp φ.toHomeomorph.continuous

/-- A continuous `η` maps a compact interval to a bounded set: every cell is bounded. -/
theorem cell_isBounded {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

/-- A continuous `η` maps an interval to a connected set: every cell is preconnected. -/
theorem cell_isPreconnected {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

/-- Every cell is nonempty when `ε > 0`. -/
theorem cell_nonempty {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (k : ℤ) : (cell ε η k).Nonempty := by
  have hle : ε * ((k : ℝ) - 1) ≤ ε * (k : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  exact (nonempty_Icc.mpr hle).image η

/-- Almost surely, for every `ε > 0`, adjacent vertices of the mated-CRT map have intersecting cells. -/
theorem ae_adjacent {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
  adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS

/-- The closed-cell form of adjacency, the hypothesis `hadj` of `ConfigBound68.trace_half`. -/
theorem closure_cells_meet_of_mult {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ}
    (h : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    ∀ u v, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty := by
  intro u v hu
  obtain ⟨x, hx1, hx2⟩ := h u v hu
  exact ⟨x, subset_closure hx1, subset_closure hx2⟩

/-- **Finitely many cells meet a bounded set.** If `η` is proper (`Tendsto η (cocompact ℝ) (cocompact ℂ)`) and
`ε > 0`, then the vertices whose cells meet a bounded set `D` form a finite set. Proof: `η⁻¹(D̄ᶜ)` contains the
complement of a compact `C ⊆ ℝ`, so every `t` with `η t ∈ D` lies in `C ⊆ [-M, M]`; a cell meeting `D` contains such
a `t`, and `ε (k - 1) ≤ t ≤ ε k` confines `k` to a finite integer interval. -/
theorem cellVertices_finite_of_tendsto {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Tendsto η (cocompact ℝ) (cocompact ℂ)) {D : Set ℂ} (hD : Bornology.IsBounded D) :
    (cellVertices ε η D).Finite := by
  have hKc : (closure D)ᶜ ∈ cocompact ℂ := hD.isCompact_closure.compl_mem_cocompact
  obtain ⟨C, hC, hCsub⟩ := Filter.mem_cocompact.mp (hη hKc)
  obtain ⟨M, hM⟩ := hC.isBounded.subset_closedBall 0
  have hbd : ∀ t, η t ∈ D → -M ≤ t ∧ t ≤ M := by
    intro t ht
    have htC : t ∈ C := by
      by_contra hn
      exact hCsub hn (subset_closure ht)
    have h1 := hM htC
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at h1
    exact h1
  apply Set.Finite.subset (Set.finite_Icc ⌊-M / ε⌋ (⌈M / ε⌉ + 1))
  intro k hk
  obtain ⟨x, hxc, hxD⟩ := hk
  obtain ⟨t, ht, rfl⟩ := hxc
  have hb := hbd _ hxD
  have hlow : -M / ε ≤ (k : ℝ) := by
    rw [div_le_iff₀ hε]
    linarith [ht.2, hb.1, mul_comm ε (k : ℝ)]
  have hup : (k : ℝ) - 1 ≤ M / ε := by
    rw [le_div_iff₀ hε]
    linarith [ht.1, hb.2, mul_comm ε ((k : ℝ) - 1)]
  have hceil := Int.le_ceil (M / ε)
  have hfl := Int.floor_le (-M / ε)
  rw [Set.mem_Icc]
  constructor
  · have : ((⌊-M / ε⌋ : ℤ) : ℝ) ≤ (k : ℝ) := hfl.trans hlow
    exact_mod_cast this
  · have : (k : ℝ) ≤ ((⌈M / ε⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this

end TraceInputs68

end MatedCRT

#print axioms MatedCRT.TraceInputs68.ae_continuous_eta
#print axioms MatedCRT.TraceInputs68.cellVertices_finite_of_tendsto
#print axioms MatedCRT.TraceInputs68.ae_adjacent
