import MatedCRT.Proofs.Infra.DiscretePotential
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Steps.Infra.MatingOfTrees

/-!
# Local finiteness of the mated-CRT map

For a continuous curve `η` with `η(t) → ∞` as `|t| → ∞`, only finitely many cells `η([ε(k-1), εk])` meet a compact
set (`cellVertices_finite_of_isCompact`). Hence a multiplicity whose adjacent vertices have intersecting cells is
locally finite (`isLocallyFiniteMult_of_cells_meet`), and, given `AdjacentCellsMeetAeStep`, the map `𝒢^ε` of a valid
environment is almost surely locally finite for every `ε > 0` (`MatedCRTEnv.IsValid.ae_isLocallyFiniteMult`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- For a continuous proper curve, finitely many cells meet a compact set. -/
theorem cellVertices_finite_of_isCompact {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) {K : Set ℂ} (hK : IsCompact K) :
    (cellVertices ε η K).Finite := by
  have hpre : IsCompact (η ⁻¹' K) :=
    (isProperMap_iff_tendsto_cocompact.mpr ⟨hη, hp⟩).isCompact_preimage hK
  obtain ⟨T, hT⟩ := hpre.isBounded.subset_closedBall 0
  refine (Set.finite_Icc (⌊-T / ε⌋) (⌈T / ε⌉ + 1)).subset ?_
  rintro k ⟨_, ⟨t, ht, rfl⟩, hz⟩
  have htT : |t| ≤ T := by
    have h := hT (show t ∈ η ⁻¹' K from hz)
    rwa [mem_closedBall_zero_iff, Real.norm_eq_abs] at h
  obtain ⟨htl, htr⟩ := abs_le.mp htT
  obtain ⟨hkl, hkr⟩ := ht
  refine ⟨?_, ?_⟩
  · have h1 : -T ≤ ε * k := by linarith
    have h2 : -T / ε ≤ k := by
      rw [div_le_iff₀ hε, mul_comm]
      exact h1
    exact_mod_cast (Int.floor_le _).trans h2
  · have h1 : ε * (k - 1) ≤ T := by linarith
    have h2 : (k : ℝ) - 1 ≤ T / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      exact h1
    have h3 : (k : ℝ) ≤ (⌈T / ε⌉ : ℝ) + 1 := by linarith [Int.le_ceil (T / ε)]
    exact_mod_cast h3

/-- For a continuous proper curve, a multiplicity whose adjacent vertices have intersecting cells is locally finite. -/
theorem isLocallyFiniteMult_of_cells_meet {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hmeet : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) : IsLocallyFiniteMult m := by
  unfold IsLocallyFiniteMult
  intro a
  have hc : IsCompact (cell ε η a) := isCompact_Icc.image hη
  refine (cellVertices_finite_of_isCompact hη hp hε hc).subset fun b hb => ?_
  obtain ⟨z, hza, hzb⟩ := hmeet a b hb
  exact ⟨z, hzb, hza⟩

/-- Given `AdjacentCellsMeetAeStep`, almost surely the map `𝒢^ε` is locally finite for every `ε > 0`. -/
theorem MatedCRTEnv.IsValid.ae_isLocallyFiniteMult {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ)
    (hcell : AdjacentCellsMeetAeStep 𝒮) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) := by
  filter_upwards [hcell γ hγ0 hγ2 Ω S hS, hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hmeet hp hap
  intro ε hε
  exact isLocallyFiniteMult_of_cells_meet hap.1 hp hε (hmeet ε hε)

end MatedCRT
