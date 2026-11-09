/- Credit: the merge rule and the direct-identification relation are Leonardo Bonanno's frozen definitions
`MatedCRTHarmonic.MatedCRT.DirectRel` (LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel, commit
31e7483, used unchanged), `MatedCRTHarmonic.MatedCRT.lrCoord` (Frozen.MatedCRTLrCoord) and the mating-of-trees
structure `IsMatingOfTreesCoupling` (Frozen.IsMatingOfTreesCoupling; its `merge` and `boundaryLawBM` fields). Local
ports used: `BrownianAdjacencyExcursions` (strict excursion witnesses, commit ccbbd7a), `AdjacentCells` (the
mating-of-trees environment and coupling-extraction pattern; its abstract `adjacentCellsMeetAeStep` is not used here)
and `CellContacts` (the `cell`/`bmEdgeCount` API, adapted from Bonanno's `MatedCRTHarmonic.RouteM.DLevels`). -/
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.MatingOfTrees.BrownianAdjacencyExcursions

/-!
# Common cell-contact times of adjacent mated-CRT cells (witness form)

Source: `notes/wpn-steps2/steps2-r3.tex` lines 602-630 (audited, sha256 88dfb1f9...), the argument that adjacent
graph cells intersect. For a fixed mesh `ε > 0` and a mating-of-trees environment `S`, almost surely, for every pair
of integers `j, k` with nonzero edge multiplicity `S.mult ε ω j k`, there are times `u` in the closed time cell
`[ε(j-1), εj]` and `v` in the closed time cell `[ε(k-1), εk]` with `S.η ω u = S.η ω v`.

* Consecutive cells `k = j + 1` share the endpoint `εj`, so `u = v = εj` (no adjacency is needed).
* Separated cells `1 < k - j`: the fixed-mesh strict excursion event
  `MatedCRTHarmonic.MatedCRT.SeparatedMinimum.ae_bmAdjacent_strict_excursions` gives, for both boundary-length
  coordinates, the unique middle minimum `τ` and the last/first level times `u`, `v`, with `u = τ` or
  `DirectRel X u τ`, and `τ = v` or `DirectRel X τ v`. The merge rule of the mating-of-trees coupling
  (the merge field of `IsMatingOfTreesCoupling`, recorded there as DMS Lemma 8.8) then gives `η u = η τ = η v`.

The quantifier order is the fixed-mesh one (`∀ ε > 0`, then `∀ᵐ ω`). No event is common to all meshes.
-/

namespace MatedCRT.AdjacentContactWitnesses

open MeasureTheory Set

/-- Merge along a witness chain. If `u` is `τ` or a direct `X`-identification of `u` with `τ`, and `τ` is `v` or a
direct `X`-identification of `τ` with `v`, then the merge rule gives `η u = η v`. -/
theorem eta_eq_of_witness_chain {η : ℝ → ℂ} {X : ℝ → ℝ}
    (hmerge : ∀ s t, MatedCRTHarmonic.MatedCRT.DirectRel X s t → η s = η t) {u τ v : ℝ}
    (h1 : u = τ ∨ MatedCRTHarmonic.MatedCRT.DirectRel X u τ)
    (h2 : τ = v ∨ MatedCRTHarmonic.MatedCRT.DirectRel X τ v) : η u = η v := by
  have e1 : η u = η τ := by
    rcases h1 with h | h
    · rw [h]
    · exact hmerge u τ h
  have e2 : η τ = η v := by
    rcases h2 with h | h
    · rw [h]
    · exact hmerge τ v h
  exact e1.trans e2

/-- Consecutive cells `j` and `j + 1` share the endpoint `εj`, so `u = v = εj` are common contact times. -/
theorem consecutive_contact_times {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) {j k : ℤ} (hk : k = j + 1) :
    ∃ u ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j), ∃ v ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k),
      η u = η v := by
  have hk' : (k : ℝ) = j + 1 := by exact_mod_cast hk
  refine ⟨ε * j, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩,
    ε * j, ⟨le_of_eq (by rw [hk']; ring), mul_le_mul_of_nonneg_left (by linarith) hε.le⟩, rfl⟩

/-- A nonzero edge multiplicity of the mated-CRT map with `j < k` forces one of the two boundary-length adjacency
inequalities (Definition 1.1, eq:edge-map). -/
theorem bmAdjacent_of_bmEdgeCount_ne_zero {ε : ℝ} {L R : ℝ → ℝ} {j k : ℤ} (hjk : j < k)
    (h : bmEdgeCount ε L R j k ≠ 0) : bmAdjacent ε L j k ∨ bmAdjacent ε R j k := by
  by_contra hn
  apply h
  simp [bmEdgeCount, ne_of_lt hjk, min_eq_left hjk.le, max_eq_right hjk.le, hn]

/-- **Fixed-mesh common contact times.** Let `S` be a mating-of-trees environment valid for `γ`, and fix a mesh
`ε > 0`. Almost surely, for all integers `j, k` with nonzero edge multiplicity, there are times `u` in the closed
time cell `[ε(j-1), εj]` and `v` in the closed time cell `[ε(k-1), εk]` with `η u = η v`. The event is simultaneous
for both boundary-length coordinates and all integer pairs. -/
theorem ae_contact_times (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      ∃ u ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j), ∃ v ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k),
        S.η ω u = S.η ω v := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have hA := MatedCRTHarmonic.MatedCRT.SeparatedMinimum.ae_bmAdjacent_strict_excursions
    hC.boundaryLawBM hε
  have hB := ae_of_ae_map hC.measurable_curves.2.2.2.aemeasurable hA
  filter_upwards [hB, hC.merge, htie] with ω hB hmerge htie
  have hmerge' : ∀ (i : Fin 2) (s t : ℝ),
      MatedCRTHarmonic.MatedCRT.DirectRel (fun r => MatedCRTHarmonic.MatedCRT.lrCoord i r (S.bm ω)) s t →
        S.η ω s = S.η ω t := by
    intro i s t h
    rw [← htie.1]
    fin_cases i
    · exact hmerge s t (Or.inl h)
    · exact hmerge s t (Or.inr h)
  have key : ∀ j k : ℤ, j < k → S.mult ε ω j k ≠ 0 →
      ∃ u ∈ Icc (ε * ((j : ℝ) - 1)) (ε * j), ∃ v ∈ Icc (ε * ((k : ℝ) - 1)) (ε * k),
        S.η ω u = S.η ω v := by
    intro j k hjk hne
    by_cases hc : k = j + 1
    · exact consecutive_contact_times hε (S.η ω) hc
    · have hgap : 1 < k - j := by omega
      rcases bmAdjacent_of_bmEdgeCount_ne_zero hjk hne with hL | hR
      · have hL' : MatedCRT.bmAdjacent ε
            (fun t => MatedCRTHarmonic.MatedCRT.lrCoord 0 t (S.bm ω)) j k := hL
        obtain ⟨u, hu, τ, -, v, hv, -, -, h1, h2⟩ := hB 0 j k hgap hL'
        exact ⟨u, by rw [mul_sub, mul_one]; exact hu, v, by rw [mul_sub, mul_one]; exact hv,
          eta_eq_of_witness_chain (hmerge' 0) h1 h2⟩
      · have hR' : MatedCRT.bmAdjacent ε
            (fun t => MatedCRTHarmonic.MatedCRT.lrCoord 1 t (S.bm ω)) j k := hR
        obtain ⟨u, hu, τ, -, v, hv, -, -, h1, h2⟩ := hB 1 j k hgap hR'
        exact ⟨u, by rw [mul_sub, mul_one]; exact hu, v, by rw [mul_sub, mul_one]; exact hv,
          eta_eq_of_witness_chain (hmerge' 1) h1 h2⟩
  intro j k hne
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · exact key j k hjk hne
  · exact absurd (S.mult_self ε ω _) hne
  · obtain ⟨v, hv, u, hu, h⟩ := key k j hkj (by rwa [S.mult_symm ε ω j k] at hne)
    exact ⟨u, hu, v, hv, h.symm⟩

/-- Fixed-mesh cell intersection in the `cell` API, read off from the contact times. Unlike
`AdjacentCellsMeetAeStep` (which places `∀ ε > 0` inside the almost-sure event), the mesh is fixed before the
almost-sure event here; no event is common to all meshes. -/
theorem ae_cell_inter_nonempty (𝒮 : SpaceFillingSLEModel) (γ : ℝ) (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
  filter_upwards [ae_contact_times 𝒮 γ Ω S hS ε hε] with ω hω j k hne
  obtain ⟨u, hu, v, hv, h⟩ := hω j k hne
  exact ⟨S.η ω u, ⟨u, hu, rfl⟩, ⟨v, hv, h.symm⟩⟩

end MatedCRT.AdjacentContactWitnesses
