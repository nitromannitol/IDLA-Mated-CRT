import MatedCRT.FirstPass.S5c.Core

/-!
# FIRST PASS, Lemma 5.3 and E-c1-5: the exterior mass of the filled cluster tends to zero (B2 outcome, deterministic)

On a fixed outcome (CHATGPT-5-1-B2-Ec15.md §1, the step `M_k := μ_h(U_{ε_k} \ Λ_t) → 0`): let `L = Λ_t` be open and bounded
with `μ L = t` and `U_k` the filled discrete clusters with `μ(U_k) ≤ t` (eq. (7)). If every compact core `K_δ` of `L`
(compactCore, eq. (10)) lies in `U_k` for all large `k`, then `μ(U_k \ L) → 0`. Proof: `μ(U \ L) ≤ μ(L \ U)` from the mass bound,
`μ(L \ U) ≤ μ(L \ K_δ)` once `K_δ ⊆ U`, and `μ(L \ K_{1/(j+1)}) → 0` since the cores exhaust `L` (continuity from above, `μ L < ∞`).
Pure measure theory and plane topology.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- The cores exhaust `L`: every point of the open set `L` lies in `K_{1/(j+1)}` for some `j`. -/
lemma exists_core_of_mem {L : Set ℂ} {ρ : ℝ} (hL : IsOpen L) (hLc : Lᶜ.Nonempty)
    (hLball : L ⊆ closedBall (0 : ℂ) ρ) {x : ℂ} (hx : x ∈ L) :
    ∃ j : ℕ, x ∈ compactCore L ρ (1 / ((j : ℝ) + 1)) := by
  have hpos : 0 < infDist x Lᶜ := (hL.isClosed_compl.notMem_iff_infDist_pos hLc).1 (not_not.2 hx)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 2 * infDist x Lᶜ by linarith)
  exact ⟨j, hLball hx, by show 1 / ((j : ℝ) + 1) / 2 ≤ infDist x Lᶜ; linarith⟩

/-- The cores increase with the index (the level `1/(j+1)` decreases). -/
lemma compactCore_mono_index {L : Set ℂ} {ρ : ℝ} {j j' : ℕ} (h : j ≤ j') :
    compactCore L ρ (1 / ((j : ℝ) + 1)) ⊆ compactCore L ρ (1 / ((j' : ℝ) + 1)) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have h2 : 1 / ((j : ℝ) + 1) / 2 ≤ infDist x Lᶜ := hx.2
  have hj : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast h
  have hle : 1 / ((j' : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  show 1 / ((j' : ℝ) + 1) / 2 ≤ infDist x Lᶜ
  linarith

/-- The complements of the cores decrease to `∅`, so their masses tend to zero (`μ L < ∞`). -/
lemma measure_core_compl_tendsto {μ : Measure ℂ} {L : Set ℂ} {ρ : ℝ} (hL : IsOpen L) (hLc : Lᶜ.Nonempty)
    (hLball : L ⊆ closedBall (0 : ℂ) ρ) (hμL : μ L ≠ ⊤) :
    Tendsto (fun j : ℕ => μ (L \ compactCore L ρ (1 / ((j : ℝ) + 1)))) atTop (𝓝 0) := by
  have hmeas : ∀ j : ℕ, NullMeasurableSet (L \ compactCore L ρ (1 / ((j : ℝ) + 1))) μ := fun j =>
    (hL.measurableSet.diff (isCompact_compactCore L ρ _).isClosed.measurableSet).nullMeasurableSet
  have hanti : Antitone (fun j : ℕ => L \ compactCore L ρ (1 / ((j : ℝ) + 1))) := by
    intro j j' h x hx
    exact ⟨hx.1, fun hc => hx.2 (compactCore_mono_index h hc)⟩
  have hfin : ∃ i : ℕ, μ (L \ compactCore L ρ (1 / ((i : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top hμL (measure_mono sdiff_subset)⟩
  have hlim := tendsto_measure_iInter_atTop hmeas hanti hfin
  have hempty : (⋂ j : ℕ, L \ compactCore L ρ (1 / ((j : ℝ) + 1))) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hxL : x ∈ L := (mem_iInter.1 hx 0).1
    obtain ⟨j, hj⟩ := exists_core_of_mem hL hLc hLball hxL
    exact (mem_iInter.1 hx j).2 hj
  rw [hempty, measure_empty] at hlim
  exact hlim

/-- **Exterior mass against the interior** (eq. (7) argument of G-5-3): if `μ U ≤ μ L < ∞` with `L` open, then
`μ(U \ L) ≤ μ(L \ U)`. -/
lemma exterior_le_interior_complement {μ : Measure ℂ} {L U : Set ℂ} (hL : IsOpen L) (hLfin : μ L ≠ ⊤)
    (hU : μ U ≤ μ L) : μ (U \ L) ≤ μ (L \ U) := by
  have hX : μ (L ∩ U) ≠ ⊤ := ne_top_of_le_ne_top hLfin (measure_mono inter_subset_left)
  have hadd : μ (U ∩ L) + μ (U \ L) = μ U := measure_inter_add_sdiff U hL.measurableSet
  have hcov : μ L ≤ μ (L ∩ U) + μ (L \ U) := by
    calc μ L ≤ μ ((L ∩ U) ∪ (L \ U)) := by
          apply measure_mono
          intro x hx
          by_cases h : x ∈ U
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
      _ ≤ _ := measure_union_le _ _
  have hle : μ (L ∩ U) + μ (U \ L) ≤ μ (L ∩ U) + μ (L \ U) := by
    calc μ (L ∩ U) + μ (U \ L) = μ (U ∩ L) + μ (U \ L) := by rw [inter_comm]
      _ = μ U := hadd
      _ ≤ μ L := hU
      _ ≤ _ := hcov
  exact ENNReal.le_of_add_le_add_left hX hle

/-- **Exterior mass tends to zero** (B2 outcome, deterministic): if `μ L = t < ∞`, the filled clusters `U_k` have `μ(U_k) ≤ t`,
and every core `K_{1/(j+1)}` lies in `U_k` for all large `k`, then `μ(U_k \ L) → 0`. -/
theorem exterior_mass_tendsto_zero_of_cover {μ : Measure ℂ} {L : Set ℂ} {ρ t : ℝ} {U : ℕ → Set ℂ}
    (hL : IsOpen L) (hLball : L ⊆ closedBall (0 : ℂ) ρ) (hLc : Lᶜ.Nonempty) (hμL : μ L = ENNReal.ofReal t)
    (hUm : ∀ k, μ (U k) ≤ ENNReal.ofReal t)
    (hcover : ∀ j : ℕ, ∀ᶠ k in atTop, compactCore L ρ (1 / ((j : ℝ) + 1)) ⊆ U k) :
    Tendsto (fun k => μ (U k \ L)) atTop (𝓝 0) := by
  have hLfin : μ L ≠ ⊤ := by
    rw [hμL]
    exact ENNReal.ofReal_ne_top
  have hcore := measure_core_compl_tendsto hL hLc hLball hLfin
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.1 hcore ε hε).exists
  filter_upwards [hcover j] with k hk
  have hU : μ (U k) ≤ μ L := (hUm k).trans_eq hμL.symm
  have h1 : μ (U k \ L) ≤ μ (L \ U k) := exterior_le_interior_complement hL hLfin hU
  have h2 : μ (L \ U k) ≤ μ (L \ compactCore L ρ (1 / ((j : ℝ) + 1))) :=
    measure_mono (sdiff_subset_sdiff_right hk)
  exact h1.trans (h2.trans hj)

end MatedCRT.S5c
