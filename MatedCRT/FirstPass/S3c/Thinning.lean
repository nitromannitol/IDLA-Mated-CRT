import MatedCRT.Steps.Sec3.DiscretePotentialTightness

/-!
# Deterministic thinning for Lemma 3.1 (corrected, [C11])

`exists_polySummable_thinning`: every deterministic sequence `σ₀ > 0` with `σ₀ → 0` has a strictly increasing
subsequence `k ↦ σ₀ (φ k)` which is polynomially summable (`IsPolySummableScales`). This is the deterministic thinning
of [C11] ("First thin each deterministic sequence deterministically"); the thinned scales feed the Borel-Cantelli step
`ae_eventually_mem_of_polyHighProb`, which needs `∑ e_j^p < ∞` for every `p > 0`.
-/

open Filter Topology

namespace MatedCRT.S3c

/-- **Deterministic thinning** (C11): a positive sequence tending to zero has a polynomially summable subsequence. -/
theorem exists_polySummable_thinning {σ₀ : ℕ → ℝ} (hpos : ∀ n, 0 < σ₀ n) (hlim : Tendsto σ₀ atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsPolySummableScales (fun k => σ₀ (φ k)) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨φ, hφ, hbd⟩ := Filter.extraction_forall_of_eventually
    (P := fun k n => σ₀ n < (1 / 2 : ℝ) ^ k)
    (fun k => hlim.eventually (gt_mem_nhds (pow_pos hhalf k)))
  refine ⟨φ, hφ, fun k => hpos (φ k), fun p hp => ?_⟩
  have hr0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p := Real.rpow_nonneg hhalf.le p
  have hr1 : (1 / 2 : ℝ) ^ p < 1 := Real.rpow_lt_one hhalf.le (by norm_num) hp
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (hpos (φ k)).le p) (fun k => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  calc σ₀ (φ k) ^ p ≤ ((1 / 2 : ℝ) ^ k) ^ p :=
        Real.rpow_le_rpow (hpos (φ k)).le (hbd k).le hp.le
    _ = ((1 / 2 : ℝ) ^ p) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hhalf.le, ← Real.rpow_natCast,
          ← Real.rpow_mul hhalf.le, mul_comm]

end MatedCRT.S3c
