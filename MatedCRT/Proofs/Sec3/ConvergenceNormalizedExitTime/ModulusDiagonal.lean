import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ModulusFromTightness

/-! Diagonal criterion for an asymptotic modulus in probability. -/

namespace MatedCRT

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- A decreasing family of oscillation events has a fixed-scale probability
bound if every deterministic subsequence has vanishing diagonal probabilities. -/
theorem exists_fixed_scale_of_diagonal_probabilities
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℕ → ℕ → Set Ω)
    (hmono : ∀ k l n, k ≤ l → E l n ⊆ E k n)
    (hdiag : ∀ ψ : ℕ → ℕ, StrictMono ψ →
      Tendsto (fun k => P (E k (ψ k))) atTop (𝓝 0))
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ k, ∀ᶠ n in atTop, P (E k n) ≤ e := by
  classical
  by_contra hcontra
  have hfail : ∀ k N, ∃ n, N ≤ n ∧ e < P (E k n) := by
    intro k N
    by_contra hnone
    apply hcontra
    refine ⟨k, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_of_not_gt (fun hb => hnone ⟨n, hn, hb⟩)
  choose g hg using fun k => hfail k k
  obtain ⟨φ, hφ, hgφ⟩ := strictMono_subseq_of_id_le (fun k => (hg k).1)
  have hlim := hdiag (g ∘ φ) hgφ
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1 hlim e he).exists
  have hφge : k ≤ φ k := hφ.id_le k
  have hcompare : P (E (φ k) (g (φ k))) ≤ P (E k (g (φ k))) :=
    measure_mono (hmono k (φ k) (g (φ k)) hφge)
  exact (not_lt_of_ge (hcompare.trans hk)) (hg (φ k)).2

end MatedCRT
