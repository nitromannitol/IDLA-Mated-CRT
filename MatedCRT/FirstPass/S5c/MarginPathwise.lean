import MatedCRT.FirstPass.S5c.MarginInf

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), outcome-wise margin): the hypotheses of `marginInf_pathwise`

For one outcome with `Λ` a cone family (`IsConeHarmonicBallFamily μ Λ`) and `t < T = clusterExitTime Λ ρ`, `0 < t`:

* the margin `A x = w_t x - 2 w_{t/2} x` is continuous on the closed ball `B̄_ρ`
  (`continuousOn_leastSupersolution_of_le_clusterExitTime`, both `t/2 ≤ t < T`);
* the fixed-index gap (A8, `fixedIndexMargin_lower_bound_on_compact`, with the frozen strong minimum principle) gives a
  uniform `β > 0` on the compact core `marginCore Λ_t ρ δ ⊆ Λ_t`;
* hence the countable infimum `marginInf` satisfies the pathwise bounds of `marginInf_pathwise`.

No measure theory and no new frozen input: the outcome-wise cover `hcover` is the (3.1) hypothesis of A8.
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric Laplacian

theorem margin_continuousOn_closedBall {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ) (ht : 0 < t) :
    ContinuousOn (fun x => leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x)
      (closedBall 0 ρ) := by
  have h1 := continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT ht le_rfl
  have h2 := continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT (half_pos ht) (by linarith)
  exact h1.sub (continuousOn_const.mul h2)

/-- The complement of the cluster is nonempty (the cluster lies in `B̄_ρ`). -/
theorem compl_cluster_nonempty {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ) (ht : 0 < t) :
    (Λ t)ᶜ.Nonempty := by
  refine ⟨((ρ + 1 : ℝ) : ℂ), fun h => ?_⟩
  have h2 := cluster_subset_closedBall_of_lt_clusterExitTime hfam hρ hT ht h
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h2
  linarith

/-- **Outcome-wise margin** (three-inputs (4.1) and (b), pathwise): for a cone family with `t < T` and the cover
`hcover`, there is `β > 0` with `min 1 β ≤ marginInf D I A` and `marginInf D I A ≤ A x` on `K_δ`. -/
theorem margin_pathwise (hmin : FPStrongMinimumPrinciple) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hT : t < clusterExitTime Λ ρ) (ht : 0 < t)
    (hcover : ∀ x ∈ Λ t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ s)
    {D : Set ℂ} (hD : Dense D) (hDne : D.Nonempty) :
    ∃ β : ℝ, 0 < β ∧
      min 1 β ≤ marginInf D (marginIndex (Λ t) ρ δ)
        (fun x => leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x) ∧
      ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x (Λ t)ᶜ →
        marginInf D (marginIndex (Λ t) ρ δ)
            (fun x => leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x) ≤
          leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x := by
  obtain ⟨β, hβ, hβA⟩ := fixedIndexMargin_lower_bound_on_compact hmin hfam hρ hT ht hcover
    (isCompact_marginCore (Λ t) ρ δ) (marginCore_subset hδ)
  obtain ⟨h1, h2⟩ := marginInf_pathwise hD hDne hρ hδ (compl_cluster_nonempty hfam hρ hT ht)
    (margin_continuousOn_closedBall hfam hρ hT ht) hβA
  exact ⟨β, hβ, h1, h2⟩

end MatedCRT.S5c
