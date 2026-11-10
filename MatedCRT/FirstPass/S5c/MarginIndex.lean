import MatedCRT.FirstPass.S5c.MarginPathwise
import MatedCRT.FirstPass.S5c.IndexPathwise

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), step M4c): the outcome-wise margin on the closure index

For one outcome with `Λ` a cone family (`IsConeHarmonicBallFamily μ Λ`) and `t < T = clusterExitTime Λ ρ`, `0 < t`:

* the obstacle characterisation (`SatisfiesObstacleCharacterization`, condition (c) of Theorem 2.3) with `r = ρ/3`
  (`subset_ball_of_lt_clusterExitTime`) gives `Λ t = interior (closure (cluster μ ρ 0 t))`;
* hence the closure index `closureIndex (cluster μ ρ 0 t) ρ δ` of the cluster is contained in the margin index
  `marginIndex (Λ t) ρ δ`, and it is `δ/2`-dense in every point `x` with `B(x, δ/2) ⊆ Λ t`
  (`closureIndex_near`), so `marginInf_pathwise_index` applies with the countable index set `ratComplexNZ`.

No measure theory and no new frozen input beyond `FPStrongMinimumPrinciple` (through `fixedIndexMargin_lower_bound_on_compact`).
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric Laplacian

/-- **Outcome-wise margin on the closure index** (three-inputs (b), M4c): for a cone family with `t < T` and the cover
`hcover`, there is `β > 0` such that the countable infimum of the margin over the Gaussian rationals `ratComplexNZ`,
restricted to the closure index of the cluster, is at least `min 1 β` and at most the margin `A x` on `K_δ`. -/
theorem margin_pathwise_closureIndex (hmin : FPStrongMinimumPrinciple) {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hT : t < clusterExitTime Λ ρ) (ht : 0 < t)
    (hcover : ∀ x ∈ Λ t, ∃ s, 0 < s ∧ s < t ∧ x ∈ Λ s) :
    ∃ β : ℝ, 0 < β ∧
      min 1 β ≤ marginInf ratComplexNZ (closureIndex (HarmonicBalls.cluster μ ρ 0 t) ρ δ)
        (fun x => leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x) ∧
      ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x (Λ t)ᶜ →
        marginInf ratComplexNZ (closureIndex (HarmonicBalls.cluster μ ρ 0 t) ρ δ)
            (fun x => leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x) ≤
          leastSupersolution μ ρ 0 t x - 2 * leastSupersolution μ ρ 0 (t / 2) x := by
  have hsub : Λ t ⊆ ball 0 (ρ / 3) := subset_ball_of_le_clusterExitTime hfam hT ht le_rfl
  have hid : Λ t = interior (closure (HarmonicBalls.cluster μ ρ 0 t)) :=
    (hfam.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
  obtain ⟨β, hβ, hβA⟩ := fixedIndexMargin_lower_bound_on_compact hmin hfam hρ hT ht hcover
    (isCompact_marginCore (Λ t) ρ δ) (marginCore_subset hδ)
  obtain ⟨p, hp, -⟩ := ratComplexNZ_meets_open isOpen_univ Set.univ_nonempty
  have hIΛ : closureIndex (HarmonicBalls.cluster μ ρ 0 t) ρ δ ⊆ marginIndex (Λ t) ρ δ := by
    rw [hid]
    exact closureIndex_subset_marginIndex
  have hIS : closureIndex (HarmonicBalls.cluster μ ρ 0 t) ρ δ ⊆ closedBall (0 : ℂ) ρ :=
    fun q hq => mem_closedBall_zero_iff.2 hq.1.le
  have happ : ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x (Λ t)ᶜ →
      ∀ ε : ℝ, 0 < ε → ∃ q ∈ ratComplexNZ, q ∈ closureIndex (HarmonicBalls.cluster μ ρ 0 t) ρ δ ∧ dist q x < ε := by
    intro x hx hxd ε hε
    have hball : ball x (δ / 2) ⊆ closure (HarmonicBalls.cluster μ ρ 0 t) := by
      refine (ball_subset_of_infDist hxd).trans ?_
      rw [hid]
      exact interior_subset
    exact closureIndex_near hρ hδ hx hball hε
  obtain ⟨h1, h2⟩ := marginInf_pathwise_index ⟨p, hp⟩ (compl_cluster_nonempty hfam hρ hT ht)
    (margin_continuousOn_closedBall hfam hρ hT ht) hβA hIΛ hIS happ
  exact ⟨β, hβ, h1, h2⟩

end MatedCRT.S5c
