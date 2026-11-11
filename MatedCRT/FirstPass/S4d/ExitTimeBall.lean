import MatedCRT.Defs.Setting

/-!
# FIRST PASS, Proposition 4.2: the stopped family lies in the stopping ball

For a realization `Λ` of the cone family and `t > 0`, the condition `t < clusterExitTime Λ ρ`
(`T_ρ = sup {u > 0 : Λ_u ⊆ B_{ρ/3}}`, eq:cluster-stopping-time) gives `Λ_t ⊆ B_{ρ/3}`: some later time `u > t` has
`Λ_u ⊆ B_{ρ/3}`, and `Λ_t ⊆ Λ_u` by monotonicity (`SatisfiesHarmonicBallConditions.monotoneOn`). This is the first
reduction and is needed by the deterministic comparison `StrictGapDeterministicComparisonStep`.
-/

namespace MatedCRT

open MeasureTheory Set

/-- `t < T_ρ` and `t > 0` give `Λ_t ⊆ B_{ρ/3}` for a realization of the cone family. -/
theorem subset_ball_of_lt_clusterExitTime {μ : Measure ℂ} {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    {ρ t : ℝ} (ht : 0 < t) (hexit : t < clusterExitTime Λ ρ) : Λ t ⊆ Metric.ball 0 (ρ / 3) := by
  unfold clusterExitTime at hexit
  have hne : {u : ℝ | 0 < u ∧ Λ u ⊆ Metric.ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sSup_empty] at hexit
    linarith
  obtain ⟨u, ⟨hu0, huΛ⟩, htu⟩ := exists_lt_of_lt_csSup hne hexit
  have hmono : Λ t ⊆ Λ u :=
    hΛ.2.1.monotoneOn (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr hu0) htu.le
  exact hmono.trans huΛ

end MatedCRT
