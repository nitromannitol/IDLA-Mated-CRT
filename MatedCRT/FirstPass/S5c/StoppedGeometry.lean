import MatedCRT.Defs.Setting
import MatedCRT.FirstPass.S5c.MassComparison

/-!
# FIRST PASS, Lemma 5.3 (three-inputs section 3, A5): the stopped geometry, and (3.4) on the stopped event

Deterministic. Let `T = clusterExitTime Λ ρ = sup {u > 0 : Λ_u ⊆ B_{ρ/3}}` (paper eq:cluster-stopping-time, line 1589).
If `t < T` then for every `0 < s ≤ t` the set `Λ_s` lies in `B_{ρ/3}`: some `u > t` in the qualifying set exists, and
monotonicity of `Λ` (`SatisfiesHarmonicBallConditions.monotoneOn`) gives `Λ_s ⊆ Λ_u ⊆ B_{ρ/3}`. Hence Theorem 2.3(c)
(`SatisfiesObstacleCharacterization`, with `r = ρ/3 < ρ`) makes each `v_s = leastSupersolution μ ρ 0 s` continuous on
`B̄_ρ`, and MassComparison.leastSupersolution_div_le gives `v_s/s ≤ v_u/u` on `B̄_ρ` for `0 < s ≤ u ≤ t`.
No new frozen input.
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric

/-- A5: on the stopped event `{t < clusterExitTime Λ ρ}`, every `Λ_s` with `0 < s ≤ t` lies in `B_{ρ/3}`. -/
theorem subset_ball_of_le_clusterExitTime {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t s : ℝ} (hT : t < clusterExitTime Λ ρ) (hs : 0 < s)
    (hst : s ≤ t) : Λ s ⊆ ball 0 (ρ / 3) := by
  have hne : {u : ℝ | 0 < u ∧ Λ u ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    unfold clusterExitTime at hT
    rw [h, Real.sSup_empty] at hT
    linarith
  obtain ⟨u, ⟨hu, huB⟩, htu⟩ := exists_lt_of_lt_csSup hne (by unfold clusterExitTime at hT; exact hT)
  have hmono : Λ s ≤ Λ u := hfam.2.1.monotoneOn hs hu (le_trans hst htu.le)
  exact fun x hx => huB (hmono hx)

/-- On the stopped event, the least supersolution at every mass `0 < s ≤ t` is continuous on `B̄_ρ` (Theorem 2.3(c),
through `SatisfiesObstacleCharacterization` at radius `ρ/3 < ρ`). -/
theorem continuousOn_leastSupersolution_of_le_clusterExitTime {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t s : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ)
    (hs : 0 < s) (hst : s ≤ t) :
    ContinuousOn (leastSupersolution μ ρ 0 s) (closedBall 0 ρ) :=
  (hfam.2.2 s (ρ / 3) hs (by linarith) (subset_ball_of_le_clusterExitTime hfam hT hs hst) ρ
    (by linarith)).2.1

/-- Conclusion (3.4) on the stopped event: for `0 < s ≤ u ≤ t` and `T = clusterExitTime Λ ρ`, `t < T` gives
`v_s(x)/s ≤ v_u(x)/u` for every `x ∈ B̄_ρ`. -/
theorem leastSupersolution_div_le_of_le_clusterExitTime {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hfam : IsConeHarmonicBallFamily μ Λ) {ρ t s u : ℝ} (hρ : 0 < ρ) (hT : t < clusterExitTime Λ ρ)
    (hs : 0 < s) (hsu : s ≤ u) (hut : u ≤ t) :
    ∀ x ∈ closedBall (0 : ℂ) ρ,
      leastSupersolution μ ρ 0 s x / s ≤ leastSupersolution μ ρ 0 u x / u :=
  leastSupersolution_div_le hρ hs hsu
    (continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT hs (hsu.trans hut))
    (continuousOn_leastSupersolution_of_le_clusterExitTime hfam hρ hT (lt_of_lt_of_le hs hsu) hut)

end MatedCRT.S5c
