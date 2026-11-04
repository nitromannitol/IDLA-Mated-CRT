import MatedCRT.Defs.Setting

/-! Continuity of the continuum obstacle solution before the cluster exit time. -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls

/-- Before the cluster exit time, monotonicity places the harmonic ball strictly inside
the comparison ball, so the obstacle characterization supplies continuity. -/
theorem coneFamily_leastSupersolution_continuous {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    {ρ t : ℝ} (hfam : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) :
    ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall 0 ρ) := by
  unfold clusterExitTime at hT
  have hnonempty : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    have hempty : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Real.sSup_empty] at hT
    linarith
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hnonempty hT
  have hsub : Λ t ⊆ ball 0 (ρ / 3) :=
    (hfam.2.1.monotoneOn ht hs.1 hts.le).trans hs.2
  exact (hfam.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).2.1

end MatedCRT
