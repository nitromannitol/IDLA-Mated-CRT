import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ContinuumFrontier

/-! An annulus around the harmonic-ball frontier. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric _root_.HarmonicBalls

/-- Before exit, a thin frontier neighborhood lies in an annulus separated from
the source, and the continuum obstacle gap is uniformly small there. -/
theorem coneFamily_exists_frontier_annulus
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t c q : ℝ}
    (hfam : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ)
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) (hq : 0 < q) :
    ∃ d : ℝ, 0 < d ∧ ∃ O : Set ℂ,
      O ⊆ ball 0 ρ ∧ O ⊆ closedBall 0 ρ \ {0} ∧ 0 < infDist (0 : ℂ) O ∧
      cthickening (2 * d) (frontier (Λ t)) ⊆ O ∧
      ∀ x ∈ cthickening (2 * d) (frontier (Λ t)),
        c * (leastSupersolution μ ρ 0 t x - (-t * greenFunction (ball 0 ρ) 0 x)) < q := by
  have hopen : IsOpen (Λ t) := (hfam.1 t ht).1
  have hzero : (0 : ℂ) ∈ Λ t := (hfam.1 t ht).2.1
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let s : ℝ := min (r / 2) (ρ / 4)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsρ : s < ρ / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let O : Set ℂ := ball (0 : ℂ) ρ \ closedBall 0 s
  have hOopen : IsOpen O := isOpen_ball.sdiff isClosed_closedBall
  have hO1 : O ⊆ ball (0 : ℂ) ρ := sdiff_subset
  have hO2 : O ⊆ closedBall (0 : ℂ) ρ \ {0} := by
    intro x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    intro hx0
    apply hx.2
    simpa [Set.mem_singleton_iff.mp hx0] using (mem_closedBall_self hs.le : (0 : ℂ) ∈ closedBall 0 s)
  have hfront := coneFamily_frontier_compact_and_punctured hfam hρ ht hT
  have hfrontO : frontier (Λ t) ⊆ O := by
    intro x hx
    refine ⟨(hfront.2 hx).1, ?_⟩
    intro hxs
    have hxr : x ∈ ball (0 : ℂ) r := by
      rw [mem_closedBall] at hxs
      rw [mem_ball]
      linarith
    have hxΛ := hrsub hxr
    exact (disjoint_left.mp disjoint_interior_frontier)
      (by simpa [hopen.interior_eq] using hxΛ) hx
  have hne : O.Nonempty := by
    refine ⟨((ρ / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      linarith
    · rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      linarith
  have hdist : 0 < infDist (0 : ℂ) O := by
    refine lt_of_lt_of_le hs ((le_infDist hne).2 ?_)
    intro x hx
    have hx' := hx.2
    rw [mem_closedBall] at hx'
    rw [dist_comm]
    exact le_of_not_ge hx'
  obtain ⟨hcont, hzeroGap⟩ := coneFamily_gap_continuous_and_zero_on_frontier (c := c) hfam hρ ht hT
  obtain ⟨d, hd, hsmall⟩ := exists_frontier_neighborhood_of_continuous_zero
    hfront.1 hOopen hfrontO (hcont.mono (fun x hx => ⟨hO1 hx, (hO2 hx).2⟩)) hzeroGap hq
  refine ⟨d / 2, by positivity, O, hO1, hO2, hdist, ?_, ?_⟩
  · intro x hx
    apply (hsmall x ?_).1
    convert hx using 1; ring
  · intro x hx
    apply (hsmall x ?_).2
    convert hx using 1; ring

end MatedCRT.Sec7
