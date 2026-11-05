import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialBoundary
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Interior
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitTime
import HarmonicBalls.Proofs.Potential.GreenBall

/-! Continuum obstacle contact on the harmonic-ball frontier. -/

namespace MatedCRT.Sec7

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- Before the cluster exit time, the harmonic-ball frontier is compact,
separated from the source, and contained in the comparison ball. -/
theorem coneFamily_frontier_compact_and_punctured {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    {ρ t : ℝ} (hfam : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ)
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) :
    IsCompact (frontier (Λ t)) ∧ frontier (Λ t) ⊆ ball (0 : ℂ) ρ \ {0} := by
  have hsub := coneFamily_subset_before_exit hfam ht hT
  have hΛopen : IsOpen (Λ t) := (hfam.1 t ht).1
  have hzero : (0 : ℂ) ∈ Λ t := (hfam.1 t ht).2.1
  have hcl : closure (Λ t) ⊆ closedBall (0 : ℂ) (ρ / 3) :=
    closure_minimal (hsub.trans ball_subset_closedBall) isClosed_closedBall
  have hfr : frontier (Λ t) ⊆ closedBall (0 : ℂ) (ρ / 3) :=
    frontier_subset_closure.trans hcl
  refine ⟨(isCompact_closedBall 0 (ρ / 3)).of_isClosed_subset isClosed_frontier hfr, ?_⟩
  intro x hx
  have hxcl := hfr hx
  have hxball : x ∈ ball (0 : ℂ) ρ := by
    rw [mem_closedBall] at hxcl
    rw [mem_ball]
    linarith
  have hxnot : x ∉ Λ t := by
    intro hxin
    exact (disjoint_left.mp disjoint_interior_frontier)
      (by simpa [hΛopen.interior_eq] using hxin) hx
  refine ⟨hxball, ?_⟩
  simpa using (fun hxzero : x = 0 => hxnot (hxzero ▸ hzero))

/-- The continuum obstacle gap is continuous away from the source and vanishes
on the frontier of a harmonic ball before its exit time. -/
theorem coneFamily_gap_continuous_and_zero_on_frontier {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    {ρ t c : ℝ} (hfam : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ)
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) :
    ContinuousOn (fun x => c * (leastSupersolution μ ρ 0 t x -
      (-t * greenFunction (ball 0 ρ) 0 x))) (ball (0 : ℂ) ρ \ {0}) ∧
    ∀ x ∈ frontier (Λ t), c * (leastSupersolution μ ρ 0 t x -
      (-t * greenFunction (ball 0 ρ) 0 x)) = 0 := by
  let U : Set ℂ := ball (0 : ℂ) ρ \ {0}
  let g : ℂ → ℝ := fun x => leastSupersolution μ ρ 0 t x -
    (-t * greenFunction (ball 0 ρ) 0 x)
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hw := coneFamily_leastSupersolution_continuous hfam hρ ht hT
  have hg : ContinuousOn g U := by
    apply (hw.mono (sdiff_subset.trans ball_subset_closedBall)).sub
    exact continuousOn_const.mul ((continuousOn_greenFunction_ball (mem_ball_self hρ)).mono
      (fun x hx => hx.2))
  refine ⟨continuousOn_const.mul hg, ?_⟩
  have hΛopen : IsOpen (Λ t) := (hfam.1 t ht).1
  have hfront := (coneFamily_frontier_compact_and_punctured hfam hρ ht hT).2
  have hsub := coneFamily_subset_before_exit hfam ht hT
  have hrepr : Λ t = interior (closure (cluster μ ρ 0 t)) :=
    (hfam.2.2 t (ρ / 3) ht (by linarith) hsub ρ (by linarith)).1
  let V : Set ℂ := U ∩ g ⁻¹' Ioi 0
  have hVopen : IsOpen V := hg.isOpen_inter_preimage hU isOpen_Ioi
  have hVcluster : V ⊆ cluster μ ρ 0 t := by
    intro x hx
    refine ⟨hx.1.1, Or.inr ?_⟩
    have h : 0 < g x := hx.2
    dsimp [g] at h
    linarith
  have hVΛ : V ⊆ Λ t := by
    rw [hrepr]
    exact interior_maximal (hVcluster.trans subset_closure) hVopen
  intro x hx
  have hxU := hfront hx
  have hxnot : x ∉ Λ t := by
    intro hxin
    exact (disjoint_left.mp disjoint_interior_frontier)
      (by simpa [hΛopen.interior_eq] using hxin) hx
  have hgle : g x ≤ 0 := by
    by_contra h
    exact hxnot (hVΛ ⟨hxU, lt_of_not_ge h⟩)
  have hgge : 0 ≤ g x := by
    dsimp [g]
    have h := le_leastSupersolution (μ := μ) (t := t) ht.le
      (ball_subset_closedBall hxU.1) (by simpa using hxU.2)
    linarith
  have heq : g x = 0 := le_antisymm hgle hgge
  change c * g x = 0
  simp [heq]


/-- The continuum obstacle gap is uniformly small near the frontier of a
harmonic ball before its exit time. -/
theorem coneFamily_exists_frontier_neighborhood_small_gap
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t c q : ℝ}
    (hfam : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ)
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) (hq : 0 < q) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ cthickening d (frontier (Λ t)),
      x ∈ ball (0 : ℂ) ρ \ {0} ∧
      c * (leastSupersolution μ ρ 0 t x -
        (-t * greenFunction (ball 0 ρ) 0 x)) < q := by
  obtain ⟨hcompact, hfront⟩ := coneFamily_frontier_compact_and_punctured hfam hρ ht hT
  obtain ⟨hcontinuous, hzero⟩ :=
    coneFamily_gap_continuous_and_zero_on_frontier (c := c) hfam hρ ht hT
  exact exists_frontier_neighborhood_of_continuous_zero hcompact
    (isOpen_ball.sdiff isClosed_singleton) hfront hcontinuous hzero hq


/-- A cellwise obstacle-gap estimate bounds the initial boundary odometer
once the cells are sufficiently small compared with the frontier neighborhood. -/
theorem coneFamily_initial_boundary_iSup_le
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {ρ t c q : ℝ}
    (hfam : IsConeHarmonicBallFamily μ Λ) (hρ : 0 < ρ)
    (ht : 0 < t) (hT : t < clusterExitTime Λ ρ) (hq : 0 < q) :
    ∃ d : ℝ, 0 < d ∧ ∀ (m : ℤ → ℤ → ℕ) (ε D B : ℝ)
      (η : ℝ → ℂ) (u : ℤ → ℝ),
      0 < ε → 0 ≤ B → Continuous η →
      (∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty) →
      (∀ a ∈ vClosure m (cellVertices ε η (Λ t)), diam (cell ε η a) ≤ D) →
      2 * D ≤ d →
      (∀ a : ℤ, cell ε η a ⊆ ball (0 : ℂ) ρ \ {0} →
        (∀ x ∈ cell ε η a, c * (leastSupersolution μ ρ 0 t x -
          (-t * greenFunction (ball 0 ρ) 0 x)) ≤ q) → ε * u a ≤ B) →
      ε * (⨆ a : vBoundary m (cellVertices ε η (Λ t)), u a) ≤ B := by
  obtain ⟨d, hd, hsmall⟩ :=
    coneFamily_exists_frontier_neighborhood_small_gap (c := c) hfam hρ ht hT hq
  refine ⟨d, hd, ?_⟩
  intro m ε D B η u hε hB hη hadj hdiam hD hbound
  have hsub := cthickening_mono hD (frontier (Λ t))
  apply initial_boundary_iSup_le_of_frontier_gap hε hB hη (hfam.1 t ht).1 hadj hdiam
    (fun x hx => (hsmall x (hsub hx)).1) ?_ hbound
  exact fun x hx => (hsmall x (hsub hx)).2.le


/-- If the cells meeting a set inside a smaller ball are sufficiently small,
then cells in their graph closure meet the larger ball. -/
theorem cellVertices_closure_subset_ball
    {m : ℤ → ℤ → ℕ} {ε D r R : ℝ} {η : ℝ → ℂ} {O : Set ℂ}
    (hη : Continuous η) (hO : O ⊆ ball (0 : ℂ) r) (hD : r + D < R)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ cellVertices ε η O, diam (cell ε η a) ≤ D) :
    vClosure m (cellVertices ε η O) ⊆ cellVertices ε η (ball (0 : ℂ) R) := by
  intro b hb
  rcases hb with hb | ⟨_, a, ha, hab⟩
  · have hdiam_b := hdiam b hb
    obtain ⟨x, hxb, hxO⟩ := hb
    refine ⟨x, hxb, ?_⟩
    have hx := hO hxO
    rw [mem_ball] at hx ⊢
    have : 0 ≤ D := (diam_nonneg).trans hdiam_b
    linarith
  · have hdiam_a := hdiam a ha
    obtain ⟨x, hxa, hxO⟩ := ha
    obtain ⟨y, hya, hyb⟩ := hadj a b hab
    refine ⟨y, hyb, ?_⟩
    have hbd : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
    have hdist := (dist_le_diam_of_mem hbd hya hxa).trans hdiam_a
    have hx := hO hxO
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle y x (0 : ℂ)]

end MatedCRT.Sec7
