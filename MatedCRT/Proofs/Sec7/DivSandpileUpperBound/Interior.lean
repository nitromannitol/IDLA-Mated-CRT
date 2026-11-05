import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeShell

/-! Graph-interior containment from Euclidean localization. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric _root_.HarmonicBalls Filter Topology

/-- If the cells of the graph closure lie inside a ball, the original vertices lie
in the graph interior of the interior cell vertices of that ball. -/
theorem subset_graphInterior_of_fillClosure_subset_ball
    {m : ℤ → ℤ → ℕ} {ε ρ : ℝ} {η : ℝ → ℂ} {A : Set ℤ}
    (hε : 0 ≤ ε) (hfill : fillCells ε η (vClosure m A) ⊆ ball 0 ρ) :
    A ⊆ vInterior m (ballInterior ε η ρ) := by
  have hcell : ∀ a ∈ vClosure m A, a ∈ ballInterior ε η ρ := by
    intro a ha
    have hsub : cell ε η a ⊆ ball 0 ρ := by
      intro z hz
      exact hfill (mem_iUnion₂.mpr ⟨a, ha, hz⟩)
    have hnonempty : (cell ε η a).Nonempty := ⟨vertexPoint ε η a, vertexPoint_mem_own_cell hε η a⟩
    obtain ⟨z, hz⟩ := hnonempty
    refine ⟨⟨z, hz, hsub hz⟩, ?_⟩
    rintro ⟨w, hw, hwfront⟩
    exact (disjoint_frontier_iff_isOpen.mpr isOpen_ball).le_bot ⟨hwfront, hsub hw⟩
  intro a ha
  refine ⟨hcell a (Or.inl ha), ?_⟩
  intro b hab
  apply hcell b
  by_cases hb : b ∈ A
  · exact Or.inl hb
  · exact Or.inr ⟨hb, a, ha, hab⟩

/-- Before the cluster exit time, the continuum harmonic ball lies in `B_(ρ/3)`. -/
theorem coneFamily_subset_before_exit {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    {ρ t : ℝ} (hfam : IsConeHarmonicBallFamily μ Λ) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) : Λ t ⊆ ball 0 (ρ / 3) := by
  unfold clusterExitTime at hT
  have hnonempty : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
    by_contra h
    have hempty : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Real.sSup_empty] at hT
    linarith
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hnonempty hT
  exact (hfam.2.1.monotoneOn ht hs.1 hts.le).trans hs.2

/-- A sufficiently small closed neighborhood of a set in `B_(ρ/3)` lies in `B_ρ`. -/
theorem outerNbhd_subset_ball_of_subset_third {ρ δ : ℝ} {X : Set ℂ}
    (hρ : 0 < ρ) (hδ : δ < ρ / 3) (hX : X ⊆ ball 0 (ρ / 3)) :
    outerNbhd δ X ⊆ ball 0 ρ := by
  change cthickening δ X ⊆ ball 0 ρ
  intro z hz
  have hz' := cthickening_subset_iUnion_closedBall_of_lt X (by linarith : 0 < ρ / 3) hδ hz
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz'
  have hy' := hX hy
  rw [mem_ball] at hy' ⊢
  rw [mem_closedBall] at hzy
  linarith [dist_triangle z y (0 : ℂ)]

/-- Filled localization at every positive radius also gives the graph-interior
containment required to compare the stopped and global sandpiles. -/
theorem stopped_interior_of_filled_localization
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (ρ t : ℝ) (hρ : 0 < ρ) (ht : 0 < t)
    (hfilled : ∀ d : ℝ, 0 < d → d < ρ →
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        fillCells ε (S.η ω) (insert 0 (vClosure (S.mult ε ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆ outerNbhd d (Λ ω t)})
    (δ : ℝ) (hδ : 0 < δ) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆
        vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) ∧
      fillCells ε (S.η ω) (insert 0 (vClosure (S.mult ε ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) ⊆ outerNbhd δ (Λ ω t)} := by
  let d := min δ (ρ / 3) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdδ : d ≤ δ := by dsimp [d]; have := min_le_left δ (ρ / 3); linarith
  have hdρ : d < ρ / 3 := by dsimp [d]; have := min_le_right δ (ρ / 3); linarith
  have hsmall := hfilled d hd (by linarith)
  unfold TendsToOneOn at hsmall ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
    (Eventually.of_forall fun _ => zero_le) ?_
  apply eventually_nhdsWithin_of_forall
  intro ε hε
  apply measure_mono_ae
  filter_upwards [hΛ] with ω hfam
  intro hbad
  refine ⟨hbad.1, ?_⟩
  intro hloc
  have hball : fillCells ε (S.η ω) (vClosure (S.mult ε ω)
      (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)) ⊆ ball 0 ρ := by
    intro z hz
    apply outerNbhd_subset_ball_of_subset_third hρ hdρ
      (coneFamily_subset_before_exit hfam ht hbad.1)
    apply hloc
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, Or.inr ha, hza⟩
  apply hbad.2
  refine ⟨subset_graphInterior_of_fillClosure_subset_ball hε.le hball, ?_⟩
  exact hloc.trans (cthickening_mono hdδ _)

end MatedCRT.Sec7
