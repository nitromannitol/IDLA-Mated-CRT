import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ExitTime

/-! # Countable tests for harmonic-ball exit times -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology

/-- The mass identity and local finiteness bound the times at which the
harmonic ball is contained in a fixed bounded ball. -/
theorem coneFamily_exitTimes_bddAbove {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ) (ρ : ℝ) :
    BddAbove {t : ℝ | 0 < t ∧ Λ t ⊆ ball 0 (ρ / 3)} := by
  refine ⟨(μ (closedBall 0 (ρ / 3))).toReal, ?_⟩
  intro t ht
  apply (ENNReal.ofReal_le_iff_le_toReal (isCompact_closedBall (0 : ℂ) (ρ / 3)).measure_lt_top.ne).mp
  rw [← hΛ.2.1.measure_eq t ht.1]
  exact measure_mono (ht.2.trans ball_subset_closedBall)

/-- Strictly before the exit time, some later rational time still has its
harmonic ball inside the comparison ball, and conversely. -/
theorem lt_clusterExitTime_iff_exists_rat {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    {ρ t : ℝ} (ht : 0 < t) :
    t < clusterExitTime Λ ρ ↔ ∃ q : ℚ, t < q ∧ Λ q ⊆ ball 0 (ρ / 3) := by
  constructor
  · intro hT
    have hnonempty : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)}.Nonempty := by
      by_contra h
      have hempty : {s : ℝ | 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp h
      simp only [clusterExitTime, hempty, Real.sSup_empty] at hT
      linarith
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hnonempty hT
    obtain ⟨q, htq, hqs⟩ := exists_rat_btwn hts
    exact ⟨q, htq, (hΛ.2.1.monotoneOn (ht.trans htq) hs.1 hqs.le).trans hs.2⟩
  · rintro ⟨q, htq, hq⟩
    apply lt_of_lt_of_le htq
    exact le_csSup (coneFamily_exitTimes_bddAbove hΛ ρ) ⟨ht.trans htq, hq⟩

/-- Containment of an open set in an open ball is determined by its points in
any dense set. The closed-ball test also detects tangency to the boundary. -/
theorem isOpen_subset_ball_iff_dense {D C : Set ℂ} (hD : IsOpen D)
    (hC : Dense C) (r : ℝ) :
    D ⊆ ball 0 r ↔ ∀ z ∈ C, z ∈ D → z ∈ closedBall 0 r := by
  constructor
  · exact fun h z _ hz => ball_subset_closedBall (h hz)
  · intro h
    have hsub : D ⊆ closedBall 0 r := by
      intro x hx
      by_contra hx'
      obtain ⟨z, hzC, hzD, hzout⟩ := hC.exists_mem_open
        (hD.inter isClosed_closedBall.isOpen_compl) ⟨x, hx, hx'⟩
      exact hzout (h z hzC hzD)
    simpa only [interior_closedBall'] using interior_maximal hsub hD

/-- If point membership at rational times is measurable, then the cluster
exit event is null measurable. The family need only satisfy its harmonic-ball
properties almost surely. -/
theorem nullMeasurableSet_lt_clusterExitTime_of_membership
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Λ : Ω → ℝ → Set ℂ)
    (hfam : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω))
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hmem : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (z : ℂ), NullMeasurableSet {ω | z ∈ Λ ω q} P)
    (ρ t : ℝ) (ht : 0 < t) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} P := by
  classical
  obtain ⟨C, hCcount, hCdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable C := hCcount.to_subtype
  let K : ℚ → Set Ω := fun q => {ω | ∀ z : C, (z : ℂ) ∈ Λ ω q → (z : ℂ) ∈ closedBall 0 (ρ / 3)}
  have hK : ∀ q : ℚ, 0 < (q : ℝ) → NullMeasurableSet (K q) P := by
    intro q hq
    have hKz : ∀ z : C, NullMeasurableSet {ω | (z : ℂ) ∈ Λ ω q → (z : ℂ) ∈ closedBall 0 (ρ / 3)} P := by
      intro z
      by_cases hz : (z : ℂ) ∈ closedBall 0 (ρ / 3)
      · simp [hz]
      · convert (hmem q hq z).compl using 1
        ext ω
        simp [hz]
    convert NullMeasurableSet.iInter hKz using 1
    ext ω
    simp [K]
  let E : Set Ω := {ω | ∃ q : ℚ, t < q ∧ ω ∈ K q}
  have hE : NullMeasurableSet E P := by
    have hq : ∀ q : ℚ, NullMeasurableSet {ω | t < q ∧ ω ∈ K q} P := by
      intro q
      by_cases htq : t < q
      · simpa [htq] using hK q (ht.trans htq)
      · simp [htq]
    convert NullMeasurableSet.iUnion hq using 1
    ext ω
    simp [E]
  apply hE.congr
  filter_upwards [hfam, hloc] with ω hω hμ
  let : IsLocallyFiniteMeasure (μ ω) := hμ
  apply propext
  change (∃ q : ℚ, t < q ∧ ω ∈ K q) ↔ _
  rw [lt_clusterExitTime_iff_exists_rat hω ht]
  apply exists_congr
  intro q
  apply and_congr_right
  intro htq
  have hopen : IsOpen (Λ ω q) := by
    rw [← hω.2.1.isRegularOpen q (ht.trans htq)]
    exact isOpen_interior
  simpa [K] using (isOpen_subset_ball_iff_dense hopen hCdense (ρ / 3)).symm

end MatedCRT
