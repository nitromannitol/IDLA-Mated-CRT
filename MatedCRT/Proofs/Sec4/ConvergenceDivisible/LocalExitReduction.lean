import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConvergenceEventMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuumOutsideBall

/-! # Local reduction of exit and convergence-event measurability -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology

/-- Containment of a later regularized local cluster is a null-measurable
outer event for the cone harmonic-ball exit event. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_localExitOuterEvent
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {ρ r t : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ht : 0 < t) :
    NullMeasurableSet {ω | ∃ q : ℚ, t < q ∧
      interior (closure (cluster (S.μ ω) r 0 q)) ⊆ ball 0 (ρ / 3)} S.P := by
  have hq : ∀ q : ℚ, NullMeasurableSet {ω | t < q ∧
      interior (closure (cluster (S.μ ω) r 0 q)) ⊆ ball 0 (ρ / 3)} S.P := by
    intro q
    by_cases htq : t < q
    · simpa [htq] using hS.nullMeasurableSet_regularizedLocalCluster_subset_ball
        hγ hγ2 h27 hr hr1 (ht.trans htq) (ρ / 3)
    · simp [htq]
  convert NullMeasurableSet.iUnion hq using 1
  ext ω
  simp

/-- Strictly before cone-ball exit, the measurable local outer event holds. -/
theorem coneFamily_mem_localExitOuterEvent {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily μ Λ)
    {ρ r t : ℝ} (hρ : 0 < ρ) (hρr : ρ / 3 < r) (ht : 0 < t)
    (hT : t < clusterExitTime Λ ρ) :
    ∃ q : ℚ, t < q ∧ interior (closure (cluster μ r 0 q)) ⊆ ball 0 (ρ / 3) := by
  obtain ⟨q, htq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hΛ ht).mp hT
  have hqpos : 0 < (q : ℝ) := ht.trans htq
  have heq := (hΛ.2.2 q (ρ / 3) hqpos (by linarith) hq r hρr).1
  exact ⟨q, htq, heq ▸ hq⟩

/-- If local-cluster containment forces cone-family containment, the local
outer event exactly determines the cone harmonic-ball exit event almost surely. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_exit_of_local_containment
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {ρ r t : ℝ} (hρ : 0 < ρ) (hρr : ρ / 3 < r)
    (hr1 : r < 1) (ht : 0 < t) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hcontain : ∀ᵐ ω ∂S.P, ∀ q : ℚ, t < q →
      interior (closure (cluster (S.μ ω) r 0 q)) ⊆ ball 0 (ρ / 3) →
        Λ ω q ⊆ ball 0 (ρ / 3)) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P := by
  have hr : 0 < r := (by linarith : 0 < ρ / 3).trans hρr
  have hm := hS.nullMeasurableSet_localExitOuterEvent hγ hγ2 h27 hr hr1 ht (ρ := ρ)
  apply hm.congr
  filter_upwards [hΛ, hcontain, hS.isLQGMeasure] with ω hω hc hμ
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  apply propext
  constructor
  · rintro ⟨q, htq, hq⟩
    exact (lt_clusterExitTime_iff_exists_rat hω ht).mpr ⟨q, htq, hc q htq hq⟩
  · exact coneFamily_mem_localExitOuterEvent hω hρ hρr ht

/-- Lemma 2.7 reduces convergence-event measurability to measurability of
the cone harmonic-ball exit event and the adjacent-cells property. -/
theorem convergenceDivisibleEventMeasurable_of_local_exit
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t δ ε ht _ hε
  have hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite := by
    filter_upwards [ae_locallyFinite_mult_of_adjacentCells hS hγ hγ2 hcell] with ω hω
    exact hω ε hε
  have hpoint : ∀ z : ℂ, AEMeasurable
      (fun ω => leastSupersolution (S.μ ω) ρ 0 t z) S.P := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) ρ
    · exact hS.aemeasurable_leastSupersolution_inside_unit hγ hγ2 h27 hρ hρ1 ht
        (mem_ball_self hρ) hz
    · exact aemeasurable_const.congr (Eventually.of_forall fun ω => by
        symm
        exact leastSupersolution_eq_zero_of_notMem_closedBall (S.μ ω) ρ t 0 z ht.le hz)
  obtain ⟨E, hEsub, hE, hEae⟩ :=
    (hexit γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht).exists_measurable_subset_ae_eq
  have hc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn
      (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) (ball 0 ρ) := by
    filter_upwards [hΛ] with ω hω hωE
    exact continuousOn_const.mul
      ((coneFamily_leastSupersolution_continuous hω hρ ht (hEsub hωE)).mono ball_subset_closedBall)
  obtain ⟨f, hf, hfae⟩ := exists_jointlyMeasurable_on_event S.P (ball (0 : ℂ) ρ)
    isOpen_ball.measurableSet 0 (mem_ball_self hρ) E hE
    (fun ω x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x)
    (fun x => aemeasurable_const.mul (hpoint x)) hc
  have hfc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (fun x => f (ω, x)) (ball 0 ρ) := by
    filter_upwards [hc, hfae] with ω hω hfω hωE
    exact (hω hωE).congr (fun x hx => hfω hωE x hx)
  have hm := hS.nullMeasurableSet_matedLeast_deviation_on_event hγ hγ2 hε ρ t ht hlf
    isOpen_ball isBounded_ball f hf E hE hfc δ
  apply hm.congr
  filter_upwards [hEae, hfae] with ω he hfω
  apply propext
  have he' : ω ∈ E ↔ t < clusterExitTime (Λ ω) ρ := iff_of_eq he
  constructor
  · rintro ⟨hEω, x, hx, hd⟩
    exact ⟨he'.mp hEω, x, hx, by simpa [hfω hEω x hx] using hd⟩
  · rintro ⟨hT, x, hx, hd⟩
    have hEω := he'.mpr hT
    exact ⟨hEω, x, hx, by simpa [hfω hEω x hx] using hd⟩

end MatedCRT
