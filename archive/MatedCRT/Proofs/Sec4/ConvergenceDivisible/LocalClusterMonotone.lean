import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalClusterMeasurable
import HarmonicBalls.Steps.Sec3.ClusterMonotone
import HarmonicBalls.Proofs.SecA.ObstacleMonotone

/-! # Bounded obstacle clusters and cone harmonic balls -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter

/-- A cone harmonic ball represented by a bounded obstacle cluster is contained
in every later regularized obstacle cluster on the same domain. -/
theorem coneFamily_subset_later_localCluster
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {Λ : ℝ → Set ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) {r βm βp : ℝ}
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp)
    {s t a : ℝ} (hs : 0 < s) (hst : s ≤ t) (ha : 0 < a) (har : a < r)
    (hsub : Λ s ⊆ ball 0 a) :
    Λ s ⊆ interior (closure (cluster μ r 0 t)) := by
  rw [(hΛ.2.2 s a hs ha hsub r har).1]
  exact interior_mono (closure_mono (cluster_subset_of_general
    obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
    inferInstance hr hV (mem_ball_self hr) hs hst))

/-- Before exit, every cone harmonic ball is contained in the regularization
of a later bounded obstacle cluster, provided the comparison ball fits inside
the obstacle domain. -/
theorem coneFamily_subset_later_localCluster_before_exit
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {Λ : ℝ → Set ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ) {r βm βp : ℝ}
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp)
    {ρ s t : ℝ} (hρ : 0 < ρ) (hρr : ρ / 3 < r)
    (hs : 0 < s) (hst : s ≤ t) (hT : s < clusterExitTime Λ ρ) :
    Λ s ⊆ interior (closure (cluster μ r 0 t)) := by
  obtain ⟨q, hsq, hq⟩ := (lt_clusterExitTime_iff_exists_rat hΛ hs).mp hT
  have hsub : Λ s ⊆ ball 0 (ρ / 3) :=
    (hΛ.2.1.monotoneOn hs (hs.trans hsq) hsq.le).trans hq
  exact coneFamily_subset_later_localCluster hΛ hr hV hs hst (by linarith) hρr hsub

/-- Lemma 2.7 gives monotonicity in time of bounded obstacle clusters
simultaneously for all positive times, almost surely. -/
theorem MatedCRTEnv.IsValid.ae_localCluster_monotone
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ᵐ ω ∂S.P, ∀ s t, 0 < s → s ≤ t →
      cluster (S.μ ω) r 0 s ⊆ cluster (S.μ ω) r 0 t := by
  filter_upwards [hS.ae_volumeGrowth_inside_unit hγ hγ2 h27 hr1, hS.isLQGMeasure] with
    ω ⟨βm, βp, hV⟩ hμ s t hs hst
  exact cluster_subset_of_general obstacleMonotoneGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ.isLocallyFiniteMeasure hr hV
    (mem_ball_self hr) hs hst

end MatedCRT
