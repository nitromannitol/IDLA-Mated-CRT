import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalExitReduction
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-! # Compatibility of local exit tests -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology

/-- If the volume-growth condition holds on one ball enclosing a cone
harmonic ball, an inner obstacle cluster confined to a smaller ball represents
the cone harmonic ball. -/
theorem coneFamily_eq_localCluster_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {Λ : ℝ → Set ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ)
    {a r b R t βm βp : ℝ} (ha : 0 < a) (har : a < r)
    (hrR : r ≤ R) (hb : 0 < b) (hbR : b < R)
    (hV : VolumeGrowth μ R βm βp) (ht : 0 < t)
    (hbound : Λ t ⊆ ball 0 b)
    (hlocal : interior (closure (cluster μ r 0 t)) ⊆ ball 0 a) :
    Λ t = interior (closure (cluster μ r 0 t)) := by
  have hr : 0 < r := ha.trans har
  have hVr := hV.mono hrR
  have hopen : IsOpen (cluster μ r 0 t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ inferInstance r βm βp hr hVr
      0 (mem_ball_self hr) t ht).2.2.1]
    exact (obstacleNonCoincidenceHarmonicGeneral_holds μ inferInstance r βm βp
      hr hVr 0 (mem_ball_self hr) t ht).1
  have hcluster : cluster μ r 0 t ⊆ ball 0 a :=
    (interior_maximal subset_closure hopen).trans hlocal
  let s : ℝ := (a + r) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have has : a < s := by dsimp [s]; linarith
  have hsr : s ≤ r := by dsimp [s]; linarith
  have hsR : s ≤ R := hsr.trans hrR
  have hclosure : closure (cluster μ r 0 t) ⊆ ball 0 s :=
    (closure_minimal (hcluster.trans ball_subset_closedBall) isClosed_closedBall).trans
      (closedBall_subset_ball has)
  have heq : cluster μ R 0 t = cluster μ r 0 t :=
    obstacleCompatibilityGeneral_holds μ inferInstance R βm βp hV t ht s hsR
      0 (mem_ball_self hs) r ⟨hsr, hrR⟩ hclosure R ⟨hsR, le_rfl⟩
  rw [(hΛ.2.2 t b ht hb hbound R hbR).1, heq]

/-- Under the same local volume-growth assumption, containment of the
regularized local cluster implies containment of the cone harmonic ball. -/
theorem coneFamily_subset_ball_of_localCluster
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {Λ : ℝ → Set ℂ}
    (hΛ : IsConeHarmonicBallFamily μ Λ)
    {a r b R t βm βp : ℝ} (ha : 0 < a) (har : a < r)
    (hrR : r ≤ R) (hb : 0 < b) (hbR : b < R)
    (hV : VolumeGrowth μ R βm βp) (ht : 0 < t)
    (hbound : Λ t ⊆ ball 0 b)
    (hlocal : interior (closure (cluster μ r 0 t)) ⊆ ball 0 a) :
    Λ t ⊆ ball 0 a := by
  rw [coneFamily_eq_localCluster_of_volumeGrowth hΛ ha har hrR hb hbR hV ht hbound hlocal]
  exact hlocal

/-- The exit event is null measurable if, at each rational time whose local
cluster passes the exit test, volume growth holds on some ball enclosing the
harmonic ball. The radius and exponents may depend on the sample and time. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_exit_of_enclosing_volumeGrowth
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (h27 : VolumeGrowthStmt) {ρ r t : ℝ} (hρ : 0 < ρ) (hρr : ρ / 3 < r)
    (hr1 : r < 1) (ht : 0 < t) (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hV : ∀ᵐ ω ∂S.P, ∀ q : ℚ, t < q →
      interior (closure (cluster (S.μ ω) r 0 q)) ⊆ ball 0 (ρ / 3) →
      ∃ b R βm βp : ℝ, 0 < b ∧ b < R ∧ r ≤ R ∧
        Λ ω q ⊆ ball 0 b ∧ VolumeGrowth (S.μ ω) R βm βp) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P := by
  apply hS.nullMeasurableSet_exit_of_local_containment hγ hγ2 h27 hρ hρr hr1 ht Λ hΛ
  filter_upwards [hΛ, hV, hS.isLQGMeasure] with ω hω hvol hμ q htq hlocal
  let : IsLocallyFiniteMeasure (S.μ ω) := hμ.isLocallyFiniteMeasure
  obtain ⟨b, R, βm, βp, hb, hbR, hrR, hbound, hvol⟩ := hvol q htq hlocal
  exact coneFamily_subset_ball_of_localCluster hω (by linarith) hρr hrR hb hbR
    hvol (ht.trans htq) hbound hlocal

end MatedCRT
