import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapVolumeGrowthScaling
import HarmonicBalls.Proofs.Sec5.CompactGeneralDomainCompatibility

/-! Transfer of compact cluster boundaries between concentric discs. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- A compactly contained disc cluster agrees with the cluster in any larger
concentric disc. -/
theorem cluster_eq_larger_disc_of_compact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r R βm βp : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hV : VolumeGrowth μ r βm βp)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) {t : ℝ} (ht : 0 < t)
    (hcl : closure (cluster μ r z t) ⊆ ball 0 r) :
    cluster μ r z t = cluster μ R z t := by
  obtain ⟨_, _, hmem⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hr hV hz ht
  have hleast : leastSupersolutionOn μ (ball 0 r) z t = leastSupersolution μ r z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hr.ne']
  have hadm : leastSupersolutionOn μ (ball 0 r) z t ∈ supersolutionsOn μ (ball 0 r) z t := by
    simpa only [hleast, supersolutionsOn_ball μ hr.ne'] using hmem
  have h := clusterOn_eq_cluster_of_compact_containment isOpen_ball (ball_subset_ball hrR) hz ht hadm
    (by simpa only [clusterOn_ball μ hr.ne'] using hcl)
  simpa only [clusterOn_ball μ hr.ne'] using h

/-- Null boundary mass in an enclosing disc transfers to a compactly
contained cluster in the smaller disc. -/
theorem measure_frontier_cluster_eq_zero_of_larger_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r R βm βp : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hV : VolumeGrowth μ r βm βp)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) {t : ℝ} (ht : 0 < t)
    (hcl : closure (cluster μ r z t) ⊆ ball 0 r)
    (hnull : μ (frontier (cluster μ R z t) ∩ ball 0 R) = 0) :
    μ (frontier (cluster μ r z t)) = 0 := by
  have heq := cluster_eq_larger_disc_of_compact hμ hr hrR hV hz ht hcl
  have hsub : frontier (cluster μ r z t) ⊆ ball 0 R :=
    frontier_subset_closure.trans (hcl.trans (ball_subset_ball hrR))
  have hinter : frontier (cluster μ r z t) ∩ ball 0 R = frontier (cluster μ r z t) :=
    inter_eq_left.mpr hsub
  rw [← heq, hinter] at hnull
  exact hnull

/-- The fixed-time reduction needs frontier nullity only in an enclosing disc. -/
theorem ae_no_regularization_defect_of_enclosing_frontier_and_restricted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : AEMeasurable μ P) {r R t γ : ℝ} {z : ℂ}
    (hr : 0 < r) (hrR : r ≤ R) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 r)
    (hvolume : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) r βm βp)
    (hfront : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      μ ω (frontier (cluster (μ ω) R z s) ∩ ball 0 R) = 0)
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 r)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 r)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      interior (closure (cluster (μ ω) r z t)) = cluster (μ ω) r z t := by
  apply ae_no_regularization_defect_of_restricted_law P μ hμm hr ht hγ hz _ hlaw
  filter_upwards [hvolume, hfront] with ω hω hf
  obtain ⟨βm, βp, hlocal, hV⟩ := hω
  refine ⟨βm, βp, hlocal, hV, ?_⟩
  intro s hs hc
  exact measure_frontier_cluster_eq_zero_of_larger_disc hlocal hr hrR hV hz hs hc (hf s hs)

end MatedCRT
