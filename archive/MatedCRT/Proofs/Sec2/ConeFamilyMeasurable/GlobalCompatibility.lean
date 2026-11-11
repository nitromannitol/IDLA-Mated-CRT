import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ContactTransfer
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import HarmonicBalls.Steps.Sec5.StrongCompatibility
import HarmonicBalls.Proofs.Sec5.CompactGeneralDomainCompatibility

/-! # Local validity from global harmonic-ball compatibility -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls TopologicalSpace

/-- A global cone harmonic-ball family gives the fixed-disc local family
whenever compactly contained fixed-disc clusters have the same closure. -/
theorem threeQuarterDiskLocalValidity_of_global_family
    {ν : Measure ℂ} (hloc : IsLocallyFiniteMeasure ν)
    (hvol : ∃ βm βp, VolumeGrowth ν (3 / 4) βm βp)
    {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily ν Λ)
    (hcompat : ∀ t : ℝ, 0 < t →
      closure (cluster ν (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) →
      closure (Λ t) = closure (cluster ν (3 / 4) 0 t)) :
    ThreeQuarterDiskLocalValidity ν := by
  intro r hr
  let C : Ioi (0 : ℝ) → Set ℂ := fun t =>
    interior (closure (cluster ν (3 / 4) 0 t))
  have hmono : Monotone C := by
    intro s t hst
    apply interior_mono (closure_mono ?_)
    obtain ⟨βm, βp, hV⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
      (mem_ball_self (by norm_num)) s.property hst
  have hbound : closure (C ⟨r, r.property⟩) ⊆ closedBall (0 : ℂ) (1 / 2) :=
    closure_subset_closedBall_of_halfBallTest isOpen_interior hr
  refine ⟨Λ, hΛ.isConeHarmonicBallFamilyOn r.property, ?_⟩
  intro t ht
  have hopen : IsOpen (cluster ν (3 / 4) 0 t) := by
    obtain ⟨βm, βp, hV⟩ := hvol
    exact (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
      (mem_ball_self (by norm_num)) ht.1).1
  have hcl : closure (cluster ν (3 / 4) 0 t) ⊆ ball (0 : ℂ) (3 / 4) := by
    have hsub : closure (C ⟨t, ht.1⟩) ⊆ ball (0 : ℂ) (3 / 4) :=
      (closure_mono (hmono ht.2.le)).trans (hbound.trans (closedBall_subset_ball (by norm_num)))
    change closure (regularizedCluster ν (3 / 4) 0 t) ⊆ ball 0 (3 / 4) at hsub
    rw [closure_regularizedCluster_eq_of_isOpen hopen] at hsub
    exact hsub
  calc
    interior (closure (cluster ν (3 / 4) 0 t)) = interior (closure (Λ t)) :=
      congrArg interior (hcompat t ht.1 hcl).symm
    _ = Λ t := hΛ.2.1.isRegularOpen t ht.1

/-- A global cone harmonic-ball family determines the compact fixed-disc
clusters, so it yields their local validity under the volume-growth bound. -/
theorem threeQuarterDiskLocalValidity_of_global_cone_family
    {ν : Measure ℂ} (hloc : IsLocallyFiniteMeasure ν)
    (hvol : ∃ βm βp, VolumeGrowth ν (3 / 4) βm βp)
    {Λ : ℝ → Set ℂ} (hΛ : IsConeHarmonicBallFamily ν Λ) :
    ThreeQuarterDiskLocalValidity ν := by
  apply threeQuarterDiskLocalValidity_of_global_family hloc hvol hΛ
  intro t ht hcl
  obtain ⟨βm, βp, hV⟩ := hvol
  obtain ⟨_, _, hv⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hloc (by norm_num : (0 : ℝ) < 3 / 4) hV (mem_ball_self (by norm_num)) ht
  have hv' : leastSupersolutionOn ν (ball 0 (3 / 4)) 0 t ∈
      supersolutionsOn ν (ball 0 (3 / 4)) 0 t := by
    have heq : leastSupersolutionOn ν (ball 0 (3 / 4)) 0 t =
        leastSupersolution ν (3 / 4) 0 t := by
      funext x
      simp only [leastSupersolutionOn, leastSupersolution,
        supersolutionsOn_ball ν (by norm_num : (3 / 4 : ℝ) ≠ 0)]
    rw [heq, supersolutionsOn_ball ν (by norm_num : (3 / 4 : ℝ) ≠ 0)]
    exact hv
  have hcl' : closure (clusterOn ν (ball 0 (3 / 4)) 0 t) ⊆ ball 0 (3 / 4) := by
    rwa [clusterOn_ball ν (by norm_num : (3 / 4 : ℝ) ≠ 0)]
  obtain ⟨s₀, hs₀⟩ := (hΛ.2.1.isBounded t ht).subset_ball (0 : ℂ)
  let s : ℝ := max s₀ 1
  let R : ℝ := max s (3 / 4) + 1
  have hs : 0 < s := by dsimp [s]; linarith [le_max_right s₀ 1]
  have hsR : s < R := by dsimp [R]; linarith [le_max_left s (3 / 4)]
  have hsmallR : (3 / 4 : ℝ) ≤ R := by dsimp [R]; linarith [le_max_right s (3 / 4)]
  have hΛs : Λ t ⊆ ball (0 : ℂ) s := hs₀.trans (ball_subset_ball (le_max_left _ _))
  have heq := (hΛ.2.2 t s ht hs hΛs R hsR).1
  have hclusters := clusterOn_eq_cluster_of_compact_containment isOpen_ball
    (ball_subset_ball hsmallR) (mem_ball_self (by norm_num)) ht hv' hcl'
  rw [clusterOn_ball ν (by norm_num : (3 / 4 : ℝ) ≠ 0)] at hclusters
  rw [heq, ← hclusters]
  have hopen : IsOpen (cluster ν (3 / 4) 0 t) :=
    (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
      (mem_ball_self (by norm_num)) ht).1
  change closure (regularizedCluster ν (3 / 4) 0 t) = _
  exact closure_regularizedCluster_eq_of_isOpen hopen

end MatedCRT
